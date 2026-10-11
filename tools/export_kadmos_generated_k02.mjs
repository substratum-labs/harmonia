#!/usr/bin/env node
// Physical K-02 export. The checker separately pins the reviewed output bytes.
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs';
import {resolve, join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';

const PIN='1ac9422a12ab743a9bbb8b8ad508d37c582637df';
const CONTRACT='kadmos.compiler.k02.v1';
const root=resolve(import.meta.dirname,'..');
const args=process.argv.slice(2);
const value=name=>{const at=args.indexOf(name);return at<0?undefined:args[at+1]};
const kadmos=resolve(value('--kadmos')??'/Users/yong/projects/substratum/kadmos');
const out=resolve(value('--out')??'/private/tmp/t398-k02-fresh');
const tracked=join(root,'conformance/kadmos-generated-k02');
const sha=x=>createHash('sha256').update(x).digest('hex');
const run=(cmd,argv)=>{const r=spawnSync(cmd,argv,{encoding:'utf8'});if(r.status!==0)throw Error(`${cmd}: ${r.stderr}`);return r.stdout.trim()};
if(run('git',['-C',kadmos,'rev-parse','HEAD'])!==PIN)throw Error('Kadmos pin mismatch');
if(run('git',['-C',kadmos,'status','--short'])!=='')throw Error('Kadmos source dirty');
mkdirSync(out,{recursive:true});
const js=join(out,'kadmos-js');mkdirSync(js,{recursive:true});
run(join(kadmos,'node_modules/.bin/tsc'),['-p',join(kadmos,'tsconfig.json'),'--outDir',js]);
const compiler=await import(pathToFileURL(join(js,'src/world_compiler.js')).href);
if(compiler.KADMOS_COMPILER_CONTRACT_VERSION!==CONTRACT)throw Error('compiler contract mismatch');
const files={};const yamlSha256={};
const sources={};
for(const name of ['balance','order_phase']){
  const yaml=readFileSync(join(root,'conformance/kadmos-ir-bridge',`${name}.world.yaml`));
  yamlSha256[name]=sha(yaml);
  const admitted=compiler.parseWorldSpec(yaml.toString('utf8'));
  const ts=compiler.compileWorldSpec(admitted),py=compiler.compileWorldSpecPython(admitted);
  const body={'world_checker.ts':ts.worldCheckerTs,'ports.d.ts':ts.portsDts,
    'world_checker.py':py.worldCheckerPy,'ports.py':py.portsPy,
    'admitted.json':JSON.stringify(admitted)+'\n'};
  const dir=join(out,name);mkdirSync(dir,{recursive:true});
  sources[name]=body;
  for(const [filename,source] of Object.entries(body)){
    const rel=`${name}/${filename}`;const bytes=Buffer.from(source,'utf8');
    files[rel]=sha(bytes);writeFileSync(join(dir,filename),bytes);
    if(args.includes('--check')&&!bytes.equals(readFileSync(join(tracked,rel))))
      throw Error(`tracked emitted bytes differ: ${rel}`);
  }
}
const lean=['import Init','namespace Harmonia.Applications.Kadmos.GeneratedFixtures',
  '-- Complete emitted source strings; semantic certificates are proved separately.'];
for(const name of ['balance','order_phase'])
  for(const [file,suffix] of [['world_checker.ts','TsSource'],['world_checker.py','PySource']])
    lean.push(`def ${name==='balance'?'balance':'order'}${suffix} : String := ${JSON.stringify(sources[name][file])}`);
lean.push('end Harmonia.Applications.Kadmos.GeneratedFixtures','');
const leanBytes=Buffer.from(lean.join('\n'));
writeFileSync(join(out,'Fixtures.lean'),leanBytes);
if(args.includes('--check')&&!leanBytes.equals(readFileSync(join(root,'Harmonia/Applications/Kadmos/Generated/Fixtures.lean'))))
  throw Error('tracked complete Lean source literals differ');
const manifest={kadmosCommit:PIN,compilerContract:CONTRACT,
  oldBridgePin:'fda8c6e42825b35afe5484a4af9d84d9d206ba9a',yamlSha256,files,
  fixturesLeanSha256:sha(leanBytes)};
const manifestText=JSON.stringify(manifest)+'\n';
writeFileSync(join(out,'provenance.json'),manifestText);
if(args.includes('--check')&&manifestText!==readFileSync(join(tracked,'provenance.json'),'utf8'))
  throw Error('tracked provenance differs');
console.log(JSON.stringify({kadmosCommit:PIN,compilerContract:CONTRACT,files}));
