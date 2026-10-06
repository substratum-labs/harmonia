#!/usr/bin/env node
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
const root=resolve(import.meta.dirname,'../conformance/kadmos-ir-bridge');
const pin='fda8c6e42825b35afe5484a4af9d84d9d206ba9a';
const hash=b=>createHash('sha256').update(b).digest('hex');
const args=process.argv.slice(2);const arg=k=>args.includes(k)?args[args.indexOf(k)+1]:undefined;
const out=arg('--out')||'/private/tmp/t395-bridge-out';mkdirSync(out,{recursive:true});
const read=p=>readFileSync(p,'utf8');
const fail=m=>{throw Error(m)};
const string=s=>{if(typeof s!=='string')fail('expected string');for(let i=0;i<s.length;i++){const c=s.charCodeAt(i);if(c<32&&![9,10,13].includes(c))fail('control string');if(c>=0xd800&&c<=0xdbff){if(i+1>=s.length||s.charCodeAt(++i)<0xdc00||s.charCodeAt(i)>0xdfff)fail('unpaired surrogate')}else if(c>=0xdc00&&c<=0xdfff)fail('unpaired surrogate')}return JSON.stringify(s)};
const optString=v=>v===undefined?'none':`some ${string(v)}`;
const optInt=v=>v===undefined?'none':`some ${integer(v)}`;
const integer=v=>{if(typeof v!=='number'||!Number.isSafeInteger(v)||Object.is(v,-0))fail(`bad integer ${String(v)}`);return String(v)};
const keys=(v,required,optional,label)=>{if(!v||typeof v!=='object'||Array.isArray(v))fail(`${label}: object`);for(const k of required)if(!Object.hasOwn(v,k))fail(`${label}: missing ${k}`);for(const k of Object.keys(v))if(!required.includes(k)&&!optional.includes(k))fail(`${label}: unknown ${k}`)};
const jsonSourceCheck=s=>{let quoted=false,esc=false;for(let i=0;i<s.length;i++){const c=s[i];if(quoted){if(esc)esc=false;else if(c==='\\')esc=true;else if(c==='"')quoted=false;continue}if(c==='"'){quoted=true;continue}if(c==='-'&&s[i+1]==='0'&&!/[0-9.]/.test(s[i+2]||''))fail('negative zero JSON token')}};
const ensureArray=(v,label)=>{if(!Array.isArray(v))fail(`${label}: array`);return v};
function validateWorld(w){keys(w,['version','name','states','context','invariants','transitions'],['description'],'world');if(w.version!=='kadmos.world.v0')fail('version');string(w.name);if(w.description!==undefined)string(w.description);
 for(const st of ensureArray(w.states,'states')){keys(st,['id'],['initial','terminal','description'],'state');string(st.id);for(const f of ['initial','terminal'])if(st[f]!==undefined&&typeof st[f]!=='boolean')fail(`state ${f}`);if(st.description!==undefined)string(st.description)}
 if(!w.context||typeof w.context!=='object'||Array.isArray(w.context))fail('context object');for(const [name,v] of Object.entries(w.context)){if(!/^[A-Za-z_][A-Za-z_0-9]*$/.test(name))fail('context name');keys(v,['type'],['min','max','default','unit'],'variable');string(v.type);for(const f of ['min','max','default'])if(v[f]!==undefined)integer(v[f]);if(v.unit!==undefined)string(v.unit)}
 for(const inv of ensureArray(w.invariants,'invariants')){keys(inv,['id','predicate'],['description'],'invariant');string(inv.id);string(inv.predicate);if(inv.description!==undefined)string(inv.description)}
 for(const tr of ensureArray(w.transitions,'transitions')){keys(tr,['id','from','to','guard','effects','directive'],[],'transition');for(const f of ['id','from','to'])string(tr[f]);if(typeof tr.guard!=='string'&&typeof tr.guard!=='boolean')fail('guard type');if(typeof tr.guard==='string')string(tr.guard);ensureArray(tr.effects,'effects').forEach(string);if(tr.directive!==null)string(tr.directive)} }
function validateProfile(p){keys(p,['balance','order_phase'],[],'profiles');for(const [key,fields] of Object.entries(p)){ensureArray(fields,`profile ${key}`);const seen=new Set();for(const f of fields){string(f);if(!/^[A-Za-z_][A-Za-z_0-9]*$/.test(f)||seen.has(f))fail('profile field');seen.add(f)}}}
function tokenize(s){const re=/\s+|=>|==|>=|<=|&&|\|\||[()+\-<>!.]|\d+|[A-Za-z_][A-Za-z_0-9]*|'[^'\\]*'/gy;let pos=0,t=[];while(pos<s.length){re.lastIndex=pos;const m=re.exec(s);if(!m)fail(`unsupported expression ${s.slice(pos)}`);pos=re.lastIndex;if(!/^\s+$/.test(m[0]))t.push(m[0])}return t}
const prec={'=>':1,'||':2,'&&':3,'==':4,'>':5,'>=':5,'<':5,'<=':5,'+':6,'-':6};
function expression(s,w,fields,invariant=false){let t=tokenize(s),pos=0;const idx=(xs,x,label)=>{const n=xs.indexOf(x);if(n<0)fail(`unbound ${label} ${x}`);return n};const phases=w.states.map(x=>x.id),contexts=Object.keys(w.context);
 const parse=(min=1)=>{let tok=t[pos++],lhs;if(tok==='('){lhs=parse();if(t[pos++]!==')')fail('missing )')}else if(tok==='!'){lhs=`.not (${parse(7)})`}else if(tok==='true'||tok==='false'){lhs=`.bool ${tok}`}else if(/^\d+$/.test(tok||'')){integer(Number(tok));lhs=`.int ${tok}`}else if(tok==='state'&&t[pos]==='=='&&/^'[^']*'$/.test(t[pos+1]||'')){pos++;lhs=`.stateIs ${idx(phases,t[pos++].slice(1,-1),'phase')}`}else if((tok==='event'||tok==='request')&&t[pos]==='.') {pos++;const name=t[pos++];if(invariant)fail('field in invariant');lhs=`.request ${idx(fields,name,'field')}`}else if(/^[A-Za-z_][A-Za-z_0-9]*$/.test(tok||'')){lhs=`.context ${idx(contexts,tok,'context')}`}else fail(`unsupported atom ${tok}`);
 while(pos<t.length&&prec[t[pos]]>=min){const op=t[pos++],right=parse(prec[op]+(op==='=>'?0:1));const l=`(${lhs})`,r=`(${right})`;lhs=op==='>'?`.not (.le ${l} ${r})`:op==='>='?`.not (.lt ${l} ${r})`:`.${({'=>':'implies','||':'or','&&':'and','==':'eqInt','<':'lt','<=':'le','+':'add','-':'sub'})[op]} ${l} ${r}`;lhs=`(${lhs})`}
 return lhs};const result=parse();if(pos!==t.length)fail(`trailing ${t[pos]}`);return result}
function render(id,w,fields){const names=Object.keys(w.context);const ls=a=>`[${a.join(',')}]`;const st=w.states.map(x=>`⟨${string(x.id)},${x.initial??false},${x.terminal??false},${optString(x.description)}⟩`);const vars=names.map(n=>{const v=w.context[n];return `(${string(n)},⟨${string(v.type)},${optInt(v.min)},${optInt(v.max)},${optInt(v.default)},${optString(v.unit)},none⟩)`});const inv=w.invariants.map(x=>`⟨${string(x.id)},${string(x.predicate)},${optString(x.description)}⟩`);const trs=w.transitions.map(t=>`⟨${string(t.id)},${string(t.from)},${string(t.to)},${typeof t.guard==='boolean'?`.bool ${t.guard}`:`.expr ${string(t.guard)}`},${ls(t.effects.map(string))},${t.directive===null?'none':`some ${string(t.directive)}`}⟩`);
 const raw=`def ${id}Raw : RawWorld := ⟨${string(w.version)},${string(w.name)},${optString(w.description)},${ls(st)},${ls(vars)},${ls(inv)},${ls(trs)},${ls(fields.map(string))},[]⟩`;
 const ef=t=>{const m=/^([A-Za-z_][A-Za-z_0-9]*)\s*=\s*(.+)$/.exec(t);if(!m)fail('effect assignment');return `⟨${idxName(names,m[1])},${expression(m[2],w,fields)}⟩`};const idxName=(xs,x)=>{const n=xs.indexOf(x);if(n<0)fail(`unbound ${x}`);return n};
 const wl=(xs,code)=>`(fun j => (${ls(xs.map(code))})[j])`;
 const candidate=`def ${id}Candidate : World ${w.states.length} ${names.length} ${fields.length} ${w.transitions.length} :=\n  ⟨${wl(w.states,x=>string(x.id))},${wl(w.states,x=>String(x.initial??false))},${wl(w.states,x=>String(x.terminal??false))},${wl(names,string)},${wl(names,n=>{const v=w.context[n];return `⟨${v.min},${v.max},${optInt(v.default)}⟩`})},${wl(fields,string)},${wl(w.transitions,x=>string(x.id))},${wl(w.transitions,t=>`⟨${idxName(w.states.map(x=>x.id),t.from)},${idxName(w.states.map(x=>x.id),t.to)},${typeof t.guard==='boolean'?`.bool ${t.guard}`:expression(t.guard,w,fields)},${ls(t.effects.map(ef))},${t.directive===null?'none':`some ${string(t.directive)}`}⟩`)},${ls(w.invariants.map(x=>`(${string(x.id)},${expression(x.predicate,w,[],true)})`))}⟩`;
 return raw+'\n'+candidate+`\ntheorem ${id}_certificate : checkBridge ${id}Raw ${id}Candidate = .ok ${id}Candidate := by decide +kernel\n`}
const vectorInputs=[
  ['balance_guard_30','event.amount > 0',{balance:100,state:'Ready',event:{amount:30},request:{amount:30}}],
  ['balance_guard_130','event.amount > 0',{balance:100,state:'Ready',event:{amount:130},request:{amount:130}}],
  ['balance_effect_30','balance - event.amount',{balance:100,state:'Ready',event:{amount:30},request:{amount:30}}],
  ['order_invariant_A',"state == 'B' => y == x",{state:'A',x:1,y:0,event:{},request:{}}],
  ['order_invariant_B',"state == 'B' => y == x",{state:'B',x:2,y:2,event:{},request:{}}],
  ['right_assoc','false => true => false',{}],
  ['eager_and','false && (9007199254740991 + 1 < 0)',{}],
  ['eager_or','true || (9007199254740991 + 1 < 0)',{}],
  ['cancellation','(9007199254740991 + 1) - 1',{}]
];
let worlds,command='pinned Kadmos node_modules/.bin/tsc -p tsconfig.json --outDir private-tmp; parseWorldSpec both fixtures';const profiles=JSON.parse(read(join(root,'profiles.json')));validateProfile(profiles);
if(arg('--kadmos')){const path=resolve(arg('--kadmos'));const git=spawnSync('git',['-C',path,'rev-parse','HEAD'],{encoding:'utf8'});if(git.status!==0||git.stdout.trim()!==pin)fail('Kadmos commit');const status=spawnSync('git',['-C',path,'status','--short'],{encoding:'utf8'});if(status.status!==0||status.stdout.trim())fail('Kadmos dirty');const fresh=join(out,'kadmos-fresh');mkdirSync(fresh,{recursive:true});const tsc=spawnSync(join(path,'node_modules/.bin/tsc'),['-p',join(path,'tsconfig.json'),'--outDir',fresh],{encoding:'utf8'});if(tsc.status!==0)fail(`tsc: ${tsc.stderr}`);const {parseWorldSpec}=await import(pathToFileURL(join(fresh,'src/world_compiler.js')).href);worlds={};for(const id of Object.keys(profiles))worlds[id]=parseWorldSpec(read(join(root,`${id}.world.yaml`)));const {evaluate}=await import(pathToFileURL(join(fresh,'src/world_expression.js')).href);const vectors=vectorInputs.map(([id,expression,environment])=>{try{return{id,expression,environment,outcome:{value:evaluate(expression,environment)}}}catch(e){return{id,expression,environment,outcome:{error:String(e)}}}});writeFileSync(join(out,'evaluate-vectors.json'),JSON.stringify(vectors)+'\n');command='pinned Kadmos node_modules/.bin/tsc -p tsconfig.json --outDir private-tmp; parseWorldSpec both fixtures';}
else if(arg('--from-parsed')){const source=read(resolve(arg('--from-parsed')));jsonSourceCheck(source);worlds=JSON.parse(source);writeFileSync(join(out,'evaluate-vectors.json'),read(join(root,'evaluate-vectors.json')));}else fail('use --kadmos or --from-parsed');
keys(worlds,['balance','order_phase'],[],'parsed fixtures');for(const [id,w] of Object.entries(worlds))validateWorld(w);
const parsedText=JSON.stringify(worlds)+'\n';const lean=`import Harmonia.Applications.Kadmos.Bridge.Certificate\nnamespace Harmonia.Applications.Kadmos.BridgeFixtures\nopen Harmonia.Applications.Kadmos.Bridge\nopen Harmonia.Applications.Kadmos\nset_option maxRecDepth 4096\nset_option maxHeartbeats 1000000\n`+Object.entries(worlds).map(([id,w])=>render(id==='order_phase'?'order':id,w,profiles[id])).join('\n')+'\nend Harmonia.Applications.Kadmos.BridgeFixtures\n';
writeFileSync(join(out,'parsed.json'),parsedText);writeFileSync(join(out,'Fixtures.lean'),lean);
const sha={};for(const id of Object.keys(profiles))sha[id]=hash(readFileSync(join(root,`${id}.world.yaml`)));
const vectors=readFileSync(join(out,'evaluate-vectors.json'));
const provenance={kadmosCommit:pin,exporterVersion:'1',checkerVersion:'1',yamlSha256:sha,profilesSha256:hash(readFileSync(join(root,'profiles.json'))),parsedSha256:hash(parsedText),evaluateVectorsSha256:hash(vectors),fixturesLeanSha256:hash(lean),parserCommand:command};writeFileSync(join(out,'provenance.json'),JSON.stringify(provenance)+'\n');
if(args.includes('--check')){for(const [outName,tracked] of [['parsed.json',join(root,'parsed.json')],['Fixtures.lean',resolve(import.meta.dirname,'../Harmonia/Applications/Kadmos/Bridge/Fixtures.lean')],['provenance.json',join(root,'provenance.json')],['evaluate-vectors.json',join(root,'evaluate-vectors.json')]])if(read(join(out,outName))!==read(tracked))fail(`${outName} drift`)}
console.log(JSON.stringify({parsedSha256:provenance.parsedSha256,fixturesLeanSha256:provenance.fixturesLeanSha256,parserCommand:command}));
