use std::env;
use std::path::PathBuf;

fn main() {
    let manifest_dir = PathBuf::from(env::var("CARGO_MANIFEST_DIR").unwrap());
    let lib_dir = manifest_dir.join("../../.lake/build/lib").canonicalize().unwrap();
    println!("cargo:rustc-link-search=native={}", lib_dir.display());
    println!("cargo:rustc-link-lib=dylib=harmonia_gatekeeper");
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", lib_dir.display());
}
