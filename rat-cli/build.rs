use std::fs;
use std::path::Path;

fn main() {
    let crate_lib_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("lib");

    println!("cargo::rerun-if-changed={}", crate_lib_path.display());

    let host_lib_path = rat::home_dir().join("lib");

    fs::create_dir_all(&host_lib_path).unwrap();

    for entry in fs::read_dir(crate_lib_path).unwrap() {
        let entry = entry.unwrap();

        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), host_lib_path.join(entry.file_name())).unwrap();
        }
    }
}
