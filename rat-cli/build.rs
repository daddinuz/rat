use std::fs;
use std::path::Path;

fn main() {
    let source_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("lib");

    let destination_path = rat::home_dir().join("lib");

    fs::create_dir_all(&destination_path).unwrap();

    for entry in fs::read_dir(source_path).unwrap() {
        let entry = entry.unwrap();

        if entry.file_type().unwrap().is_file() {
            fs::copy(entry.path(), destination_path.join(entry.file_name())).unwrap();
        }
    }
}
