use std::path::Path;
use std::{fs, io};

pub const LIB_VERSION: &str = rat::VERSION;

fn main() {
    let crate_lib_path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .join("lib");

    let host_lib_path = rat::home_dir().join("lib").join(LIB_VERSION);

    println!("cargo::rerun-if-changed={}", crate_lib_path.display());
    println!("cargo::rerun-if-changed={}", host_lib_path.display());

    println!("cargo::warning=removing lib files from: {host_lib_path:?}");
    let _ = fs::remove_dir_all(&host_lib_path);

    println!("cargo::warning= copying lib files from: {crate_lib_path:?} to: {host_lib_path:?}");
    copy_dir(&crate_lib_path, &host_lib_path).unwrap();
}

fn copy_dir(source_path: &Path, dest_path: &Path) -> Result<(), io::Error> {
    assert!(source_path.is_dir());
    assert!(!dest_path.exists() || dest_path.is_dir());

    fs::create_dir_all(dest_path)?;

    for entry in fs::read_dir(source_path)? {
        let entry = entry?;
        let file_type = entry.file_type()?;

        if file_type.is_file() {
            fs::copy(entry.path(), dest_path.join(entry.file_name()))?;
        } else if file_type.is_dir() {
            let dest_dir_path = dest_path.join(entry.file_name());
            fs::create_dir_all(&dest_dir_path)?;
            copy_dir(&entry.path(), &dest_dir_path)?;
        } else {
            return Err(io::Error::other(format!(
                "File: {:?} of type: {:?} is not allowed",
                entry.path(),
                file_type
            )));
        }
    }

    Ok(())
}
