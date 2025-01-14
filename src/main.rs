use std::fs;

use anyhow::Result;
use camino::Utf8PathBuf;

mod parser;

fn main() -> Result<()> {
    let test_file_path = Utf8PathBuf::from("./src/test.ml");
    let test_source = fs::read_to_string(test_file_path)?;

    let p = parser::LangParser::parse(&test_source, "test")?;

    for v in p.ast {
        println!("{:?}", v);
    }

    println!("Hello, world!");
    Ok(())
}
