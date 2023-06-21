use clap::Parser;

#[derive(Debug, Parser)]
struct Sketch {
    filename: std::path::PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Sketch::parse();

    let buffer = std::fs::read(args.filename)?;
    let object = object::File::parse(&*buffer)?;

    debugdb::parse_file(&object)?;

    Ok(())
}
