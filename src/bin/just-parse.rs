use structopt::StructOpt;

#[derive(Debug, StructOpt)]
struct Sketch {
    filename: std::path::PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Sketch::from_args();

    let buffer = std::fs::read(args.filename)?;
    let object = object::File::parse(&*buffer)?;

    debugdb::parse_file(&object)?;

    Ok(())
}
