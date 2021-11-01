use structopt::StructOpt;

use debugdb::{Type, Encoding, TypeId};

#[derive(Debug, StructOpt)]
struct TySh {
    filename: std::path::PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = TySh::from_args();

    let buffer = std::fs::read(args.filename)?;
    let object = object::File::parse(&*buffer)?;
    let everything = debugdb::parse_file(&object)?;

    println!("Loaded; {} types found in program.", everything.type_count());
    println!("To quit: ^D or exit");

    let mut rl = rustyline::Editor::<()>::new();
    let prompt = ansi_term::Colour::Green.paint(">> ").to_string();
    'lineloop:
    loop {
        match rl.readline(&prompt) {
            Ok(line) => {
                let line = line.trim();
                let (cmd, rest) = line.split_once(char::is_whitespace)
                    .unwrap_or((line, ""));
                if line.is_empty() {
                    continue 'lineloop;
                }

                rl.add_history_entry(line);

                match cmd {
                    "exit" => break,
                    "help" => {
                        println!("commands:");
                        for (name, _, desc) in COMMANDS {
                            println!("{:12} {}", name, desc);
                        }
                    }
                    _ => {
                        for (name, imp, _) in COMMANDS {
                            if *name == cmd {
                                imp(&everything, rest);
                                continue 'lineloop;
                            }
                        }
                        println!("unknown command: {}", cmd);
                        println!("for help, try: help");
                    }
                }
            }
            Err(rustyline::error::ReadlineError::Interrupted) => {
                println!("^C");
                continue;
            }
            Err(e) => {
                println!("{:?}", e);
                break;
            }
        }
    }

    Ok(())
}

struct Goff(gimli::UnitSectionOffset);

impl std::fmt::Display for Goff {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self.0 {
            gimli::UnitSectionOffset::DebugInfoOffset(gimli::DebugInfoOffset(x)) => {
                write!(f, "<.debug_info+0x{:08x}>", x)
            }
            gimli::UnitSectionOffset::DebugTypesOffset(gimli::DebugTypesOffset(x)) => {
                write!(f, "<.debug_types+0x{:08x}>", x)
            }
        }
    }
}

struct NamedGoff<'a>(&'a debugdb::DebugDb, TypeId);

impl std::fmt::Display for NamedGoff<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let bold = ansi_term::Style::new().bold();
        let dim = ansi_term::Style::new().dimmed();

        let n = if let Some(name) = self.0.type_name(self.1) {
            name
        } else {
            "<anonymous type>".into()
        };

        write!(f, "{}", bold.paint(n))?;
        match self.1.0 {
            gimli::UnitSectionOffset::DebugInfoOffset(gimli::DebugInfoOffset(x)) => {
                write!(f, " {}<.debug_info+0x{:08x}>{}", dim.prefix(), x, dim.suffix())
            }
            gimli::UnitSectionOffset::DebugTypesOffset(gimli::DebugTypesOffset(x)) => {
                write!(f, " {}<.debug_types+0x{:08x}>{}", dim.prefix(), x, dim.suffix())
            }
        }
    }
}

type Command = fn(&debugdb::DebugDb, &str);

static COMMANDS: &[(&str, Command, &str)] = &[
    ("list", cmd_list, "print names of ALL types, or types containing a string"),
    ("info", cmd_info, "print a summary of a type"),
    ("def", cmd_def, "print a type as a pseudo-Rust definition"),
    ("sizeof", cmd_sizeof, "print size of type in bytes"),
    ("alignof", cmd_alignof, "print alignment of type in bytes"),
    ("addr2line", cmd_addr2line, "look up line number information"),
    ("addr2stack", cmd_addr2stack, "display inlined stack frames"),
    ("vars", cmd_vars, "list static variables"),
    ("var", cmd_var, "get info on a static variable"),
];

fn cmd_list(
    db: &debugdb::DebugDb,
    args: &str,
) {
    for (goff, ty) in db.types() {
        if !args.is_empty() {
            if let Some(name) = db.type_name(goff) {
                if !name.contains(args) {
                    continue;
                }
            }
        }

        let kind = match ty {
            Type::Base(_) => "base",
            Type::Struct(_) => "struct",
            Type::Enum(_) => "enum",
            Type::CEnum(_) => "c-enum",
            Type::Array(_) => "array",
            Type::Pointer(_) => "ptr",
            Type::Union(_) => "union",
            Type::Subroutine(_) => "subr",
        };

        println!("{:6} {}", kind, NamedGoff(db, goff));
    }
}

fn parse_type_name(s: &str) -> Option<ParsedTypeName<'_>> {
    if s.starts_with("<.debug_") && s.ends_with('>') {
        // Try parsing as a debug section reference.
        let rest = &s[8..];
        return if rest.starts_with("info+0x") {
            let num = &rest[7..rest.len() - 1];
            if let Ok(n) = usize::from_str_radix(num, 16) {
                Some(ParsedTypeName::Goff(TypeId(gimli::DebugInfoOffset(n).into())))
            } else {
                println!("can't parse {} as hex", num);
                None
            }
        } else if rest.starts_with("types+0x") {
            let num = &rest[8..rest.len() - 1];
            if let Ok(n) = usize::from_str_radix(num, 16) {
                Some(ParsedTypeName::Goff(TypeId(gimli::DebugTypesOffset(n).into())))
            } else {
                println!("can't parse {} as hex", num);
                None
            }
        } else {
            println!("bad offset reference: {}", s);
            None
        };
    }

    Some(ParsedTypeName::Name(s))
}

enum ParsedTypeName<'a> {
    Name(&'a str),
    Goff(TypeId),
}

fn simple_query_cmd(
    db: &debugdb::DebugDb,
    args: &str,
    q: fn(&debugdb::DebugDb, &debugdb::Type),
) {
    let type_name = args.trim();
    let types: Vec<_> = match parse_type_name(type_name) {
        None => return,
        Some(ParsedTypeName::Name(n)) => {
            db.types_by_name(n).collect()
        }
        Some(ParsedTypeName::Goff(o)) => {
            db.type_by_id(o).into_iter()
                .map(|t| (o, t))
                .collect()
        }
    };
    if type_name.starts_with("<.debug_") && type_name.ends_with('>') {
        // Try parsing as a debug section reference.
        let rest = &type_name[8..];
        if rest.starts_with("info+0x") {
        } else if rest.starts_with("types+0x") {
        }
    }

    let many = match types.len() {
        0 => {
            println!("{}", ansi_term::Colour::Red.paint("No types found."));
            return;
        }
        1 => false,
        n => {
            println!("{}{} types found with that name:",
                ansi_term::Color::Yellow.paint("note: "),
                n,
            );
            true
        }
    };

    for (goff, t) in types {
        if many { println!() }
        print!("{}: ", NamedGoff(db, goff));
        q(db, t);
    }
}

fn cmd_info(db: &debugdb::DebugDb, args: &str) {
    simple_query_cmd(db, args, |db, t| {
        match t {
            Type::Base(s) => {
                println!("base type");
                println!("- encoding: {:?}", s.encoding);
                println!("- byte size: {}", s.byte_size);
            }
            Type::Pointer(s) => {
                println!("pointer type");
                println!("- points to: {}", NamedGoff(db, s.type_id));
            }
            Type::Array(s) => {
                println!("array type");
                println!("- element type: {}", NamedGoff(db, s.element_type_id));
                println!("- lower bound: {}", s.lower_bound);
                if let Some(n) = s.count {
                    println!("- count: {}", n);
                } else {
                    println!("- size not given");
                }
            }
            Type::Struct(s) => {
                if s.tuple_like {
                    println!("struct type (tuple-like)");
                } else {
                    println!("struct type");
                }
                println!("- byte size: {}", s.byte_size);
                if let Some(a) = s.alignment {
                    println!("- alignment: {}", a);
                } else {
                    println!("- not aligned");
                }
                if !s.template_type_parameters.is_empty() {
                    println!("- template type parameters:");
                    for ttp in &s.template_type_parameters {
                        println!("  - {} = {}", ttp.name, NamedGoff(db, ttp.type_id));
                    }
                }
                if !s.members.is_empty() {
                    println!("- members:");
                    for mem in s.members.values() {
                        if let Some(name) = &mem.name {
                            println!("  - {}: {}", name, NamedGoff(db, mem.type_id));
                        } else {
                            println!("  - <unnamed>: {}", NamedGoff(db, mem.type_id));
                        }
                        println!("    - offset: {} bytes", mem.location);
                        if let Some(a) = mem.alignment {
                            println!("    - aligned: {} bytes", a);
                        }
                        if mem.artificial {
                            println!("    - artificial");
                        }
                    }
                } else {
                    println!("- no members");
                }
            }
            Type::Enum(s) => {
                println!("enum type");
                println!("- byte size: {}", s.byte_size);
                if let Some(a) = s.alignment {
                    println!("- alignment: {}", a);
                } else {
                    println!("- not aligned");
                }
                if !s.template_type_parameters.is_empty() {
                    println!("- type parameters:");
                    for ttp in &s.template_type_parameters {
                        println!("  - {} = {}", ttp.name, NamedGoff(db, ttp.type_id));
                    }
                }

                match &s.shape {
                    debugdb::VariantShape::Zero => {
                        println!("- empty (uninhabited) enum");
                    }
                    debugdb::VariantShape::One(v) => {
                        println!("- single variant enum w/o discriminator");
                        println!("  - content type: {}", NamedGoff(db, v.member.type_id));
                        println!("  - offset: {} bytes", v.member.location);
                        if let Some(a) = v.member.alignment {
                            println!("  - aligned: {} bytes", a);
                        }
                        if !v.member.artificial {
                            println!("  - not artificial, oddly");
                        }
                    }
                    debugdb::VariantShape::Many { member, variants, .. }=> {
                        if let Some(dname) = db.type_name(member.type_id) {
                            println!("- {} variants discriminated by {} at offset {}", variants.len(), dname, member.location);
                        } else {
                            println!("- {} variants discriminated by an anonymous type at offset {}", variants.len(), member.location);
                        }
                        if !member.artificial {
                            println!("  - not artificial, oddly");
                        }
                        
                        // Print explicit values first
                        for (val, var) in variants {
                            if let Some(val) = val {
                                println!("- when discriminator == {}", val);
                                println!("  - contains type: {}", NamedGoff(db, var.member.type_id));
                                println!("  - at offset: {} bytes", var.member.location);
                                if let Some(a) = var.member.alignment {
                                    println!("  - aligned: {} bytes", a);
                                }
                            }
                        }
                        // Now, default.
                        for (val, var) in variants {
                            if val.is_none() {
                                println!("- any other discriminator value");
                                println!("  - contains type: {}", NamedGoff(db, var.member.type_id));
                                println!("  - at offset: {} bytes", var.member.location);
                                if let Some(a) = var.member.alignment {
                                    println!("  - aligned: {} bytes", a);
                                }
                            }
                        }
                    }
                }
            }
            Type::CEnum(s) => {
                println!("C-like enum type");
                println!("- byte size: {}", s.byte_size);
                println!("- alignment: {}", s.alignment);
                println!("- {} values defined", s.enumerators.len());
                for e in s.enumerators.values() {
                    println!("  - {} = 0x{:x}", e.name, e.const_value);

                }
            }
            Type::Union(s) => {
                println!("union type");
                println!("- byte size: {}", s.byte_size);
                println!("- alignment: {}", s.alignment);
                if !s.template_type_parameters.is_empty() {
                    println!("- template type parameters:");
                    for ttp in &s.template_type_parameters {
                        println!("  - {} = {}", ttp.name, NamedGoff(db, ttp.type_id));
                    }
                }
                if !s.members.is_empty() {
                    println!("- members:");
                    for mem in &s.members {
                        if let Some(name) = &mem.name {
                            println!("  - {}: {}", name, NamedGoff(db, mem.type_id));
                        } else {
                            println!("  - <unnamed>: {}", NamedGoff(db, mem.type_id));
                        }
                        println!("    - offset: {} bytes", mem.location);
                        if let Some(a) = mem.alignment {
                            println!("    - aligned: {} bytes", a);
                        }
                        if mem.artificial {
                            println!("    - artificial");
                        }
                    }
                } else {
                    println!("- no members");
                }
            }
            Type::Subroutine(s) => {
                println!("subroutine type");
                if let Some(rt) = s.return_type_id {
                    println!("- return type: {}", NamedGoff(db, rt));
                }
                if !s.formal_parameters.is_empty() {
                    println!("- formal parameters:");
                    for &fp in &s.formal_parameters {
                        println!("  - {}", NamedGoff(db, fp));
                    }
                }
            }
        }
    })
}

fn cmd_sizeof(db: &debugdb::DebugDb, args: &str) {
    simple_query_cmd(db, args, |db, t| {
        if let Some(sz) = t.byte_size(db) {
            println!("{} bytes", sz);
        } else {
            println!("unsized");
        }
    })
}

fn cmd_alignof(db: &debugdb::DebugDb, args: &str) {
    simple_query_cmd(db, args, |db, t| {
        if let Some(sz) = t.alignment(db) {
            println!("align to {} bytes", sz);
        } else {
            println!("no alignment information");
        }
    })
}

fn cmd_def(db: &debugdb::DebugDb, args: &str) {
    simple_query_cmd(db, args, |db, t| {
        println!();
        match t {
            Type::Base(s) => {
                print!("type _ = ");
                match (s.encoding, s.byte_size) {
                    (_, 0) => print!("()"),
                    (Encoding::Unsigned, 1) => print!("u8"),
                    (Encoding::Unsigned, 2) => print!("u16"),
                    (Encoding::Unsigned, 4) => print!("u32"),
                    (Encoding::Unsigned, 8) => print!("u64"),
                    (Encoding::Unsigned, 16) => print!("u128"),
                    (Encoding::Signed, 1) => print!("i8"),
                    (Encoding::Signed, 2) => print!("i16"),
                    (Encoding::Signed, 4) => print!("i32"),
                    (Encoding::Signed, 8) => print!("i64"),
                    (Encoding::Signed, 16) => print!("i128"),
                    (Encoding::Float, 4) => print!("f32"),
                    (Encoding::Float, 8) => print!("f64"),
                    (Encoding::Boolean, 1) => print!("bool"),
                    (Encoding::UnsignedChar, 4) => print!("char"),
                    (Encoding::UnsignedChar, 1) => print!("c_uchar"),
                    (Encoding::SignedChar, 1) => print!("c_schar"),

                    (e, s) => print!("Unhandled{:?}{}", e, s),
                }
                println!(";");
            }
            Type::Pointer(s) => {
                println!("{}", s.name);
            }
            Type::Array(s) => {
                let name = db.type_name(s.element_type_id).unwrap();
                if let Some(n) = s.count {
                    println!("[{}; {}]", name, n);
                } else {
                    println!("[{}]", name);
                }
            }
            Type::Struct(s) => {
                print!("struct {}", s.name);

                if !s.template_type_parameters.is_empty() {
                    print!("<");
                    for ttp in &s.template_type_parameters {
                        print!("{},", ttp.name);
                    }
                    print!(">");
                }
                
                if s.members.is_empty() {
                    println!(";");
                } else {
                    if s.tuple_like {
                        println!("(");
                        for mem in s.members.values() {
                            println!("    {},", db.type_name(mem.type_id).unwrap());
                        }
                        println!(");");
                    } else {
                        println!(" {{");
                        for mem in s.members.values() {
                            if let Some(name) = &mem.name {
                                println!("    {}: {},", name, db.type_name(mem.type_id).unwrap());
                            } else {
                                println!("    ANON: {},", db.type_name(mem.type_id).unwrap());
                            }
                        }
                        println!("}}");
                    }
                }
            }
            Type::Enum(s) => {
                print!("enum {}", s.name);
                if !s.template_type_parameters.is_empty() {
                    print!("<");
                    for ttp in &s.template_type_parameters {
                        print!("{}", ttp.name);
                    }
                    print!(">");
                }
                println!(" {{");

                match &s.shape {
                    debugdb::VariantShape::Zero => (),
                    debugdb::VariantShape::One(var) => {
                        if let Some(name) = &var.member.name {
                            print!("    {}", name);
                        } else {
                            print!("    ANON");
                        }

                        let mty = db.type_by_id(var.member.type_id)
                            .unwrap();
                        if let Type::Struct(s) = mty {
                            if !s.members.is_empty() {
                                if s.tuple_like {
                                    println!("(");
                                    for mem in s.members.values() {
                                        let mtn = db.type_name(mem.type_id).unwrap();
                                        println!("        {},", mtn);
                                    }
                                    print!("    )");
                                } else {
                                    println!(" {{");
                                    for mem in s.members.values() {
                                        let mtn = db.type_name(mem.type_id).unwrap();
                                        println!("        {}: {},", mem.name.as_ref().unwrap(), mtn);
                                    }
                                    print!("    }}");
                                }
                            }
                        } else {
                            print!("(unexpected weirdness)");
                        }

                        println!(",");
                    }
                    debugdb::VariantShape::Many { variants, .. }=> {
                        for var in variants.values() {
                            if let Some(name) = &var.member.name {
                                print!("    {}", name);
                            } else {
                                print!("    ANON");
                            }

                            let mty = db.type_by_id(var.member.type_id)
                                .unwrap();
                            if let Type::Struct(s) = mty {
                                if !s.members.is_empty() {
                                    if s.tuple_like {
                                        println!("(");
                                        for mem in s.members.values() {
                                            let mtn = db.type_name(mem.type_id).unwrap();
                                            println!("        {},", mtn);
                                        }
                                        print!("    )");
                                    } else {
                                        println!(" {{");
                                        for mem in s.members.values() {
                                            let mtn = db.type_name(mem.type_id).unwrap();
                                            println!("        {}: {},", mem.name.as_ref().unwrap(), mtn);
                                        }
                                        print!("    }}");
                                    }
                                }
                            } else {
                                print!("(unexpected weirdness)");
                            }

                            println!(",");
                        }
                    }
                }
                println!("}}");

            }
            Type::CEnum(s) => {
                println!("enum {} {{", s.name);
                for (val, e) in &s.enumerators {
                    println!("    {} = 0x{:x},", e.name, val);
                }
                println!("}}");
            }
            Type::Union(s) => {
                print!("union {}", s.name);

                if !s.template_type_parameters.is_empty() {
                    print!("<");
                    for ttp in &s.template_type_parameters {
                        print!("{},", ttp.name);
                    }
                    print!(">");
                }

                println!(" {{");
                for mem in &s.members {
                    if let Some(name) = &mem.name {
                        println!("    {}: {},", name, db.type_name(mem.type_id).unwrap());
                    } else {
                        println!("    ANON: {},", db.type_name(mem.type_id).unwrap());
                    }
                }
                println!("}}");
            }
            Type::Subroutine(s) => {
                println!("fn(");
                for &p in &s.formal_parameters {
                    println!("    {},", db.type_name(p).unwrap());
                }
                if let Some(rt) = s.return_type_id {
                    println!(") -> {} {{", db.type_name(rt).unwrap());
                } else {
                    println!(") {{");
                }
                println!("    // code goes here");
                println!("    // (this is a subroutine type, _not_ a fn ptr)");
                println!("    unimplemented!();");
                println!("}}");
            }
        }
    })
}

fn cmd_addr2line(db: &debugdb::DebugDb, args: &str) {
    let addr = if args.starts_with("0x") {
        if let Ok(a) = u64::from_str_radix(&args[2..], 16) {
            a
        } else {
            println!("can't parse {} as an address", args);
            return;
        }
    } else if let Ok(a) = args.parse::<u64>() {
        a
    } else {
        println!("can't parse {} as an address", args);
        return;
    };

    if let Some(row) = db.lookup_line_row(addr) {
        print!("{}:", row.file);
        if let Some(line) = row.line {
            print!("{}:", line);
        } else {
            print!("?:");
        }
        if let Some(col) = row.column {
            print!("{}", col);
        } else {
            print!("?");
        }
        println!();
    } else {
        println!("no line number information available for address");
    }
}

fn cmd_addr2stack(db: &debugdb::DebugDb, args: &str) {
    let addr = if args.starts_with("0x") {
        if let Ok(a) = u64::from_str_radix(&args[2..], 16) {
            a
        } else {
            println!("can't parse {} as an address", args);
            return;
        }
    } else if let Ok(a) = args.parse::<u64>() {
        a
    } else {
        println!("can't parse {} as an address", args);
        return;
    };

    let bold = ansi_term::Style::new().bold();
    let dim = ansi_term::Style::new().dimmed();

    match db.static_stack_for_pc(addr) {
        Ok(trc) => {
            println!("Static stack trace fragment for address 0x{:x}", addr);
            println!("(innermost / most recent first)");
            for (i, record) in trc.iter().rev().enumerate() {
                let subp = db.subprogram_by_id(record.subprogram).unwrap();

                print!("{:4}   ", i);
                if let Some(n) = &subp.name {
                    println!("{}", bold.paint(n));
                } else {
                    println!("{}", bold.paint("<unknown-subprogram>"));
                }
                print!("{}", dim.prefix());
                print!("    {}:", record.file);
                if let Some(line) = record.line {
                    print!("{}:", line);
                } else {
                    print!("?:");
                }
                if let Some(col) = record.column {
                    print!("{}", col);
                } else {
                    print!("?");
                }
                print!("{}", dim.suffix());
                println!();
            }
        }
        Err(e) => {
            println!("failed: {}", e);
        }
    }
}

fn cmd_vars(db: &debugdb::DebugDb, args: &str) {
    for (_id, v) in db.static_variables() {
        if !args.is_empty() {
            if !v.name.contains(args) {
                continue;
            }
        }

        println!("0x{:0width$x} {}: {}", v.location, v.name, NamedGoff(db, v.type_id),
            width = db.pointer_size() as usize * 2);
    }
}

fn cmd_var(db: &debugdb::DebugDb, args: &str) {
    let results = db.static_variables_by_name(args).collect::<Vec<_>>();

    match results.len() {
        0 => println!("no variables found by that name"),
        1 => (),
        n => println!("note: {} variables found by that name", n),
    }

    for (_id, v) in results {
        println!("{} @ {}", v.name, Goff(v.offset));
        println!("- type: {}", NamedGoff(db, v.type_id));
        println!("- address: 0x{:x}", v.location);
    }
}
