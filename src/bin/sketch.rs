use structopt::StructOpt;

use debugdb::{Type, Variant, VariantShape};

#[derive(Debug, StructOpt)]
struct Sketch {
    filename: std::path::PathBuf,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Sketch::from_args();

    let buffer = std::fs::read(args.filename)?;
    let object = object::File::parse(&*buffer)?;

    dump_file(&object)?;

    Ok(())
}

fn dump_file<'a>(
    object: &'a object::File,
) -> Result<(), Box<dyn std::error::Error>> {
    let everything = debugdb::parse_file(object)?;

    println!("-- stuff parsed --");
    for (goff, e) in everything.types() {
        match e {
            Type::Base(s) => {
                println!("{:x?} = base {}", goff, s.name);
                println!("    encoding: {:?}", s.encoding);
                println!("    byte_size: {}", s.byte_size);
                println!("    offset: {:x?}", s.offset);
            }
            Type::Struct(s) => {
                println!("{:x?} = struct {}", goff, s.name);
                println!("    byte_size: {}", s.byte_size);
                println!("    alignment: {:?}", s.alignment);
                println!("    offset: {:x?}", s.offset);
                println!("    tuple_like: {:?}", s.tuple_like);
                for m in &s.template_type_parameters {
                    let tyname = everything
                        .type_name(m.type_id)
                        .unwrap_or("???".into());
                    println!(
                        "    template_type_parameter {}: {} ({:x?})",
                        m.name, tyname, m.type_id,
                    );
                }
                for m in s.members.values() {
                    println!("    member:");
                    if let Some(name) = &m.name {
                        println!("        name: {:?}", name);
                    } else {
                        println!("        name: -none-");
                    }
                    println!("        alignment: {:?}", m.alignment);
                    println!("        location: {}", m.location);
                    println!("        offset: {:x?}", m.offset);
                    if m.artificial {
                        println!("        artificial: true");
                    }
                    let tyname = everything
                        .type_name(m.type_id)
                        .unwrap_or("???".into());
                    println!("        type: {:?} ({:x?})", tyname, m.type_id);
                }
            }
            Type::Union(s) => {
                println!("{:x?} = union {}", goff, s.name);
                println!("    byte_size: {}", s.byte_size);
                println!("    alignment: {}", s.alignment);
                println!("    offset: {:x?}", s.offset);
                for m in &s.template_type_parameters {
                    let tyname = everything
                        .type_name(m.type_id)
                        .unwrap_or("???".into());
                    println!(
                        "    template_type_parameter {}: {} ({:x?})",
                        m.name, tyname, m.type_id,
                    );
                }
                for m in &s.members {
                    println!("    member:");
                    if let Some(name) = &m.name {
                        println!("        name: {:?},", name);
                    }
                    println!("        alignment: {:?},", m.alignment);
                    println!("        location: {},", m.location);
                    println!("        offset: {:x?},", m.offset);
                    if m.artificial {
                        println!("        artificial: true,");
                    }
                    let tyname = everything
                        .type_name(m.type_id)
                        .unwrap_or("???".into());
                    println!("        type: {:?} ({:x?}),", tyname, m.type_id);
                }
            }
            Type::Enum(s) => {
                println!("{:x?} = enum {}", goff, s.name);
                println!("    byte_size: {}", s.byte_size);
                println!("    alignment: {:?}", s.alignment);
                println!("    offset: {:x?}", s.offset);
                for m in &s.template_type_parameters {
                    let tyname = everything
                        .type_name(m.type_id)
                        .unwrap_or("???".into());
                    println!(
                        "    template_type_parameter {}: {} ({:x?})",
                        m.name, tyname, m.type_id,
                    );
                }

                let print_variant = |discr_value: Option<u64>, v: &Variant| {
                    if let Some(n) = discr_value {
                        println!("    variant 0x{:x}:", n);
                    } else {
                        println!("    variant default:");
                    }
                    let m = &v.member;
                    if let Some(name) = &m.name {
                        println!("        name: {:?},", name);
                    } else {
                        println!("        name: -none-,");
                    }
                    println!("        alignment: {:?},", m.alignment);
                    println!("        location: {},", m.location);
                    println!("        offset: {:x?},", m.offset);
                    if m.artificial {
                        println!("        artificial: true,");
                    }
                    let tyname = everything
                        .type_name(m.type_id)
                        .unwrap_or("???".into());
                    println!("        type: {:?} ({:x?}),", tyname, m.type_id);
                };
                match &s.shape {
                    VariantShape::Many {
                        member, variants, ..
                    } => {
                        println!("    discriminator:");
                        if let Some(name) = &member.name {
                            println!("        name: {:?},", name);
                        }
                        println!("        alignment: {:?},", member.alignment);
                        println!("        location: {},", member.location);
                        println!("        offset: {:x?},", member.offset);
                        if member.artificial {
                            println!("        artificial: true,");
                        }
                        let tyname = everything
                            .type_name(member.type_id)
                            .unwrap_or("???".into());
                        println!(
                            "        type: {:?} ({:x?}),",
                            tyname, member.type_id
                        );
                        for (&d, v) in variants {
                            print_variant(d, v);
                        }
                    }
                    VariantShape::One(v) => {
                        print_variant(None, v);
                    }
                    VariantShape::Zero => (),
                }
            }
            Type::CEnum(s) => {
                println!("{:x?} = c-like enum {}", goff, s.name);
                println!("    enum_class: {:?}", s.enum_class);
                println!("    byte_size: {}", s.byte_size);
                println!("    alignment: {}", s.alignment);
                println!("    offset: {:x?},", s.offset);
                for e in s.enumerators.values() {
                    println!("    enumerator 0x{:x}:", e.const_value);
                    println!("        name: {}", e.name);
                    println!("        offset: {:x?},", s.offset);
                }
            }
            Type::Pointer(s) => {
                println!("{:x?} = ptr {}", goff, s.name);
                let tyname = everything
                    .type_name(s.type_id)
                    .unwrap_or("???".into());
                println!("    points_to: {} ({:x?})", tyname, s.type_id);
                println!("    offset: {:x?},", s.offset);
            }
            Type::Subroutine(s) => {
                println!("{:x?} = subroutine", goff);
                for &p in &s.formal_parameters {
                    let tyname = everything
                        .type_name(p.into())
                        .unwrap_or("???".into());
                    println!("    param: {}", tyname);
                }
                if let Some(t) = s.return_type_id {
                    let tyname = everything
                        .type_name(t.into())
                        .unwrap_or("???".into());
                    println!("    returns: {}", tyname);
                }
            }
            Type::Array(a) => {
                println!("{:x?} = array", goff);
                {
                    let tyname = everything
                        .type_name(a.element_type_id)
                        .unwrap_or("???".into());
                    println!("    element_type: {}", tyname);
                }
                {
                    let tyname = everything
                        .type_name(a.index_type_id)
                        .unwrap_or("???".into());
                    println!("    index_type: {}", tyname);
                }
                println!("    lower_bound: 0x{:x}", a.lower_bound);
                if let Some(n) = a.count {
                    println!("    count: 0x{:x}", n);
                } else {
                    println!("    count: none");
                }
            }
        }
    }

    println!("--- subprograms ---");
    for (goff, sp) in everything.subprograms() {
        println!("{:x?} = {:?}", goff, sp.name);
        if let Some(ln) = &sp.linkage_name {
            println!("- linkage name: {}", ln);
        }
        if let Some(pcr) = &sp.pc_range {
            println!("- PC range: {:#x?}", pcr);
        }
        if let Some(ao) = sp.abstract_origin {
            println!("- abstract origin: {:x?}", ao);
        }

        println!("- decl: {}:{}:{}",
            sp.decl_coord.file.as_deref().unwrap_or("????"),
            sp.decl_coord.line.map(|x| x.get()).unwrap_or(0),
            sp.decl_coord.column.map(|x| x.get()).unwrap_or(0),
            );
        if let Some(rt) = sp.return_type_id {
            println!("- returns: {}",
                everything.type_name(rt)
                .unwrap_or("???".into()));
        }
        if sp.noreturn {
            println!("- NORETURN");
        }
        if !sp.template_type_parameters.is_empty() {
            println!("- type parameters:");
            for ttp in &sp.template_type_parameters {
                println!("  - {} = {:x?}", ttp.name, ttp.type_id);
            }
        }
        if !sp.formal_parameters.is_empty() {
            println!("- formal parameters:");
            for p in &sp.formal_parameters {
                if let Some(n) = &p.name {
                    println!("  - {}:", n);
                } else {
                    println!("  - <anon>:");
                }
                println!("    - decl: {}:{}:{}",
                    p.decl_coord.file.as_deref().unwrap_or("????"),
                    p.decl_coord.line.map(|x| x.get()).unwrap_or(0),
                    p.decl_coord.column.map(|x| x.get()).unwrap_or(0),
                );
                if let Some(t) = p.type_id {
                    println!("    - type: {}",
                        everything.type_name(t)
                        .unwrap_or("???".into()));
                }
                if let Some(ao) = p.abstract_origin {
                    println!("    - abstract origin: {:x?}", ao);
                }
            }
        }
        if !sp.inlines.is_empty() {
            for is in &sp.inlines {
                print_inlined_subroutine(&everything, is, 0);
            }
        }

        println!();
    }

    println!("--- line number table ---");
    for (_addr, rows) in everything.line_table_rows() {
        for row in rows {
            println!("Range: {:#x?}{}",
                row.pc_range,
                if row.pc_range.is_empty() {
                    " (empty!)"
                } else {
                    ""
                });
            println!("- file: {:?}", row.file);
            println!("- line: {:?}", row.line);
            println!("- col:  {:?}", row.column);
        }
    }

    Ok(())
}

fn print_inlined_subroutine(everything: &debugdb::DebugDb, is: &debugdb::InlinedSubroutine, level: usize) {
    let indent = 2 * level;
    println!("{:indent$}- inlined subroutine:", "", indent = indent);
    if let Some(ao) = is.abstract_origin {
        println!("{:indent$}  - abstract origin: {:x?}", "", ao, indent = indent);
    }
    println!("{:indent$}  - call: {}:{}:{}",
        "",
        is.call_coord.file.as_deref().unwrap_or("????"),
        is.call_coord.line.map(|x| x.get()).unwrap_or(0),
        is.call_coord.column.map(|x| x.get()).unwrap_or(0),
        indent = indent
    );
    println!("{:indent$}  - PC ranges:", "", indent = indent);
    for r in &is.pc_ranges {
        println!("{:indent$}    - {:#x}..{:#x}", "", r.begin, r.end, indent = indent);
    }

    if !is.formal_parameters.is_empty() {
        println!("{:indent$}  - formal parameters:", "", indent = indent);
        for p in &is.formal_parameters {
            if let Some(n) = &p.name {
                println!("{:indent$}    - {}:", "", n, indent = indent);
            } else {
                println!("{:indent$}    - <anon>:", "", indent = indent);
            }
            println!("{:indent$}      - decl: {}:{}:{}",
                "",
                p.decl_coord.file.as_deref().unwrap_or("????"),
                p.decl_coord.line.map(|x| x.get()).unwrap_or(0),
                p.decl_coord.column.map(|x| x.get()).unwrap_or(0),
                indent = indent,
            );
            if let Some(t) = p.type_id {
                println!("{:indent$}      - type: {}",
                    "",
                    everything.type_name(t).unwrap_or("???".into()),
                    indent = indent
                );
            }
            if let Some(ao) = p.abstract_origin {
                println!("{:indent$}      - abstract origin: {:x?}", "", ao, indent = indent);
            }
        }
    }
    for sub in &is.inlines {
        print_inlined_subroutine(everything, sub, level + 1);
    }
}
