use structopt::StructOpt;

use dwarfldr::{Type, Variant, VariantShape};

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
    let everything = dwarfldr::parse_file(object)?;

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
                        .name_from_goff(m.ty_goff.into())
                        .unwrap_or("???".into());
                    println!(
                        "    template_type_parameter {}: {} ({:x?})",
                        m.name, tyname, m.ty_goff,
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
                        .name_from_goff(m.ty_goff.into())
                        .unwrap_or("???".into());
                    println!("        type: {:?} ({:x?})", tyname, m.ty_goff);
                }
            }
            Type::Union(s) => {
                println!("{:x?} = union {}", goff, s.name);
                println!("    byte_size: {}", s.byte_size);
                println!("    alignment: {}", s.alignment);
                println!("    offset: {:x?}", s.offset);
                for m in &s.template_type_parameters {
                    let tyname = everything
                        .name_from_goff(m.ty_goff.into())
                        .unwrap_or("???".into());
                    println!(
                        "    template_type_parameter {}: {} ({:x?})",
                        m.name, tyname, m.ty_goff,
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
                        .name_from_goff(m.ty_goff.into())
                        .unwrap_or("???".into());
                    println!("        type: {:?} ({:x?}),", tyname, m.ty_goff);
                }
            }
            Type::Enum(s) => {
                println!("{:x?} = enum {}", goff, s.name);
                println!("    byte_size: {}", s.byte_size);
                println!("    alignment: {:?}", s.alignment);
                println!("    offset: {:x?}", s.offset);
                for m in &s.template_type_parameters {
                    let tyname = everything
                        .name_from_goff(m.ty_goff.into())
                        .unwrap_or("???".into());
                    println!(
                        "    template_type_parameter {}: {} ({:x?})",
                        m.name, tyname, m.ty_goff,
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
                        .name_from_goff(m.ty_goff.into())
                        .unwrap_or("???".into());
                    println!("        type: {:?} ({:x?}),", tyname, m.ty_goff);
                };
                match &s.variant_part.shape {
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
                            .name_from_goff(member.ty_goff.into())
                            .unwrap_or("???".into());
                        println!(
                            "        type: {:?} ({:x?}),",
                            tyname, member.ty_goff
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
                    .name_from_goff(s.ty_goff.into())
                    .unwrap_or("???".into());
                println!("    points_to: {} ({:x?})", tyname, s.ty_goff);
                println!("    offset: {:x?},", s.offset);
            }
            Type::Subroutine(s) => {
                println!("{:x?} = subroutine", goff);
                for &p in &s.formal_parameters {
                    let tyname = everything
                        .name_from_goff(p.into())
                        .unwrap_or("???".into());
                    println!("    param: {}", tyname);
                }
                if let Some(t) = s.return_ty_goff {
                    let tyname = everything
                        .name_from_goff(t.into())
                        .unwrap_or("???".into());
                    println!("    returns: {}", tyname);
                }
            }
            Type::Array(a) => {
                println!("{:x?} = array", goff);
                {
                    let tyname = everything
                        .name_from_goff(a.element_ty_goff.into())
                        .unwrap_or("???".into());
                    println!("    element_type: {}", tyname);
                }
                {
                    let tyname = everything
                        .name_from_goff(a.index_ty_goff.into())
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
    Ok(())
}
