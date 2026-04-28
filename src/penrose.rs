//! Penrose diagram generation for geometry declarations.
//!
//! Converts geometry types, predicates, and definitions from the CIC environment
//! into Penrose Domain/Substance/Style programs for automatic diagram layout.

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use crate::environment::Environment;
use crate::expr::{Expr, Name};
use crate::format::format_expr;

/// Generate Penrose trio files (.domain, .substance, .style) from geometry declarations.
pub fn export_geometry(
    env: &Environment,
    theorem_name: Option<&str>,
    out_dir: &Path,
) -> Result<(), String> {
    fs::create_dir_all(out_dir).map_err(|e| format!("Cannot create dir: {}", e))?;

    let domain = generate_domain();
    let style = generate_style();

    let substance = match theorem_name {
        Some(name) => generate_substance_for_theorem(env, name)?,
        None => generate_substance_all(env),
    };

    let domain_path = out_dir.join("geometry.domain");
    let substance_path = out_dir.join("geometry.substance");
    let style_path = out_dir.join("geometry.style");

    fs::write(&domain_path, domain)
        .map_err(|e| format!("Cannot write domain: {}", e))?;
    fs::write(&substance_path, substance)
        .map_err(|e| format!("Cannot write substance: {}", e))?;
    fs::write(&style_path, style)
        .map_err(|e| format!("Cannot write style: {}", e))?;

    println!("Generated Penrose files:");
    println!("  Domain:    {}", domain_path.display());
    println!("  Substance: {}", substance_path.display());
    println!("  Style:     {}", style_path.display());

    Ok(())
}

fn generate_domain() -> String {
    r#"-- Penrose Domain for Euclidean Geometry
-- Auto-generated from CIC geometry declarations

type Point
type Line

-- Incidence and order
predicate OnLine(Point, Line)
predicate Between(Point, Point, Point)

-- Congruence
predicate SegCongruent(Point, Point, Point, Point)
predicate AngleCongruent(Point, Point, Point, Point, Point, Point)

-- Parallelism and perpendicularity
predicate Parallel(Line, Line)
predicate Perpendicular(Line, Line)

-- Derived predicates
predicate Collinear(Point, Point, Point)
predicate Midpoint(Point, Point, Point)
predicate RightAngle(Point, Point, Point)
predicate Triangle(Point, Point, Point)
predicate OnCircle(Point, Point, Point)
predicate Isosceles(Point, Point, Point)
predicate Equilateral(Point, Point, Point)

-- Functions
function MakeLine(Point, Point) -> Line
"#
    .to_string()
}

fn generate_style() -> String {
    r#"-- Penrose Style for Euclidean Geometry
-- Auto-generated style program

canvas {
    width = 400
    height = 400
}

-- Points are small circles with labels
forall Point p {
    p.icon = Circle {
        center: (?, ?)
        r: 3
        fillColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 0
    }
    p.text = Text {
        string: p.label
        center: (p.icon.center[0] + 10, p.icon.center[1] - 10)
        fontSize: "12px"
    }
    ensure contains(canvas, p.icon, 20)
}

-- Lines are segments between points
forall Line l {
    l.icon = Line {
        start: (?, ?)
        end: (?, ?)
        strokeColor: rgba(0, 0, 0, 1.0)
        strokeWidth: 1.5
    }
}

-- Points on a line should lie on the line segment
forall Point p; Line l where OnLine(p, l) {
    ensure in(p.icon, l.icon)
}

-- Betweenness: B lies between A and C on the same line
forall Point a; Point b; Point c where Between(a, b, c) {
    ensure in(b.icon, a.icon, c.icon)
}

-- Parallel lines should not intersect
forall Line l; Line m where Parallel(l, m) {
    ensure disjoint(l.icon, m.icon, 20)
}

-- Perpendicular lines form a right angle
forall Line l; Line m where Perpendicular(l, m) {
    -- This is a weak constraint; exact right angle is hard without coordinates
    encourage equal(vdist(l.icon.start, m.icon.start), vdist(l.icon.end, m.icon.end))
}

-- Triangles: three points connected by lines
forall Point a; Point b; Point c where Triangle(a, b, c) {
    ensure distinct(a.icon, b.icon, c.icon)
    encourage not(Collinear(a, b, c))
}

-- Non-degeneracy: distinct points should not overlap
forall Point p; Point q where p != q {
    ensure disjoint(p.icon, q.icon, 10)
}

-- Spread points across the canvas
forall Point p {
    encourage near(p.icon.center, canvas.center)
}
"#
    .to_string()
}

fn generate_substance_all(env: &Environment) -> String {
    let mut out = String::from("-- Auto-generated Substance program from CIC geometry declarations\n\n");

    let mut points = HashSet::new();

    env.for_each_constant(|info| {
        let name_str = info.name().to_string();
        if is_geometry_predicate(&name_str) {
            let ty = info.get_type();
            let arg_names = extract_arg_names_from_type(ty);
            for an in &arg_names {
                if is_point_name(an) && points.insert(an.clone()) {
                    out.push_str(&format!("Point {}\n", an));
                }
            }
            let pred_name = penrose_predicate_name(&name_str);
            if !pred_name.is_empty() && !arg_names.is_empty() {
                out.push_str(&format!("{}({})\n", pred_name, arg_names.join(", ")));
            }
        }
    });

    if out.trim() == "-- Auto-generated Substance program from CIC geometry declarations" {
        out.push_str("-- No geometry predicates found; add a theorem name to generate a specific diagram.\n");
        out.push_str("\nPoint A, B, C\n");
        out.push_str("Triangle(A, B, C)\n");
    }

    out
}

fn generate_substance_for_theorem(env: &Environment, theorem_name: &str) -> Result<String, String> {
    let info = env.find(&Name::new(theorem_name))
        .ok_or_else(|| format!("Theorem '{}' not found in environment", theorem_name))?;

    let ty = info.get_type();
    let mut out = String::new();
    out.push_str(&format!("-- Substance for theorem: {}\n", theorem_name));
    out.push_str(&format!("-- Type: {}\n\n", format_expr(ty)));

    // Extract parameter names from Pi binders
    let (params, conclusion) = collect_pi_params(ty);

    // Declare points based on parameter names
    let mut points = HashSet::new();
    for (name, _) in &params {
        let short = clean_param_name(name);
        if is_point_name(&short) {
            if points.insert(short.clone()) {
                out.push_str(&format!("Point {}\n", short));
            }
        }
    }

    // If no points found, add defaults
    if points.is_empty() {
        out.push_str("Point A, B, C\n");
        points.insert("A".to_string());
        points.insert("B".to_string());
        points.insert("C".to_string());
    }

    // Try to infer predicates from conclusion
    if let Some(pred_str) = extract_predicate_from_expr(conclusion) {
        out.push('\n');
        out.push_str(&pred_str);
    } else {
        // Default: assume it's a triangle
        let pts: Vec<_> = points.into_iter().collect();
        if pts.len() >= 3 {
            out.push('\n');
            out.push_str(&format!("Triangle({}, {}, {})\n", pts[0], pts[1], pts[2]));
        }
    }

    Ok(out)
}

fn is_geometry_predicate(name: &str) -> bool {
    matches!(name,
        "on_line" | "between" | "seg_congruent" | "angle_congruent" |
        "parallel" | "perpendicular" | "collinear" | "midpoint" |
        "right_angle" | "triangle" | "on_circle" | "isosceles" | "equilateral"
    )
}

fn penrose_predicate_name(name: &str) -> String {
    match name {
        "on_line" => "OnLine",
        "between" => "Between",
        "seg_congruent" => "SegCongruent",
        "angle_congruent" => "AngleCongruent",
        "parallel" => "Parallel",
        "perpendicular" => "Perpendicular",
        "collinear" => "Collinear",
        "midpoint" => "Midpoint",
        "right_angle" => "RightAngle",
        "triangle" => "Triangle",
        "on_circle" => "OnCircle",
        "isosceles" => "Isosceles",
        "equilateral" => "Equilateral",
        _ => "",
    }.to_string()
}

fn is_point_name(name: &str) -> bool {
    name.len() == 1 && name.chars().next().unwrap().is_uppercase()
}

fn clean_param_name(name: &str) -> String {
    name.split('.').next().unwrap_or(name).to_string()
}

fn extract_arg_names_from_type(e: &Expr) -> Vec<String> {
    let (params, _) = collect_pi_params(e);
    params.into_iter().map(|(n, _)| clean_param_name(&n)).filter(|n| is_point_name(n)).collect()
}

fn collect_pi_params<'a>(e: &'a Expr) -> (Vec<(String, &'a Expr)>, &'a Expr) {
    let mut params = Vec::new();
    let mut current = e;
    loop {
        match current {
            Expr::Pi(name, _, ty, body) => {
                params.push((name.to_string(), ty.as_ref()));
                current = body;
            }
            _ => break,
        }
    }
    (params, current)
}

fn extract_predicate_from_expr(e: &Expr) -> Option<String> {
    let (head, args) = e.get_app_args();
    let head = head?;
    if let Expr::Const(name, _) = head {
        let name_str = name.to_string();
        if is_geometry_predicate(&name_str) {
            let pred = penrose_predicate_name(&name_str);
            let arg_names: Vec<String> = args.iter()
                .filter_map(|a| match a {
                    Expr::FVar(n) => Some(n.to_string()),
                    Expr::BVar(n) => Some(format!("v{}", n)),
                    _ => None,
                })
                .collect();
            if !pred.is_empty() && !arg_names.is_empty() {
                return Some(format!("{}({})\n", pred, arg_names.join(", ")));
            }
        }
    }
    None
}
