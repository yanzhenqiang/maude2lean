//! Penrose diagram generation for geometry declarations.
//!
//! Converts geometry types, predicates, and definitions from the CIC environment
//! into Penrose Domain/Substance/Style programs for automatic diagram layout.

use std::collections::HashSet;
use std::fs;
use std::path::Path;

use crate::environment::Environment;
use crate::expr::{Expr, Name};

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
    encourage equal(vdist(l.icon.start, m.icon.start), vdist(l.icon.end, m.icon.end))
}

-- Triangles: three points connected by lines
forall Point a; Point b; Point c where Triangle(a, b, c) {
    ensure distinct(a.icon, b.icon, c.icon)
    encourage not(Collinear(a, b, c))
}

-- Isosceles triangle: two sides should be roughly equal in length
forall Point a; Point b; Point c where Isosceles(a, b, c) {
    encourage equal(vdist(a.icon.center, b.icon.center), vdist(a.icon.center, c.icon.center))
}

-- Equilateral triangle: all three sides roughly equal
forall Point a; Point b; Point c where Equilateral(a, b, c) {
    encourage equal(vdist(a.icon.center, b.icon.center), vdist(b.icon.center, c.icon.center))
    encourage equal(vdist(b.icon.center, c.icon.center), vdist(c.icon.center, a.icon.center))
}

-- SegCongruent: the two segments should have similar lengths
forall Point a; Point b; Point c; Point d where SegCongruent(a, b, c, d) {
    encourage equal(vdist(a.icon.center, b.icon.center), vdist(c.icon.center, d.icon.center))
}

-- AngleCongruent: place the angles at corresponding vertices
forall Point b; Point a; Point c; Point b2; Point a2; Point c2 where AngleCongruent(b, a, c, b2, a2, c2) {
    encourage equal(angleBetween(a.icon.center, b.icon.center, c.icon.center), angleBetween(a2.icon.center, b2.icon.center, c2.icon.center))
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

/// Default mode: scan environment for geometry-related declarations and generate
/// a focused substance program.
fn generate_substance_all(env: &Environment) -> String {
    let mut out = String::from("-- Auto-generated Substance program (geometry only)\n\n");

    let mut any = false;
    env.for_each_constant(|info| {
        let name = info.name().to_string();
        // Only consider axioms, theorems, and definitions whose names are
        // geometry predicates or theorems (not recursors/constructors).
        let is_geo = is_geometry_predicate(&name)
            || name.contains("_angle") || name.contains("parallel")
            || name.contains("perpendicular") || name.contains("midpoint")
            || name.contains("collinear") || name.contains("triangle")
            || name.contains("isosceles") || name.contains("equilateral")
            || name.contains("between") || name.contains("segment")
            || name.contains("right_") || name.contains("circle")
            || name.contains("rectangle") || name.contains("parallelogram");
        if is_geo && (info.is_axiom() || info.is_theorem() || info.is_definition()) {
            any = true;
            out.push_str(&format!("-- {}\n", name));
            let ty = info.get_type();
            if let Ok(sub) = theorem_type_to_substance(ty) {
                out.push_str(&sub);
            }
            out.push('\n');
        }
    });

    if !any {
        out.push_str("-- No geometry statements found.\n");
        out.push_str("Point A, B, C\n");
        out.push_str("Triangle(A, B, C)\n");
    }

    out
}

fn generate_substance_for_theorem(env: &Environment, theorem_name: &str) -> Result<String, String> {
    let info = env.find(&Name::new(theorem_name))
        .ok_or_else(|| format!("Theorem '{}' not found in environment", theorem_name))?;

    let ty = info.get_type();
    let mut out = String::new();
    out.push_str(&format!("-- Theorem: {}\n", theorem_name));
    out.push_str(&theorem_type_to_substance(ty)?);
    Ok(out)
}

/// Convert a theorem's Pi-type into Penrose Substance statements.
/// Handles BVar-to-parameter-name resolution at the correct de Bruijn depth.
fn theorem_type_to_substance(ty: &Expr) -> Result<String, String> {
    let (params, conclusion) = collect_pi_params(ty);
    let n = params.len();

    // BVar resolution: in a context with `base_depth` enclosing binders,
    // BVar(k) refers to params[base_depth - 1 - k].
    let bvar_name = |base_depth: usize, k: u64| -> String {
        let k = k as usize;
        if k < base_depth && base_depth >= 1 {
            let idx = base_depth - 1 - k;
            if idx < n {
                return clean_param_name(&params[idx].0);
            }
        }
        format!("v{}", k)
    };

    let mut out = String::new();

    // Declare points and lines from parameter types
    let mut points = HashSet::new();
    for (name, pty) in &params {
        let short = clean_param_name(name);
        if is_point_name(&short) && points.insert(short.clone()) {
            out.push_str(&format!("Point {}\n", short));
        }
        if is_line_type(pty) && points.insert(format!("line_{}", short)) {
            out.push_str(&format!("Line {}\n", short));
        }
    }

    // Extract hypotheses: each parameter i lives at depth i
    let mut has_hypothesis = false;
    for i in 0..n {
        let (_name, pty) = &params[i];
        if let Some(pred_str) = expr_to_substance_predicate(pty, i, &bvar_name) {
            if !has_hypothesis {
                out.push('\n');
                out.push_str("-- Given:\n");
                has_hypothesis = true;
            }
            out.push_str(&pred_str);
        }
    }

    // Extract conclusion at full depth n
    if let Some(pred_str) = expr_to_substance_predicate(conclusion, n, &bvar_name) {
        out.push('\n');
        out.push_str("-- Prove:\n");
        out.push_str(&pred_str);
    } else if points.is_empty() {
        out.push_str("Point A, B, C\n");
        out.push_str("Triangle(A, B, C)\n");
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

fn is_line_type(e: &Expr) -> bool {
    match e {
        Expr::Const(name, _) => name.to_string() == "Line",
        _ => false,
    }
}

fn clean_param_name(name: &str) -> String {
    name.split('.').next().unwrap_or(name).to_string()
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

/// Convert a predicate application into Penrose Substance, resolving BVars at the
/// given de Bruijn depth.
fn expr_to_substance_predicate<F>(e: &Expr, base_depth: usize, bvar_name: &F) -> Option<String>
where
    F: Fn(usize, u64) -> String,
{
    let (head, args) = e.get_app_args();
    let head = head?;
    if let Expr::Const(name, _) = head {
        let name_str = name.to_string();
        if is_geometry_predicate(&name_str) {
            let pred = penrose_predicate_name(&name_str);
            let arg_names: Vec<String> = args.iter()
                .filter_map(|a| expr_to_arg_name(a, base_depth, bvar_name))
                .collect();
            if !pred.is_empty() && !arg_names.is_empty() {
                return Some(format!("{}({})\n", pred, arg_names.join(", ")));
            }
        }
    }
    None
}

fn expr_to_arg_name<F>(e: &Expr, base_depth: usize, bvar_name: &F) -> Option<String>
where
    F: Fn(usize, u64) -> String,
{
    match e {
        Expr::FVar(n) => Some(n.to_string()),
        Expr::BVar(n) => Some(bvar_name(base_depth, *n)),
        _ => None,
    }
}
