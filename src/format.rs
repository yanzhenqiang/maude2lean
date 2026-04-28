use crate::expr::*;

// Precedence levels for parentheses.
const PREC_ARROW: u8 = 1;
const PREC_EQ: u8 = 2;
const PREC_AND: u8 = 3;
const PREC_OR: u8 = 4;
const PREC_NOT: u8 = 5;
const PREC_ADD: u8 = 6;
const PREC_MUL: u8 = 7;
const PREC_APP: u8 = 8;

/// Format an Expr into a human-readable string.
pub fn format_expr(e: &Expr) -> String {
    format_expr_with_binders(e, 0, &[])
}

/// Format an Expr with a stack of binder names for BVar resolution.
pub fn format_expr_with_binders(e: &Expr, prec: u8, binders: &[String]) -> String {
    if let Some((s, op_prec)) = try_format_special(e, binders) {
        return if prec > op_prec {
            format!("({})", s)
        } else {
            s
        };
    }

    // Try to format as a numeric literal
    if let Some(n) = try_format_nat_lit(e) {
        return n.to_string();
    }

    match e {
        Expr::BVar(n) => {
            let idx = *n as usize;
            if idx < binders.len() {
                binders[binders.len() - 1 - idx].clone()
            } else {
                format!("x{}", n)
            }
        }
        Expr::FVar(name) => pretty_fvar_name(name),
        Expr::Const(name, _) => {
            let s = name.to_string();
            match s.as_str() {
                "Nat.zero" => "0".to_string(),
                _ => s,
            }
        }
        Expr::App(_, _) => {
            let (head, args) = e.get_app_args();
            let head_str = if let Some(h) = head {
                match h {
                    Expr::Const(n, _) => n.to_string(),
                    _ => format_expr_with_binders(h, PREC_APP + 1, binders),
                }
            } else {
                "?".to_string()
            };
            let args_str: Vec<String> = args
                .iter()
                .map(|a| format_expr_with_binders(a, PREC_APP + 1, binders))
                .collect();
            if args_str.is_empty() {
                head_str
            } else {
                let s = format!("{} {}", head_str, args_str.join(" "));
                if prec > PREC_APP {
                    format!("({})", s)
                } else {
                    s
                }
            }
        }
        Expr::Lambda(name, _, ty, body) => {
            let mut new_binders = binders.to_vec();
            let display_name = if name.to_string() == "_" {
                format!("_{}", binders.len())
            } else {
                name.to_string()
            };
            new_binders.push(display_name.clone());
            let s = format!(
                "fun {} : {} => {}",
                display_name,
                format_expr_with_binders(ty, 0, binders),
                format_expr_with_binders(body, 0, &new_binders)
            );
            if prec > 0 {
                format!("({})", s)
            } else {
                s
            }
        }
        Expr::Pi(name, _, ty, body) => {
            let is_prop = is_prop_type(body);
            let mut new_binders = binders.to_vec();
            let display_name = if name.to_string() == "_" {
                format!("_{}", binders.len())
            } else {
                name.to_string()
            };
            new_binders.push(display_name.clone());
            let s = if is_prop && name.to_string() != "_" {
                format!(
                    "forall ({} : {}), {}",
                    display_name,
                    format_expr_with_binders(ty, 0, binders),
                    format_expr_with_binders(body, 0, &new_binders)
                )
            } else if name.to_string() == "_" {
                format!(
                    "{} -> {}",
                    format_expr_with_binders(ty, PREC_ARROW, binders),
                    format_expr_with_binders(body, PREC_ARROW, &new_binders)
                )
            } else {
                format!(
                    "({} : {}) -> {}",
                    display_name,
                    format_expr_with_binders(ty, 0, binders),
                    format_expr_with_binders(body, 0, &new_binders)
                )
            };
            if prec > PREC_ARROW {
                format!("({})", s)
            } else {
                s
            }
        }
        Expr::Let(name, ty, val, body, _) => {
            let s = format!(
                "let {} : {} := {} in {}",
                name.to_string(),
                format_expr_with_binders(ty, 0, binders),
                format_expr_with_binders(val, 0, binders),
                format_expr_with_binders(body, 0, binders)
            );
            if prec > 0 {
                format!("({})", s)
            } else {
                s
            }
        }
        Expr::Sort(l) => format_sort(l),
        Expr::MVar(name) => format!("?{}", name.to_string()),
        Expr::Proj(name, idx, e) => format!(
            "{}.{}{})",
            format_expr_with_binders(e, 0, binders),
            idx,
            name.to_string()
        ),
        Expr::Lit(l) => format!("{:?}", l),
        _ => format!("{:?}", e),
    }
}

/// Try to detect and format a Nat literal: succ^n zero -> n.
fn try_format_nat_lit(e: &Expr) -> Option<u64> {
    let mut current = e;
    let mut count = 0u64;
    loop {
        let (head, args) = current.get_app_args();
        let head = head?;
        if let Expr::Const(name, _) = head {
            if name.to_string() == "Nat.succ" && args.len() == 1 {
                count += 1;
                current = args[0];
                continue;
            }
            if name.to_string() == "Nat.zero" && args.is_empty() {
                return Some(count);
            }
        }
        return None;
    }
}

/// Try to format common patterns as infix operators.
/// Returns (formatted_string, precedence).
fn try_format_special(e: &Expr, binders: &[String]) -> Option<(String, u8)> {
    let (head, args) = e.get_app_args();
    let head = head?;

    if let Expr::Const(name, _) = head {
        let n = name.to_string();
        match n.as_str() {
            "Eq" if args.len() >= 2 => {
                let a = format_expr_with_binders(args[args.len() - 2], PREC_EQ + 1, binders);
                let b = format_expr_with_binders(args[args.len() - 1], PREC_EQ + 1, binders);
                Some((format!("{} = {}", a, b), PREC_EQ))
            }
            "And" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_AND + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_AND + 1, binders);
                Some((format!("{} /\\ {}", a, b), PREC_AND))
            }
            "Or" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_OR + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_OR + 1, binders);
                Some((format!("{} \\/ {}", a, b), PREC_OR))
            }
            "Not" if args.len() == 1 => {
                let a = format_expr_with_binders(args[0], PREC_NOT + 1, binders);
                Some((format!("~{}", a), PREC_NOT))
            }
            "le" | "nat_le" | "Nat.le" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_EQ + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_EQ + 1, binders);
                Some((format!("{} <= {}", a, b), PREC_EQ))
            }
            "lt" | "nat_lt" | "Nat.lt" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_EQ + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_EQ + 1, binders);
                Some((format!("{} < {}", a, b), PREC_EQ))
            }
            "ge" | "nat_ge" | "Nat.ge" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_EQ + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_EQ + 1, binders);
                Some((format!("{} >= {}", a, b), PREC_EQ))
            }
            "gt" | "nat_gt" | "Nat.gt" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_EQ + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_EQ + 1, binders);
                Some((format!("{} > {}", a, b), PREC_EQ))
            }
            "add"
            | "nat_add"
            | "Nat.add"
            | "int_add"
            | "Int.add"
                if args.len() == 2 =>
            {
                let a = format_expr_with_binders(args[0], PREC_ADD + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_ADD + 1, binders);
                Some((format!("{} + {}", a, b), PREC_ADD))
            }
            "mul"
            | "nat_mul"
            | "Nat.mul"
            | "int_mul"
            | "Int.mul"
                if args.len() == 2 =>
            {
                let a = format_expr_with_binders(args[0], PREC_MUL + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_MUL + 1, binders);
                Some((format!("{} * {}", a, b), PREC_MUL))
            }
            "sub"
            | "nat_sub"
            | "Nat.sub"
            | "int_sub"
            | "Int.sub"
                if args.len() == 2 =>
            {
                let a = format_expr_with_binders(args[0], PREC_ADD + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_ADD + 1, binders);
                Some((format!("{} - {}", a, b), PREC_ADD))
            }
            "div" | "nat_div" | "Nat.div" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_MUL + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_MUL + 1, binders);
                Some((format!("{} / {}", a, b), PREC_MUL))
            }
            "mod" | "nat_mod" | "Nat.mod" if args.len() == 2 => {
                let a = format_expr_with_binders(args[0], PREC_MUL + 1, binders);
                let b = format_expr_with_binders(args[1], PREC_MUL + 1, binders);
                Some((format!("{} % {}", a, b), PREC_MUL))
            }
            "Nat.succ" if args.len() == 1 => {
                let a = format_expr_with_binders(args[0], PREC_APP + 1, binders);
                Some((format!("succ {}", a), PREC_APP))
            }
            _ => None,
        }
    } else {
        None
    }
}

/// Strip generated suffix like ".0" from FVar names.
fn pretty_fvar_name(name: &Name) -> String {
    let s = name.to_string();
    if let Some(dot_pos) = s.rfind('.') {
        if s[dot_pos + 1..].chars().all(|c| c.is_ascii_digit()) {
            return s[..dot_pos].to_string();
        }
    }
    s
}

fn format_sort(l: &Level) -> String {
    match l {
        Level::Zero => "Prop".to_string(),
        Level::Succ(inner) => {
            if **inner == Level::Zero {
                "Type".to_string()
            } else {
                format!("Type_{}", level_to_num(l))
            }
        }
        _ => format!("Sort({})", format_level(l)),
    }
}

fn format_level(l: &Level) -> String {
    match l {
        Level::Zero => "0".to_string(),
        Level::Succ(inner) => format!("{}+1", format_level(inner)),
        Level::Max(a, b) => format!("max({}, {})", format_level(a), format_level(b)),
        Level::IMax(a, b) => format!("imax({}, {})", format_level(a), format_level(b)),
        Level::Param(n) => n.to_string(),
        Level::MVar(n) => format!("?{}", n.to_string()),
    }
}

fn level_to_num(l: &Level) -> u32 {
    match l {
        Level::Zero => 0,
        Level::Succ(inner) => level_to_num(inner) + 1,
        _ => 0,
    }
}

fn is_prop_type(e: &Expr) -> bool {
    match e {
        Expr::Sort(l) => *l == Level::Zero,
        Expr::Pi(_, _, _, body) => is_prop_type(body),
        _ => false,
    }
}
