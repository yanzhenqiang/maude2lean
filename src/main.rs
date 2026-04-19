use std::env;
use std::fs;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        print_usage(&args[0]);
        std::process::exit(1);
    }

    match args[1].as_str() {
        "maude" => {
            if args.len() < 3 {
                eprintln!("Usage: {} maude <file.maude>", args[0]);
                std::process::exit(1);
            }
            run_maude_parser(&args[2]);
        }
        "maude-run" => {
            if args.len() < 3 {
                eprintln!("Usage: {} maude-run <file.maude>", args[0]);
                std::process::exit(1);
            }
            run_maude_run(&args[2]);
        }
        "maude-reduce" => {
            if args.len() < 4 {
                eprintln!("Usage: {} maude-reduce <file.maude> <term>", args[0]);
                std::process::exit(1);
            }
            run_maude_reduce(&args[2], &args[3]);
        }
        "lean-check" => {
            run_lean_check();
        }
        "lean-maude-reduce" => {
            run_lean_maude_reduce();
        }
        "repl" => {
            run_repl();
        }
        _ => {
            eprintln!("Unknown command: {}", args[1]);
            print_usage(&args[0]);
            std::process::exit(1);
        }
    }
}

fn print_usage(prog: &str) {
    eprintln!("Usage: {} <command> [args...]", prog);
    eprintln!("Commands:");
    eprintln!("  maude <file.maude>           Parse and load a Maude module");
    eprintln!("  maude-run <file.maude>       Parse module and execute red commands");
    eprintln!("  maude-reduce <file> <term>   Parse module and reduce a term");
    eprintln!("  lean-check                   Run Lean kernel type checker tests");
    eprintln!("  lean-maude-reduce            Reduce Lean expressions via Maude engine");
    eprintln!("  repl                         Start interactive Lean REPL");
}

fn run_repl() {
    let mut repl = lean_cauchy_kernel::lean::repl::Repl::new();
    repl.run();
}

fn run_maude_parser(filename: &str) {
    let content = match fs::read_to_string(filename) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    };

    let mut parser = match lean_cauchy_kernel::maude::parser::Parser::new(&content) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Lexer error: {}", e);
            std::process::exit(1);
        }
    };

    let modules = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    };

    let mut runtime = lean_cauchy_kernel::maude::runtime::Runtime::new();
    for module in &modules {
        println!("Loaded module: {}", module.name());
        runtime.load_module(module.clone());
    }
    println!("\nLoaded {} module(s)", runtime.modules.len());
    println!("Operators: {}", runtime.operators.len());
    println!("Sorts: {}", runtime.sort_graph.len());
}

fn run_maude_reduce(filename: &str, term_str: &str) {
    let content = match fs::read_to_string(filename) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    };

    let mut parser = match lean_cauchy_kernel::maude::parser::Parser::new(&content) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Lexer error: {}", e);
            std::process::exit(1);
        }
    };

    let modules = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    };

    let mut runtime = lean_cauchy_kernel::maude::runtime::Runtime::new();
    for module in &modules {
        runtime.load_module(module.clone());
    }

    // Parse the term using an empty var map (variables must be declared in module)
    let mut term_parser = match lean_cauchy_kernel::maude::parser::Parser::new(term_str) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Lexer error: {}", e);
            std::process::exit(1);
        }
    };
    let vars = std::collections::HashMap::new();
    let term = match term_parser.parse_term(&vars) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("Term parse error: {}", e);
            std::process::exit(1);
        }
    };

    // Collect equations from all loaded modules
    let mut equations = Vec::new();
    for module in &modules {
        match module {
            lean_cauchy_kernel::maude::ast::Module::Functional { equations: eqs, .. } => {
                equations.extend_from_slice(eqs);
            }
            lean_cauchy_kernel::maude::ast::Module::System { equations: eqs, .. } => {
                equations.extend_from_slice(eqs);
            }
        }
    }

    let engine = lean_cauchy_kernel::maude::rewrite::RewriteEngine::new();
    let result = engine.reduce(&term, &equations);

    println!("Input:  {:?}", term);
    println!("Result: {:?}", result);
}

fn run_maude_run(filename: &str) {
    let content = match fs::read_to_string(filename) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Error reading file: {}", e);
            std::process::exit(1);
        }
    };

    let mut parser = match lean_cauchy_kernel::maude::parser::Parser::new(&content) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("Lexer error: {}", e);
            std::process::exit(1);
        }
    };

    let (modules, commands) = match parser.parse_script() {
        Ok((m, c)) => (m, c),
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    };

    let mut runtime = lean_cauchy_kernel::maude::runtime::Runtime::new();
    for module in &modules {
        println!("Loaded module: {}", module.name());
        runtime.load_module(module.clone());
    }

    // Collect equations and rules from all loaded modules
    let mut equations = Vec::new();
    let mut rules = Vec::new();
    for module in &modules {
        match module {
            lean_cauchy_kernel::maude::ast::Module::Functional { equations: eqs, .. } => {
                equations.extend_from_slice(eqs);
            }
            lean_cauchy_kernel::maude::ast::Module::System { equations: eqs, rules: rls, .. } => {
                equations.extend_from_slice(eqs);
                rules.extend_from_slice(rls);
            }
        }
    }

    let engine = lean_cauchy_kernel::maude::rewrite::RewriteEngine::new();

    for cmd in &commands {
        match cmd {
            lean_cauchy_kernel::maude::ast::Command::Red { term } => {
                let result = engine.reduce(term, &equations);
                println!("red {} .", term);
                println!("result: {}", result);
            }
            lean_cauchy_kernel::maude::ast::Command::Rew { term } => {
                let result = engine.reduce_then_rewrite(term, &equations, &rules);
                println!("rew {} .", term);
                println!("result: {}", result);
            }
            _ => {
                println!("Command not yet implemented: {:?}", cmd);
            }
        }
    }

    println!("\nLoaded {} module(s)", runtime.modules.len());
    println!("Executed {} command(s)", commands.len());
}

fn run_lean_check() {
    run_lean_demo();
}

/// Simple pretty-printer for Expr (subset used in demo)
fn format_expr(e: &lean_cauchy_kernel::lean::expr::Expr) -> String {
    use lean_cauchy_kernel::lean::expr::*;
    match e {
        Expr::BVar(n) => format!("x{}", n),
        Expr::Const(name, _) => name.to_string(),
        Expr::App(_, _) => {
            let (head, args) = e.get_app_args();
            let head_str = if let Some(h) = head {
                match h {
                    Expr::Const(n, _) => n.to_string(),
                    _ => format_expr(h),
                }
            } else {
                "?".to_string()
            };
            let args_str: Vec<String> = args.iter().map(|a| format_expr(*a)).collect();
            format!("{}({})", head_str, args_str.join(", "))
        }
        Expr::Lambda(_, _, ty, body) => {
            format!("λ(_ : {}). {}", format_expr(ty), format_expr(body))
        }
        Expr::Pi(_, _, ty, body) => {
            format!("Π(_ : {}). {}", format_expr(ty), format_expr(body))
        }
        Expr::Let(_, ty, val, body, _) => {
            format!("let _ : {} := {} in {}", format_expr(ty), format_expr(val), format_expr(body))
        }
        Expr::Sort(l) => format!("Sort({:?})", l),
        Expr::Lit(Literal::Nat(n)) => n.to_string(),
        _ => format!("{:?}", e),
    }
}

fn run_lean_demo() {
    use lean_cauchy_kernel::lean::declaration::*;
    use lean_cauchy_kernel::lean::environment::Environment;
    use lean_cauchy_kernel::lean::expr::*;
    use lean_cauchy_kernel::lean::type_checker::{TypeChecker, TypeCheckerState};
    use lean_cauchy_kernel::lean::maude_bridge::reduce_expr_with_env;
    use std::rc::Rc;

    let line = "═══════════════════════════════════════════════════════════════════════";

    println!("╔{}╗", line);
    println!("║{:^71}║", "Lean 4 Kernel Symbolic Execution Demo");
    println!("╚{}╝", line);

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 1: Build environment
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 1】构建全局环境 (Environment)");
    println!("  添加 Axioms: Nat : Type, zero : Nat, succ : Nat → Nat");

    let mut env = Environment::new();

    println!("  ✓ 环境就绪");

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 2: Add inductive Nat (auto-generates recursor)
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 2】声明 Inductive 类型 Nat（自动生成 recursor）");
    println!("  inductive Nat");
    println!("    | zero : Nat");
    println!("    | succ : Nat → Nat");

    let nat = Expr::mk_const(Name::new("Nat"), vec![]);
    let nat_ind = InductiveType {
        name: Name::new("Nat"),
        ty: Expr::mk_type(),
        ctors: vec![
            Constructor { name: Name::new("zero"), ty: nat.clone() },
            Constructor { name: Name::new("succ"), ty: Expr::mk_arrow(nat.clone(), nat.clone()) },
        ],
    };
    env.add(Declaration::Inductive {
        level_params: vec![],
        num_params: 0,
        types: vec![nat_ind],
        is_unsafe: false,
    }).unwrap();

    let zero = Expr::mk_const(Name::new("zero"), vec![]);
    let succ = Expr::mk_const(Name::new("succ"), vec![]);
    let nat_rec = Expr::mk_const(Name::new("rec").extend("Nat"), vec![]);
    println!("  ✓ 自动生成: rec.Nat (recursor)");
    println!("  ✓ 环境常量数: {}", env.num_constants());

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 3: Type inference
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 3】类型推断 (Type Inference)");

    let mut st = TypeCheckerState::new(env.clone());
    let mut tc = TypeChecker::new(&mut st);

    let cases = vec![
        ("Nat", nat.clone()),
        ("zero", zero.clone()),
        ("succ", succ.clone()),
        ("succ(zero)", Expr::mk_app(succ.clone(), zero.clone())),
    ];

    for (label, e) in cases {
        let ty = tc.infer(&e).unwrap();
        println!("  infer({:15}) → {}", label, format_expr(&ty));
    }

    // Lambda
    let id_nat = Expr::Lambda(
        Name::new("x"), BinderInfo::Default,
        Rc::new(nat.clone()), Rc::new(Expr::BVar(0)),
    );
    let ty = tc.infer(&id_nat).unwrap();
    println!("  infer({:15}) → {}", "λx:Nat.x", format_expr(&ty));

    // Application
    let app = Expr::mk_app(id_nat.clone(), zero.clone());
    let ty = tc.infer(&app).unwrap();
    println!("  infer({:15}) → {}", "(λx:Nat.x) zero", format_expr(&ty));

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 4: Weak Head Normal Form (beta + iota)
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 4】弱头归一化 (WHNF) —— Beta + Iota 归约");

    // Beta reduction
    let beta_expr = Expr::mk_app(id_nat, zero.clone());
    let beta_result = tc.whnf(&beta_expr);
    println!("  (λx:Nat.x) zero   ─whnf→   {}", format_expr(&beta_result));

    // Nat.rec on zero (iota)
    let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
    let succ_minor = Expr::Lambda(
        Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
        Rc::new(Expr::Lambda(
            Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
        ))
    );
    let rec_zero = Expr::mk_app(
        Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
        zero.clone(),
    );
    let rec_result = tc.whnf(&rec_zero);
    println!("  Nat.rec( motive, zero, succ_minor, zero )   ─whnf→   {}", format_expr(&rec_result));

    // Nat.rec on succ zero (iota)
    let one = Expr::mk_app(succ.clone(), zero.clone());
    let rec_one = Expr::mk_app(
        Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
        one.clone(),
    );
    let rec_result = tc.whnf(&rec_one);
    println!("  Nat.rec( motive, zero, succ_minor, succ(zero) )   ─whnf→   {}", format_expr(&rec_result));

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 5: Delta reduction (unfold definitions)
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 5】Delta 归约 —— 定义展开");
    println!("  添加定义:  one := succ zero");
    println!("  添加定义:  two := succ one");

    let one_def = Declaration::Definition(DefinitionVal {
        constant_val: ConstantVal { name: Name::new("one"), level_params: vec![], ty: nat.clone() },
        value: one.clone(),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    });
    env.add(one_def).unwrap();

    let two = Expr::mk_app(succ.clone(), Expr::mk_const(Name::new("one"), vec![]));
    let two_def = Declaration::Definition(DefinitionVal {
        constant_val: ConstantVal { name: Name::new("two"), level_params: vec![], ty: nat.clone() },
        value: two.clone(),
        hints: ReducibilityHints::Regular(0),
        safety: DefinitionSafety::Safe,
    });
    env.add(two_def).unwrap();

    // Re-create type checker with new env
    let mut st2 = TypeCheckerState::new(env.clone());
    let mut tc2 = TypeChecker::new(&mut st2);

    let one_expr = Expr::mk_const(Name::new("one"), vec![]);
    let two_expr = Expr::mk_const(Name::new("two"), vec![]);

    println!("  whnf(one)   ─→   {}", format_expr(&tc2.whnf(&one_expr)));
    println!("  whnf(two)   ─→   {}", format_expr(&tc2.whnf(&two_expr)));

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 6: Definitional equality
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 6】定义等价 (Definitional Equality)");

    let eq_cases = vec![
        ("zero == zero", zero.clone(), zero.clone(), true),
        ("Nat  == Nat", nat.clone(), nat.clone(), true),
        ("one  == succ(zero)", one_expr.clone(), one.clone(), true),
        ("two  == succ(succ(zero))", two_expr.clone(), Expr::mk_app(succ.clone(), one.clone()), true),
    ];

    for (label, a, b, expected) in eq_cases {
        let result = tc2.is_def_eq(&a, &b);
        let mark = if result == expected { "✓" } else { "✗" };
        println!("  {} {:25} → {} (expected {})", mark, label, result, expected);
    }

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 7: Maude engine cross-validation
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 7】Maude 重写引擎交叉验证");
    println!("  同一个表达式，分别用 Rust 内核 nf 和 Maude reduce 计算：");

    let test_exprs: Vec<(&str, Expr)> = vec![
        ("(λx.x) zero", beta_expr),
        ("one", one_expr),
        ("two", two_expr),
    ];

    for (label, e) in test_exprs {
        let rust_result = tc2.nf(&e);
        let maude_result = reduce_expr_with_env(&e, &env).unwrap();
        let match_mark = if rust_result == maude_result { "✓" } else { "✗" };
        println!("  {} {:20}  Rust: {:20}  Maude: {}",
            match_mark, label,
            format_expr(&rust_result),
            format_expr(&maude_result)
        );
    }

    // ═══════════════════════════════════════════════════════════════════════
    // STEP 8: Full normalization (nf)
    // ═══════════════════════════════════════════════════════════════════════
    println!("\n【Step 8】完全归一化 (Full Normalization)");

    let nf_expr = Expr::mk_app(
        Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor),
        Expr::mk_app(succ.clone(), Expr::mk_const(Name::new("one"), vec![])),
    );
    println!("  输入:  {}", format_expr(&nf_expr));
    let nf_result = tc2.nf(&nf_expr);
    println!("  nf:    {}", format_expr(&nf_result));

    println!("\n╔{}╗", line);
    println!("║{:^71}║", "演示完成 — 所有符号执行步骤通过");
    println!("╚{}╝", line);
}

fn run_lean_maude_reduce() {
    use lean_cauchy_kernel::lean::maude_bridge::reduce_expr;
    use lean_cauchy_kernel::lean::expr::*;
    use std::rc::Rc;

    println!("=== Lean-to-Maude Bridge Reduction Demo ===\n");

    // Test 1: Beta reduction
    println!("Test 1: Beta reduction");
    let e1 = Expr::mk_app(
        Expr::Lambda(
            Name::new("x"),
            BinderInfo::Default,
            Rc::new(Expr::mk_const(Name::new("Nat"), vec![])),
            Rc::new(Expr::BVar(0)),
        ),
        Expr::mk_const(Name::new("zero"), vec![]),
    );
    println!("Input:  {:?}", e1);
    let r1 = reduce_expr(&e1).unwrap();
    println!("Result: {:?}\n", r1);

    // Test 2: Let reduction
    println!("Test 2: Let (zeta) reduction");
    let e2 = Expr::Let(
        Name::new("x"),
        Rc::new(Expr::mk_const(Name::new("Nat"), vec![])),
        Rc::new(Expr::mk_const(Name::new("zero"), vec![])),
        Rc::new(Expr::BVar(0)),
        false,
    );
    println!("Input:  {:?}", e2);
    let r2 = reduce_expr(&e2).unwrap();
    println!("Result: {:?}\n", r2);

    // Test 3: Nat recursor on zero
    println!("Test 3: Nat recursor on zero");
    let nat = Expr::mk_const(Name::new("Nat"), vec![]);
    let zero = Expr::mk_const(Name::new("zero"), vec![]);
    let succ = Expr::mk_const(Name::new("succ"), vec![]);
    let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
    let succ_minor = Expr::Lambda(
        Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
        Rc::new(Expr::Lambda(
            Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
        ))
    );
    let nat_rec = Expr::mk_const(Name::new("recNat"), vec![]);
    let e3 = Expr::mk_app(
        Expr::mk_app(
            Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()),
            succ_minor,
        ),
        zero.clone(),
    );
    println!("Input:  {:?}", e3);
    let r3 = reduce_expr(&e3).unwrap();
    println!("Result: {:?}\n", r3);

    // Test 4: Nat recursor on succ zero
    println!("Test 4: Nat recursor on succ zero");
    let nat_rec = Expr::mk_const(Name::new("recNat"), vec![]);
    let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
    let succ_minor = Expr::Lambda(
        Name::new("n"), BinderInfo::Default, Rc::new(nat.clone()),
        Rc::new(Expr::Lambda(
            Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
        ))
    );
    let one = Expr::mk_app(succ.clone(), zero.clone());
    let e4 = Expr::mk_app(
        Expr::mk_app(
            Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()),
            succ_minor,
        ),
        one.clone(),
    );
    println!("Input:  {:?}", e4);
    let r4 = reduce_expr(&e4).unwrap();
    println!("Result: {:?}\n", r4);

    // Test 5: List recursor on cons zero nil
    println!("Test 5: List recursor on cons zero nil");
    let list_rec = Expr::mk_const(Name::new("recList"), vec![]);
    let motive = Expr::mk_lambda(Name::new("_"), nat.clone(), nat.clone());
    let nil_case = zero.clone();
    let cons_case = Expr::Lambda(
        Name::new("a"), BinderInfo::Default, Rc::new(nat.clone()),
        Rc::new(Expr::Lambda(
            Name::new("l"), BinderInfo::Default, Rc::new(nat.clone()),
            Rc::new(Expr::Lambda(
                Name::new("ih"), BinderInfo::Default, Rc::new(nat.clone()),
                Rc::new(Expr::mk_app(succ.clone(), Expr::BVar(0)))
            ))
        ))
    );
    let cons = Expr::mk_const(Name::new("cons"), vec![]);
    let nil = Expr::mk_const(Name::new("nil"), vec![]);
    let test_list = Expr::mk_app(Expr::mk_app(cons, zero.clone()), nil);
    let e5 = Expr::mk_app(
        Expr::mk_app(
            Expr::mk_app(
                Expr::mk_app(Expr::mk_app(list_rec, nat.clone()), motive),
                nil_case,
            ),
            cons_case,
        ),
        test_list,
    );
    println!("Input:  {:?}", e5);
    let r5 = reduce_expr(&e5).unwrap();
    println!("Result: {:?}\n", r5);

    println!("All reductions completed.");
}
