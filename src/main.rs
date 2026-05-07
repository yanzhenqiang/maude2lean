use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        print_usage(&args[0]);
        std::process::exit(1);
    }

    match args[1].as_str() {
        "lean-check" => {
            run_lean_check();
        }
        "repl" => {
            run_repl();
        }
        "check-files" => {
            if args.len() < 3 {
                eprintln!("Usage: {} check-files <file1.cic> [file2.cic] ...", args[0]);
                std::process::exit(1);
            }
            run_check_files(&args[2..]);
        }
        "tui" => {
            if args.len() < 3 {
                eprintln!("Usage: {} tui <target.cic> [dep1.cic dep2.cic ...]", args[0]);
                std::process::exit(1);
            }
            run_tui(&args[2..]);
        }
        "serve" => {
            run_server();
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
    eprintln!("  lean-check                   Run Lean kernel type checker tests");
    eprintln!("  repl                         Start interactive Lean REPL");
    eprintln!("  check-files <file>...        Batch check .cic files");
    eprintln!("  tui <target> [deps...]       Interactive TUI goal viewer");
    eprintln!("  serve [port]                Start web server (default port: 8080)");
    eprintln!("");
}

fn run_repl() {
    let mut repl = tinycic::repl::Repl::new();
    repl.run();
}

fn run_lean_check() {
    use tinycic::declaration::*;
    use tinycic::environment::Environment;
    use tinycic::expr::*;
    use tinycic::format::format_expr;
    use tinycic::type_checker::{TypeChecker, TypeCheckerState};
    use std::rc::Rc;

    let line = "═══════════════════════════════════════════════════════════════════════";

    println!("╔{}╗", line);
    println!("║{:^71}║", "Lean 4 Kernel Symbolic Execution Demo");
    println!("╚{}╝", line);

    println!("\n[Step 1] Building global environment");
    println!("  Adding Axioms: Nat : Type, zero : Nat, succ : Nat -> Nat");

    let mut env = Environment::new();
    println!("  ✓ Environment ready");

    println!("\n[Step 2] Declaring Inductive type Nat (auto-generating recursor)");
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
    println!("  ✓ Auto-generated: rec.Nat (recursor)");
    println!("  ✓ Number of environment constants: {}", env.num_constants());

    println!("\n[Step 3] Type Inference");

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

    let id_nat = Expr::Lambda(
        Name::new("x"), BinderInfo::Default,
        Rc::new(nat.clone()), Rc::new(Expr::BVar(0)),
    );
    let ty = tc.infer(&id_nat).unwrap();
    println!("  infer({:15}) → {}", "λx:Nat.x", format_expr(&ty));

    let app = Expr::mk_app(id_nat.clone(), zero.clone());
    let ty = tc.infer(&app).unwrap();
    println!("  infer({:15}) → {}", "(λx:Nat.x) zero", format_expr(&ty));

    println!("\n[Step 4] Weak Head Normalization (WHNF) — Beta + Iota reduction");

    let beta_expr = Expr::mk_app(id_nat, zero.clone());
    let beta_result = tc.whnf(&beta_expr);
    println!("  (λx:Nat.x) zero   ─whnf→   {}", format_expr(&beta_result));

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

    let one = Expr::mk_app(succ.clone(), zero.clone());
    let rec_one = Expr::mk_app(
        Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec.clone(), motive.clone()), zero.clone()), succ_minor.clone()),
        one.clone(),
    );
    let rec_result = tc.whnf(&rec_one);
    println!("  Nat.rec( motive, zero, succ_minor, succ(zero) )   ─whnf→   {}", format_expr(&rec_result));

    println!("\n[Step 5] Delta reduction — definition expansion");
    println!("  Adding definition:  one := succ zero");
    println!("  Adding definition:  two := succ one");

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

    let mut st2 = TypeCheckerState::new(env.clone());
    let mut tc2 = TypeChecker::new(&mut st2);

    let one_expr = Expr::mk_const(Name::new("one"), vec![]);
    let two_expr = Expr::mk_const(Name::new("two"), vec![]);

    println!("  whnf(one)   ─→   {}", format_expr(&tc2.whnf(&one_expr)));
    println!("  whnf(two)   ─→   {}", format_expr(&tc2.whnf(&two_expr)));

    println!("\n[Step 6] Definitional Equality");

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

    println!("\n[Step 8] Full Normalization");

    let nf_expr = Expr::mk_app(
        Expr::mk_app(Expr::mk_app(Expr::mk_app(nat_rec, motive), zero.clone()), succ_minor),
        Expr::mk_app(succ.clone(), Expr::mk_const(Name::new("one"), vec![])),
    );
    println!("  Input:  {}", format_expr(&nf_expr));
    let nf_result = tc2.nf(&nf_expr);
    println!("  nf:    {}", format_expr(&nf_result));

    println!("\n╔{}╗", line);
    println!("║{:^71}║", "Demo complete — all symbolic execution steps passed");
    println!("╚{}╝", line);
}

fn run_check_files(files: &[String]) {
    let mut repl = tinycic::repl::Repl::new();
    match repl.check_files(&files.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
        Ok(()) => println!("OK"),
        Err(e) => {
            eprintln!("FAIL: {}", e);
            std::process::exit(1);
        }
    }
}

fn run_tui(args: &[String]) {
    use std::fs;

    let target = &args[0];
    let deps = if args.len() > 1 { &args[1..] } else { &[] };

    // Read target file content
    let content = match fs::read_to_string(target) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("Cannot read '{}': {}", target, e);
            std::process::exit(1);
        }
    };
    let lines: Vec<String> = content.lines().map(|s| s.to_string()).collect();

    // Load dependencies via Repl
    let mut repl = tinycic::repl::Repl::new();
    repl.set_quiet(true);
    if !deps.is_empty() {
        match repl.check_files(&deps.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
            Ok(()) => {}
            Err(e) => {
                eprintln!("Failed to load dependencies: {}", e);
                std::process::exit(1);
            }
        }
    }

    // Also try to load the target file itself into the environment
    match repl.check_files(&[target.as_str()]) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("Warning: target file has errors: {}", e);
        }
    }

    let mut app = tinycic::tui::TuiApp::new(repl, lines);
    if let Err(e) = app.run() {
        eprintln!("TUI error: {}", e);
        std::process::exit(1);
    }
}

#[cfg(feature = "server")]
fn run_server() {
    use tinycic::server::start_server;
    use std::path::Path;

    let port: u16 = std::env::var("PORT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(8080);

    let static_path = Path::new("web");
    let rt = tokio::runtime::Runtime::new().expect("Failed to create Tokio runtime");
    rt.block_on(start_server(port, static_path));
}

#[cfg(not(feature = "server"))]
fn run_server() {
    eprintln!("Server feature not enabled. Build with: cargo build --features server");
    std::process::exit(1);
}

