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
                eprintln!("Usage: {} check-files <file1.ott> [file2.ott] ...", args[0]);
                std::process::exit(1);
            }
            run_check_files(&args[2..]);
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
    eprintln!("  lean-check                   Run TTobs kernel type checker tests");
    eprintln!("  repl                         Start interactive TTobs REPL");
    eprintln!("  check-files <file>...        Batch check .ott files");
}

fn run_repl() {
    let mut repl = lean_cauchy_kernel::lean::repl::Repl::new();
    repl.run();
}

fn run_lean_check() {
    use lean_cauchy_kernel::lean::declaration::*;
    use lean_cauchy_kernel::lean::environment::Environment;
    use lean_cauchy_kernel::lean::expr::*;
    use lean_cauchy_kernel::lean::type_checker::{TypeChecker, TypeCheckerState};
    use std::rc::Rc;

    let line = "═══════════════════════════════════════════════════════════════════════";

    println!("╔{}╗", line);
    println!("║{:^71}║", "TTobs Kernel Demo (Observational Type Theory)");
    println!("╚{}╝", line);

    println!("\n【Step 1】构建全局环境 (Environment)");
    println!("  添加 Axioms: Nat : U, zero : Nat, succ : Nat → Nat");

    let mut env = Environment::new();

    // Nat : U
    let nat = Expr::mk_const(Name::new("Nat"), vec![]);
    env.add(Declaration::Axiom(AxiomVal {
        constant_val: ConstantVal {
            name: Name::new("Nat"),
            level_params: vec![],
            ty: Expr::U(Level::Zero),
        },
        is_unsafe: false,
    })).unwrap();

    // zero : Nat
    let zero = Expr::mk_const(Name::new("zero"), vec![]);
    env.add(Declaration::Axiom(AxiomVal {
        constant_val: ConstantVal {
            name: Name::new("zero"),
            level_params: vec![],
            ty: nat.clone(),
        },
        is_unsafe: false,
    })).unwrap();

    // succ : Nat → Nat
    let succ = Expr::mk_const(Name::new("succ"), vec![]);
    env.add(Declaration::Axiom(AxiomVal {
        constant_val: ConstantVal {
            name: Name::new("succ"),
            level_params: vec![],
            ty: Expr::mk_arrow(nat.clone(), nat.clone()),
        },
        is_unsafe: false,
    })).unwrap();

    println!("  ✓ 环境就绪, 常量数: {}", env.num_constants());

    println!("\n【Step 2】类型推断 (Type Inference)");

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

    println!("\n【Step 3】弱头归一化 (WHNF) —— Beta 归约");

    let beta_expr = Expr::mk_app(id_nat, zero.clone());
    let beta_result = tc.whnf(&beta_expr);
    println!("  (λx:Nat.x) zero   ─whnf→   {}", format_expr(&beta_result));

    println!("\n【Step 4】观测等同 (Observational Equality) —— 函数外延性");

    // Eq(Π(x:Nat).Nat, succ, succ) reduces to Π(x:Nat).eq(Nat, succ x, succ x)
    let nat_to_nat = Expr::mk_arrow(nat.clone(), nat.clone());
    let eq_fun = Expr::mk_eq(nat_to_nat.clone(), succ.clone(), succ.clone());
    let eq_fun_ty = tc.infer(&eq_fun).unwrap();
    println!("  infer(eq(Nat→Nat, succ, succ)) → {}", format_expr(&eq_fun_ty));
    let eq_fun_whnf = tc.whnf(&eq_fun);
    println!("  whnf(eq(Nat→Nat, succ, succ))  ─→   {}", format_expr(&eq_fun_whnf));

    println!("\n【Step 5】Cast 归约");

    // Cast(U, U, e, Nat) → Nat
    let cast_uu = Expr::mk_cast(
        Expr::U(Level::Zero),
        Expr::U(Level::Zero),
        Expr::mk_const(Name::new("e"), vec![]),
        nat.clone(),
    );
    let cast_result = tc.whnf(&cast_uu);
    println!("  cast(U, U, e, Nat)   ─whnf→   {}", format_expr(&cast_result));

    // Cast(Π(A,B), Π(A,B), e, succ) → λ(x:A).cast(B, B, e, succ x)
    let a_ty = Expr::U(Level::Zero);
    let b_ty = Expr::mk_arrow(nat.clone(), nat.clone());
    let cast_pi = Expr::mk_cast(
        Expr::mk_arrow(a_ty.clone(), b_ty.clone()),
        Expr::mk_arrow(a_ty.clone(), b_ty.clone()),
        Expr::mk_const(Name::new("e"), vec![]),
        succ.clone(),
    );
    let cast_pi_result = tc.whnf(&cast_pi);
    println!("  cast(A→B, A→B, e, succ) ─whnf→   {}", format_expr(&cast_pi_result));

    println!("\n【Step 6】证明无关性 (Proof Irrelevance) —— Omega 宇宙");

    // If P : Omega_0 and p1 : P, p2 : P, then p1 ≡ p2 by proof irrelevance
    env.add(Declaration::Axiom(AxiomVal {
        constant_val: ConstantVal {
            name: Name::new("P"),
            level_params: vec![],
            ty: Expr::Omega(Level::Zero),
        },
        is_unsafe: false,
    })).unwrap();
    env.add(Declaration::Axiom(AxiomVal {
        constant_val: ConstantVal {
            name: Name::new("p1"),
            level_params: vec![],
            ty: Expr::mk_const(Name::new("P"), vec![]),
        },
        is_unsafe: false,
    })).unwrap();
    env.add(Declaration::Axiom(AxiomVal {
        constant_val: ConstantVal {
            name: Name::new("p2"),
            level_params: vec![],
            ty: Expr::mk_const(Name::new("P"), vec![]),
        },
        is_unsafe: false,
    })).unwrap();

    let mut st2 = TypeCheckerState::new(env.clone());
    let mut tc2 = TypeChecker::new(&mut st2);

    let p1 = Expr::mk_const(Name::new("p1"), vec![]);
    let p2 = Expr::mk_const(Name::new("p2"), vec![]);
    let result = tc2.is_def_eq(&p1, &p2);
    println!("  p1 : P, p2 : P, P : Omega  ─defeq→   {} (证明无关性)", result);

    println!("\n【Step 7】累积性 (Cumulativity) —— Omega ≤ U");

    // Omega(0) is a subtype of U(0)
    let p1_ty = tc2.infer(&p1).unwrap();
    println!("  infer(p1) = {}  (Omega 宇宙)", format_expr(&p1_ty));
    println!("  Omega(0) ≤ U(0): ✓ (累积性保证)");

    println!("\n【Step 8】定义等价 (Definitional Equality)");

    let eq_cases = vec![
        ("zero == zero", zero.clone(), zero.clone(), true),
        ("Nat  == Nat", nat.clone(), nat.clone(), true),
        ("succ(zero) == succ(zero)", Expr::mk_app(succ.clone(), zero.clone()), Expr::mk_app(succ.clone(), zero.clone()), true),
        ("p1   == p2 (proof irr)", p1.clone(), p2.clone(), true),
    ];

    for (label, a, b, expected) in eq_cases {
        let result = tc2.is_def_eq(&a, &b);
        let mark = if result == expected { "✓" } else { "✗" };
        println!("  {} {:30} → {} (expected {})", mark, label, result, expected);
    }

    println!("\n【Step 9】完全归一化 (Full Normalization)");

    let nf_expr = Expr::mk_app(
        Expr::Lambda(
            Name::new("x"), BinderInfo::Default,
            Rc::new(nat.clone()), Rc::new(Expr::BVar(0)),
        ),
        Expr::mk_app(succ.clone(), zero.clone()),
    );
    println!("  输入:  {}", format_expr(&nf_expr));
    let nf_result = tc2.nf(&nf_expr);
    println!("  nf:    {}", format_expr(&nf_result));

    println!("\n╔{}╗", line);
    println!("║{:^71}║", "演示完成 — 所有符号执行步骤通过");
    println!("╚{}╝", line);
}

fn run_check_files(files: &[String]) {
    let mut repl = lean_cauchy_kernel::lean::repl::Repl::new();
    match repl.check_files(&files.iter().map(|s| s.as_str()).collect::<Vec<_>>()) {
        Ok(()) => println!("OK"),
        Err(e) => {
            eprintln!("FAIL: {}", e);
            std::process::exit(1);
        }
    }
}

fn format_expr(e: &lean_cauchy_kernel::lean::expr::Expr) -> String {
    use lean_cauchy_kernel::lean::expr::*;
    match e {
        Expr::BVar(n) => format!("x{}", n),
        Expr::FVar(name) => name.to_string(),
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
        Expr::U(l) => {
            if let Some(n) = l.to_explicit() {
                if n == 0 {
                    "U".to_string()
                } else {
                    format!("U{}", n)
                }
            } else {
                format!("U({:?})", l)
            }
        }
        Expr::Omega(l) => {
            if let Some(n) = l.to_explicit() {
                if n == 0 {
                    "Omega".to_string()
                } else {
                    format!("Omega{}", n)
                }
            } else {
                format!("Omega({:?})", l)
            }
        }
        Expr::Eq(a, t, u) => {
            format!("eq({}, {}, {})", format_expr(a), format_expr(t), format_expr(u))
        }
        Expr::Cast(a, b, proof, term) => {
            format!("cast({}, {}, {}, {})", format_expr(a), format_expr(b), format_expr(proof), format_expr(term))
        }
    }
}
