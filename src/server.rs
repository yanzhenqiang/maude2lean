#[cfg(feature = "server")]
use std::collections::HashMap;
#[cfg(feature = "server")]
use std::fs;
#[cfg(feature = "server")]
use std::net::SocketAddr;
#[cfg(feature = "server")]
use std::path::PathBuf;
#[cfg(feature = "server")]
use std::rc::Rc;

#[cfg(feature = "server")]
use axum::{
    http::StatusCode,
    response::IntoResponse,
    routing::{get, get_service, post},
    Json, Router,
};
#[cfg(feature = "server")]
use tower_http::cors::{Any, CorsLayer};
#[cfg(feature = "server")]
use tower_http::services::ServeFile;

#[cfg(feature = "server")]
use crate::environment::Environment;
#[cfg(feature = "server")]
use crate::expr::*;
#[cfg(feature = "server")]
use crate::format::*;
#[cfg(feature = "server")]
use crate::repl::Repl;
#[cfg(feature = "server")]
use crate::repl_parser::{ParsedDecl, ParsedExpr, Parser as ReplParser};
#[cfg(feature = "server")]
use crate::tactic::TacticEngine;
#[cfg(feature = "server")]
use crate::type_checker::{TypeChecker, TypeCheckerState};

// Use tokio's async-aware lock for shared state
#[cfg(feature = "server")]
use tokio::sync::RwLock;

#[cfg(feature = "server")]
#[derive(Clone)]
struct AppState {
    file_lines: Vec<String>,
    current_file: String,
    declarations: Vec<String>,
}

// Global state - we store file info but NOT the Repl state (which contains Rc)
#[cfg(feature = "server")]
static APP_STATE: std::sync::Mutex<Option<AppState>> = std::sync::Mutex::new(None);

#[derive(serde::Deserialize)]
pub struct LoadRequest {
    pub target: String,
    pub dependencies: Vec<String>,
}

#[derive(serde::Serialize)]
pub struct LoadResponse {
    pub success: bool,
    pub error: Option<String>,
}

#[derive(serde::Serialize)]
pub struct LineInfoResponse {
    pub success: bool,
    pub line: usize,
    pub info: Vec<String>,
    pub goals: Option<Vec<TacticGoal>>,
    pub penrose_available: bool,
    pub error: Option<String>,
}

#[derive(serde::Serialize, Clone)]
pub struct TacticGoal {
    pub hypotheses: Vec<String>,
    pub goal: String,
}

#[derive(serde::Serialize)]
pub struct EnvResponse {
    pub success: bool,
    pub declarations: Vec<String>,
    pub error: Option<String>,
}

#[derive(serde::Serialize)]
pub struct InfixOpsResponse {
    pub success: bool,
    pub ops: HashMap<String, String>,
}

#[derive(serde::Serialize)]
pub struct NotationsResponse {
    pub success: bool,
    pub notations: HashMap<String, String>,
}

#[derive(serde::Serialize)]
pub struct ListFilesResponse {
    pub success: bool,
    pub files: Vec<String>,
    pub error: Option<String>,
}

// --- Helper functions (same as tui.rs) ---

#[cfg(feature = "server")]
fn find_decl_start(file_lines: &[String], line_idx: usize) -> Option<usize> {
    for i in (0..=line_idx).rev() {
        let trimmed = file_lines[i].trim();
        if trimmed.starts_with("theorem ") || trimmed.starts_with("def ") || trimmed.starts_with("solve ") {
            return Some(i);
        }
        if trimmed.starts_with("inductive ") || trimmed.starts_with("axiom ") || trimmed.starts_with("structure ")
            || trimmed.starts_with("import ") || trimmed.starts_with("namespace ") || trimmed.starts_with("mutual ") {
            break;
        }
    }
    None
}

#[cfg(feature = "server")]
fn find_decl_end(file_lines: &[String], start: usize) -> usize {
    for i in (start + 1)..file_lines.len() {
        let trimmed = file_lines[i].trim();
        if trimmed.starts_with("|") {
            continue;
        }
        if trimmed.starts_with("theorem ") || trimmed.starts_with("def ") || trimmed.starts_with("solve ")
            || trimmed.starts_with("inductive ") || trimmed.starts_with("axiom ") || trimmed.starts_with("structure ")
            || trimmed.starts_with("import ") || trimmed.starts_with("namespace ") || trimmed.starts_with("end ")
            || trimmed.starts_with("mutual ") || trimmed.starts_with("variable ") || trimmed.starts_with("notation ")
            || trimmed.starts_with("infix ") || trimmed.starts_with("infixl ") || trimmed.starts_with("section ") {
            return i - 1;
        }
    }
    file_lines.len() - 1
}

#[cfg(feature = "server")]
fn find_by_offset(file_lines: &[String], decl_start: usize, decl_end: usize) -> Option<(usize, usize)> {
    for i in decl_start..=decl_end {
        let line = &file_lines[i];
        if let Some(pos) = line.find(":= by") {
            return Some((i, pos + 3)); // position of 'b' in 'by'
        }
        if let Some(pos) = line.find("by") {
            let after = &line[pos..];
            if after.starts_with("by") {
                let before = &line[..pos];
                if before.trim().is_empty() || before.trim_end().ends_with(":=") {
                    return Some((i, pos));
                }
            }
        }
    }
    None
}

#[cfg(feature = "server")]
fn extract_premises(e: &Expr) -> (Vec<String>, String) {
    let mut premises = Vec::new();
    let mut current = e;
    let mut binders: Vec<String> = Vec::new();
    while let Expr::Pi(name, _, dom, body) = current {
        let display_name = if name.to_string() == "_" {
            format!("_{}", binders.len())
        } else {
            name.to_string()
        };
        premises.push(format!("{} : {}", display_name, format_expr_with_binders(dom, 0, &binders)));
        binders.push(display_name);
        current = body;
    }
    (premises, format_expr_with_binders(current, 0, &binders))
}

#[cfg(feature = "server")]
fn format_goals(engine: &TacticEngine) -> Vec<String> {
    let mut lines = Vec::new();
    if engine.num_goals() == 0 {
        lines.push("No goals".to_string());
        return lines;
    }

    for (i, goal) in engine.goals.iter().enumerate() {
        if i > 0 {
            lines.push("".to_string());
        }
        // Local context (in order)
        for decl in goal.lctx.iter_decls() {
            let name = decl.get_user_name().to_string();
            let ty = format_expr(decl.get_type());
            let prefix = if decl.get_value().is_some() {
                format!("let {} : {} := ...", name, ty)
            } else {
                format!("{} : {}", name, ty)
            };
            lines.push(prefix);
        }
        if !goal.lctx.empty() {
            lines.push("────────────────────".to_string());
        }
        let target = format_expr(&goal.target);
        lines.push(format!("⊢ {}", target));
    }
    lines
}

#[cfg(feature = "server")]
fn try_tactic_goals(
    env: &Environment,
    tc_state: &mut TypeCheckerState,
    env_bindings: &HashMap<String, Expr>,
    infix_ops: &HashMap<String, (i32, String, bool)>,
    notations: &HashMap<String, ParsedExpr>,
    file_lines: &[String],
    line_idx: usize,
) -> Option<Vec<String>> {
    let decl_start = find_decl_start(file_lines, line_idx)?;
    let decl_end = find_decl_end(file_lines, decl_start);
    let decl_text: String = file_lines[decl_start..=decl_end].join("\n");

    let mut parser = ReplParser::new_with_state(&decl_text, infix_ops.clone(), notations.clone());
    let decl = parser.parse_decl().ok()?;

    let (params, ret_ty, value) = match decl {
        ParsedDecl::Theorem { params, ret_ty, value, .. } => (params, Some(ret_ty), value),
        ParsedDecl::Def { params, ret_ty, value, .. } => (params, ret_ty, value),
        ParsedDecl::Solve { params, ret_ty, value, .. } => (params, Some(ret_ty), value),
        _ => return None,
    };

    match &value {
        ParsedExpr::TacticBlock(_) => {}
        _ => return None,
    }

    let (by_line, by_offset) = find_by_offset(file_lines, decl_start, decl_end)?;

    let mut partial_text = String::new();
    for i in by_line..=line_idx {
        if i == by_line {
            partial_text.push_str(&file_lines[i][by_offset..]);
        } else {
            partial_text.push('\n');
            partial_text.push_str(&file_lines[i]);
        }
    }

    let partial_tactics = if partial_text.trim() == "by" {
        Vec::new()
    } else {
        let mut partial_parser = ReplParser::new_with_state(&partial_text, infix_ops.clone(), notations.clone());
        match partial_parser.parse_expr().ok()? {
            ParsedExpr::TacticBlock(t) => t,
            _ => return None,
        }
    };

    let mut bound_vars: Vec<String> = Vec::new();
    let mut param_exprs: Vec<(String, Expr)> = Vec::new();

    for (pname, pty) in &params {
        let ty_expr = pty.to_expr(env_bindings, env, &mut bound_vars);
        param_exprs.push((pname.clone(), ty_expr));
        bound_vars.push(pname.clone());
    }

    let mut target_expr = if let Some(rt) = ret_ty {
        rt.to_expr(env_bindings, env, &mut bound_vars)
    } else {
        return None;
    };
    for (pname, pty) in param_exprs.iter().rev() {
        target_expr = Expr::Pi(Name::new(pname), BinderInfo::Default, Rc::new(pty.clone()), Rc::new(target_expr));
    }

    let mut engine = TacticEngine::new(tc_state, env, env_bindings, target_expr);
    engine.num_params = param_exprs.len();

    for cmd in &partial_tactics {
        if let Err(e) = crate::repl::execute_tactic(
            env, env_bindings, infix_ops, notations, &mut engine, cmd
        ) {
            return Some(vec![format!("Tactic error: {}", e)]);
        }
    }

    Some(format_goals(&engine))
}

#[cfg(feature = "server")]
fn try_decl_type(
    env: &Environment,
    line: &str,
) -> Option<(String, Vec<String>, String)> {
    let words: Vec<&str> = line.split_whitespace().collect();
    if words.len() < 2 {
        return None;
    }
    let kind = words[0];
    if kind != "theorem" && kind != "def" && kind != "inductive" && kind != "axiom" && kind != "solve" {
        return None;
    }
    let name = words[1];
    if let Some(info) = env.find(&Name::new(name)) {
        let ty = info.get_type();
        let (premises, goal) = extract_premises(ty);
        return Some((format!("{} {}", kind, name), premises, goal));
    }
    None
}

#[cfg(feature = "server")]
fn try_infer_expr(
    env: &Environment,
    tc_state: &mut TypeCheckerState,
    env_bindings: &HashMap<String, Expr>,
    line: &str,
) -> Option<String> {
    let stripped = if line.starts_with("theorem") || line.starts_with("def") || line.starts_with("axiom") || line.starts_with("solve") {
        if let Some(pos) = line.find(":=") {
            line[pos + 2..].trim()
        } else {
            return None;
        }
    } else if line.starts_with("inductive") {
        return None;
    } else if line.starts_with("|") {
        if let Some(pos) = line.find(':') {
            line[pos + 1..].trim()
        } else {
            return None;
        }
    } else {
        line.trim()
    };

    if stripped.is_empty() {
        return None;
    }

    let mut parser = ReplParser::new(stripped);
    let parsed = match parser.parse_expr() {
        Ok(p) => p,
        Err(_) => return None,
    };
    let expr = parsed.to_expr(env_bindings, env, &mut Vec::new());

    let mut tc = TypeChecker::with_local_ctx(tc_state, crate::local_ctx::LocalCtx::new());
    match tc.infer(&expr) {
        Ok(ty) => Some(format_expr(&ty)),
        Err(_) => None,
    }
}

#[cfg(feature = "server")]
pub async fn start_server(port: u16, static_path: PathBuf) {
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any);

    let api_static_path = static_path.clone();
    let index_path = static_path.join("tui").join("index.html");
    let lib_path = static_path.parent().unwrap().join("lib");

    let app = Router::new()
        .route("/", get_service(ServeFile::new(&index_path)).layer(cors.clone()))
        .route("/api/load", post(load_handler))
        .route("/api/line-info", get(line_info_handler))
        .route("/api/env", get(env_handler))
        .route("/api/infix-ops", get(infix_ops_handler))
        .route("/api/notations", get(notations_handler))
        .route("/api/list-files", get(move || async move { list_cic_files(&lib_path) }))
        .route("/api/file", get(move |axum::extract::Query(params): axum::extract::Query<HashMap<String, String>>| async move {
            file_handler_impl(params, api_static_path.clone())
        }))
        .layer(cors);

    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    println!("Server running at http://localhost:{}", port);
    println!("Open http://localhost:{}?target=<file.cic> to view a file", port);

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

#[cfg(feature = "server")]
async fn load_handler(Json(req): Json<LoadRequest>) -> Json<LoadResponse> {
    let mut repl = Repl::new();
    repl.set_quiet(true);

    let target_content = match fs::read_to_string(&req.target) {
        Ok(c) => c,
        Err(e) => return Json(LoadResponse {
            success: false,
            error: Some(format!("Cannot read target file: {}", e)),
        }),
    };

    let file_lines: Vec<String> = target_content.lines().map(|s| s.to_string()).collect();

    let mut all_files: Vec<&str> = req.dependencies.iter().map(|s| s.as_str()).collect();
    all_files.push(&req.target);

    match repl.check_files(&all_files) {
        Ok(_) => {
            let (env, _, _, _, _) = repl.into_state();
            let declarations: Vec<String> = env.iter_names().map(|n| n.to_string()).collect();
            let mut state = APP_STATE.lock().unwrap();
            *state = Some(AppState {
                file_lines,
                current_file: req.target,
                declarations,
            });
            Json(LoadResponse { success: true, error: None })
        }
        Err(e) => Json(LoadResponse {
            success: false,
            error: Some(e),
        }),
    }
}

#[cfg(feature = "server")]
async fn line_info_handler(axum::extract::Query(params): axum::extract::Query<HashMap<String, String>>) -> Json<LineInfoResponse> {
    let line = params
        .get("line")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0);

    // Get file info from global state
    let state_lock = APP_STATE.lock().unwrap();
    let app_state = match state_lock.as_ref() {
        Some(s) => s.clone(),
        None => {
            return Json(LineInfoResponse {
                success: true,
                line,
                info: vec!["Select a file first".to_string()],
                goals: None,
                penrose_available: false,
                error: None,
            });
        }
    };
    drop(state_lock);

    // Re-run the repl to get the full state (including env, tc_state, etc.)
    // This is needed because Rc types can't be stored in global state
    let mut repl = Repl::new();
    repl.set_quiet(true);
    
    let mut all_files: Vec<&str> = vec![];
    // Try to load dependencies if any
    let deps: Vec<String> = vec![];
    for dep in &deps {
        all_files.push(dep);
    }
    all_files.push(&app_state.current_file);
    
    let mut info = Vec::new();
    let mut goals_result = None;
    let mut penrose_available = false;

    match repl.check_files(&all_files) {
        Ok(_) => {
            let (env, mut tc_state, env_bindings, infix_ops, notations) = repl.into_state();

            if app_state.file_lines.is_empty() {
                info.push("⊢ (empty file)".to_string());
            } else {
                let line_content = app_state.file_lines.get(line).cloned().unwrap_or_default();
                let trimmed = line_content.trim();

                // Try tactic goals first (even on empty/comment lines inside a by block)
                if let Some(goal_lines) = try_tactic_goals(
                    &env, &mut tc_state, &env_bindings, &infix_ops, &notations,
                    &app_state.file_lines, line
                ) {
                    goals_result = Some(parse_goal_lines(&goal_lines));
                    for gl in &goal_lines {
                        info.push(gl.clone());
                    }
                } else if trimmed.is_empty() {
                    info.push("⊢ (empty line)".to_string());
                } else if trimmed.starts_with("--") {
                    info.push("⊢ Comment".to_string());
                } else {
                    if let Some((sig, premises, goal)) = try_decl_type(&env, &trimmed) {
                        for p in &premises {
                            info.push(p.clone());
                        }
                        if !premises.is_empty() {
                            info.push("────────────────────".to_string());
                        }
                        info.push(format!("⊢ {}", sig));
                        info.push(format!("  {}", goal));
                    } else if let Some(ty) = try_infer_expr(&env, &mut tc_state, &env_bindings, &trimmed) {
                        if !ty.is_empty() {
                            info.push("⊢".to_string());
                            info.push(format!("  {}", ty));
                        }
                    }
                }

                let is_geometry = if let Some(path) = params.get("file") {
                    path.to_lowercase().contains("geometry")
                } else {
                    app_state.current_file.to_lowercase().contains("geometry")
                };

                if is_geometry {
                    penrose_available = true;
                    if let Some(decl_start) = find_decl_start(&app_state.file_lines, line) {
                        let decl_line = app_state.file_lines[decl_start].to_lowercase();
                        penrose_available = decl_line.contains("theorem") || decl_line.contains("lemma") || decl_line.contains("definition");
                    }
                }
            }
        }
        Err(e) => {
            info.push(format!("Error: {}", e));
        }
    }

    Json(LineInfoResponse {
        success: true,
        line,
        info,
        goals: goals_result,
        penrose_available,
        error: None,
    })
}

#[cfg(feature = "server")]
fn parse_goal_lines(lines: &[String]) -> Vec<TacticGoal> {
    let mut goals = Vec::new();
    let mut current_hypotheses = Vec::new();
    let mut current_goal = String::new();
    let mut in_goal = false;

    for line in lines {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            if in_goal && !current_goal.is_empty() {
                goals.push(TacticGoal {
                    hypotheses: current_hypotheses.clone(),
                    goal: current_goal.clone(),
                });
                current_hypotheses.clear();
                current_goal.clear();
                in_goal = false;
            }
        } else if trimmed.starts_with("⊢") {
            current_goal = trimmed[1..].trim().to_string();
            in_goal = true;
        } else if trimmed.starts_with("─") {
            // separator, skip
        } else if trimmed.starts_with("let ") || trimmed.contains(" : ") {
            current_hypotheses.push(trimmed.to_string());
        }
    }

    if in_goal && !current_goal.is_empty() {
        goals.push(TacticGoal {
            hypotheses: current_hypotheses,
            goal: current_goal,
        });
    }

    goals
}

#[cfg(feature = "server")]
async fn env_handler() -> Json<EnvResponse> {
    let state_lock = APP_STATE.lock().unwrap();
    let state = match state_lock.as_ref() {
        Some(s) => s.clone(),
        None => {
            return Json(EnvResponse {
                success: true,
                declarations: Vec::new(),
                error: None,
            });
        }
    };

    Json(EnvResponse {
        success: true,
        declarations: state.declarations,
        error: None,
    })
}

#[cfg(feature = "server")]
async fn infix_ops_handler() -> Json<InfixOpsResponse> {
    Json(InfixOpsResponse {
        success: true,
        ops: HashMap::new(),
    })
}

#[cfg(feature = "server")]
async fn notations_handler() -> Json<NotationsResponse> {
    Json(NotationsResponse {
        success: true,
        notations: HashMap::new(),
    })
}

#[cfg(feature = "server")]
fn list_cic_files(lib_path: &PathBuf) -> Json<ListFilesResponse> {
    let mut files = Vec::new();
    
    fn collect_cic_files(dir: &PathBuf, base: &PathBuf, files: &mut Vec<String>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.is_dir() {
                    collect_cic_files(&path, base, files);
                } else if path.extension().map(|e| e == "cic").unwrap_or(false) {
                    if let Ok(relative) = path.strip_prefix(base) {
                        files.push(format!("lib/{}", relative.to_string_lossy()));
                    }
                }
            }
        }
    }
    
    collect_cic_files(lib_path, lib_path, &mut files);
    files.sort();
    
    Json(ListFilesResponse {
        success: true,
        files,
        error: None,
    })
}

#[cfg(feature = "server")]
fn file_handler_impl(params: HashMap<String, String>, static_path: PathBuf) -> axum::response::Response {
    if let Some(path) = params.get("path") {
        let project_root = static_path.parent().unwrap();
        let full_path = project_root.join(path);
        if full_path.exists() && full_path.is_file() {
            match fs::read_to_string(&full_path) {
                Ok(content) => {
                    return (StatusCode::OK, content).into_response();
                }
                Err(_) => {
                    return (StatusCode::INTERNAL_SERVER_ERROR, "Cannot read file").into_response();
                }
            }
        }
    }
    (StatusCode::NOT_FOUND, "File not found").into_response()
}
