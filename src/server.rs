#[cfg(feature = "server")]
use std::collections::HashMap;
#[cfg(feature = "server")]
use std::fs;
#[cfg(feature = "server")]
use std::net::SocketAddr;
#[cfg(feature = "server")]
use std::path::PathBuf;
#[cfg(feature = "server")]
use std::sync::Arc;

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
use crate::repl::Repl;

#[cfg(feature = "server")]
#[derive(Clone)]
struct AppState {
    file_lines: Vec<String>,
    current_file: String,
    declarations: Vec<String>,
}

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

    let state_lock = APP_STATE.lock().unwrap();
    let state = match state_lock.as_ref() {
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

    let mut info = Vec::new();
    let mut goals_result = None;
    let mut penrose_available = false;

    if state.file_lines.is_empty() {
        info.push("⊢ (empty file)".to_string());
    } else {
        let line_content = state.file_lines.get(line).cloned().unwrap_or_default();
        let trimmed = line_content.trim();

        if trimmed.is_empty() {
            info.push("⊢ (empty line)".to_string());
        } else if trimmed.starts_with("--") {
            info.push("⊢ Comment".to_string());
        } else {
            info.push(format!("⊢ Line {}: {}", line + 1, trimmed));
            info.push("Type information will be shown here when available".to_string());
        }

        let is_geometry = if let Some(path) = params.get("file") {
            path.to_lowercase().contains("geometry")
        } else {
            state.current_file.to_lowercase().contains("geometry")
        };

        if is_geometry {
            penrose_available = true;
            if let Some(decl_start) = find_decl_start(&state.file_lines, line) {
                let decl_line = state.file_lines[decl_start].to_lowercase();
                penrose_available = decl_line.contains("theorem") || decl_line.contains("lemma") || decl_line.contains("definition");
            }
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
