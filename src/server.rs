#[cfg(feature = "server")]
use std::collections::HashMap;
#[cfg(feature = "server")]
use std::fs;
#[cfg(feature = "server")]
use std::net::SocketAddr;
#[cfg(feature = "server")]
use std::path::PathBuf;

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

pub struct ServerState {
    loaded_files: Vec<String>,
    infix_ops: HashMap<String, String>,
    notations: HashMap<String, String>,
    declarations: Vec<String>,
}

impl Default for ServerState {
    fn default() -> Self {
        Self {
            loaded_files: Vec::new(),
            infix_ops: HashMap::new(),
            notations: HashMap::new(),
            declarations: Vec::new(),
        }
    }
}

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
    pub error: Option<String>,
}

#[derive(serde::Serialize)]
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

    let mut all_files: Vec<&str> = req.dependencies.iter().map(|s| s.as_str()).collect();
    all_files.push(&req.target);

    match repl.check_files(&all_files) {
        Ok(_) => {
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

    Json(LineInfoResponse {
        success: true,
        line,
        info: vec![format!("Line: {}", line + 1)],
        goals: None,
        error: None,
    })
}

#[cfg(feature = "server")]
async fn env_handler() -> Json<EnvResponse> {
    let mut repl = Repl::new();
    repl.set_quiet(true);
    
    match repl.check_files(&["lib/Nat.cic"]) {
        Ok(_) => {
            let names: Vec<String> = repl.env().iter_names().map(|n| n.to_string()).collect();
            Json(EnvResponse {
                success: true,
                declarations: names,
                error: None,
            })
        }
        Err(e) => Json(EnvResponse {
            success: false,
            declarations: Vec::new(),
            error: Some(e),
        }),
    }
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
