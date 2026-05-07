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
    response::{Html, IntoResponse, Response},
    routing::{get, post},
    Json, Router,
};
#[cfg(feature = "server")]
use tower_http::cors::{Any, CorsLayer};

#[cfg(feature = "server")]
use crate::repl::Repl;

#[cfg(feature = "server")]
pub struct ServerState {
    loaded_files: Vec<String>,
    infix_ops: HashMap<String, String>,
    notations: HashMap<String, String>,
    declarations: Vec<String>,
}

#[cfg(feature = "server")]
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

#[cfg(feature = "server")]
pub async fn start_server(port: u16, static_path: PathBuf) {
    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any);

    let api_static_path = static_path.clone();
    let tui_static_path = static_path.join("tui");
    let gallery_static_path = static_path.join("gallery");

    let app = Router::new()
        .route("/", get(|| async { Html(tmpl_index()) }))
        .route("/tui", get(|| async { Html(tmpl_tui_index()) }))
        .route("/tui/", get(|| async { Html(tmpl_tui_index()) }))
        .route("/api/load", post(load_handler))
        .route("/api/line-info", get(line_info_handler))
        .route("/api/env", get(env_handler))
        .route("/api/infix-ops", get(infix_ops_handler))
        .route("/api/notations", get(notations_handler))
        .route("/api/file", get(move |axum::extract::Query(params): axum::extract::Query<HashMap<String, String>>| async move {
            file_handler_impl(params, api_static_path.clone())
        }))
        .nest_service("/tui/assets", tower_http::services::ServeDir::new(tui_static_path))
        .nest_service("/gallery", tower_http::services::ServeDir::new(gallery_static_path))
        .layer(cors);

    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    println!("Server running at http://localhost:{}", port);
    println!("TUI at http://localhost:{}/tui/", port);

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
fn file_handler_impl(params: HashMap<String, String>, static_path: PathBuf) -> Response {
    if let Some(path) = params.get("path") {
        let full_path = static_path.join(path);
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

fn tmpl_index() -> String {
    r#"<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>TinyCIC</title>
</head>
<body>
  <h1>TinyCIC Server</h1>
  <ul>
    <li><a href="/tui/">Interactive Goal Viewer (TUI)</a></li>
    <li><a href="/gallery/index.html">Geometry Gallery</a></li>
  </ul>
</body>
</html>"#.to_string()
}

fn tmpl_tui_index() -> String {
    let css_path = "/tui/assets/styles.css";
    let js_path = "/tui/assets/app.js";

    format!(r#"<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>TinyCIC - Interactive Goal Viewer</title>
  <link rel="stylesheet" href="{}">
</head>
<body>
  <div id="app"></div>
  <script type="module" src="{}"></script>
</body>
</html>"#, css_path, js_path)
}
