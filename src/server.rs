use std::collections::HashMap;
use std::fs;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::sync::Arc;

#[cfg(feature = "server")]
use parking_lot::Mutex;

#[cfg(feature = "server")]
use crate::repl::Repl;

#[cfg(feature = "server")]
pub struct ServerState {
    pub loaded_files: Vec<String>,
    pub infix_ops: HashMap<String, String>,
    pub notations: HashMap<String, String>,
    pub declarations: Vec<String>,
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

#[cfg(feature = "server")]
pub type SharedState = Arc<Mutex<ServerState>>;

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
    use axum::{
        extract::State,
        http::StatusCode,
        response::{Html, IntoResponse, Response},
        routing::{get, post},
        Json, Router,
    };
    use tower_http::cors::{Any, CorsLayer};

    let state: SharedState = Arc::new(Mutex::new(ServerState::default()));
    let static_path_clone = static_path.clone();

    let cors = CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any);

    let app = Router::new()
        .route("/", get(move || async move { Html(tmpl_index()) }))
        .route("/tui/", get(move || async move { Html(tmpl_tui_index()) }))
        .route("/api/load", post(load_handler))
        .route("/api/line-info", get(line_info_handler))
        .route("/api/env", get(env_handler))
        .route("/api/infix-ops", get(infix_ops_handler))
        .route("/api/notations", get(notations_handler))
        .route("/api/file", get(move |axum::extract::Query(params): axum::extract::Query<HashMap<String, String>>| async move {
            file_handler_impl(params, static_path_clone.clone())
        }))
        .with_state(state)
        .layer(cors);

    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    println!("Server running at http://localhost:{}", port);
    println!("TUI at http://localhost:{}/tui/", port);

    let listener = tokio::net::TcpListener::bind(addr).await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

#[cfg(feature = "server")]
async fn load_handler(
    State(state): State<SharedState>,
    Json(req): Json<LoadRequest>,
) -> Json<LoadResponse> {
    let mut repl = Repl::new();
    repl.set_quiet(true);

    let mut all_files: Vec<&str> = req.dependencies.iter().map(|s| s.as_str()).collect();
    all_files.push(&req.target);

    match repl.check_files(&all_files) {
        Ok(_) => {
            let names: Vec<String> = repl.env().iter_names().map(|n| n.to_string()).collect();
            let mut state = state.lock();
            state.loaded_files.push(req.target.clone());
            state.declarations = names;
            Json(LoadResponse { success: true, error: None })
        }
        Err(e) => Json(LoadResponse {
            success: false,
            error: Some(e),
        }),
    }
}

#[cfg(feature = "server")]
async fn line_info_handler(
    State(state): State<SharedState>,
    axum::extract::Query(params): axum::extract::Query<HashMap<String, String>>,
) -> Json<LineInfoResponse> {
    let line = params
        .get("line")
        .and_then(|s| s.parse::<usize>().ok())
        .unwrap_or(0);

    let state = state.lock();
    let info = vec![format!("Environment: {} declarations", state.declarations.len())];

    Json(LineInfoResponse {
        success: true,
        line,
        info,
        goals: None,
        error: None,
    })
}

#[cfg(feature = "server")]
async fn env_handler(State(state): State<SharedState>) -> Json<EnvResponse> {
    let state = state.lock();
    Json(EnvResponse {
        success: true,
        declarations: state.declarations.clone(),
        error: None,
    })
}

#[cfg(feature = "server")]
async fn infix_ops_handler(State(state): State<SharedState>) -> Json<InfixOpsResponse> {
    let state = state.lock();
    Json(InfixOpsResponse {
        success: true,
        ops: state.infix_ops.clone(),
    })
}

#[cfg(feature = "server")]
async fn notations_handler(State(state): State<SharedState>) -> Json<NotationsResponse> {
    let state = state.lock();
    Json(NotationsResponse {
        success: true,
        notations: state.notations.clone(),
    })
}

#[cfg(feature = "server")]
fn file_handler_impl(params: HashMap<String, String>, static_path: PathBuf) -> Response {
    use axum::http::StatusCode;

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
    let base_path = std::env::var("TUI_BASE_PATH").unwrap_or_else(|_| "/tui".to_string());
    let css_path = format!("{}/styles.css", base_path);
    let js_path = format!("{}/app.js", base_path);

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
