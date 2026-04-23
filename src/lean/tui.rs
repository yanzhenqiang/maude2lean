use crossterm::event::{self, Event, KeyCode, KeyEventKind};
use crossterm::terminal::{disable_raw_mode, enable_raw_mode, Clear, ClearType};
use crossterm::cursor::{MoveTo, Show, Hide};
use crossterm::{ExecutableCommand, QueueableCommand};
use std::collections::HashMap;
use std::io::{self, stdout, Write};

use super::environment::Environment;
use super::expr::*;
use super::repl::Repl;
use super::repl_parser::Parser as ReplParser;
use super::type_checker::{TypeChecker, TypeCheckerState};

/// Terminal UI for browsing a Lean file and inspecting goals/types at each line.
pub struct TuiApp {
    env: Environment,
    tc_state: TypeCheckerState,
    env_bindings: HashMap<String, Expr>,
    file_lines: Vec<String>,
    selected: usize,
    scroll: usize,
    info_lines: Vec<String>,
    term_w: u16,
    term_h: u16,
    left_w: u16,
}

impl TuiApp {
    /// Create a TUI app by loading dependencies via Repl, then taking its state.
    pub fn new(repl: Repl, file_lines: Vec<String>) -> Self {
        let (env, tc_state, env_bindings) = repl.into_state();
        let mut app = TuiApp {
            env,
            tc_state,
            env_bindings,
            file_lines,
            selected: 0,
            scroll: 0,
            info_lines: Vec::new(),
            term_w: 80,
            term_h: 24,
            left_w: 50,
        };
        app.refresh_size();
        app.update_info();
        app
    }

    fn refresh_size(&mut self) {
        if let Ok((w, h)) = crossterm::terminal::size() {
            self.term_w = w.max(40);
            self.term_h = h.max(10);
        }
        self.left_w = (self.term_w as f32 * 0.55) as u16;
        self.left_w = self.left_w.max(20).min(self.term_w - 22);
    }

    pub fn run(&mut self) -> io::Result<()> {
        // Try to enter interactive TUI mode; if terminal doesn't support it,
        // fall back to printing a single static frame (useful in CI/pipes).
        if enable_raw_mode().is_err() {
            return self.run_static();
        }
        let mut stdout = stdout();
        let _ = stdout.execute(Hide);

        loop {
            self.refresh_size();
            self.draw(&mut stdout)?;

            if let Event::Key(key) = event::read()? {
                if key.kind == KeyEventKind::Press {
                    let mut changed = false;
                    match key.code {
                        KeyCode::Char('q') | KeyCode::Char('Q') => break,
                        KeyCode::Up => { self.move_up(); changed = true; }
                        KeyCode::Down => { self.move_down(); changed = true; }
                        KeyCode::PageUp => { self.page_up(); changed = true; }
                        KeyCode::PageDown => { self.page_down(); changed = true; }
                        KeyCode::Home => { self.go_top(); changed = true; }
                        KeyCode::End => { self.go_bottom(); changed = true; }
                        _ => {}
                    }
                    if changed {
                        self.update_info();
                    }
                }
            }
        }

        let _ = stdout.execute(Show);
        let _ = disable_raw_mode();
        let _ = stdout.execute(Clear(ClearType::All));
        Ok(())
    }

    /// Static mode: print one frame and exit (for non-interactive terminals).
    fn run_static(&mut self) -> io::Result<()> {
        self.refresh_size();
        // Use a fixed smaller size for static output
        self.term_h = 30;
        self.term_w = 100;
        self.left_w = 55;
        let mut stdout = stdout();
        self.draw(&mut stdout)?;
        println!();
        println!("(Static mode - no interactive terminal detected. Use a real terminal for TUI mode.)");
        Ok(())
    }

    // --- Navigation ---

    fn move_up(&mut self) {
        if self.selected > 0 {
            self.selected -= 1;
        }
        self.adjust_scroll();
    }

    fn move_down(&mut self) {
        if self.selected + 1 < self.file_lines.len() {
            self.selected += 1;
        }
        self.adjust_scroll();
    }

    fn page_up(&mut self) {
        let page = self.content_height() as usize;
        self.selected = self.selected.saturating_sub(page);
        self.adjust_scroll();
    }

    fn page_down(&mut self) {
        let page = self.content_height() as usize;
        self.selected = (self.selected + page).min(self.file_lines.len().saturating_sub(1));
        self.adjust_scroll();
    }

    fn go_top(&mut self) {
        self.selected = 0;
        self.scroll = 0;
    }

    fn go_bottom(&mut self) {
        if !self.file_lines.is_empty() {
            self.selected = self.file_lines.len() - 1;
        }
        self.adjust_scroll();
    }

    fn adjust_scroll(&mut self) {
        let visible = self.content_height() as usize;
        if self.selected < self.scroll {
            self.scroll = self.selected;
        } else if self.selected >= self.scroll + visible {
            self.scroll = self.selected.saturating_sub(visible - 1);
        }
    }

    fn content_height(&self) -> u16 {
        self.term_h.saturating_sub(3) // title + separator + status
    }

    // --- Info Panel ---

    fn update_info(&mut self) {
        self.info_lines.clear();
        if self.file_lines.is_empty() {
            self.info_lines.push("(empty file)".to_string());
            return;
        }

        let line = self.file_lines[self.selected].clone();
        let line_num = self.selected + 1;

        self.info_lines.push(format!("Line {}", line_num));
        self.info_lines.push("-".repeat(self.info_width() as usize));

        let trimmed = line.trim().to_string();
        if trimmed.is_empty() {
            self.info_lines.push("(empty line)".to_string());
        } else if trimmed.starts_with("--") {
            self.info_lines.push("Comment".to_string());
        } else {
            // Try to identify declaration
            if let Some(info) = self.try_decl_info(&trimmed) {
                self.info_lines.push(info);
            }
            // Try to parse as expression and infer type
            if let Some(type_str) = self.try_infer_expr(&trimmed) {
                self.info_lines.push("Type:".to_string());
                for wrapped in self.wrap_text(&type_str, self.info_width() as usize - 2) {
                    self.info_lines.push(format!("  {}", wrapped));
                }
            }
        }

        // Environment context
        self.info_lines.push(String::new());
        self.info_lines.push("Environment:".to_string());
        self.info_lines.push("-".repeat(self.info_width() as usize));

        let mut names: Vec<String> = self.env_bindings.keys().cloned().collect();
        names.sort();
        let total = names.len();
        // Collect (name, expr) pairs first to avoid borrow issues
        let pairs: Vec<(String, Expr)> = names.iter()
            .filter_map(|n| self.env_bindings.get(n).map(|e| (n.clone(), e.clone())))
            .collect();
        let mut count = 0;
        for (name, expr) in pairs {
            if count >= 15 {
                self.info_lines.push(format!("  ... and {} more", total - 15));
                break;
            }
            if let Ok(ty) = self.infer_expr(&expr) {
                let ty_short = self.truncate(&ty, self.info_width() as usize - 6 - name.len());
                self.info_lines.push(format!("  {} : {}", name, ty_short));
                count += 1;
            }
        }
    }

    fn try_decl_info(&mut self, line: &str) -> Option<String> {
        let words: Vec<&str> = line.split_whitespace().collect();
        if words.len() < 2 {
            return None;
        }
        let kind = words[0];
        if kind != "theorem" && kind != "def" && kind != "inductive" && kind != "axiom" {
            return None;
        }
        let name = words[1];
        if let Some(info) = self.env.find(&Name::new(name)) {
            let ty = format_expr(info.get_type());
            return Some(format!("{} {} : {}", kind, name, ty));
        }
        None
    }

    fn try_infer_expr(&mut self, line: &str) -> Option<String> {
        // Strip common prefixes that are not expressions
        let stripped = if line.starts_with("theorem") || line.starts_with("def") || line.starts_with("axiom") {
            // Try to extract the body after ":="
            if let Some(pos) = line.find(":=") {
                line[pos + 2..].trim()
            } else {
                return None;
            }
        } else if line.starts_with("inductive") {
            return None;
        } else if line.starts_with("|") {
            // Constructor line: extract after ":"
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
        let expr = parsed.to_expr(&self.env_bindings, &self.env, &mut Vec::new());

        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        match tc.infer(&expr) {
            Ok(ty) => Some(format_expr(&ty)),
            Err(_) => None,
        }
    }

    fn infer_expr(&mut self, expr: &Expr) -> Result<String, String> {
        let mut tc = TypeChecker::with_local_ctx(&mut self.tc_state, super::local_ctx::LocalCtx::new());
        let ty = tc.infer(expr).map_err(|e| e)?;
        Ok(format_expr(&ty))
    }

    fn info_width(&self) -> u16 {
        self.term_w.saturating_sub(self.left_w).saturating_sub(3)
    }

    fn truncate(&self, s: &str, max_len: usize) -> String {
        let chars: Vec<char> = s.chars().collect();
        if chars.len() <= max_len {
            s.to_string()
        } else {
            let mut result: String = chars.iter().take(max_len.saturating_sub(3)).collect();
            result.push_str("...");
            result
        }
    }

    fn wrap_text(&self, text: &str, width: usize) -> Vec<String> {
        let chars: Vec<char> = text.chars().collect();
        if chars.len() <= width {
            return vec![text.to_string()];
        }
        let mut result = Vec::new();
        let mut start = 0;
        while start < chars.len() {
            let end = (start + width).min(chars.len());
            result.push(chars[start..end].iter().collect());
            start = end;
        }
        result
    }

    // --- Drawing ---

    fn draw(&self, stdout: &mut io::Stdout) -> io::Result<()> {
        stdout.queue(Clear(ClearType::All))?;

        let w = self.term_w;
        let h = self.term_h;
        let lw = self.left_w;

        // Title bar
        let title = if self.file_lines.is_empty() {
            "Lean Goal Viewer".to_string()
        } else {
            format!("Lean Goal Viewer - {} lines", self.file_lines.len())
        };
        let title_chars = title.chars().count();
        let title_pad = (w as usize).saturating_sub(title_chars + 10) / 2;
        stdout.queue(MoveTo(0, 0))?;
        print!("{}{}", " ".repeat(title_pad), title);
        print!("{}[q:quit]", " ".repeat((w as usize).saturating_sub(title_pad + title_chars + 8)));

        // Separator under title
        stdout.queue(MoveTo(0, 1))?;
        print!("{}", "─".repeat(lw as usize));
        stdout.queue(MoveTo(lw + 1, 1))?;
        print!("┬{}" , "─".repeat((w - lw - 2) as usize));

        // Content area
        let content_h = self.content_height();
        for row in 0..content_h {
            let y = row + 2;
            stdout.queue(MoveTo(0, y))?;

            let line_idx = self.scroll + row as usize;
            if line_idx < self.file_lines.len() {
                let is_selected = line_idx == self.selected;
                let prefix = format!("{:3} ", line_idx + 1);
                let line_text = &self.file_lines[line_idx];
                let avail = (lw as usize).saturating_sub(prefix.len() + 1);
                let display = self.truncate(line_text, avail);
                if is_selected {
                    print!("{}> {}", prefix, display);
                } else {
                    print!("{}  {}", prefix, display);
                }
            } else {
                print!("{:3}  ~", " ");
            }

            // Right border
            stdout.queue(MoveTo(lw + 1, y))?;
            print!("│");

            // Info panel
            let info_idx = row as usize;
            if info_idx < self.info_lines.len() {
                let info = &self.info_lines[info_idx];
                let avail = (w - lw - 3) as usize;
                let display = self.truncate(info, avail);
                stdout.queue(MoveTo(lw + 3, y))?;
                print!("{}", display);
            }
        }

        // Bottom separator
        let bottom_y = h - 1;
        stdout.queue(MoveTo(0, bottom_y))?;
        print!("{}", "─".repeat(lw as usize));
        stdout.queue(MoveTo(lw + 1, bottom_y))?;
        print!("┴{}", "─".repeat((w - lw - 2) as usize));

        // Status line
        let status = format!("Line {}/{} | {} declarations",
            self.selected + 1,
            self.file_lines.len(),
            self.env_bindings.len()
        );
        stdout.queue(MoveTo(0, bottom_y))?;
        print!(" {}", status);

        stdout.flush()?;
        Ok(())
    }
}

/// Format an Expr for display (simplified).
fn format_expr(e: &Expr) -> String {
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
            if args_str.is_empty() {
                head_str
            } else {
                format!("{}({})", head_str, args_str.join(", "))
            }
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
        Expr::MVar(name) => format!("?{}", name.to_string()),
        Expr::Proj(name, idx, e) => format!("proj({}, {}, {})", name.to_string(), idx, format_expr(e)),
        _ => format!("{:?}", e),
    }
}
