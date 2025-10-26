//! Syntax highlighting for REPL input

use colored::Colorize;
use rustyline::highlight::Highlighter;

/// Command highlighter
pub struct CommandHighlighter {
    commands: Vec<String>,
}

impl CommandHighlighter {
    pub fn new() -> Self {
        Self {
            commands: vec![
                "query",
                "q",
                "insert",
                "add",
                "delete",
                "remove",
                "rm",
                "contains",
                "has",
                "load",
                "save",
                "backend",
                "use",
                "algorithm",
                "algo",
                "distance",
                "dist",
                "prefix",
                "show-distances",
                "show-dist",
                "limit",
                "clear",
                "compact",
                "minimize",
                "dump",
                "list",
                "stats",
                "info",
                "settings",
                "config",
                "set",
                "help",
                "?",
                "exit",
                "quit",
            ]
            .into_iter()
            .map(String::from)
            .collect(),
        }
    }

    fn highlight_command(&self, line: &str) -> String {
        if line.trim().is_empty() {
            return line.to_string();
        }

        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return line.to_string();
        }

        let cmd = parts[0].to_lowercase();

        // Check if it's a known command
        if self.commands.iter().any(|c| c == &cmd) {
            // Highlight the command in bold blue
            let highlighted_cmd = parts[0].blue().bold().to_string();

            // Reconstruct the line with highlighted command
            if parts.len() == 1 {
                highlighted_cmd
            } else {
                let rest = line[parts[0].len()..].to_string();
                format!("{}{}", highlighted_cmd, self.highlight_args(&rest, &cmd))
            }
        } else {
            line.to_string()
        }
    }

    fn highlight_args(&self, args: &str, _cmd: &str) -> String {
        let mut result = String::new();
        let mut in_option = false;

        for part in args.split_whitespace() {
            result.push(' ');

            if part.starts_with("--") || part.starts_with('-') {
                // Highlight options in yellow
                result.push_str(&part.yellow().to_string());
                in_option = true;
            } else if in_option {
                // Highlight option values in cyan
                result.push_str(&part.cyan().to_string());
                in_option = false;
            } else if part.parse::<usize>().is_ok() {
                // Highlight numbers in magenta
                result.push_str(&part.magenta().to_string());
            } else {
                // Regular arguments
                result.push_str(part);
            }
        }

        result
    }
}

impl Default for CommandHighlighter {
    fn default() -> Self {
        Self::new()
    }
}

impl Highlighter for CommandHighlighter {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> std::borrow::Cow<'l, str> {
        std::borrow::Cow::Owned(self.highlight_command(line))
    }

    fn highlight_char(&self, _line: &str, _pos: usize, _forced: bool) -> bool {
        true
    }
}
