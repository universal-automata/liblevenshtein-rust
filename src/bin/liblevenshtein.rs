//! liblevenshtein - Fast fuzzy string matching with Levenshtein automata
//!
//! Provides CLI utilities and an interactive REPL for dictionary operations.

use clap::Parser;
use colored::Colorize;
use std::process;

use liblevenshtein::cli::commands;
use liblevenshtein::cli::paths::PersistentConfig;
use liblevenshtein::cli::{Cli, Commands};
use liblevenshtein::repl::{Command, CommandResult, LevenshteinHelper, ReplConfig, ReplState};
use rustyline::error::ReadlineError;
use rustyline::{Config, Editor};

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Repl {
            dict,
            backend,
            format,
            algorithm,
            max_distance,
            prefix,
            show_distances,
            limit,
            auto_sync,
        } => {
            // Launch REPL with provided configuration
            run_repl(
                dict,
                backend,
                format,
                algorithm,
                max_distance,
                prefix,
                show_distances,
                limit,
                auto_sync,
            )
        }
        _ => {
            // Execute CLI command
            commands::execute(cli.command)
        }
    };

    if let Err(e) = result {
        eprintln!("{}: {}", "Error".red().bold(), e);
        process::exit(1);
    }
}

#[allow(clippy::too_many_arguments)]
fn run_repl(
    dict_path: Option<std::path::PathBuf>,
    backend_opt: Option<liblevenshtein::repl::state::DictionaryBackend>,
    format_opt: Option<liblevenshtein::cli::args::SerializationFormat>,
    algorithm: liblevenshtein::transducer::Algorithm,
    max_distance: usize,
    prefix: bool,
    show_distances: bool,
    limit: Option<usize>,
    auto_sync: bool,
) -> anyhow::Result<()> {
    use liblevenshtein::cli::detect::detect_format;
    use liblevenshtein::cli::paths::default_dict_path;

    // Load persistent config
    let config = PersistentConfig::load().unwrap_or_default();

    // Merge with CLI options
    let merged_config = config.merge_with_cli(
        dict_path.clone(),
        backend_opt,
        format_opt,
        Some(algorithm),
        Some(max_distance),
        Some(prefix),
        Some(show_distances),
        Some(limit),
        Some(auto_sync),
    );

    // Save merged config for future use
    let _ = merged_config.save();

    // Print banner
    print_banner();

    // Initialize REPL state with configured options
    let mut state = ReplState::new();
    state.algorithm = merged_config.algorithm.unwrap_or(algorithm);
    state.max_distance = merged_config.max_distance.unwrap_or(max_distance);
    state.prefix_mode = merged_config.prefix_mode.unwrap_or(prefix);
    state.show_distances = merged_config.show_distances.unwrap_or(show_distances);
    state.result_limit = merged_config.result_limit.unwrap_or(limit);
    if let Some(fmt) = merged_config.format.or(format_opt) {
        state.serialization_format = fmt;
    }

    // Determine dictionary path
    let dict_path = if let Some(path) = dict_path {
        Some(path)
    } else if let Some(path) = merged_config.dict_path {
        Some(path)
    } else {
        // Use default path if it exists
        let backend = merged_config.backend.unwrap_or(state.backend);
        let format = merged_config
            .format
            .unwrap_or(liblevenshtein::cli::args::SerializationFormat::Text);
        default_dict_path(backend, format).ok()
    };

    // Try to auto-load dictionary if path exists
    if let Some(ref path) = dict_path {
        if path.exists() {
            match detect_format(
                path,
                backend_opt.or(merged_config.backend),
                format_opt.or(merged_config.format),
            ) {
                Ok(detection) => {
                    println!(
                        "  Loading dictionary from {} ({}, {})...",
                        path.display().to_string().cyan(),
                        detection.format.backend.to_string().green(),
                        detection.format.format.to_string().green()
                    );

                    match liblevenshtein::cli::commands::load_dictionary(path, detection.format) {
                        Ok(container) => {
                            let count = container.len();
                            state.dictionary = container;
                            state.backend = detection.format.backend;
                            state.auto_sync_path = Some(path.clone());
                            println!("  Loaded {} term(s)", count.to_string().green().bold());
                            println!();
                        }
                        Err(e) => {
                            eprintln!("  {}: Could not load dictionary: {}", "Warning".yellow(), e);
                            println!();
                        }
                    }
                }
                Err(e) => {
                    eprintln!(
                        "  {}: Could not detect dictionary format: {}",
                        "Warning".yellow(),
                        e
                    );
                    println!();
                }
            }
        }
    }

    let repl_config = ReplConfig::default();

    // Initialize Rustyline
    let rustyline_config = Config::builder()
        .auto_add_history(true)
        .history_ignore_dups(true)?
        .history_ignore_space(true)
        .build();

    let helper = LevenshteinHelper::new();
    let mut editor: Editor<LevenshteinHelper, rustyline::history::DefaultHistory> =
        Editor::with_config(rustyline_config)?;
    editor.set_helper(Some(helper));

    // Load history if it exists
    if let Some(history_path) = &repl_config.history_file {
        if history_path.exists() {
            let _ = editor.load_history(history_path);
        }
    }

    // Main REPL loop
    let mut line_num = 0;
    loop {
        line_num += 1;

        // Generate prompt with line number
        let prompt = format!("{}[{}]> ", "liblevenshtein".bright_cyan().bold(), line_num);

        // Read input
        let readline = editor.readline(&prompt);

        match readline {
            Ok(line) => {
                let line = line.trim();

                // Skip empty lines
                if line.is_empty() {
                    continue;
                }

                // Parse and execute command
                match Command::parse(line) {
                    Ok(command) => match command.execute(&mut state) {
                        Ok(CommandResult::Continue(output)) => {
                            if !output.is_empty() {
                                println!("{}", output);
                            }

                            // Auto-sync if enabled
                            if auto_sync {
                                if let Some(ref _path) = dict_path {
                                    // TODO: Implement auto-save
                                }
                            }
                        }
                        Ok(CommandResult::Exit) => {
                            println!("{}", "Goodbye!".green());
                            break;
                        }
                        Ok(CommandResult::Silent) => {}
                        Err(e) => {
                            eprintln!("{}: {}", "Error".red().bold(), e);
                        }
                    },
                    Err(e) => {
                        eprintln!("{}: {}", "Parse error".red().bold(), e);
                    }
                }
            }
            Err(ReadlineError::Interrupted) => {
                // Ctrl+C - cancel current line
                println!("{}", "^C (Use 'exit' or Ctrl+D to quit)".yellow());
                continue;
            }
            Err(ReadlineError::Eof) => {
                // Ctrl+D - exit
                println!("{}", "Goodbye!".green());
                break;
            }
            Err(err) => {
                eprintln!("{}: {:?}", "Readline error".red().bold(), err);
                break;
            }
        }
    }

    // Save history
    if let Some(history_path) = &repl_config.history_file {
        if let Err(e) = editor.save_history(history_path) {
            eprintln!("{}: Failed to save history: {}", "Warning".yellow(), e);
        }
    }

    Ok(())
}

fn print_banner() {
    println!();
    println!(
        "{}",
        "═══════════════════════════════════════════════════════".bright_cyan()
    );
    println!(
        "{}",
        "   liblevenshtein - Fast Fuzzy String Matching"
            .bright_cyan()
            .bold()
    );
    println!(
        "{}",
        "═══════════════════════════════════════════════════════".bright_cyan()
    );
    println!();
    println!("  Version: {}", env!("CARGO_PKG_VERSION").green());
    println!("  Type {} for available commands", "'help'".yellow().bold());
    println!(
        "  Type {} or press {} to exit",
        "'exit'".yellow().bold(),
        "Ctrl+D".yellow().bold()
    );
    println!();
    println!("{}", "  Quick Start:".bold());
    println!(
        "    • Load a dictionary: {}",
        "load /usr/share/dict/words".cyan()
    );
    println!("    • Query for matches: {}", "query test 2".cyan());
    println!("    • Insert terms:      {}", "insert hello world".cyan());
    println!("    • Show settings:     {}", "settings".cyan());
    println!();
}
