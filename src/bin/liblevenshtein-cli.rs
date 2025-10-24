//! CLI tool for liblevenshtein fuzzy string matching.
//!
//! This binary provides a command-line interface for using the liblevenshtein
//! library to perform fuzzy string matching against dictionaries.

use liblevenshtein::prelude::*;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::path::PathBuf;
use clap::{Parser, Subcommand, ValueEnum};
use anyhow::{Context, Result};

#[derive(Parser)]
#[command(name = "liblevenshtein")]
#[command(about = "Fuzzy string matching using Levenshtein automata", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Search for terms similar to a query string
    Query {
        /// Dictionary file (one term per line)
        #[arg(short, long)]
        dict: PathBuf,

        /// Query term to search for
        #[arg(short, long)]
        term: String,

        /// Maximum edit distance
        #[arg(short = 'n', long, default_value = "2")]
        distance: usize,

        /// Levenshtein algorithm to use
        #[arg(short, long, value_enum, default_value = "standard")]
        algorithm: AlgorithmChoice,

        /// Dictionary type to use
        #[arg(long, value_enum, default_value = "pathmap")]
        dict_type: DictType,

        /// Include distances in output
        #[arg(long)]
        with_distance: bool,
    },

    /// Show dictionary statistics
    Info {
        /// Dictionary file (one term per line)
        #[arg(short, long)]
        dict: PathBuf,

        /// Dictionary type to use
        #[arg(long, value_enum, default_value = "pathmap")]
        dict_type: DictType,
    },
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum AlgorithmChoice {
    /// Standard Levenshtein (insert, delete, substitute)
    Standard,
    /// Includes transposition operations
    Transposition,
    /// Includes merge and split operations
    MergeAndSplit,
}

impl From<AlgorithmChoice> for Algorithm {
    fn from(choice: AlgorithmChoice) -> Self {
        match choice {
            AlgorithmChoice::Standard => Algorithm::Standard,
            AlgorithmChoice::Transposition => Algorithm::Transposition,
            AlgorithmChoice::MergeAndSplit => Algorithm::MergeAndSplit,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum DictType {
    /// PathMap-based trie
    Pathmap,
    /// DAWG (shares suffixes)
    Dawg,
}

fn load_terms(path: &PathBuf) -> Result<Vec<String>> {
    let file = File::open(path)
        .with_context(|| format!("Failed to open dictionary file: {}", path.display()))?;
    let reader = BufReader::new(file);

    let mut terms = Vec::new();
    for (line_num, line) in reader.lines().enumerate() {
        let line = line.with_context(|| format!("Failed to read line {} from {}", line_num + 1, path.display()))?;
        let trimmed = line.trim();
        if !trimmed.is_empty() && !trimmed.starts_with('#') {
            terms.push(trimmed.to_string());
        }
    }

    if terms.is_empty() {
        anyhow::bail!("Dictionary file is empty: {}", path.display());
    }

    Ok(terms)
}

fn run_query_pathmap(terms: Vec<String>, query: &str, distance: usize, algorithm: Algorithm, with_distance: bool) {
    let dict = PathMapDictionary::from_iter(terms);
    let transducer = Transducer::new(dict, algorithm);

    if with_distance {
        for candidate in transducer.query_with_distance(query, distance) {
            println!("{}\t{}", candidate.term, candidate.distance);
        }
    } else {
        for term in transducer.query(query, distance) {
            println!("{}", term);
        }
    }
}

fn run_query_dawg(terms: Vec<String>, query: &str, distance: usize, algorithm: Algorithm, with_distance: bool) {
    let dict = DawgDictionary::from_iter(terms);
    let transducer = Transducer::new(dict, algorithm);

    if with_distance {
        for candidate in transducer.query_with_distance(query, distance) {
            println!("{}\t{}", candidate.term, candidate.distance);
        }
    } else {
        for term in transducer.query(query, distance) {
            println!("{}", term);
        }
    }
}

fn show_info_pathmap(terms: Vec<String>) {
    let dict = PathMapDictionary::from_iter(terms);
    println!("Dictionary Type: PathMap");
    println!("Terms: {}", dict.len().unwrap());
}

fn show_info_dawg(terms: Vec<String>) {
    let dict = DawgDictionary::from_iter(terms);
    println!("Dictionary Type: DAWG");
    println!("Terms: {}", dict.term_count());
    println!("Nodes: {}", dict.node_count());
    let compression = 100.0 * (1.0 - (dict.node_count() as f64 / dict.term_count() as f64));
    println!("Compression: {:.1}% (vs simple trie)", compression);
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::Query {
            dict,
            term,
            distance,
            algorithm,
            dict_type,
            with_distance,
        } => {
            let terms = load_terms(&dict)?;
            let algo = Algorithm::from(algorithm);

            match dict_type {
                DictType::Pathmap => run_query_pathmap(terms, &term, distance, algo, with_distance),
                DictType::Dawg => run_query_dawg(terms, &term, distance, algo, with_distance),
            }
        }

        Commands::Info { dict, dict_type } => {
            let terms = load_terms(&dict)?;

            match dict_type {
                DictType::Pathmap => show_info_pathmap(terms),
                DictType::Dawg => show_info_dawg(terms),
            }
        }
    }

    Ok(())
}
