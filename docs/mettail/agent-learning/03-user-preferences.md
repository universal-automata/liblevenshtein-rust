# User Preferences

## Overview

The user preferences layer models individual user characteristics to personalize correction
behavior. This includes vocabulary preferences (personal dictionary, technical terms),
writing style (formality, tone), domain detection (medical, legal, programming), and
correction settings (aggressiveness, thresholds).

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    USER PREFERENCES ARCHITECTURE                             │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  FeedbackStore (PathMap)                                                     │
│  (User actions: accepts, rejects, modifications)                             │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    VOCABULARY MODELER                                  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Personal Dictionary                                             │  │  │
│  │  │  - Words user always accepts (rejected corrections for them)    │  │  │
│  │  │  - Proper nouns, names, brand names                            │  │  │
│  │  │  - Intentional spellings, neologisms                           │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Technical Vocabulary                                            │  │  │
│  │  │  - Domain-specific terms (medical, legal, programming)         │  │  │
│  │  │  - Acronyms and abbreviations                                  │  │  │
│  │  │  - Industry jargon                                             │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Ignored Words                                                   │  │  │
│  │  │  - Words to never flag (slang, informal spellings)             │  │  │
│  │  │  - Code identifiers, variable names                            │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    STYLE PROFILER                                      │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Formality Level (0.0 = casual, 1.0 = formal)                   │  │  │
│  │  │  - Detected from word choice, punctuation, structure           │  │  │
│  │  │  - Influences suggestion style                                 │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Vocabulary Complexity (0.0 = simple, 1.0 = advanced)           │  │  │
│  │  │  - Average word length, syllable count                         │  │  │
│  │  │  - Rare word usage frequency                                   │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Language Variety                                                │  │  │
│  │  │  - British vs American vs Australian English                   │  │  │
│  │  │  - Regional variations                                         │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    DOMAIN DETECTOR                                     │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Domain Classification                                           │  │  │
│  │  │  - Medical, Legal, Technical, Academic, Casual, Business       │  │  │
│  │  │  - Programming (with language detection)                       │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Context Detection                                               │  │  │
│  │  │  - Email, Chat, Document, Code Comment, Social Media           │  │  │
│  │  │  - Audience-appropriate suggestions                            │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    CORRECTION PREFERENCES                              │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Aggressiveness (0.0 = conservative, 1.0 = aggressive)          │  │  │
│  │  │  - How readily to suggest corrections                          │  │  │
│  │  │  - Learned from accept/reject ratios                           │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Thresholds                                                      │  │  │
│  │  │  - Suggestion threshold: minimum confidence to show            │  │  │
│  │  │  - Auto-correct threshold: minimum confidence to auto-apply    │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  │  ┌─────────────────────────────────────────────────────────────────┐  │  │
│  │  │ Feature Toggles                                                 │  │  │
│  │  │  - Enable/disable auto-correction                              │  │  │
│  │  │  - Enable/disable learning                                     │  │  │
│  │  │  - Correction categories to include/exclude                    │  │  │
│  │  └─────────────────────────────────────────────────────────────────┘  │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│      │                                                                       │
│      ▼                                                                       │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    USER PROFILE STORE (PathMap)                       │  │
│  └───────────────────────────────────────────────────────────────────────┘  │
│                                                                              │
└──────────────────────────────────────────────────────────────────────────────┘
```

---

## Core Data Structures

### User Profile

```rust
/// Complete user preference profile
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UserProfile {
    /// User identifier
    pub user_id: UserId,

    /// Vocabulary preferences
    pub vocabulary: VocabularyProfile,

    /// Writing style preferences
    pub style: StyleProfile,

    /// Detected domains
    pub domains: Vec<DomainProfile>,

    /// Correction behavior preferences
    pub correction: CorrectionPreferences,

    /// Profile metadata
    pub metadata: ProfileMetadata,
}

/// Profile metadata
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ProfileMetadata {
    /// When profile was created
    pub created_at: Timestamp,

    /// When profile was last updated
    pub updated_at: Timestamp,

    /// Total feedback items processed
    pub feedback_count: u64,

    /// Profile version (for migrations)
    pub version: u32,

    /// Profile confidence (how much data we have)
    pub confidence: f64,
}
```

### Vocabulary Profile

```rust
/// User vocabulary preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct VocabularyProfile {
    /// Words the user always accepts (personal dictionary)
    pub accepted_words: HashSet<String>,

    /// Words to never flag
    pub ignored_words: HashSet<String>,

    /// Technical vocabulary by domain
    pub technical_vocab: HashMap<Domain, HashSet<String>>,

    /// Vocabulary complexity level (0.0 = simple, 1.0 = advanced)
    pub complexity_level: f64,

    /// Recently used words (for suggestions)
    pub recent_words: LruCache<String, u64>,

    /// Word frequency statistics
    pub word_stats: WordStats,
}

/// Word usage statistics
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WordStats {
    /// Total words processed
    pub total_words: u64,

    /// Unique words seen
    pub unique_words: u64,

    /// Average word length
    pub avg_word_length: f64,

    /// Average syllable count
    pub avg_syllables: f64,

    /// Rare word percentage (words not in common dictionary)
    pub rare_word_pct: f64,
}
```

### Style Profile

```rust
/// User writing style preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyleProfile {
    /// Formality level (0.0 = casual, 1.0 = formal)
    pub formality: f64,

    /// Correction aggressiveness (0.0 = conservative, 1.0 = aggressive)
    pub aggressiveness: f64,

    /// Preferred language variety
    pub language_variety: LanguageVariety,

    /// Tone preferences
    pub tone: TonePreferences,

    /// Punctuation style
    pub punctuation: PunctuationStyle,

    /// Capitalization preferences
    pub capitalization: CapitalizationStyle,
}

/// Language variety preferences
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum LanguageVariety {
    AmericanEnglish,
    BritishEnglish,
    AustralianEnglish,
    CanadianEnglish,
    IndianEnglish,
    Mixed,  // User uses multiple varieties
    Unknown,
}

/// Tone preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TonePreferences {
    /// Directness level (0.0 = indirect, 1.0 = direct)
    pub directness: f64,

    /// Politeness level (0.0 = casual, 1.0 = very polite)
    pub politeness: f64,

    /// Humor tolerance (0.0 = serious only, 1.0 = humor welcome)
    pub humor_tolerance: f64,
}

/// Punctuation style preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PunctuationStyle {
    /// Oxford comma preference
    pub oxford_comma: Option<bool>,

    /// Single vs double quotes
    pub quote_style: QuoteStyle,

    /// Exclamation point usage frequency
    pub exclamation_frequency: f64,

    /// Ellipsis usage
    pub uses_ellipsis: bool,
}

/// Quote style preference
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum QuoteStyle {
    Single,
    Double,
    Mixed,
    Unknown,
}

/// Capitalization style preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CapitalizationStyle {
    /// Sentence case vs title case for headings
    pub heading_style: HeadingCapitalization,

    /// All caps usage frequency
    pub all_caps_frequency: f64,
}

/// Heading capitalization preference
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub enum HeadingCapitalization {
    SentenceCase,
    TitleCase,
    AllCaps,
    Unknown,
}
```

### Domain Profile

```rust
/// Domain-specific preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct DomainProfile {
    /// The domain
    pub domain: Domain,

    /// Confidence that user works in this domain
    pub confidence: f64,

    /// Domain-specific vocabulary
    pub vocabulary: HashSet<String>,

    /// Domain-specific abbreviations
    pub abbreviations: HashMap<String, String>,

    /// Domain-specific style adjustments
    pub style_overrides: Option<StyleOverrides>,

    /// Last detected in this domain
    pub last_seen: Timestamp,
}

/// Domain classification
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Domain {
    Medical,
    Legal,
    Technical,
    Academic,
    Business,
    Creative,
    Casual,
    Programming(ProgrammingLanguage),
    Science(ScienceField),
    Other(String),
}

/// Programming language for code context
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ProgrammingLanguage {
    Rust,
    Python,
    JavaScript,
    TypeScript,
    Java,
    CSharp,
    Go,
    Ruby,
    Rholang,
    MeTTa,
    Other(String),
}

/// Science field
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum ScienceField {
    Physics,
    Chemistry,
    Biology,
    Mathematics,
    ComputerScience,
    Other(String),
}

/// Style overrides for a specific domain
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyleOverrides {
    /// Override formality level
    pub formality: Option<f64>,

    /// Override aggressiveness
    pub aggressiveness: Option<f64>,

    /// Additional accepted words
    pub additional_accepted: HashSet<String>,

    /// Words to always correct in this domain
    pub always_correct: HashMap<String, String>,
}
```

### Correction Preferences

```rust
/// User correction behavior preferences
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CorrectionPreferences {
    /// Enable auto-correction (vs suggestions only)
    pub auto_correct: bool,

    /// Minimum confidence to show a suggestion
    pub suggestion_threshold: f64,

    /// Minimum confidence for auto-correction
    pub auto_correct_threshold: f64,

    /// Maximum number of suggestions to show
    pub max_suggestions: usize,

    /// Enable learning from user actions
    pub enable_learning: bool,

    /// Correction categories to include
    pub enabled_categories: HashSet<CorrectionCategory>,

    /// Correction categories to exclude
    pub disabled_categories: HashSet<CorrectionCategory>,

    /// Per-tier settings
    pub tier_settings: TierSettings,
}

/// Correction categories
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum CorrectionCategory {
    Spelling,
    Grammar,
    Punctuation,
    Capitalization,
    Style,
    Wordiness,
    Clarity,
    Tone,
}

/// Per-tier correction settings
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct TierSettings {
    /// Tier 1 (lexical) enabled
    pub tier1_enabled: bool,

    /// Tier 2 (syntactic) enabled
    pub tier2_enabled: bool,

    /// Tier 3 (semantic) enabled
    pub tier3_enabled: bool,

    /// Per-tier confidence adjustments
    pub tier_adjustments: HashMap<CorrectionTier, f64>,
}

impl Default for CorrectionPreferences {
    fn default() -> Self {
        Self {
            auto_correct: false,
            suggestion_threshold: 0.7,
            auto_correct_threshold: 0.95,
            max_suggestions: 5,
            enable_learning: true,
            enabled_categories: CorrectionCategory::all(),
            disabled_categories: HashSet::new(),
            tier_settings: TierSettings::default(),
        }
    }
}
```

---

## Profile Learning

### Vocabulary Learning

```rust
/// Learns vocabulary preferences from user actions
pub struct VocabularyModeler {
    /// Minimum rejections before adding to personal dictionary
    min_rejections_for_accept: u32,

    /// Decay rate for word recency
    recency_decay: f64,
}

impl VocabularyModeler {
    /// Update vocabulary profile from feedback
    pub fn update_from_feedback(
        &self,
        profile: &mut VocabularyProfile,
        feedback: &Feedback,
    ) {
        match &feedback.response {
            FeedbackResponse::Reject(_) => {
                // User rejected correction → they want to keep original
                let original = &feedback.correction.original;

                // Check if this word has been rejected multiple times
                let rejection_count = self.get_rejection_count(original);

                if rejection_count >= self.min_rejections_for_accept {
                    // Add to personal dictionary
                    profile.accepted_words.insert(original.clone());
                }

                // Track the rejection
                self.track_rejection(original);
            }

            FeedbackResponse::Modify(m) => {
                // User provided their own correction
                // Learn their vocabulary choice
                let user_words: Vec<&str> = m.modified_text.split_whitespace().collect();

                for word in user_words {
                    profile.recent_words.put(word.to_string(), 1);
                }
            }

            FeedbackResponse::Accept(_) => {
                // User accepted correction
                // Learn the corrected vocabulary
                let corrected_words: Vec<&str> = feedback.correction.proposed
                    .split_whitespace().collect();

                for word in corrected_words {
                    profile.recent_words.put(word.to_string(), 1);
                }
            }

            _ => {}
        }

        // Update word statistics
        self.update_word_stats(profile, feedback);
    }

    /// Detect technical vocabulary from usage patterns
    pub fn detect_technical_vocab(
        &self,
        profile: &mut VocabularyProfile,
        text: &str,
        domain: &Domain,
    ) {
        let words: Vec<&str> = text.split_whitespace().collect();

        for word in words {
            // Check if word is not in common dictionary but user uses it
            if self.is_potential_technical_term(word) {
                let domain_vocab = profile.technical_vocab
                    .entry(domain.clone())
                    .or_insert_with(HashSet::new);

                domain_vocab.insert(word.to_string());
            }
        }
    }

    fn is_potential_technical_term(&self, word: &str) -> bool {
        // Heuristics for technical terms:
        // - Contains numbers (e.g., "HTTP2", "IPv6")
        // - All caps acronym (e.g., "API", "SDK")
        // - CamelCase (e.g., "PathMap", "MeTTa")
        // - Contains underscore (e.g., "snake_case")
        // - Not in common dictionary

        let has_numbers = word.chars().any(|c| c.is_ascii_digit());
        let is_all_caps = word.len() >= 2 && word.chars().all(|c| c.is_uppercase());
        let is_camel_case = word.chars().skip(1).any(|c| c.is_uppercase());
        let has_underscore = word.contains('_');

        has_numbers || is_all_caps || is_camel_case || has_underscore
    }

    fn update_word_stats(&self, profile: &mut VocabularyProfile, feedback: &Feedback) {
        let text = &feedback.correction.original;
        let words: Vec<&str> = text.split_whitespace().collect();

        for word in words {
            profile.word_stats.total_words += 1;

            // Update average word length
            let len = word.len() as f64;
            let n = profile.word_stats.total_words as f64;
            profile.word_stats.avg_word_length =
                (profile.word_stats.avg_word_length * (n - 1.0) + len) / n;
        }
    }

    fn get_rejection_count(&self, _word: &str) -> u32 {
        // Would query PathMap for rejection history
        0
    }

    fn track_rejection(&self, _word: &str) {
        // Would store rejection in PathMap
    }
}
```

### Style Learning

```rust
/// Learns writing style preferences from user text
pub struct StyleProfiler {
    /// Formality indicators
    formal_indicators: Vec<&'static str>,
    informal_indicators: Vec<&'static str>,

    /// Language variety indicators
    variety_indicators: HashMap<LanguageVariety, Vec<&'static str>>,
}

impl StyleProfiler {
    pub fn new() -> Self {
        let mut variety_indicators = HashMap::new();

        variety_indicators.insert(LanguageVariety::BritishEnglish, vec![
            "colour", "favour", "behaviour", "organise", "realise",
            "centre", "theatre", "programme", "defence", "licence",
        ]);

        variety_indicators.insert(LanguageVariety::AmericanEnglish, vec![
            "color", "favor", "behavior", "organize", "realize",
            "center", "theater", "program", "defense", "license",
        ]);

        Self {
            formal_indicators: vec![
                "therefore", "consequently", "furthermore", "moreover",
                "nevertheless", "notwithstanding", "accordingly", "hence",
            ],
            informal_indicators: vec![
                "gonna", "wanna", "gotta", "kinda", "sorta",
                "yeah", "yep", "nope", "ok", "okay",
            ],
            variety_indicators,
        }
    }

    /// Update style profile from feedback
    pub fn update_from_feedback(
        &self,
        profile: &mut StyleProfile,
        feedback: &Feedback,
    ) {
        let text = match &feedback.response {
            FeedbackResponse::Modify(m) => &m.modified_text,
            _ => &feedback.correction.original,
        };

        // Update formality
        let formality_delta = self.compute_formality(text);
        profile.formality = self.smooth_update(profile.formality, formality_delta, 0.1);

        // Update language variety
        if let Some(variety) = self.detect_variety(text) {
            profile.language_variety = variety;
        }

        // Update punctuation style
        self.update_punctuation_style(&mut profile.punctuation, text);

        // Update aggressiveness based on feedback patterns
        self.update_aggressiveness(profile, feedback);
    }

    fn compute_formality(&self, text: &str) -> f64 {
        let lower = text.to_lowercase();
        let words: Vec<&str> = lower.split_whitespace().collect();

        let formal_count = words.iter()
            .filter(|w| self.formal_indicators.contains(w))
            .count();

        let informal_count = words.iter()
            .filter(|w| self.informal_indicators.contains(w))
            .count();

        let total = formal_count + informal_count;
        if total == 0 {
            return 0.5;  // Neutral
        }

        formal_count as f64 / total as f64
    }

    fn detect_variety(&self, text: &str) -> Option<LanguageVariety> {
        let lower = text.to_lowercase();
        let words: HashSet<&str> = lower.split_whitespace().collect();

        let mut variety_scores: HashMap<LanguageVariety, usize> = HashMap::new();

        for (variety, indicators) in &self.variety_indicators {
            let count = indicators.iter()
                .filter(|w| words.contains(*w))
                .count();

            if count > 0 {
                *variety_scores.entry(variety.clone()).or_insert(0) += count;
            }
        }

        variety_scores.into_iter()
            .max_by_key(|(_, count)| *count)
            .map(|(variety, _)| variety)
    }

    fn update_punctuation_style(&self, style: &mut PunctuationStyle, text: &str) {
        // Detect Oxford comma
        if text.contains(", and ") {
            // Might have Oxford comma
            // Would need more sophisticated detection
        }

        // Detect quote style
        if text.contains('"') {
            style.quote_style = QuoteStyle::Double;
        } else if text.contains('\'') {
            style.quote_style = QuoteStyle::Single;
        }

        // Count exclamation points
        let exclamations = text.chars().filter(|c| *c == '!').count();
        let sentences = text.split('.').count() + text.split('!').count() + text.split('?').count();

        if sentences > 0 {
            let freq = exclamations as f64 / sentences as f64;
            style.exclamation_frequency = self.smooth_update(
                style.exclamation_frequency,
                freq,
                0.1,
            );
        }
    }

    fn update_aggressiveness(&self, profile: &mut StyleProfile, feedback: &Feedback) {
        // If user frequently rejects corrections, reduce aggressiveness
        // If user frequently accepts, increase aggressiveness

        let delta = match &feedback.response {
            FeedbackResponse::Accept(_) => 0.02,   // Slight increase
            FeedbackResponse::Reject(_) => -0.05,  // Larger decrease
            FeedbackResponse::Modify(_) => -0.01,  // Slight decrease
            _ => 0.0,
        };

        profile.aggressiveness = (profile.aggressiveness + delta).clamp(0.0, 1.0);
    }

    fn smooth_update(&self, current: f64, new: f64, alpha: f64) -> f64 {
        current * (1.0 - alpha) + new * alpha
    }
}
```

### Domain Detection

```rust
/// Detects user's working domains
pub struct DomainDetector {
    /// Domain keyword dictionaries
    domain_keywords: HashMap<Domain, HashSet<String>>,

    /// Minimum confidence to add domain to profile
    min_confidence: f64,
}

impl DomainDetector {
    pub fn new() -> Self {
        let mut domain_keywords = HashMap::new();

        domain_keywords.insert(Domain::Medical, hashset![
            "patient", "diagnosis", "treatment", "symptoms", "prescription",
            "surgery", "medication", "doctor", "nurse", "hospital",
            "clinical", "therapy", "chronic", "acute", "prognosis",
        ]);

        domain_keywords.insert(Domain::Legal, hashset![
            "plaintiff", "defendant", "court", "judge", "attorney",
            "contract", "liability", "statute", "verdict", "jurisdiction",
            "prosecution", "testimony", "evidence", "lawsuit", "settlement",
        ]);

        domain_keywords.insert(Domain::Technical, hashset![
            "algorithm", "implementation", "database", "server", "api",
            "function", "variable", "parameter", "interface", "protocol",
            "architecture", "framework", "deployment", "testing", "debugging",
        ]);

        domain_keywords.insert(Domain::Academic, hashset![
            "hypothesis", "methodology", "analysis", "conclusion", "abstract",
            "citation", "bibliography", "peer-reviewed", "dissertation", "thesis",
            "research", "study", "findings", "empirical", "theoretical",
        ]);

        domain_keywords.insert(Domain::Business, hashset![
            "revenue", "profit", "stakeholder", "strategy", "marketing",
            "budget", "quarterly", "roi", "kpi", "deliverable",
            "initiative", "synergy", "leverage", "optimize", "scalable",
        ]);

        Self {
            domain_keywords,
            min_confidence: 0.3,
        }
    }

    /// Detect domain from text
    pub fn detect(&self, text: &str) -> Vec<(Domain, f64)> {
        let lower = text.to_lowercase();
        let words: HashSet<&str> = lower.split_whitespace().collect();

        let mut scores: Vec<(Domain, f64)> = self.domain_keywords.iter()
            .map(|(domain, keywords)| {
                let matches = keywords.iter()
                    .filter(|k| words.contains(k.as_str()))
                    .count();

                let confidence = if keywords.is_empty() {
                    0.0
                } else {
                    (matches as f64 / keywords.len() as f64).min(1.0)
                };

                (domain.clone(), confidence)
            })
            .filter(|(_, conf)| *conf >= self.min_confidence)
            .collect();

        // Check for programming languages
        if let Some((lang, conf)) = self.detect_programming_language(text) {
            scores.push((Domain::Programming(lang), conf));
        }

        scores.sort_by(|(_, a), (_, b)| b.partial_cmp(a).unwrap());
        scores
    }

    fn detect_programming_language(&self, text: &str) -> Option<(ProgrammingLanguage, f64)> {
        let indicators: Vec<(ProgrammingLanguage, Vec<&str>)> = vec![
            (ProgrammingLanguage::Rust, vec![
                "fn ", "let mut", "impl ", "pub fn", "use std::", "&str", "Vec<",
            ]),
            (ProgrammingLanguage::Python, vec![
                "def ", "import ", "from ", "class ", "self.", "__init__",
            ]),
            (ProgrammingLanguage::JavaScript, vec![
                "const ", "function ", "=>", "async ", "await ", "console.log",
            ]),
            (ProgrammingLanguage::Rholang, vec![
                "contract ", "for(", "<-", "new ", "@", "Nil",
            ]),
            (ProgrammingLanguage::MeTTa, vec![
                "(:", "(=", "(->", "Atom", "Space", "!",
            ]),
        ];

        for (lang, patterns) in indicators {
            let matches = patterns.iter()
                .filter(|p| text.contains(*p))
                .count();

            if matches >= 2 {
                return Some((lang, (matches as f64 / patterns.len() as f64).min(1.0)));
            }
        }

        None
    }

    /// Update profile with detected domain
    pub fn update_profile(
        &self,
        profile: &mut Vec<DomainProfile>,
        text: &str,
    ) {
        let detected = self.detect(text);

        for (domain, confidence) in detected {
            if let Some(existing) = profile.iter_mut().find(|p| p.domain == domain) {
                // Update existing domain profile
                existing.confidence = (existing.confidence + confidence) / 2.0;
                existing.last_seen = Timestamp::now();
            } else {
                // Add new domain profile
                profile.push(DomainProfile {
                    domain,
                    confidence,
                    vocabulary: HashSet::new(),
                    abbreviations: HashMap::new(),
                    style_overrides: None,
                    last_seen: Timestamp::now(),
                });
            }
        }

        // Sort by confidence
        profile.sort_by(|a, b| b.confidence.partial_cmp(&a.confidence).unwrap());
    }
}

// Helper macro for hashset creation
macro_rules! hashset {
    ($($x:expr),*$(,)?) => {{
        let mut set = HashSet::new();
        $(set.insert($x.to_string());)*
        set
    }};
}
use hashset;
```

---

## Profile Application

### Personalized Correction

```rust
/// Applies user preferences to corrections
pub struct PreferenceApplicator {
    /// Default correction confidence threshold
    default_threshold: f64,
}

impl PreferenceApplicator {
    /// Apply user preferences to candidate corrections
    pub fn apply(
        &self,
        candidates: Vec<CorrectionCandidate>,
        profile: &UserProfile,
    ) -> Vec<CorrectionCandidate> {
        candidates.into_iter()
            .filter_map(|c| self.filter_and_adjust(c, profile))
            .collect()
    }

    fn filter_and_adjust(
        &self,
        mut candidate: CorrectionCandidate,
        profile: &UserProfile,
    ) -> Option<CorrectionCandidate> {
        // Check if word is in personal dictionary
        if profile.vocabulary.accepted_words.contains(&candidate.original) {
            return None;  // Don't correct accepted words
        }

        // Check if word should be ignored
        if profile.vocabulary.ignored_words.contains(&candidate.original) {
            return None;
        }

        // Check if word is in technical vocabulary
        for domain_vocab in profile.vocabulary.technical_vocab.values() {
            if domain_vocab.contains(&candidate.original) {
                return None;
            }
        }

        // Check correction category preferences
        if !profile.correction.enabled_categories.contains(&candidate.category) {
            return None;
        }

        if profile.correction.disabled_categories.contains(&candidate.category) {
            return None;
        }

        // Adjust confidence based on user aggressiveness
        candidate.confidence *= self.aggressiveness_factor(profile.style.aggressiveness);

        // Check threshold
        let threshold = self.get_effective_threshold(profile);
        if candidate.confidence < threshold {
            return None;
        }

        // Adjust for language variety
        if let Some(adjusted) = self.adjust_for_variety(&candidate, &profile.style.language_variety) {
            candidate = adjusted;
        }

        Some(candidate)
    }

    fn aggressiveness_factor(&self, aggressiveness: f64) -> f64 {
        // Low aggressiveness → higher threshold → lower effective confidence
        // High aggressiveness → lower threshold → higher effective confidence
        0.8 + 0.4 * aggressiveness  // Range: 0.8 to 1.2
    }

    fn get_effective_threshold(&self, profile: &UserProfile) -> f64 {
        let base = profile.correction.suggestion_threshold;

        // Adjust based on aggressiveness
        // High aggressiveness → lower threshold
        base * (1.5 - profile.style.aggressiveness)
    }

    fn adjust_for_variety(
        &self,
        candidate: &CorrectionCandidate,
        variety: &LanguageVariety,
    ) -> Option<CorrectionCandidate> {
        // Adjust spelling corrections based on language variety
        let variety_spellings: HashMap<&str, HashMap<LanguageVariety, &str>> = hashmap! {
            "colour" => hashmap! {
                LanguageVariety::AmericanEnglish => "color",
                LanguageVariety::BritishEnglish => "colour",
            },
            "color" => hashmap! {
                LanguageVariety::BritishEnglish => "colour",
                LanguageVariety::AmericanEnglish => "color",
            },
            // ... more mappings
        };

        if let Some(variants) = variety_spellings.get(candidate.original.as_str()) {
            if let Some(&preferred) = variants.get(variety) {
                if candidate.proposed == preferred {
                    return Some(candidate.clone());
                } else if let Some(&correct) = variants.get(variety) {
                    let mut adjusted = candidate.clone();
                    adjusted.proposed = correct.to_string();
                    return Some(adjusted);
                }
            }
        }

        Some(candidate.clone())
    }
}

/// A candidate correction
#[derive(Clone, Debug)]
pub struct CorrectionCandidate {
    pub original: String,
    pub proposed: String,
    pub confidence: f64,
    pub category: CorrectionCategory,
    pub tier: CorrectionTier,
}

// Helper macro for hashmap creation
macro_rules! hashmap {
    ($($key:expr => $value:expr),*$(,)?) => {{
        let mut map = HashMap::new();
        $(map.insert($key, $value);)*
        map
    }};
}
use hashmap;
```

---

## PathMap Storage Schema

```
PathMap Key Structure (User Preferences):
=========================================

/learning/user/{user_id}/
    /vocabulary/
        /accepted/
            {word_hash} -> word  ; Personal dictionary
        /ignored/
            {word_hash} -> word  ; Words to skip
        /technical/{domain}/
            {word_hash} -> word  ; Domain-specific terms
        /recent/
            {word_hash} -> (word, timestamp, count)
        /stats/
            total_words -> u64
            unique_words -> u64
            avg_word_length -> float
            avg_syllables -> float
            rare_word_pct -> float
        complexity_level -> float

    /style/
        formality -> float
        aggressiveness -> float
        variety -> american|british|australian|etc
        /tone/
            directness -> float
            politeness -> float
            humor_tolerance -> float
        /punctuation/
            oxford_comma -> optional bool
            quote_style -> single|double|mixed
            exclamation_frequency -> float
            uses_ellipsis -> bool
        /capitalization/
            heading_style -> sentence|title|allcaps
            all_caps_frequency -> float

    /domains/
        {domain_id}/
            domain_type -> medical|legal|technical|etc
            confidence -> float
            last_seen -> timestamp
            /vocabulary/
                {word_hash} -> word
            /abbreviations/
                {abbrev} -> expansion
            /style_overrides/
                formality -> optional float
                aggressiveness -> optional float

    /preferences/
        auto_correct -> bool
        suggestion_threshold -> float
        auto_correct_threshold -> float
        max_suggestions -> int
        enable_learning -> bool
        /enabled_categories/
            {category} -> true
        /disabled_categories/
            {category} -> true
        /tier_settings/
            tier1_enabled -> bool
            tier2_enabled -> bool
            tier3_enabled -> bool
            /adjustments/
                {tier} -> float

    /metadata/
        created_at -> timestamp
        updated_at -> timestamp
        feedback_count -> u64
        version -> u32
        confidence -> float
```

---

## MeTTa Predicates

### Profile Predicates

```metta
; Profile types
(: UserProfile Type)
(: VocabularyProfile Type)
(: StyleProfile Type)
(: DomainProfile Type)

; Profile queries
(: user-profile (-> UserId (Maybe UserProfile)))
(: user-vocabulary (-> UserId VocabularyProfile))
(: user-style (-> UserId StyleProfile))
(: user-domains (-> UserId (List DomainProfile)))
```

### Vocabulary Predicates

```metta
; Vocabulary operations
(: accepts-word (-> UserId String Bool))
(: ignores-word (-> UserId String Bool))
(: technical-word (-> UserId Domain String Bool))

; Vocabulary modification
(: add-accepted-word (-> UserId String (Result () Error)))
(: add-ignored-word (-> UserId String (Result () Error)))
(: add-technical-word (-> UserId Domain String (Result () Error)))
(: remove-accepted-word (-> UserId String (Result () Error)))
```

### Style Predicates

```metta
; Style queries
(: user-formality (-> UserId Float))
(: user-aggressiveness (-> UserId Float))
(: user-variety (-> UserId LanguageVariety))

; Style inference
(: compute-formality (-> String Float))
(: detect-variety (-> String (Maybe LanguageVariety)))
(: detect-tone (-> String TonePreferences))
```

### Domain Predicates

```metta
; Domain detection
(: detect-domain (-> String (List (Pair Domain Float))))
(: detect-programming-language (-> String (Maybe (Pair ProgrammingLanguage Float))))

; Domain queries
(: user-primary-domain (-> UserId (Maybe Domain)))
(: domain-confidence (-> UserId Domain Float))
(: domain-vocabulary (-> UserId Domain (Set String)))
```

### Preference Application Predicates

```metta
; Personalization
(: personalize-corrections (-> UserId (List Correction) (List Correction)))
(: effective-threshold (-> UserId Float))
(: should-suggest (-> UserId Correction Bool))
(: should-auto-correct (-> UserId Correction Bool))

; Profile updates
(: update-from-feedback (-> UserId Feedback (Result UserProfile Error)))
(: reset-profile (-> UserId (Result () Error)))
```

---

## Related Documentation

- [README](./README.md) - Agent learning overview
- [Feedback Collection](./01-feedback-collection.md) - Input to preference learning
- [Pattern Learning](./02-pattern-learning.md) - Learned patterns interact with preferences
- [Online Learning](./04-online-learning.md) - Weight updates based on preferences
