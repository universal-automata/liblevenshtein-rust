# Test Corpora for liblevenshtein-rust

This directory contains standard test corpora used for validating spelling correction algorithms and benchmarking performance. These corpora are **not committed to the repository** and must be downloaded using the provided script.

## Quick Start

Download all corpora:

```bash
./scripts/download_corpora.sh
```

Extract Birkbeck archive (after download):

```bash
unzip data/corpora/birkbeck.zip -d data/corpora/birkbeck/
```

## Available Corpora

### 1. Norvig's big.txt

**Purpose**: Dictionary source and realistic query distribution
**Size**: 6.5 MB (~230K words, 32,192 unique)
**Source**: [Peter Norvig](https://norvig.com/big.txt)
**Format**: Plain text, one token per line

This is a concatenation of several public domain texts, widely used in spelling correction literature for benchmarking. It provides a natural language word frequency distribution (approximately Zipfian).

**Use cases**:
- Dictionary construction benchmarks (32K unique words)
- Realistic query workload generation (frequency-stratified sampling)
- Natural language distribution testing

**Citation**:
> Norvig, P. (2007). How to Write a Spelling Corrector. Available at https://norvig.com/spell-correct.html

---

### 2. Birkbeck Spelling Error Corpus

**Purpose**: Real-world spelling error validation
**Size**: 607 KB (36,133 misspellings of 6,136 words)
**Source**: [Oxford Text Archive](https://ota.bodleian.ox.ac.uk/repository/xmlui/handle/20.500.12024/0643)
**Format**: ZIP archive containing multiple `.DAT` files

The Birkbeck corpus (Mitton, 1985) contains real spelling errors from native English speakers, including:
- Spelling test results
- Free writing samples
- Errors from schoolchildren, university students, and adult literacy learners

**Files after extraction** (in `data/corpora/birkbeck/`):
- `HOLBROOKDAT.643`: Secondary school errors
- `EXAMSDAT.643`: University exam errors
- `MASTERSDAT.643`: Graduate student errors
- Many others (see `AAAREADMEDOC.643` for details)

**Use cases**:
- Primary validation corpus for recall testing
- Real-world error pattern analysis
- Target: >95% recall at Levenshtein distance ≤3

**Citation**:
> Mitton, R. (1985). Birkbeck spelling error corpus. Oxford Text Archive, http://ota.ox.ac.uk/desc/0643

---

### 3. Holbrook Corpus (Processed)

**Purpose**: Secondary school spelling errors
**Size**: 24 KB (1,791 misspellings of 1,200 words)
**Source**: [Roger Mitton's processed version](https://titan.dcs.bbk.ac.uk/~ROGER/holbrook-missp.dat)
**Format**: `$correct_word` followed by `misspelling frequency` (one per line)

Extracted from the Birkbeck corpus, this file contains spelling errors from secondary school students' free writing.

**Format example**:
```
$After
Artair 1
$America
American 1
$And
Ane 1
```

**Use cases**:
- Educational domain validation
- Younger learner error patterns
- Target: >90% recall at distance ≤2

---

### 4. Aspell Corpus

**Purpose**: Technical and domain-specific terms
**Size**: 9 KB (531 misspellings)
**Source**: [Roger Mitton's collection](https://titan.dcs.bbk.ac.uk/~ROGER/aspell.dat)
**Format**: `$correct_word` followed by misspellings (one per line)

Common misspellings extracted from GNU Aspell, including technical vocabulary and proper nouns.

**Format example**:
```
$Nevada
nevade
$Presbyterian
presbyterian
$ability
abilitey
```

**Use cases**:
- Technical term validation
- Domain-specific error patterns
- Target: >85% coverage

---

### 5. Wikipedia Common Misspellings

**Purpose**: High-frequency web-scale errors
**Size**: 43 KB (2,455 common misspellings)
**Source**: [Roger Mitton's processed version](https://titan.dcs.bbk.ac.uk/~ROGER/wikipedia.dat)
**Format**: `$correct_word` followed by misspellings (one per line)

Curated from Wikipedia's list of common misspellings, representing errors frequently seen in web content.

**Format example**:
```
$Apennines
Apenines
Appenines
$Caesar
Ceasar
```

**Use cases**:
- High-frequency error validation
- Web-scale coverage testing
- Target: >90% coverage for common errors

---

## File Formats

### Norvig's big.txt Format

Plain text with one token per line, preserving frequency:

```
the
the
the
...
```

To get word frequencies, count occurrences.

### Mitton `.dat` Format

Each correct word is preceded by `$` and followed by its misspellings:

```
$correct_word
misspelling1 frequency1
misspelling2 frequency2
...
```

If frequency is omitted, it defaults to 1.

---

## Corpus Statistics

| Corpus | Size | Misspellings | Unique Words | Error Rate | Source Type |
|--------|------|--------------|--------------|------------|-------------|
| **big.txt** | 6.5 MB | - | 32,192 | - | Literature |
| **Birkbeck** | 607 KB | 36,133 | 6,136 | High | Native speakers |
| **Holbrook** | 24 KB | 1,791 | 1,200 | Medium | Secondary school |
| **Aspell** | 9 KB | 531 | - | Low | Technical terms |
| **Wikipedia** | 43 KB | 2,455 | - | High | Web content |

---

## Usage in Tests

Corpora are loaded via the `corpus` module (test-only):

```rust
use liblevenshtein::corpus::{BigTxtCorpus, MittonCorpus};

// Load Norvig's big.txt
let dict = BigTxtCorpus::load("data/corpora/big.txt")?;

// Load Holbrook corpus
let holbrook = MittonCorpus::load("data/corpora/holbrook.dat")?;
for (correct, misspellings) in &holbrook.errors {
    for (misspelling, frequency) in misspellings {
        // Test spell correction...
    }
}
```

---

## Licensing and Attribution

All corpora are freely available for research and educational use:

- **Norvig's big.txt**: Public domain texts
- **Birkbeck corpus**: Available via Oxford Text Archive for research
- **Holbrook/Aspell/Wikipedia**: Processed versions by Roger Mitton (Birkbeck College)

When publishing results using these corpora, please cite:

1. **Norvig, P.** (2007). How to Write a Spelling Corrector.
   https://norvig.com/spell-correct.html

2. **Mitton, R.** (1985). Birkbeck spelling error corpus.
   Oxford Text Archive, http://ota.ox.ac.uk/desc/0643

3. **Mitton, R.** Spelling error corpora.
   https://www.dcs.bbk.ac.uk/~ROGER/corpora.html

---

## Maintenance

**Download script**: `scripts/download_corpora.sh`
**Checksum verification**: SHA256 (automatic in download script)
**Git policy**: Corpora are excluded (`.gitignore`)
**CI caching**: Configured in `.github/workflows/` (see CI docs)

To update checksums after corpus changes:

```bash
sha256sum data/corpora/big.txt
sha256sum data/corpora/holbrook.dat
# ... update scripts/download_corpora.sh
```

---

## Validation Success Criteria

When running corpus validation tests:

| Corpus | Metric | Target | Distance |
|--------|--------|--------|----------|
| **Birkbeck** | Recall | >95% | ≤3 |
| **Holbrook** | Recall | >90% | ≤2 |
| **Aspell** | Coverage | >85% | ≤2 |
| **Wikipedia** | Coverage | >90% | ≤2 |

**Performance targets** (big.txt, 32K words):
- Construction time: <500ms
- Query p50: <20µs
- Query p95: <100µs
- Memory: <50 MB

---

## Generating Synthetic Errors

For additional testing, synthetic errors can be generated from big.txt:

```rust
use liblevenshtein::corpus::TypoGenerator;

let generator = TypoGenerator::new(seed);
let typos = generator.generate_typos("hello", distance, count);
// ["helo", "hllo", "hell", ...]
```

See `src/corpus/generator.rs` for implementation.

---

## References

1. Mitton, R. (1985). *Birkbeck spelling error corpus*. Oxford Text Archive.
2. Norvig, P. (2007). *How to Write a Spelling Corrector*. Available at https://norvig.com/spell-correct.html
3. Kukich, K. (1992). Techniques for automatically correcting words in text. *ACM Computing Surveys*, 24(4), 377-439.
4. Damerau, F. J. (1964). A technique for computer detection and correction of spelling errors. *Communications of the ACM*, 7(3), 171-176.
