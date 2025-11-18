# Makefile for Rocq/Coq verification proofs

.PHONY: all clean phonetic regex cfg html extract check

# Coq compiler
COQC := coqc
COQDOC := coqdoc

# Directories
PHONETIC_DIR := phonetic
REGEX_DIR := regex
CFG_DIR := cfg
HTML_DIR := html
EXTRACT_DIR := extracted

# Phonetic proof files
PHONETIC_FILES := \
	$(PHONETIC_DIR)/rewrite_rules.v \
	$(PHONETIC_DIR)/zompist_rules.v

# Extraction file
EXTRACTION_FILE := $(PHONETIC_DIR)/extraction.v

# Compiled objects
PHONETIC_VO := $(PHONETIC_FILES:.v=.vo)

# Default target: compile all proofs
all: phonetic

# Compile phonetic proofs
phonetic: $(PHONETIC_VO)

# Pattern rule for .vo files
%.vo: %.v
	@echo "Compiling $<..."
	$(COQC) -Q $(PHONETIC_DIR) PhoneticRewrites $<

# Dependency tracking
$(PHONETIC_DIR)/zompist_rules.vo: $(PHONETIC_DIR)/rewrite_rules.vo

# Generate HTML documentation
html: $(PHONETIC_VO)
	@echo "Generating HTML documentation..."
	@mkdir -p $(HTML_DIR)
	$(COQDOC) --html -d $(HTML_DIR) $(PHONETIC_FILES)
	@echo "Documentation generated in $(HTML_DIR)/"

# Extract OCaml code
extract: $(PHONETIC_VO)
	@echo "Extracting OCaml code..."
	@mkdir -p $(EXTRACT_DIR)
	$(COQC) -Q $(PHONETIC_DIR) PhoneticRewrites $(EXTRACTION_FILE)
	@echo "Moving extracted files to $(EXTRACT_DIR)/..."
	@mv *.ml *.mli $(EXTRACT_DIR)/ 2>/dev/null || true
	@echo "✓ Extraction complete! Generated files:"
	@ls -lh $(EXTRACT_DIR)/ 2>/dev/null || echo "No files generated"

# Check proofs without compiling
check:
	@echo "Checking proofs..."
	@for file in $(PHONETIC_FILES); do \
		echo "Checking $$file..."; \
		$(COQC) -Q $(PHONETIC_DIR) PhoneticRewrites $$file > /dev/null && echo "  ✓ OK" || echo "  ✗ FAILED"; \
	done

# Clean compiled files
clean:
	@echo "Cleaning compiled files..."
	@rm -f $(PHONETIC_DIR)/*.vo $(PHONETIC_DIR)/*.vok $(PHONETIC_DIR)/*.vos
	@rm -f $(PHONETIC_DIR)/*.glob $(PHONETIC_DIR)/.*.aux
	@rm -rf $(HTML_DIR)
	@rm -rf $(EXTRACT_DIR)
	@echo "Clean complete."

# Help target
help:
	@echo "Rocq Verification Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  all       - Compile all proofs (default)"
	@echo "  phonetic  - Compile phonetic rewrite rule proofs"
	@echo "  html      - Generate HTML documentation"
	@echo "  extract   - Extract OCaml reference implementation"
	@echo "  check     - Type-check proofs without full compilation"
	@echo "  clean     - Remove all compiled files"
	@echo "  help      - Show this help message"
	@echo ""
	@echo "Files:"
	@echo "  Phonetic: $(PHONETIC_FILES)"
