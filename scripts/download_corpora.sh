#!/usr/bin/env bash
set -euo pipefail

# Download script for test corpora used in liblevenshtein-rust
# This script downloads standard corpora for spelling correction validation and benchmarking

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
CORPORA_DIR="$PROJECT_ROOT/data/corpora"

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Create corpora directory if it doesn't exist
mkdir -p "$CORPORA_DIR"

# Function to download and verify a file
download_and_verify() {
    local url="$1"
    local output_file="$2"
    local expected_sha256="$3"
    local description="$4"

    echo -e "${YELLOW}Downloading $description...${NC}"

    if [ -f "$output_file" ]; then
        echo "  File already exists: $output_file"
        echo "  Verifying checksum..."

        actual_sha256=$(sha256sum "$output_file" | awk '{print $1}')
        if [ "$actual_sha256" = "$expected_sha256" ]; then
            echo -e "  ${GREEN}✓ Checksum verified, skipping download${NC}"
            return 0
        else
            echo -e "  ${RED}✗ Checksum mismatch, re-downloading${NC}"
            rm "$output_file"
        fi
    fi

    # Download with retry logic
    local max_retries=3
    local retry=0

    while [ $retry -lt $max_retries ]; do
        if curl -L -f -o "$output_file" "$url"; then
            break
        else
            retry=$((retry + 1))
            if [ $retry -lt $max_retries ]; then
                echo -e "  ${YELLOW}Download failed, retrying ($retry/$max_retries)...${NC}"
                sleep 2
            else
                echo -e "  ${RED}✗ Download failed after $max_retries attempts${NC}"
                return 1
            fi
        fi
    done

    # Verify checksum
    echo "  Verifying checksum..."
    actual_sha256=$(sha256sum "$output_file" | awk '{print $1}')

    if [ "$actual_sha256" = "$expected_sha256" ]; then
        echo -e "  ${GREEN}✓ Checksum verified${NC}"
        return 0
    else
        echo -e "  ${RED}✗ Checksum mismatch!${NC}"
        echo "    Expected: $expected_sha256"
        echo "    Got:      $actual_sha256"
        rm "$output_file"
        return 1
    fi
}

echo "==================================================================="
echo "Downloading Test Corpora for liblevenshtein-rust"
echo "==================================================================="
echo ""

# 1. Norvig's big.txt - Primary dictionary and benchmark source
download_and_verify \
    "https://norvig.com/big.txt" \
    "$CORPORA_DIR/big.txt" \
    "fa066c7d40f0f201ac4144e652aa62430e58a6b3805ec70650f678da5804e87b" \
    "Norvig's big.txt (6.5 MB, ~230K words)"

# 2. Birkbeck spelling error corpus (Oxford Text Archive - official source)
# Contains 36,133 misspellings of 6,136 words from native speakers
echo ""
download_and_verify \
    "https://ota.bodleian.ox.ac.uk/repository/xmlui/bitstream/handle/20.500.12024/0643/0643.zip" \
    "$CORPORA_DIR/birkbeck.zip" \
    "5032f22ff572c3ad5906f82ddadcd54712abd233ccf01a6c05b86bd29a352c30" \
    "Birkbeck corpus (OTA official archive, 607 KB)"

# 3. Holbrook corpus (processed format from Roger Mitton's site)
# Contains 1,791 misspellings of 1,200 words from secondary school students
echo ""
download_and_verify \
    "https://titan.dcs.bbk.ac.uk/~ROGER/holbrook-missp.dat" \
    "$CORPORA_DIR/holbrook.dat" \
    "e2f0f0564954d049a1f663f3c7e72899382570a4fe575015169b1117de85ae3c" \
    "Holbrook corpus (24 KB)"

# 4. Aspell corpus (from Roger Mitton's site)
# Contains 531 misspellings, including technical terms
echo ""
download_and_verify \
    "https://titan.dcs.bbk.ac.uk/~ROGER/aspell.dat" \
    "$CORPORA_DIR/aspell.dat" \
    "0198fa5c343f82f0541ae39a0116b534e14bfadc54144377cadee2bd6d288988" \
    "Aspell corpus (9 KB)"

# 5. Wikipedia common misspellings (from Roger Mitton's site)
# Contains 2,455 common misspellings from Wikipedia
echo ""
download_and_verify \
    "https://titan.dcs.bbk.ac.uk/~ROGER/wikipedia.dat" \
    "$CORPORA_DIR/wikipedia.dat" \
    "061ec33aa12a4aea718a7bb121360812c8348770833e730124af1eecdc2cd380" \
    "Wikipedia corpus (43 KB)"

echo ""
echo "==================================================================="
echo "Download Summary"
echo "==================================================================="
echo -e "${GREEN}✓ Norvig's big.txt (6.5 MB, ~230K words)${NC}"
echo -e "${GREEN}✓ Birkbeck corpus (607 KB, 36K misspellings)${NC}"
echo -e "${GREEN}✓ Holbrook corpus (24 KB, 1.8K misspellings)${NC}"
echo -e "${GREEN}✓ Aspell corpus (9 KB, 531 misspellings)${NC}"
echo -e "${GREEN}✓ Wikipedia corpus (43 KB, 2.5K misspellings)${NC}"
echo ""
echo "Downloaded files are in: $CORPORA_DIR"
echo ""
echo -e "${YELLOW}Note:${NC} Birkbeck is a ZIP archive containing multiple corpus files."
echo "      Extract it with: unzip $CORPORA_DIR/birkbeck.zip -d $CORPORA_DIR/birkbeck/"
echo ""
echo -e "${YELLOW}Note:${NC} Downloaded corpora are excluded from git (.gitignore)"
echo "      Run this script on each machine or in CI to obtain test data."
echo ""
echo "Corpus formats:"
echo "  - big.txt: Plain text, one token per line (frequency list)"
echo "  - *.dat: \$correct_word followed by misspellings (one per line with frequency)"
