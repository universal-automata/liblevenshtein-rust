#!/bin/bash
#
# Install git hooks from .githooks/ directory
#
# This script copies the hooks from .githooks/ to .git/hooks/
# and makes them executable.

set -e

# Colors for output
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Get the root directory of the git repository
REPO_ROOT=$(git rev-parse --show-toplevel)

if [ ! -d "$REPO_ROOT/.githooks" ]; then
    echo "Error: .githooks directory not found"
    exit 1
fi

echo "Installing git hooks from .githooks/..."

# Copy all hooks from .githooks to .git/hooks
for hook in "$REPO_ROOT/.githooks"/*; do
    if [ -f "$hook" ]; then
        hook_name=$(basename "$hook")
        target="$REPO_ROOT/.git/hooks/$hook_name"

        cp "$hook" "$target"
        chmod +x "$target"

        echo -e "${GREEN}✓ Installed: $hook_name${NC}"
    fi
done

echo ""
echo -e "${GREEN}Git hooks installed successfully!${NC}"
echo ""
echo "Installed hooks:"
echo "  - pre-commit: Checks for local development overrides in Cargo.toml"
echo ""
echo -e "${YELLOW}Note:${NC} To bypass hooks during commit, use: git commit --no-verify"
