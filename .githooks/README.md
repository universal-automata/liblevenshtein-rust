# Git Hooks

This directory contains git hooks that help maintain code quality and prevent common mistakes.

## Installation

To install these hooks, run:

```bash
./scripts/install-git-hooks.sh
```

This will copy all hooks from `.githooks/` to `.git/hooks/` and make them executable.

## Available Hooks

### pre-commit

**Purpose**: Prevents accidentally committing local development overrides

**Checks**:
- Detects uncommented `[patch]` sections in `Cargo.toml`
- Detects local path dependencies that should use git sources (e.g., PathMap)

**Example of blocked commit**:

```bash
$ git commit -m "Update feature"
Checking Cargo.toml for local development overrides...
ERROR: Uncommented [patch] override detected in Cargo.toml

Found an uncommented [patch] section that would override dependencies.
This is likely a local development override that shouldn't be committed.
```

**Bypassing the hook** (not recommended):

```bash
git commit --no-verify
```

## Why These Hooks?

### Problem
When developing with local dependencies (like PathMap), developers often uncomment the `[patch]` section in `Cargo.toml`. This is correct for local development, but should never be committed to the repository.

### Solution
The pre-commit hook automatically checks for these overrides and prevents the commit, giving clear instructions on how to fix the issue.

## For Contributors

After cloning the repository, remember to install the hooks:

```bash
./scripts/install-git-hooks.sh
```

This is a one-time setup that will help you avoid accidentally committing local development configurations.
