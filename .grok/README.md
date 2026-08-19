# Grok Build

Grok Build is configured for this repository as a separate coding agent. It is not connected to Leanstral.

## Install

```bash
curl -fsSL https://x.ai/cli/install.sh | bash
grok --version
```

Start Grok from the repository root:

```bash
grok --trust
```

`--trust` enables the project-local safety hook. You can inspect what Grok loaded with:

```bash
grok inspect
grok mcp list
```

## Repository policy

Grok is PR-only:

1. Start from an up-to-date `main`.
2. Create a `grok/<task>` branch before editing.
3. Make and validate the change on that branch.
4. Push only that branch.
5. Open a PR targeting `main`.
6. Stop after the PR is open; a human reviews and merges it.

The policy is defined in `.grok/rules/01-pr-only.md`, backed by native deny rules in `.grok/config.toml`, and enforced at tool-call time by `.grok/hooks/pr-only-guard.py` when the project is trusted.
