#!/usr/bin/env python3
"""Grok Build PreToolUse guard for the repository's PR-only workflow."""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys

PROTECTED = {"main", "master"}


def _deny(reason: str) -> None:
    payload = {
        "decision": "deny",
        "reason": reason,
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        },
    }
    print(json.dumps(payload))
    print(reason, file=sys.stderr)
    raise SystemExit(2)


def _current_branch(cwd: str) -> str:
    try:
        proc = subprocess.run(
            ["git", "-C", cwd, "branch", "--show-current"],
            check=False,
            capture_output=True,
            text=True,
            timeout=2,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    return proc.stdout.strip() if proc.returncode == 0 else ""


def _field(obj: object, *names: str) -> object | None:
    if not isinstance(obj, dict):
        return None
    for name in names:
        if name in obj:
            return obj[name]
    return None


def _is_edit_tool(tool: str) -> bool:
    return tool in {"search_replace", "Edit", "Write", "edit", "write_file"}


def _has_git_subcommand(command: str, subcommand: str) -> bool:
    # Covers ordinary `git <subcommand>` plus common `git -C path <subcommand>` use.
    pattern = rf"\bgit(?:\s+-C\s+\S+)?\s+{re.escape(subcommand)}\b"
    return re.search(pattern, command) is not None


def _push_targets_protected(command: str) -> bool:
    if not _has_git_subcommand(command, "push"):
        return False
    if re.search(r"\bgit(?:\s+-C\s+\S+)?\s+push\b[^\n;&|]*(?:--all|--mirror)\b", command):
        return True
    # Protect explicit branch/refspec destinations such as `origin main`,
    # `HEAD:main`, and `HEAD:refs/heads/main` without rejecting branch names
    # that merely contain the word "main".
    return re.search(
        r"\bgit(?:\s+-C\s+\S+)?\s+push\b[^\n;&|]*(?:^|[\s:])(?:refs/heads/)?(?:main|master)(?=$|[\s;&|])",
        command,
    ) is not None


def main() -> None:
    try:
        event = json.load(sys.stdin)
    except (OSError, ValueError):
        return

    tool = _field(event, "toolName", "tool_name")
    tool = tool if isinstance(tool, str) else ""
    tool_input = _field(event, "toolInput", "tool_input")
    tool_input = tool_input if isinstance(tool_input, dict) else {}
    cwd = _field(event, "cwd", "workspaceRoot", "workspace_root")
    cwd = cwd if isinstance(cwd, str) and cwd else os.getcwd()
    branch = _current_branch(cwd)

    if _is_edit_tool(tool) and branch in PROTECTED:
        _deny(
            f"PR-only policy: file edits are blocked on {branch}. "
            "Create a `grok/<task>` branch first, then make the change and open a PR."
        )

    command = tool_input.get("command")
    if not isinstance(command, str) or not command:
        return

    if re.search(r"\bgh\s+pr\s+merge\b", command):
        _deny("PR-only policy: Grok may open or update PRs, but a human must merge them.")

    if re.search(r"\bgh\s+api\b[^\n;&|]*(?:-X|--method)\s+(?:PUT|POST|PATCH|DELETE)\b[^\n;&|]*/(?:merge|merges)(?:\s|$)", command, re.I):
        _deny("PR-only policy: merge operations through the GitHub API are blocked.")

    if _push_targets_protected(command):
        _deny("PR-only policy: direct pushes to main/master (including refspec pushes) are blocked.")

    if branch in PROTECTED:
        if _has_git_subcommand(command, "push"):
            _deny(f"PR-only policy: pushing while checked out on {branch} is blocked. Create a `grok/<task>` branch first.")
        if any(_has_git_subcommand(command, sub) for sub in ("commit", "merge", "rebase", "cherry-pick", "revert")):
            _deny(f"PR-only policy: mutating git history on {branch} is blocked. Work on a `grok/<task>` branch.")


if __name__ == "__main__":
    main()
