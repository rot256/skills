---
name: codex
description: Invoke Codex CLI as a sub-agent for code tasks. Useful for second opinions, parallel exploration, or offloading isolated subtasks.
version: 1.0.0
---

## Basic invocation

Pipe the prompt on stdin; use `exec` for non-interactive output:

```bash
echo "<prompt>" | codex exec --skip-git-repo-check
```

`--skip-git-repo-check` lets it run outside a git repo. Drop it when invoking inside a repo where codex should see git context.

## Useful flags

- `-m <model>` — override model (e.g. `gpt-5.1-codex`).
- `-C <dir>` — set working directory.
- `-s read-only` — sandbox mode (`read-only`, `workspace-write`, `danger-full-access`).
- `--dangerously-bypass-approvals-and-sandbox` — fully autonomous; only inside an already-sandboxed env.
- `-i <file>` — attach image(s).
- `--output-schema <file.json>` — constrain final response to a JSON schema.

## Patterns

Heredoc for multi-line prompts:

```bash
codex exec --skip-git-repo-check <<'EOF'
Review foo.rs for race conditions.
Report findings as a bullet list.
EOF
```

From a file:

```bash
codex exec --skip-git-repo-check < prompt.txt
```

Inside a repo, read-only second opinion:

```bash
echo "Audit auth.rs for input validation gaps." | codex exec -s read-only
```

## Notes

- Output goes to stdout; redirect or pipe as needed.
- Long runs: launch via Bash `run_in_background` and read output later.
- Prompt is self-contained — codex has no access to this conversation.
