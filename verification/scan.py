#!/usr/bin/env python3
"""Find unfinished-proof tokens in every Git-visible project Lean source.

This is a source census, not a replacement for Lean's kernel or axiom check.
Comments, strings and character literals are ignored. Build products are
excluded by the repository's .gitignore, not a source-file exclusion list.
"""

from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


def code_only(source: str) -> str:
    chars = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source.startswith("/-", i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError("unterminated block comment")
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == "\\":
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            else:
                raise ValueError("unterminated string")
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'.")):
            match = re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", source[i:])
            if match:
                i += len(match.group())
            else:
                i += 1
                continue
        elif source[i] == "\u00ab":
            end = source.find("\u00bb", i + 1)
            if end < 0:
                raise ValueError("unterminated quoted identifier")
            i = end + 1
        else:
            i += 1
            continue
        chars[start:i] = ("\n" if c == "\n" else " " for c in source[start:i])
    return "".join(chars)


def axiom_declarations(clean: str) -> list[dict]:
    declarations = []
    for keyword in re.finditer(r"(?<![\w'.])axiom(?![\w'.])", clean):
        name = re.match(r"\s+([^\s{:(]+)", clean[keyword.end():])
        declarations.append({"name": name.group(1) if name else None, "offset": keyword.start()})
    return declarations


def main() -> int:
    root = Path(__file__).resolve().parents[1]
    names = subprocess.check_output(
        ["git", "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--", "*.lean"],
        cwd=root,
    ).decode().split("\0")
    files = sorted(set(filter(None, names)))
    if not files:
        raise RuntimeError("No Lean sources found")
    hits = []
    axioms = []
    for name in files:
        file = root / name
        if file.is_symlink():
            raise RuntimeError(f"Lean source must not be a symlink: {name}")
        source = file.read_text(encoding="utf-8")
        clean = code_only(source)
        for match in re.finditer(r"(?<![\w'.])(?:sorry|admit)(?![\w'.])", clean):
            start = match.start()
            hits.append({"file": name, "line": clean.count("\n", 0, start) + 1,
                         "column": start - clean.rfind("\n", 0, start), "token": match.group()})
        for declaration in axiom_declarations(clean):
            axioms.append({"file": name, "name": declaration["name"],
                           "line": clean.count("\n", 0, declaration["offset"]) + 1})
    boundary_ok = not axioms
    print(json.dumps({"lean_files": len(files), "unfinished_tokens": len(hits), "occurrences": hits,
                      "project_axioms": axioms, "axiom_free_boundary": boundary_ok}, indent=2))
    return 1 if hits or not boundary_ok else 0


if __name__ == "__main__":
    raise SystemExit(main())
