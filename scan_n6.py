# N6 zero-trust scan for A046156 : forbidden tokens on the
# publishable .lean files of this repository.
# Comments (nested /- -/ blocks and line --) and string literals
# are stripped by a Python STATE MACHINE - never a regex - then
# each surviving code line is searched for the forbidden tokens.
# Exit code 0 = zero hit. Usage : python scan_n6.py

import re
import sys

FILES = [
    "A046253Defs.lean",
    "A014080Defs.lean",
    "A046156Defs.lean",
    "A046156Basin0.lean",
    "A046156Basin1.lean",
    "A046156.lean",
    "Spec_A046156.lean",
    "Check_Spec_A046156.lean",
    "Check_AntiVacuite_A046156.lean",
]

# Forbidden tokens (N6). \baxiom\b does NOT match "axioms", so the
# N4 audit command '#print axioms' is not a hit.
TOKENS = [
    "sorry", "admit", "axiom", "unsafe", "implemented_by", "extern",
    "csimp", "native_decide", "bv_decide", "initialize",
    "builtin_initialize", "run_meta", "notation", "syntax", "macro",
    "macro_rules", "elab_rules",
]
PATTERNS = [(t, re.compile(r"\b" + re.escape(t) + r"\b")) for t in TOKENS]
IO_PAT = re.compile(r"\bIO\.")


def strip_comments(src):
    """Replace comments and strings by spaces, keeping newlines
    (line numbers preserved 1:1).
    States : NORMAL / IN_LINE(--) / IN_BLOCK(depth, nested /- -/)
    / IN_STR("...")."""
    out = []
    i = 0
    n = len(src)
    depth = 0        # >0 : inside a /- -/ block (nesting counted)
    in_line = False  # inside a -- comment
    in_str = False   # inside a "..." literal
    while i < n:
        c = src[i]
        if in_str:
            if c == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append("\n" if src[i + 1] == "\n" else " ")
                i += 2
                continue
            if c == '"':
                in_str = False
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if depth > 0:
            if src.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
                continue
            out.append("\n" if c == "\n" else " ")
            i += 1
            continue
        if in_line:
            if c == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue
        # NORMAL state : test /- BEFORE -- (/-- starts with /-)
        if src.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
            continue
        if src.startswith("--", i):
            in_line = True
            out.append("  ")
            i += 2
            continue
        if c == '"':
            in_str = True
            out.append(" ")
            i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out), depth, in_str


def main():
    total_hits = 0
    for path in FILES:
        try:
            with open(path, "r", encoding="utf-8") as f:
                src = f.read()
        except OSError as e:
            print("ERREUR lecture %s : %s" % (path, e))
            total_hits += 1
            continue
        stripped, depth, in_str = strip_comments(src)
        if depth != 0 or in_str:
            print("%s : AVERTISSEMENT bloc non ferme (depth=%d, str=%s)"
                  % (path, depth, in_str))
        hits = []
        for ln, line in enumerate(stripped.split("\n"), 1):
            for tok, pat in PATTERNS:
                if pat.search(line):
                    hits.append((ln, tok))
            if IO_PAT.search(line):
                hits.append((ln, "IO."))
        if hits:
            total_hits += len(hits)
            for ln, tok in hits:
                print("%s:%d : TOKEN INTERDIT '%s'" % (path, ln, tok))
        else:
            print("%s : 0 hit" % path)
    print("TOTAL : %d hit(s)" % total_hits)
    sys.exit(1 if total_hits else 0)


if __name__ == "__main__":
    main()
