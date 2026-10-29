#!/usr/bin/env python3
"""Extract declaration statements from the Lean sources, and check that the
```lean blocks of docs/report.md are verbatim copies of them.

  scripts/statements.py show NAME...     print the statement(s)
  scripts/statements.py check            verify docs/report.md

A statement is the text from the declaration keyword (`theorem`, `def`,
`structure`, ...) through the end of its signature: up to `:= by`, `:=`
at the end of a line, or `where`. Only declarations under Linera/ are
indexed, by their final name component or any dotted suffix. The check
accepts any ```lean block that is, after whitespace normalisation, a
verbatim excerpt of some source file (a statement, or a structure with
its fields); blank lines split a block into independently checked pieces.
"""
import re, sys, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
KEYWORDS = r"(?:theorem|lemma|def|structure|inductive|class|abbrev|instance|noncomputable def)"
DECL = re.compile(r"^(" + KEYWORDS + r")\s+([A-Za-z_][\w'.₀-₉]*)", re.M)

def statements():
    index = {}
    for path in sorted((ROOT / "Linera").rglob("*.lean")):
        text = path.read_text()
        lines = text.split("\n")
        for i, line in enumerate(lines):
            m = DECL.match(line)
            if not m:
                continue
            name = m.group(2)
            block = []
            for j in range(i, len(lines)):
                l = lines[j]
                block.append(l)
                stripped = l.rstrip()
                if stripped.endswith(":= by") or stripped.endswith(":=") or stripped.endswith(" where") \
                        or stripped.endswith(":= rfl") or re.search(r":=\s*\S", stripped) and not stripped.endswith("where"):
                    break
            stmt = "\n".join(block)
            stmt = re.sub(r"\s*:=\s*(by)?\s*$", "", stmt)
            stmt = re.sub(r"\s*where\s*$", "", stmt)
            index.setdefault(name, []).append((path.relative_to(ROOT), stmt))
    return index

def lookup(index, name):
    if name in index:
        return index[name]
    hits = [v for k, v in index.items() if k.endswith("." + name)]
    return [h for hs in hits for h in hs]

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

def main():
    index = statements()
    if len(sys.argv) >= 2 and sys.argv[1] == "show":
        for name in sys.argv[2:]:
            for path, stmt in lookup(index, name):
                print(f"-- {path}\n{stmt}\n")
        return
    if len(sys.argv) >= 2 and sys.argv[1] == "check":
        report = (ROOT / "docs" / "report.md").read_text()
        blocks = re.findall(r"```lean\n(.*?)```", report, re.S)
        sources = [norm(p.read_text()) for p in (ROOT / "Linera").rglob("*.lean")]
        bad = 0
        for b in blocks:
            for piece in re.split(r"\n\s*\n", b.strip()):
                if not any(norm(piece) in src for src in sources):
                    bad += 1
                    print("NOT VERBATIM:\n" + piece + "\n")
        print(f"{len(blocks)} blocks checked, {bad} not verbatim")
        sys.exit(1 if bad else 0)
    print(__doc__)

if __name__ == "__main__":
    main()
