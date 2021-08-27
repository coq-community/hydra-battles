#!/usr/bin/env python3
from os import getenv, sep
from pathlib import Path

root, snippets = Path(getenv("coq_root")), Path(getenv("snippets_root"))

RULE = """
{}: {}
	$(alectryon) "$<"
	@touch "$@"
"""

targets = []

for coqfile in root.glob('**/*.v'):
    pth = coqfile.relative_to(root)
    target = str(snippets / pth.stem) + sep
    targets.append(target)
    print(RULE.format(target, coqfile))

print("targets := {}".format(" ".join(str(t) for t in targets)))
