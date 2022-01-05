#!/usr/bin/env python3
from os import getenv
from pathlib import Path

RULE = """
{}: $(coq_root)/{}
	$(alectryon) "$<"
	@touch "$@"
"""

targets = []
root = Path(getenv("coq_root"))

for coqfile in root.glob('**/*.v'):
    relpath = coqfile.relative_to(root)
    target = "$(snippets_root)/{}/".format(relpath.stem)
    targets.append(target)
    print(RULE.format(target, relpath))

print("targets := {}".format(" ".join(str(t) for t in targets)))
