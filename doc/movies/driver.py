#!/usr/bin/env python3
import re
from collections import namedtuple
from itertools import zip_longest, groupby
from pathlib import Path

from alectryon import cli, transforms
from alectryon.latex import ASSETS

def pair(*iterable):
    iters = [iter(iterable)] * 2
    return zip_longest(*iters, fillvalue=None)

Snippet = namedtuple("Snippet", "name io_annots s")

SNIPPET_DELIM_RE = re.compile(r"""
  [(][*]\s*
    (?P<kind>begin|end)\s+ snippet\s+ (?P<name>[^ ]+)
    (?:[:][:]\s+ (?P<io_flags>.*?))?
  \s*[*][)]
""", re.VERBOSE)

SNIPPET_IO_FLAGS_RE = re.compile(r"""
  (?:\n\s*)? # As if flags were at end of last non-empty line
  [(][*][|]\s*
    (?:..\s+ coq::\s+ (.*?))?
  \s*[|]?[*][)]
""", re.VERBOSE)

class NoSnippets(Exception):
    pass

def check_snippet_boundaries(before, after):
    assert before
    if not after:
        MSG = "Missing final ``(* end snippet {} *)`` delimiter"
        raise ValueError(MSG.format(before.group("before_name")))
    if before.group("kind") != "begin":
        raise ValueError("Unexpected delimiter ``{}``".format(before.group()))
    if after.group("kind") != "end":
        raise ValueError("Unexpected delimiter ``{}``".format(before.group()))
    if before.group("name") != after.group("name"):
        MSG = "Mismatched delimiters: (* begin snippet {} *) and (* end snippet {} *)"
        raise ValueError(MSG.format(before.group("name"), after.group("name")))

def split_snippet(name, io_flags, contents):
    for substr, subsnippet in pair(io_flags, *SNIPPET_IO_FLAGS_RE.split(contents)):
        io_annots = transforms.read_all_io_flags(substr or "")
        yield Snippet(name, io_annots, subsnippet)

def parse_coq_snippets(coq, ctx):
    end, chunks = 0, []
    for before, after in pair(*SNIPPET_DELIM_RE.finditer(coq)):
        check_snippet_boundaries(before, after)
        if before.start() > end:
            chunks.append(coq[end:before.start()])
        name, io_flags = before.group("name", "io_flags")
        chunks.extend(split_snippet(name, io_flags, coq[before.end():after.start()]))
        end = after.end()
    if not chunks:
        raise NoSnippets()
    if end < len(coq):
        chunks.append(coq[end:])
    ctx["chunks"] = chunks
    return [(c.s if isinstance(c, Snippet) else c) for c in chunks]

def _prepare_snippets(annotated, chunks):
    for chunk, frs in zip(chunks, annotated):
        if isinstance(chunk, Snippet):
            frs = transforms.inherit_io_annots(frs, chunk.io_annots)
            yield chunk, list(frs)

def prepare_snippets(annotated, chunks, ctx):
    ctx["snippets"], annotated = zip(*_prepare_snippets(annotated, chunks))
    return annotated

def drop_hidden(annotated, snippets):
    for snippet, frs in zip(snippets, annotated):
        yield [] if transforms.all_hidden(frs, snippet.io_annots) else frs

def _group_subsnippets(annotated, snippets):
    for name, group in groupby(zip(snippets, annotated), lambda p: p[0].name):
        frs = transforms.coalesce_text(fr for _, frs in group for fr in frs)
        yield name, list(frs)

def group_subsnippets(annotated, snippets, ctx):
    ctx["names"], annotated = zip(*_group_subsnippets(annotated, snippets))
    return annotated

def trim_annotated(annotated):
    for frs in annotated:
        yield transforms.strip_text(frs)

def write_snippets(latex, names, fpath, output_directory):
    for name, ltx in zip(names, latex):
        target = (Path(output_directory) / name).with_suffix(".tex")
        print(">> {} → {}".format(fpath, target))
        target.write_text(ltx.render())

def record_assets(v, assets):
    cli._record_assets(assets, ASSETS.PATH, ASSETS.ALECTRYON_STY + ASSETS.PYGMENTS_STY)
    return v

cli.PIPELINES['coq']['snippets-hydras'] = (
    cli.read_plain, parse_coq_snippets, cli.annotate_chunks, prepare_snippets,
    # Transforms applied twice: once to prepare comments for drop_hidden, once
    # to add comments and newlines to sentences after grouping subsnippets.
    cli.apply_transforms, drop_hidden, group_subsnippets,
    cli.apply_transforms, trim_annotated, cli.gen_latex_snippets, write_snippets
)

cli.PIPELINES['coq']['assets'] = (record_assets, cli.copy_assets)

if __name__ == '__main__':
    try:
        cli.main()
    except NoSnippets:
        pass
