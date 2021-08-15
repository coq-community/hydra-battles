# Snippets coq+rst

The script `extract_snippets.py` extract snippets block in coq+rst files.\
This script has been tested with Python 3.7 or above and uses [Alectryon](https://github.com/cpitclaudel/alectryon),
to transform "coq+rst" to "latex" file.

## Requirements
Alectryon >=1.3

You can install with command:
```shell
pip install -r requirements.txt
```

## Snippet Block
A snippet blocs is a block formed by this template:
```coq
(* begin snippet NAME *)
    ...
(* end snippet NAME *)
```

## Script

The script take coq file, extract snippets blocks, and make directory with name of coq file. 
Make latex files with name of snippets, in directory.
Now you can include your snippet file in your main latex file (using `\input{foo/snippet1}` in LaTeX).

## Usage
```shell
$ python extract_snippets.py foo.v
$ ls -l foo/
snippet1.tex  snippet2.tex
```

For more informations do `python extract_snippets -h`


## Makefile
Command `make file.v` extracts `.v` found in `theories/oridinals` and makes a latex file. \
And extract snippets and in directory snippets.
