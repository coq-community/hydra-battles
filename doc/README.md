# README : doc with alectryon

  We describe the scripts for building `hydra.pdf`
  
  
## Json movies

   - Json movies are made in [movies](./movies/) by `make all`
   - The movies are called `<name>.io.json`.
   
   
## From json to latex

In [cutting-table](./cutting-table/) 

```
  python3 jsonToLatex.py ../movies/<file-name>.io.json > ../<file-name>.tex
```

### Examples:

 ```
  python3 jsonToLatex.py ../movies/Issue_Program.io.json > ../program_issue.tex
 ```
   
## pdf generation

In the [doc](.) directory,
the files obtained with `jsonToLatex.py` are inserted in  a global latex file as `alectryon` environments.

   - [hydras.tex](./hydras.tex) : the big document
   - [Program_issue2.tex](./Program_issue2.tex) : A wrapper for [program_issue.tex](./program_issue.tex) .
   
   
### known issues 

```
  lualatex --shell-escape Program_issue2.tex
```

Latex error message due to the underscore in `Heq_ab`
If we resume (by typing `return`) the compilation, a math mode is inserted and `a` is converted into an indice.
