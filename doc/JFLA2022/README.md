# Files to upload

## tex files

- paper.tex

## bibliography files

- paper.bbl

## snippets

- `E0_Ex42.tex`
- `Schutte_Ex42c.tex`
- `Hprime_HprimeDef.tex`
- `Schutte_Ex42d.tex`
- `Schutte_Ex42a.tex`
- `Schutte_Ex42b.tex`
- `Pow_evalPow17LetIn.tex`
- `Schutte_Ex42e.tex`

## packages

- pygments.sty
- alectryon.sty
- easychair.tex

# Changes

## Requested by reviewers

- explain the motivation of a coq_makefile workflow

- Clarify the new mathematical stuff (Section 2) (cf. the third referee's remarks).

## Nice to have

- clarify contribution to include:
  - extensions on top of Alectryon for snippet processing and inclusion in LaTeX documents
  - tooling and workflow based on Dune+Docker+Nix+GitHub to continually test and deploy code+book

- link to book files more clearly (ideally not the continuously deployed version, which will change)



- Add some remarks about the "Gaia diamond": 
      -  Both libraries are quite big (even if we consider only the  `ssete9` module and its descendents)
      -  Many lemmas are proved in both libraries
      -  Many other lemmas belong to only one library
      -  So, it's highly desirable to give the Coq user interested in ordinals a way to search, get and apply the appropriate theorem, whichever the Coq dialect it was proven.
      - It won't be trivial, but it's a motivating goal. The fact that both libraries have a common ancestor will help a lot.
      


- Add a mention to the referees in the acknowledgments?

- The last paragraph by the second referee is very interesting. Should we answer in the paper? 