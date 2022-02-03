From LibHyps Require Export LibHyps.

Tactic Notation (at level 4) tactic4(Tac) "/" "dr" := Tac ; {< fun h
=> try revert dependent h }.
Tactic Notation (at level 4) tactic4(Tac) "/" "r?" :=
  Tac ; {< fun h  => try revert h }.


(*  move to experimental file (not to export *)


