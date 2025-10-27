From TAPL Require Import Tactics.

(* solve_by_inverts *)
Inductive even : nat -> Prop :=
| even_O : even 0
| even_SS : forall n, even n -> even (S (S n)).

