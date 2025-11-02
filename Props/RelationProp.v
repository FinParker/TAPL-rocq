(* relation *)
Definition relation (X Y: Type) := X -> Y -> Prop.

(* deterministic on relation *)
Definition deterministic {X Y: Type} (R: relation X Y): Prop :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Definition normal_form {X Y : Type}
(R : relation X Y) (t : X) : Prop :=
~ exists t', R t t'.

(* multi_step on Self Relation *)
Inductive multi {X: Type} (R : relation X X):relation X X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X), R x y -> multi R y z -> multi R x z.

Theorem multi_R : forall (X : Type) (R : relation X X) (x y : X),
R x y -> (multi R) x y.
Proof.
  intros X R x y H.
  apply multi_step with (y := y).
  - exact H.
  - apply multi_refl.
Qed.

Theorem multi_trans :
  forall (X : Type) (R : relation X X) (x y z : X),
  (multi R) x y -> (multi R) y z -> (multi R) x z.
Proof.
  intros X R x y z Hxy Hyz.
  induction Hxy.
  - exact Hyz.
  - apply IHHxy in Hyz.
    apply multi_step with (y := y).
    + exact H.
    + exact Hyz.
Qed.