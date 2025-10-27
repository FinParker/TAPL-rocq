From Stdlib Require Import List.
Import ListNotations.
From TAPL Require Import Tactics.

(* relation *)
Definition relation (X Y: Type) := X -> Y -> Prop.

(* deterministic on relation *)
Definition deterministic {X Y: Type} (R: relation X Y): Prop :=
  forall x y1 y2, R x y1 -> R x y2 -> y1 = y2.

Definition normal_form {X Y : Type}
(R : relation X Y) (t : X) : Prop :=
~ exists t', R t t'.

(* multi_step on relation *)
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

Module Boolean.

(* Syntax *)
Inductive bterm: Type :=
  | BTTrue 
  | BTFalse 
  | BTIf (t1: bterm) (t2: bterm) (t3: bterm).

Inductive bvalue: Type :=
  | BTrue 
  | BFalse.

(* BigStep *)
(* Evaluation *)
Fixpoint bteval (t: bterm): bvalue :=
  match t with 
  | BTTrue => BTrue
  | BTFalse => BFalse
  | BTIf t1 t2 t3 =>
      match bteval t1 with
      | BTrue => bteval t2
      | BFalse => bteval t3
      end
  end.

Reserved Notation "t '==>' v" (at level 90, left associativity).

Inductive btevalR: bterm -> bvalue -> Prop :=
  | E_True: BTTrue ==> BTrue
  | E_False: BTFalse ==> BFalse
  | E_IfTrue: forall t2 t3 v2,
      (t2 ==> v2) ->
      (BTIf BTTrue t2 t3) ==> v2
  | E_IfFalse: forall t2 t3 v3,
      (t3 ==> v3) ->
      (BTIf BTFalse t2 t3) ==> v3
where "t '==>' v" := (btevalR t v).

Theorem btevalR_deterministic:
  deterministic btevalR.
Proof.
  intros t v1 v2 H1 H2.
  generalize dependent v2.
  induction H1.
  - intros v2 H2. inversion H2. reflexivity.
  - intros v2 H2. inversion H2. reflexivity.
  - intros v0 H0. inversion H0. subst. apply IHbtevalR. exact H4.
  - intros v0 H0. inversion H0. subst. apply IHbtevalR. exact H4.
Qed.

Example test_bevalR1:
  btevalR (BTIf BTTrue BTFalse BTTrue) BFalse.
Proof. apply E_IfTrue. apply E_False. Qed.

Example test_bevalR2:
  btevalR (BTIf BTFalse BTTrue BTFalse) BFalse.
Proof. apply E_IfFalse. apply E_False. Qed.


(* SmallStep *)
Reserved Notation "e '-->' n" (at level 90, left associativity).
Inductive btstep: bterm -> bterm -> Prop :=
  | ST_IfTrue (t2 t3: bterm): BTIf BTTrue t2 t3 --> t2
  | ST_IfFalse (t2 t3: bterm): BTIf BTFalse t2 t3 --> t3
  | ST_If (t1 t1' t2 t3: bterm): 
    (t1 --> t1') -> (BTIf t1 t2 t3 --> BTIf t1' t2 t3)
where "e '-->' n" := (btstep e n) : type_scope.

(* Deterministic of small step *)
(* if t-->t' /\ t-->t'' then t' = t'' *)
Theorem btstep_deterministic:
  deterministic btstep.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1.
  - (* ST_IfTrue *) intros. inv Hy2.
    + reflexivity.
    + inv H3.
  - (* ST_IfFalse *) intros. inv Hy2.
    + reflexivity.
    + inv H3.
  - (* ST_If *) intros. inv Hy2. 
    + inv Hy1.
    + inv Hy1.
    + f_equal. apply IHHy1. exact H3.
Qed.

Inductive value_b: bterm -> Prop :=
  | v_btrue: value_b BTTrue
  | v_bfalse: value_b BTFalse.

Theorem strong_progress : forall t,
value_b t \/ (exists t', t --> t').
Proof.
  intros t. induction t.
  - left. apply v_btrue.
  - left. apply v_bfalse.
  - right. destruct t1. 
    + exists t2. apply ST_IfTrue.
    + exists t3. apply ST_IfFalse.
    + destruct IHt1 as [Hval | Hstep].
      * inversion Hval.
      * destruct Hstep as [t1' H]. exists (BTIf t1' t2 t3). apply ST_If. apply H.
Qed.

Lemma value_b_is_nf : forall v, value_b v -> normal_form btstep v.
Proof.
  intros v Hval. unfold normal_form. intros [t' Hstep]. inv Hval; inv Hstep.
Qed.

Lemma nf_is_value_b : forall t, normal_form btstep t -> value_b t.
Proof.
  intros t Hnf. destruct (strong_progress t) as [Hval | Hstep].
  - exact Hval.
  - unfold normal_form in Hnf. contradiction.
Qed.
  
Corollary nf_same_as_value : forall t,
normal_form btstep t <-> value_b t.
Proof.
  split; intros H.
  - apply nf_is_value_b. exact H.
  - apply value_b_is_nf. exact H.
Qed.

Inductive multi_btstep: bterm -> bterm -> Prop :=
  | multi_refl: forall t, multi_btstep t t
  | multi_step: forall t1 t2 t3,
      (t1 --> t2) ->
      (multi_btstep t2 t3) ->
      (multi_btstep t1 t3).

Definition multi_btstep' := multi btstep.

Notation "t '-->*' n" := (multi_btstep t n) (at level 90, left associativity).

Example test_multi_btstep:
  BTIf (BTIf BTTrue BTFalse BTTrue) BTTrue BTFalse -->* BTFalse.
Proof.
  apply multi_step with (t2 := BTIf BTFalse BTTrue BTFalse).
  - assert (BTIf BTTrue BTFalse BTTrue --> BTFalse).
    + apply ST_IfTrue.
    + apply ST_If. exact H.
  - apply multi_step with (t2 := BTFalse).
    + apply ST_IfFalse.
    + apply multi_refl.
Qed.

End Boolean.

Inductive constant: Type:=
  | CTrue 
  | CFalse 
  | CZero.

Inductive term: Type:=
  | TTrue 
  | TFalse 
  | TIf (t1: term) (t2: term) (t3: term)
  | TZero
  | TSucc (t: term)
  | TPred (t: term)
  | TIsZero (t: term).

Fixpoint Consts (t: term): list constant :=
  match t with
  | TTrue => [CTrue]
  | TFalse => [CFalse]
  | TIf t1 t2 t3 => Consts t1 ++ Consts t2 ++ Consts t3
  | TZero => [CZero]
  | TSucc t1 => Consts t1
  | TPred t1 => Consts t1
  | TIsZero t1 => Consts t1
  end.

Example test_Consts:
  Consts (TIf TTrue (TSucc TZero) (TPred (TSucc TZero)))
  = [CTrue; CZero; CZero].
Proof. reflexivity. Qed.

Fixpoint teval (t: term): term :=
  match t with
  | TTrue => TTrue
  | TFalse => TFalse
  | TIf t1 t2 t3 =>
      match teval t1 with
      | TTrue => teval t2
      | TFalse => teval t3
      | _ => TIf (teval t1) (teval t2) (teval t3)
      end
  | TZero => TZero
  | TSucc t1 => TSucc (teval t1)
  | TPred t1 =>
      match teval t1 with
      | TZero => TZero
      | TSucc nv1 => nv1
      | _ => TPred (teval t1)
      end
  | TIsZero t1 =>
      match teval t1 with
      | TZero => TTrue
      | TSucc nv1 => TFalse
      | _ => TIsZero (teval t1)
      end
  end.

Example test_teval1:
  teval (TIf TTrue (TSucc TZero) (TPred (TSucc TZero))) = TSucc TZero.
Proof. reflexivity. Qed.



