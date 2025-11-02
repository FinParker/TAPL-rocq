(* v0.0.1 *)
From Stdlib Require Import List.
Import ListNotations.
From TAPL Require Import Tactics RelationProp.

Module NumberBoolean.

(* Syntax *)
Inductive tm: Type :=
  | tm_true 
  | tm_false 
  | tm_if (t1: tm) (t2: tm) (t3: tm)
  | tm_zero
  | tm_succ (t: tm)
  | tm_pred (t: tm)
  | tm_iszero (t: tm).

Inductive bv: tm -> Prop :=
  | bv_true: bv tm_true
  | bv_false: bv tm_false.

Inductive nv: tm -> Prop :=
  | nv_zero: nv tm_zero
  | nv_succ: forall t, nv t -> nv (tm_succ t).

Inductive value: tm -> Prop :=
  | v_true: value tm_true
  | v_false: value tm_false
  | v_num: forall t, nv t -> value t.

(* Evaluation *)
(* SmallStep Semantics *)
Reserved Notation "e '-->' n" (at level 90, left associativity).
Inductive step: tm -> tm -> Prop :=
  | E_IfTrue (t2 t3: tm): tm_if tm_true t2 t3 --> t2
  | E_IfFalse (t2 t3: tm): tm_if tm_false t2 t3 --> t3
  | E_If (t1 t1' t2 t3: tm): 
    (t1 --> t1') -> (tm_if t1 t2 t3 --> tm_if t1' t2 t3)
  | E_Succ (t t': tm):
    (t --> t') -> (tm_succ t --> tm_succ t')
  | E_PredZero: tm_pred tm_zero --> tm_zero
  | E_PredSucc (t: tm):
    nv t -> (tm_pred (tm_succ t) --> t)
  | E_Pred (t t': tm):
    (t --> t') -> (tm_pred t --> tm_pred t')
  | E_IszeroZero: tm_iszero tm_zero --> tm_true
  | E_IszeroSucc (t: tm):
    nv t -> (tm_iszero (tm_succ t) --> tm_false)
  | E_Iszero (t t': tm):
    (t --> t') -> (tm_iszero t --> tm_iszero t')
where "e '-->' n" := (step e n) : type_scope.

Lemma bvalue_is_normal_form: forall t,
bv t -> normal_form step t.
Proof.
  intros t Hbv. unfold normal_form.
  induction Hbv.
  - (* bv_true *) intros [t' Hstep]. inv Hstep.
  - (* bv_false *) intros [t' Hstep]. inv Hstep.
Qed.

Lemma nvalue_is_normal_form: forall t,
nv t -> normal_form step t.
Proof.
  intros t Hnv. unfold normal_form.
  induction Hnv.
  - (* nv_zero *) intros [t' Hstep]. inv Hstep.
  - (* nv_succ *) intros [t' Hstep]. inv Hstep; try (inv H).
    + (* E_PredSucc *) apply IHHnv. exists t'0. assumption.
Qed.

Lemma value_is_normal_form: forall t,
value t -> normal_form step t.
Proof.
  intros t Hval. unfold normal_form.
  destruct Hval.
  - (* v_true *) apply bvalue_is_normal_form. apply bv_true.
  - (* v_false *) apply bvalue_is_normal_form. apply bv_false.
  - (* v_num *) apply nvalue_is_normal_form. assumption.
Qed.

(* Deterministic of small step *)
(* if t-->t' /\ t-->t'' then t' = t'' *)
Theorem step_deterministic:
  deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1.
  - (* E_IfTrue *) intros. inv Hy2.
    + reflexivity.
    + inv H3.
  - (* E_IfFalse *) intros. inv Hy2.
    + reflexivity.
    + inv H3.
  - (* E_If *) intros. inv Hy2.
    + inv Hy1.
    + inv Hy1.
    + f_equal. apply IHHy1. assumption.
  - (* E_Succ *) intros. inv Hy2. f_equal. apply IHHy1. assumption.
  - (* E_PredZero *) intros. inv Hy2.
    + reflexivity.
    + inv H0.
  - (* E_PredSucc *) intros. inv Hy2.
    + reflexivity.
    + inv H1.  
Admitted.

Notation " t '-->*' t' " := (multi step t t') (at level 40).
Example test_multi_step:
  tm_if (tm_if tm_true tm_false tm_true) tm_true tm_false -->* tm_false.
Proof.
  apply multi_step with (y := tm_if tm_false tm_true tm_false).
  - apply E_If. apply E_IfTrue.
  - apply multi_step with (y := tm_false).
    + apply E_IfFalse.
    + apply multi_refl.
Qed.

(* Big Step Semantics *)
Reserved Notation "e '==>' n" (at level 90, left associativity).
Inductive tevalR: tm -> tm -> Prop :=
  | B_Val (t: tm):
      value t -> (t ==> t)
  | B_IfTrue (t1 t2 t3 t2': tm):
      (value t2) ->
      (t1 ==> tm_true) ->
      (t2 ==> t2') ->
      (tm_if t1 t2 t3 ==> t2')
  | B_IfFalse (t1 t2 t3 t3': tm):
      (value t3) ->
      (t1 ==> tm_false) ->
      (t3 ==> t3') ->
      (tm_if t1 t2 t3 ==> t3')
  | B_Succ (t t' : tm):
      (nv t') ->
      (t ==> t') ->
      (tm_succ t ==> tm_succ t')
  | B_PredZero (t: tm):
      (t ==> tm_zero) ->
      (tm_pred t ==> tm_zero)
  | B_PredSucc (t t' : tm):
      (nv t') ->
      (t ==> tm_succ t') ->
      (tm_pred t ==> t')
  | B_IszeroZero (t: tm):
      (t ==> tm_zero) ->
      (tm_iszero t ==> tm_true)
  | B_IszeroSucc (t t' : tm):
      (nv t') ->
      (t ==> tm_succ t') ->
      (tm_iszero t ==> tm_false)
where "e '==>' n" := (tevalR e n) : type_scope.

Lemma step_eval: forall t t' v,
  (value v) -> (t --> t') -> (t' ==> v) -> (t ==> v).
Proof.
  auto.
Admitted.

Theorem coinsident_eval:
  forall t t', (value t') ->
  (t -->* t') <-> (t ==> t').
Proof.
  intros t t'. split.
  - (* t -->* t' -> t ==> t' *)
    intros Hmulti. induction Hmulti.
    + (* multi_refl *) apply B_Val. assumption.
    + (* multi_step *) destruct H0 eqn:E.
      * (* E_IfTrue *) apply B_IfTrue. 
Admitted.

Lemma nf_multi_btstep :
  forall t1 t2,
  normal_form btstep t1 ->
  t1 -->* t2 ->
  t1 = t2.
Proof.
  intros t1 t2 Hnf Hmulti.
  induction Hmulti.
  - (* multi_refl *) reflexivity.
  - (* multi_step *) unfold normal_form in Hnf. exfalso. apply Hnf. exists t2. exact H.
Qed.

Theorem unique_normal_forms :
  forall t t1 t2,
  t -->* t1 ->
  normal_form btstep t1 ->
  t -->* t2 ->
  normal_form btstep t2 ->
  t1 = t2.
Proof.
  intros t t1 t2 Hmulti1 Hnf1 Hmulti2 Hnf2.
  induction Hmulti1.
  - (* multi_refl *)
    apply nf_multi_btstep with (t1 := t) (t2 := t2).
    exact Hnf1.
    exact Hmulti2.
  - (* multi_step *)

Lemma multi_btstep_If : forall t1 t1' t2 t3,
t1 -->* t1' ->
BTIf t1 t2 t3 -->* BTIf t1' t2 t3.
Proof.
  intros t1 t1' t2 t3 Hmulti.
  induction Hmulti. 
  - (* multi_refl *)
    apply multi_refl.
  - (* multi_step *)
    eapply multi_step.
    eapply ST_If. exact H. exact IHHmulti.
Qed.

Example btstep_If_true_normalizing : forall t1 t2 t3, exists t', (t1 -->* BTTrue) -> (BTIf t1 t2 t3) -->* t'.
Proof.
  intros t1 t2 t3. eexists.
  apply multi_btstep_If.
Qed.

Example btstep_If_false_normalizing : forall t1 t2 t3, exists t', (t1 -->* BTFalse) -> (BTIf t1 t2 t3) -->* t'.
Proof.
  intros t1 t2 t3. eexists.
  apply multi_btstep_If.
Qed.

Theorem btstep_normarlizing:
  forall t: bterm, exists t',
  (t -->* t') /\ normal_form btstep t'.
Proof.
  intros t.
  induction t.
  - exists BTTrue. split.
    + apply multi_refl.
    + unfold normal_form. intros [t' Hstep]. inv Hstep.
  - exists BTFalse. split.
    + apply multi_refl.
    + unfold normal_form. intros [t' Hstep]. inv Hstep.
  - destruct IHt1 as [t1' [Hmulti1 Hnf1]].
    destruct IHt2 as [t2' [Hmulti2 Hnf2]].
    destruct IHt3 as [t3' [Hmulti3 Hnf3]].
    destruct (nf_same_as_value t1') as [Hval1 _].
    destruct (nf_same_as_value t2') as [Hval2 _].
    destruct (nf_same_as_value t3') as [Hval3 _].
    apply Hval1 in Hnf1. apply Hval2 in Hnf2. apply Hval3 in Hnf3.
    clear Hval1 Hval2 Hval3.
    inv Hnf1; inv Hnf2; inv Hnf3.
    + (* t1' = BTTrue *) eexists. split.
Admitted.

End NumberBoolean.



