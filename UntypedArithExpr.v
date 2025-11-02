(* v0.0.1 *)
From Stdlib Require Import List.
Import ListNotations.
From TAPL Require Import Tactics RelationProp.

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

Check multi_btstep_ind.

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
    apply IHHmulti1.
    + exact Hnf1. 
    + inv Hmulti2.
      * (* multi_refl *) unfold normal_form in Hnf2. exfalso. apply Hnf2. exists t0. exact H.
      * (* multi_step *) assert(Hder: t0=t5).
        { eapply btstep_deterministic. 
          - exact H.
          - exact H0. }
        subst. assumption.
Qed.

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
      
End Boolean.



