(** * Types: Type Systems *)

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Arith.
From TAPL.plf Require Import Maps.
From TAPL.Props Require Import RelationProp.
From TAPL.Tactics Require Import Tactics.
Set Default Goal Selector "!".

Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic Expressions *)

(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
*)
(** And here it is formally: *)
Module TM.

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
Local Open Scope tm_scope.

(** _Values_ are [true], [false], and numeric values... *)
(* Check true.
Check <{true}>. *)
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue <{ true }>
  | bv_false : bvalue <{ false }>.

Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_IsZero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IsZeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_IsZero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep]
    chapter fails here.  That is, there are terms that are normal
    forms (they can't take a step) but not values (they are not
    included in our definition of possible "results of reduction").

    Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(** **** Exercise: 2 stars, standard (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists <{ pred true }>. split.
  - unfold step_normal_form. intros [t' Hstep].
    inv Hstep. inv H0.
  - unfold not. intros [Hbv | Hnv].
    + inv Hbv.
    + inv Hnv.
Qed.
(** [] *)

(** However, although values and normal forms are _not_ the same in this
    language, the set of values is a subset of the set of normal forms.

    This is important because it shows we did not accidentally define
    things so that some value could still take a step. *)

(** **** Exercise: 3 stars, standard (value_is_nf) *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.)

    [] *)

(** **** Exercise: 3 stars, standard, optional (step_deterministic)

    Use [value_is_nf] to show that the [step] relation is also
    deterministic. *)

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Declare Custom Entry ty.
Notation "'Nat'" := Nat (in custom ty).
Notation "'Bool'" := Bool (in custom ty).
Notation "x" := x (in custom ty, x global).

Reserved Notation "<{ '|--' t '\in' T }>"
            (at level 0, t custom tm, T custom ty).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       <{ |-- true \in Bool }>
  | T_False :
       <{ |-- false \in Bool }>
  | T_If : forall t1 t2 t3 T,
       <{ |-- t1 \in Bool }> ->
       <{ |-- t2 \in T }> ->
       <{ |-- t3 \in T }> ->
       <{ |-- if t1 then t2 else t3 \in T }>
  | T_0 :
       <{ |-- 0 \in Nat }>
  | T_Succ : forall t1,
       <{ |-- t1 \in Nat }> ->
       <{ |-- succ t1 \in Nat }>
  | T_Pred : forall t1,
       <{ |-- t1 \in Nat }> ->
       <{ |-- pred t1 \in Nat }>
  | T_Iszero : forall t1,
       <{ |-- t1 \in Nat }> ->
       <{ |-- iszero t1 \in Bool }>

where "<{ '|--' t '\in' T }>" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  <{ |-- if false then 0 else (succ 0) \in Nat }>.
Proof.
  (* This can be used only by auto *)
  apply T_If.
  - apply T_False.
  - apply T_0.
  - apply T_Succ. apply T_0.
Qed.

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ <{ |-- if false then 0 else true \in Bool }>.
Proof.
  intros Contra. solve_by_inverts 2.  Qed.

(** **** Exercise: 1 star, standard, optional (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : forall t,
  <{ |--  succ t \in Nat }> ->
  <{ |-- t \in Nat }>.
Proof.
  intros.
  inv H.
  assumption.
Qed.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental fact that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  <{ |-- t \in Bool }> -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  <{ |-- t \in Nat }> -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.

    The first is that well-typed normal forms are not stuck -- or
    conversely, if a term is well typed, then either it is a value or it
    can take at least one step.  We call this _progress_. *)

(** **** Exercise: 3 stars, standard (finish_progress) *)
Theorem progress : forall t T,
  <{ |-- t \in T }> ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_True and
     T_False, are eliminated immediately by auto *)
  - (* T_If *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists <{ if t1' then t2 else t3 }>. auto.
  - (* T_Zero *)
    destruct IHHT.
    + (* t is a value *)
      apply (nat_canonical t1 HT) in H. left.
      right. auto.
    + destruct H as [t' H'].
      right.
      exists <{ succ t' }>. auto.
  - (* T_Pred *)
    destruct IHHT as [Hval | Hstep].
    + (* t1 is a value *)
      apply (nat_canonical t1 HT) in Hval. inv Hval. 
      * right. exists <{ 0 }>. auto.
      * right. exists t. auto.
    + (* t1 can take a step *)
      destruct Hstep as [t1' Hstep'].
      right. 
      exists <{ pred t1' }>. auto.
  - (* T_Iszero *)
    destruct IHHT as [Hval | Hstep].
    + (* t1 is a value *)
      apply (nat_canonical t1 HT) in Hval. inv Hval.
      * right. exists <{ true }>. auto.
      * right. exists <{ false }>. auto.
    + (* t1 can take a step *)
      destruct Hstep as [t1' Hstep'].
      right. exists <{ iszero t1' }>. auto.
Qed.
(** [] *)

(** This theorem is more interesting than the strong progress theorem
    that we saw in the [Smallstep] chapter, where _all_ normal forms
    were values.  Here a term can be stuck, but only if it is ill
    typed. *)

(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is a well-typed term (of the same type). *)

(** **** Exercise: 2 stars, standard (finish_preservation) *)
Theorem preservation : forall t t' T,
  <{ |-- t \in T }> ->
  t --> t' ->
  <{ |-- t' \in T }>.

(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;(* every case needs to introduce a couple of things *)intros t' HE;(* and we can deal with several impossible cases all at once *)try solve_by_invert.
    - (* T_If *) inv HE.
      + (* ST_IFTrue *) assumption.
      + (* ST_IfFalse *) assumption.
      + (* ST_If *) apply T_If; try assumption.
        apply IHHT1; assumption.
    - (* T_Succ *) inv HE.
      apply T_Succ. apply IHHT; assumption.
    - (* T_Pred *) inversion HE; subst; clear HE.
      + (* ST_Pred0 *) apply T_0.
      + (* ST_PredSucc *) inv HT. assumption.
      + (* ST_Pred *) apply T_Pred. apply IHHT; assumption.
    - (* T_Iszero *) inv HE.
      + (* ST_IsZero0 *) apply T_True.
      + (* ST_IsZeroSucc *) inv HT. apply T_False.
      + (* ST_IsZero *) apply T_Iszero. apply IHHT; assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars, standard (preservation_alternate_proof)

    Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proofs to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem preservation' : forall t t' T,
  <{ |-- t \in T }> ->
  t --> t' ->
  <{ |-- t' \in T }>.
Proof with eauto.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The preservation theorem is often called _subject reduction_,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  <{ |-- t \in T }> ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S]. (* From definition of stuck *)
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + auto.
Qed.

(* ================================================================= *)
(** ** Additional Exercises *)

(** **** Exercise: 3 stars, standard, especially useful (subject_expansion)

    Having seen the subject reduction property, one might
    wonder whether the opposite property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t --> t']
    and [|-- t' \in T], then [|-- t \in T]?  If so, prove it.  If
    not, give a counter-example.

    (* FILL IN HERE *)
*)

Theorem subject_expansion:
  (forall t t' T, t --> t' /\ <{ |-- t' \in T }> -> <{ |-- t \in T }>)
  \/
  ~ (forall t t' T, t --> t' /\ <{ |-- t' \in T }> -> <{ |-- t \in T }>).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (variation1)

    Suppose that we add this new rule to the typing relation:

      | T_SuccBool : forall t,
           <{ |-- t \in Bool }> ->
           <{ |--  succ t \in Bool }>

   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
            (* FILL IN HERE *)
      - Progress
            (* FILL IN HERE *)
      - Preservation
            (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation1 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard (variation2)

    Suppose, instead, that we add this new rule to the [step] relation:

      | ST_Funny1 : forall t2 t3,
           (<{ if true then t2 else t3 }>) --> t3

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_variation2 : option (nat*string) := None.
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation3)

    Suppose instead that we add this rule:

      | ST_Funny2 : forall t1 t2 t2' t3,
           t2 --> t2' ->
           (<{ if t1 then t2 else t3 }>) --> (<{ if t1 then t2' else t3 }>)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
            (* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation4)

    Suppose instead that we add this rule:

      | ST_Funny3 :
          (<{pred false}>) --> (<{ pred (pred false)}>)

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation5)

    Suppose instead that we add this rule:

      | T_Funny4 :
            |-- <{ 0 }> \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 2 stars, standard, optional (variation6)

    Suppose instead that we add this rule:

      | T_Funny5 :
            |--  pred 0 }> \in Bool

   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
(* FILL IN HERE *)
*)
(** [] *)

(** **** Exercise: 3 stars, standard, optional (more_variations)

    Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 1 star, standard (remove_pred0)

    The reduction rule [ST_Pred0] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of [0] to
    be undefined, rather than being defined to be [0].  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere?

(* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_remove_pred0  : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (prog_pres_bigstep)

    Suppose our evaluation relation is defined in the big-step style.
    State appropriate analogs of the progress and preservation
    properties. (You do not need to prove them.)

    Can you see any limitations of either of your properties?  Do they
    allow for nonterminating programs?  Why might we prefer the
    small-step semantics for stating preservation and progress?

(* FILL IN HERE *)
*)
(* Do not modify the following line: *)
Definition manual_grade_for_prog_pres_bigstep : option (nat*string) := None.
(** [] *)
End TM.

(* 2025-08-24 13:47 *)
