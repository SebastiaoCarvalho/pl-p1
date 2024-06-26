From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).


Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
  | E_Skip : forall st q,
    st / q =[ skip ]=> st / q / Success
  | E_Asgn (x : string) (a : aexp) : forall st q, 
    st / q =[ CAsgn x a ]=> (t_update st x (aeval st a)) / q / Success
  | E_Seq (c1 c2 : com) : forall st st1 st2 q q1 q2 suc,
    st / q =[ c1 ]=> st1 / q1 / Success ->
    st1 / q1 =[ c2 ]=> st2 / q2 / suc ->
    st / q =[ CSeq c1 c2 ]=> st2 / q2 / suc
  | E_IfTrue (b : bexp) (c1 c2 : com) : forall st1 st2 q1 q2 suc,
    beval st1 b = true ->
    st1 / q1 =[ c1 ]=> st2 / q2 / suc ->
    st1 / q1 =[ CIf b c1 c2 ]=> st2 / q2 / suc
  | E_IfFalse (b : bexp) (c1 c2 : com) : forall st1 st2 q1 q2 suc,
    beval st1 b = false ->
    st1 / q1 =[ c2 ]=> st2 / q2 / suc ->
    st1 / q1 =[ CIf b c1 c2 ]=> st2 / q2 / suc
  | E_WhileTrue (b : bexp) (c : com) : forall st1 st2 st3 q1 q2 q3 suc,
    beval st1 b = true ->
    st1 / q1 =[ c ]=> st2 / q2 / suc ->
    st2 / q2 =[ CWhile b c ]=> st3 / q3 / suc ->
    st1 / q1 =[ CWhile b c ]=> st3 / q3 / suc
  | E_WhileFalse (b : bexp) (c : com) : forall st q,
    beval st b = false ->
    st / q =[ CWhile b c ]=> st / q / Success
  | E_CNDetFirst (c1 c2 : com): forall st st1 q q1 result,
    st / q =[ c1 ]=> st1 / q1 / result ->
    st / q =[ CNDet c1 c2 ]=> st1 / ((st, c2)::q1) / result
  | E_CNDetSecond (c1 c2 : com): forall st st1 q q1 result,
    st / q =[ c2 ]=> st1 / q1 / result ->
    st / q =[ CNDet c1 c2 ]=> st1 / ((st, c1)::q1) / result
  | E_CCGuardTrue (b : bexp) (c : com): forall st st1 q q1 suc,
    beval st b = true ->
    st / q =[ c ]=> st1 / q1 / suc ->
    st / q =[ CCGuard b c ]=> st1 / q1 / suc
  | E_CCGuardFalseEmpty (b : bexp) (c : com): forall st q,
    beval st b = false ->
    q = [] ->
    st / q =[ CCGuard b c ]=> empty_st / q / Fail
  | E_CCGuardFalseNotEmpty (b : bexp) (c : com): forall st st1 st2 q q1 q2 c1 suc,
    beval st b = false ->
    q = (st1, c1)::q1 ->
    st1 / q1 =[ CSeq c1 (CCGuard b c) ]=> st2 / q2 / suc ->
    st / q =[ CCGuard b c ]=> st2 / q2 / suc

where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).



Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [].
  - apply E_Asgn.
  - apply E_IfFalse.
    + reflexivity.
    + apply E_Asgn.
Qed.


Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  apply E_Seq with (X !-> 2) [].
  - apply E_Asgn.
  - apply E_CCGuardFalseEmpty.
    + reflexivity.
    + reflexivity.
Qed. 

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2) [].
  - apply E_Asgn.
  - apply E_CCGuardTrue.
    + reflexivity.
    + apply E_Asgn.
Qed. 

Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  exists [].
  apply E_Seq with (X !-> 1) [(empty_st, <{ X := 2 }>)].
  - apply E_CNDetFirst; apply E_Asgn.
  - apply E_CCGuardFalseNotEmpty with empty_st [] <{ X := 2 }>.
    + reflexivity.
    + reflexivity.
    + apply E_Seq with (X !-> 2) [].
      * apply E_Asgn.
      * apply E_CCGuardTrue.
        -- reflexivity.
        -- replace (X !-> 3) with (X !-> 3; X !-> 2). 
          ++ apply E_Asgn.
          ++ apply t_update_shadow.
Qed.
    
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  exists [(empty_st, <{ X := 1 }>)].
  apply E_Seq with (X !-> 2) [(empty_st, <{ X := 1 }>)].
  - apply E_CNDetSecond; apply E_Asgn.
  - apply E_CCGuardTrue.
    + reflexivity.
    + replace (X !-> 3) with (X !-> 3; X !-> 2). 
      * apply E_Asgn.
      * apply t_update_shadow.
Qed.



(* 3.2. Behavioral equivalence *)

Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  unfold cequiv. unfold cequiv_imp. split.
  - intros.
    exists q2.
    inversion H; subst.
    inversion H2; subst.
    inversion H8; subst; simpl in *; try discriminate.
    inversion H10; subst.
    apply E_Asgn.
  - intros.
    exists q2.
    inversion H. subst.
    apply E_Seq with (X !-> aeval st1 2; st1) q2.
    + assumption.
    + apply E_CCGuardTrue.
      * reflexivity.
      * apply E_Skip.
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  unfold cequiv. split; unfold cequiv_imp; intros.
  - (* <- *)
    inversion H; subst. (* ; *)
    inversion H2; subst. (* !! *)
    + (* X := 1 *)
      inversion H9; subst.
      inversion H8; subst; simpl in *; try discriminate.
      inversion H4; subst.
      inversion H12; subst.
      inversion H5; subst.
      inversion H14; subst; simpl in *; try discriminate.
      inversion H16; subst.
      exists q2.
      apply E_Asgn.
    + (* X := 2*)
      inversion H9; subst.
      inversion H8; subst; simpl in *; try discriminate.
      inversion H11; subst.
      exists q3.
      apply E_Asgn.
  - (* -> *)
    intros.
    inversion H; subst.
    eexists.
    apply E_Seq with (X !-> aeval st1 2; st1) ((st1, <{ X := 1 }>)::q2).
    + apply E_CNDetSecond. apply E_Asgn.
    + apply E_CCGuardTrue.
      * reflexivity.
      * apply E_Skip.
Qed.


Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  intros.
  split; unfold cequiv_imp; intros.
  - inversion H; subst; exists q0; assumption.
  - eexists. apply E_CNDetFirst. eassumption.
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros.
  unfold cequiv. unfold cequiv_imp. split;
  intros; inversion H; subst; eexists.
  - apply E_CNDetSecond. eassumption. (* choose c1 with  c2 !! c1 *)
  - apply E_CNDetFirst. eassumption.  (* choose c2 with  c2 !! c1 *)
  - apply E_CNDetSecond. eassumption. (* choose c1 with  c1 !! c2 *)
  - apply E_CNDetFirst. eassumption.  (* choose c1 with  c1 !! c2 *)
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  intros.
  unfold cequiv. unfold cequiv_imp. split;
  intros; inversion H; subst.
  - inversion H7; subst; eexists.
    + (* choose c1 with c1 !! (c2 !! c3 *)
      apply E_CNDetFirst. eassumption.
    + (* choose c2 with c1 !! (c2 !! c3 *)
      apply E_CNDetSecond. apply E_CNDetFirst.
      eassumption.
  - (* choose c3 with c1 !! (c2 !! c3 *)
    eexists; apply E_CNDetSecond; 
    apply E_CNDetSecond; eassumption.
  - (* choose c1 with (c1 !! c2) !! c3 *)
    eexists; apply E_CNDetFirst. 
    apply E_CNDetFirst. eassumption.
  - inversion H7; subst; eexists.
    + (* choose c2 with (c1 !! c2) !! c3 *)
      apply E_CNDetFirst. apply E_CNDetSecond. 
      eassumption.
    + (* choose c3 with (c1 !! c2) !! c3 *)
      apply E_CNDetSecond. eassumption.
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  intros c1 c2 c3.
  split; unfold cequiv_imp; intros; inversion H; subst. 
  (*c1;c2 !! c1;c3*)
  -inversion H8; subst; eexists. 
    (* Choose c1;c2*)
    -- eapply E_CNDetFirst. eapply E_Seq.
      (* c1 *)
      --- eassumption.
      (* c2 *)
      --- eassumption.
    (*Choose c1;c3*)
    -- eapply E_CNDetSecond. eapply E_Seq.
      (* c1 *)
      --- eassumption.
      (* c3 *)
      --- eassumption.
  (*c1; (c2 !! c3) choosing c2 *)
  - inversion H7; subst; eexists.
    -- eapply E_Seq.
      (* c1 *)
      --- eassumption.
      (* c2 !! c3 *)      
      --- eapply E_CNDetFirst. eassumption.
  (*c1; (c2 !! c3) choosing c3 *)
  - inversion H7; subst; eexists.
    -- eapply E_Seq.
      --- eassumption.
      --- eapply E_CNDetSecond. eassumption.
Qed.
    


Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2.
   split; unfold cequiv_imp; intros; inversion H; subst.
   (* c1' !! c2'  choosing c1'*)
   - apply H1 in H9. inversion H9. eexists. apply E_CNDetFirst. eassumption.
   (* c1' !! c2' choosing c2'*)
   - apply H2 in H9. inversion H9. eexists. apply E_CNDetSecond. eassumption.
    (* c1 !! c2 choosing c1*)
   - apply H1 in H9. inversion H9. eexists. apply E_CNDetFirst. eassumption.
    (* c1 !! c2 choosing c2*)
   - apply H2 in H9. inversion H9. eexists. apply E_CNDetSecond. eassumption.
Qed.