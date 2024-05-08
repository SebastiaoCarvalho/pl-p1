
From FirstProject Require Import Maps Imp RelationalEvaluation.


(*
If a command c1 leads to a state st2 where b is true
then executing a non determinist choice between c1 and
c2 and then having a guard on b is the same as having an
if else.
*)
Lemma determinism_with_guard_true_equals_if : 
forall c1 c2 c3 st st' st'' q q' q'' result result' b, 
st / q =[ c1 ]=> st' / q' / result ->
st / q =[ c2 ]=> st'' / q'' / result' ->
beval st'' b = false ->
beval st' b = true ->
<{(c1 !! c2); (b) -> c3}> 
== <{c1; if b then c3 else skip end}>
.
Proof.
    intros.
    split; unfold cequiv_imp; intros.
    - inversion H3; subst.
      inversion H6; subst.
      + inversion H12; subst; simpl in *; try discriminate.
        * eexists. apply E_Seq with st3 q4.
          -- assumption.
          -- apply E_IfTrue. try assumption.
          admit.
        * admit.
      + 
      admit.
    - inversion H3; subst.
      eexists.
      apply E_Seq with st3 q3.
      + 
          
               
Qed.

(* Lemma choice_seq_distr_r: forall c1 c2 c3,
<{ (c1 !! c2 ) ; c3}> == <{ (c1;c3) !! (c2;c3) }>.
Proof.
  intros.
  split; unfold cequiv_imp; intros.
  - inversion H; subst.
    inversion H2; subst; eexists.
    * 
      apply E_CNDetFirst.
      eapply E_Seq.
      -- eassumption.
      -- admit.
    * apply E_CNDetSecond.
      eapply E_Seq.
      -- eassumption.
      -- eassumption.

Qed. *)

