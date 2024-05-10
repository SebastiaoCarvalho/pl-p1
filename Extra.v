
From FirstProject Require Import Maps Imp RelationalEvaluation.
From Coq Require Import Lists.List. Import ListNotations.

(* 
  We will define a property inverse and prove 
  some properties about it
*)

Definition inverse (c1 c2: com) : Prop :=
  forall st1 st2 q1 q2,
  st1 / q1 =[ c1 ]=> st2 / q2 / Success <->
  st2 / q2 =[ c2 ]=> st1 / q1 / Success
.

(*
  The skip command is the inverse of itself
*)

Lemma skip_inverse :
inverse <{skip}> <{skip}>.

Proof.
  unfold inverse; split; intros; 
  inversion H; subst; assumption.
Qed.

(*
  Applying a command followed by it's
  inverse is the same as not doing anything
*)

Lemma seq_with_inverse_eq_skip :
forall c1 c2,
inverse c1 c2 ->
<{skip}> == <{c1 ; c2}>.

Proof.
  intros;
  unfold inverse in H;
  split;
  unfold cequiv_imp;
  intros.
  - (* -> *)
    inversion H0; subst.
    exists q2.
    (* The idea would be to create a state stq and 
      continuation q1 such that 
      st2 / q2 =[ c1 ]=> stq / q1 / Success
      and use this to apply E_Seq
    *)
    apply E_Seq with st2 q2.
    admit.
  - (* <- *)
    inversion H0; subst.
    apply H in H3.
      
Qed.

Lemma inverse_of_inverse :
forall c1,
inverse c1 c1 ->
<{c1}> == <{skip}>.

Proof.
  intros. unfold inverse in H.
  split; unfold cequiv_imp; intros.
  - (* -> *)
    exists q2.
    
    
Qed.

