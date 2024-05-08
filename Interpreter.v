From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.


Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)


Notation "'LETOPT' x <== e1 'IN' e2"
  := (match e1 with
          | Success x => e2
          | Fail => Fail
          | OutOfGas => OutOfGas
        end)
(right associativity, at level 60).


Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=

 match i with
  | O => OutOfGas
  | S i' =>
    match c with
    | <{ skip }> =>
        Success (st, continuation)
    | <{ x := a }> =>
        Success (t_update st x (aeval st a), continuation)
    | <{ c1 ; c2 }> =>
         LETOPT res <== ceval_step st c1 continuation i' IN
          ceval_step (fst res) c2 (snd res) i'
    | <{ if b then c1 else c2 end }> =>
        if (beval st b) then
          ceval_step st c1 continuation i'
        else
          ceval_step st c2 continuation i'
    | <{ while b do c1 end }> =>
        if (beval st b)
          then LETOPT n <== ceval_step st c1 continuation i' IN
          ceval_step (fst n) c (snd n)  i'
        else
          Success (st, continuation)
    | <{ c1 !! c2 }> =>
        ceval_step st c1 ((st, c2)::continuation) i'
    | <{ b -> c }> =>
        if (beval st b) then
          ceval_step st c continuation i'
        else
          match continuation with
          | [] => Fail
          | (st', c')::cont' => ceval_step st' (CSeq c' (CCGuard b c)) cont' i'
          end
    end
  end.

(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)
Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.

Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 =  ceval_step st p2 cont i1)).
Proof.
 intros st cont.
  exists 5. 
  intros i1 H_ge.
  destruct i1 as [|i1'].
  - inversion H_ge.
  - simpl.
    destruct i1' as [|i1''].
    + simpl. 
      assert (contra : 1 >= 5 -> False) by lia.
      apply contra in H_ge. destruct H_ge.
    + simpl. 
      destruct i1'' as [|i1'''].
      * assert (contra : 2 >= 5 -> False) by lia.
        apply contra in H_ge. destruct H_ge.
      * simpl.
        destruct i1''' as [|i1''''].
        -- assert (contra : 3 >= 5 -> False) by lia.
           apply contra in H_ge. destruct H_ge.
        -- simpl.
            destruct i1'''' as [|i1'''''].
            ++ assert (contra : 4 >= 5 -> False) by lia.
                apply contra in H_ge. destruct H_ge.
            ++ simpl. reflexivity.
Qed.

Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  induction i1 as [| i1' IH1]; 
  intros i2 st st' c cont cont' Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct i2 as [| i2'].
    + inversion Hle.
    + assert (Hle': i1' <= i2') by lia.
      destruct c.
      * (* skip *)
        simpl in Hceval. simpl. rewrite Hceval. reflexivity.
      * (* := *)
        simpl in Hceval. simpl. rewrite Hceval. reflexivity.
      * (* ; *)
        simpl in Hceval. simpl. 
        destruct (ceval_step st c1 cont i1') eqn:Heqst1'o. 
        -- destruct s as [st'' cont''].
          apply (IH1 i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. simpl. simpl in Hceval.
          apply (IH1 i2') in Hceval; try assumption.
        -- discriminate Hceval.
        -- discriminate Hceval.
      * (* if *)
        simpl in Hceval. simpl. destruct (beval st b);
        apply (IH1 i2') in Hceval; assumption.
      * (* while *)
        simpl in Hceval. simpl. destruct (beval st b);
        try assumption. destruct (ceval_step st c cont i1') eqn:Heqst1'o.
        -- destruct s as [st'' cont''].
          apply (IH1 i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. simpl. simpl in Hceval.
          apply (IH1 i2') in Hceval; try assumption.
        -- discriminate Hceval.
        -- discriminate Hceval.
      * (* !! *)
        simpl in Hceval. simpl.
        destruct (ceval_step st c1 ((st, c2) :: cont) i1') eqn:Heqst1'o.
        -- destruct s as [st'' cont''].
          apply (IH1 i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. simpl. simpl in Hceval.
          rewrite Hceval. reflexivity.
        -- discriminate Hceval.
        -- discriminate Hceval.
      * (* -> *)
        simpl in Hceval. simpl. destruct (beval st b).
        -- apply (IH1 i2') in Hceval; assumption.
        -- destruct cont. 
          ++ discriminate.
          ++ destruct p as [st'' c']. apply (IH1 i2') in Hceval; try assumption.
Qed.
