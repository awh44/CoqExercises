(*
    Exercise 1.
*)

(*a*)
Theorem taut1: (True \/ False) /\ (False \/ True).
    split. left. constructor. right. constructor.
Qed.

(*b - doesn't stick to the right tactics*)
Theorem taut2: forall P: Prop, P -> ~~P.
    intros. unfold not. intro. destruct H0. assumption.
Qed.

(*c*)
Theorem taut3: forall P Q R,
    P /\ (Q \/ R) -> (P /\ Q) \/ (P /\ R).
    intros.
    destruct H. (* Split P /\ (Q \/ R) into P and Q \/ R *)
    destruct H0. (* Split Q \/ R into Q and R *)
    left. split. assumption. assumption. (* Prove the P /\ Q case *)
    right. split. assumption. assumption. (* Prove the P /\ R case *)
Qed.