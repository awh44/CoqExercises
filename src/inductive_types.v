(*
    Exercise 1.
*)
Inductive truth: Set :=
    | Yes
    | No
    | Maybe.

Definition and (a b: truth): truth :=
    match a, b with
        | _, No => No
        | No, _ => No
        | _, Maybe => Maybe
        | Maybe, _ => Maybe
        | Yes, Yes => Yes
    end.

Definition or (a b: truth): truth :=
    match a, b with
        | _, Yes => Yes
        | Yes, _ => Yes
        | Maybe, _ => Maybe
        | _, Maybe => Maybe
        | No, No => No
    end.

Definition not (a: truth): truth :=
    match a with
        | Yes => No
        | No => Yes
        | Maybe => Maybe
    end.

Theorem and_commutative: forall a b: truth, and a b = and b a.
    destruct a; destruct b; reflexivity.
Qed.

Theorem and_distribute: forall a b c: truth, and a (or b c) = or (and a b) (and a c).
    destruct a; destruct b; destruct c; reflexivity.
Qed.

(*
    Exercise 2.
*)
Require Import List.

Inductive slist (T: Set): Set :=
    | empty: slist T
    | single: T -> slist T
    | concat: slist T -> slist T -> slist T.

Fixpoint flatten T (l: slist T): list T :=
    match l with
        | empty => nil
        | single a => cons a nil
        | concat l1 l2 => flatten T l1 ++ flatten T l2
    end.
Check concat.
Theorem flatten_distribute: forall T (l1 l2: slist T),
    (flatten T (concat T l1 l2)) = (flatten T l1) ++ (flatten T l2).
    destruct l1; destruct l2; reflexivity.
Qed.
