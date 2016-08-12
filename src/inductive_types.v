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

Section slist.
    Variable T: Set.

    Inductive slist: Set :=
        | empty: slist
        | single: T -> slist
        | concat: slist -> slist -> slist.

    Fixpoint flatten (l: slist): list T :=
        match l with
            | empty => nil
            | single a => cons a nil
            | concat l1 l2 => flatten l1 ++ flatten l2
        end.

    Theorem flatten_distribute: forall l1 l2: slist,
        (flatten (concat l1 l2)) = (flatten l1) ++ (flatten l2).
        destruct l1; destruct l2; reflexivity.
    Qed.
End slist.
Implicit Arguments empty [T].

(*
    Exercise 3.
*)
Inductive binop: Set := Plus | Times.

Inductive exp: Set :=
    | Const: nat -> exp
    | Binop: binop -> exp -> exp -> exp.

Definition binopDenote (b: binop): nat -> nat -> nat :=
    match b with
        | Plus => plus
        | Times => mult
    end.

Fixpoint expDenote (e: exp): nat :=
    match e with
        | Const n => n
        | Binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)
    end.

Inductive instr: Set :=
    | iConst: nat -> instr
    | iBinop: binop -> instr.
Definition prog := list instr.
Definition stack := list nat.

Definition instrDenote (i: instr) (s: stack): option stack :=
    match i with
        | iConst n => Some (n :: s)
        | iBinop b =>
            match s with
                | arg1 :: arg2 :: s' => Some ((binopDenote b) arg1 arg2 :: s')
                | _ => None
            end
    end.

Fixpoint progDenote (p: prog) (s: stack): option stack :=
    match p with
        | nil => Some s
        | i :: p' =>
            match instrDenote i s with
                | None => None
                | Some s' => progDenote p' s'
            end
    end.

Fixpoint compile (e: exp): prog :=
    match e with
        | Const n => iConst n :: nil
        | Binop b e1 e2 => compile e2 ++ compile e1 ++ iBinop b :: nil
    end.