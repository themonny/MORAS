Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Lia.




Inductive B : Type :=
  | O : B
  | I : B.

Definition And (x y : B) : B :=
  match x with
    | O => O
    | I => y
  end.

Definition Or (x y : B) : B :=
  match x with
    | O => y
    | I => I
  end.

Definition Not (x : B) : B :=
  match x with
    | O => I
    | I => O
  end.

Definition Add (x y c : B) : B :=
  match x, y with
    | O, O => c
    | I, I => c
    | _, _ => Not c
  end.

Definition Rem (x y c : B) : B :=
  match x, y with
    | O, O => O
    | I, I => I
    | _, _ => c
  end.

(* List *)

Fixpoint AndL (x y : list B) : list B :=
  match x, y with
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => And x y :: AndL xs ys
  end.

Fixpoint OrL (x y : list B) : list B :=
  match x, y with
    | [], _ => []
    | _, [] => []
    | x :: xs, y :: ys => Or x y :: OrL xs ys
  end.

Fixpoint NotL (x : list B) : list B :=
  match x with
    | [] => []
    | x :: xs => Not x :: NotL xs
  end.




Lemma ALU_And (x y : list B) :
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof.
intros. simpl. reflexivity.
Qed.

Lemma ALU_Or (x y : list B) :
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof.
intros. simpl.
destruct x,y ; simpl; try reflexivity. 
destruct NotL, OrL, AndL; simpl; try reflexivity; try assumption.

 Abort.


Lemma ALU_one (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof.
intros. simpl. destruct H. destruct H0. Abort.
