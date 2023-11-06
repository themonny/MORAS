Set Implicit Arguments.
Require Import Setoid.
Require Import Arith.
Import Coq.Bool.Bool.
Goal forall X Y : bool, ((X && negb Y) || (negb X && negb Y) || (negb X && Y)) = negb (X && Y).
intros.
destruct X, Y;simpl;reflexivity.
Qed.

Goal forall x y z:bool, negb (negb x && y && z) && negb (x&&y&&negb z)&&(x&&negb y&&z)=x&&negb y&&z.
Proof.
intros.
destruct x, y, z; simpl; reflexivity.
Qed.


