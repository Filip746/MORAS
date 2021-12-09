Inductive bool : Set := 
  | true : bool 
  | false : bool.

Definition negb (x:bool) := 
 if x then false
 else true.

Definition andb (x y: bool) : bool :=
 if x then y 
 else false.

Definition orb (x y: bool) : bool := 
 if x then true 
 else y.

Lemma prviA (x y: bool):
 orb (orb (negb (andb x y)) (andb (negb x) y)) (andb (negb x) (negb y))= orb (negb x) (negb y).
Proof.
  induction x, y ; simpl ; reflexivity.
Qed.

Lemma prviB (x y z: bool):
 andb (andb(negb (andb (andb (negb x) y) (negb z))) (negb (andb (andb x y) z))) (andb (andb x (negb y)) (negb z)) = andb (andb x (negb y)) (negb z).
Proof.
  induction x, y, z; simpl ; reflexivity.
Qed.

 