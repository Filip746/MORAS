Set Implicit Arguments.
Require Import List.
Import ListNotations.
Require Import Omega.

(* Bit *)

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

Fixpoint AddLr (x y : list B) (c : B) : list B :=
match x, y with
| [], _ => []
| _, [] => []
| x :: xs, y :: ys => Add x y c :: AddLr xs ys (Rem x y c)
end.

Definition AddL (x y : list B) : list B := rev (AddLr (rev x) (rev y) O).

Fixpoint IncLr (x : list B) (c : B) : list B :=
match x with
| [] => []
| x :: xs => Add x I c :: IncLr xs (Rem x I c)
end.

Definition IncL (x : list B) : list B := rev (IncLr (rev x) O).

(* ALU *)

Definition flag_zx (f : B) (x : list B) : list B :=
match f with
| I => repeat O (length x)
| O => x
end.

Definition flag_nx (f : B) (x : list B) : list B :=
match f with
| I => NotL x
| O => x
end.

Definition flag_f (f : B) (x y : list B) : list B :=
match f with
| I => AddL x y
| O => AndL x y
end.

Definition ALU (x y : list B) (zx nx zy ny f no : B) : list B := 
  flag_nx no (flag_f f (flag_nx nx (flag_zx zx x)) (flag_nx ny (flag_zx zy y))).

(* Teoremi *)

Lemma ALU_zero (x y : list B) :
  length x = length y -> ALU x y I O I O I O = repeat O (length x).
Proof.
    assert (P : forall (n : nat), AddL (repeat O n) (repeat O n) = repeat O n).
    {
      assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. reflexivity.
      }
      assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
      }
      intros. unfold AddL.
      rewrite P_rev_2. 
      induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    }
    intros H. simpl. rewrite H. rewrite P. reflexivity.
Qed.

Lemma ALU_minus_one (x y : list B) : 
  length x = length y -> ALU x y I I I O I O = repeat I (length x).
Proof.
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  assert (P_AddL : forall (n : nat), AddL (repeat I n) (repeat O n) = repeat I n).
  {
    assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
    {
      intros. induction n.
      - reflexivity.
      - simpl. rewrite IHn. reflexivity.
    }
    assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
    {
      intros. induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    }
    intros. unfold AddL. rewrite P_rev_2, P_rev_2. induction n.
    - reflexivity.
    - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
  }
  intros H. simpl. rewrite H, P_NotL. rewrite P_AddL. reflexivity.
Qed.

Lemma ALU_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O O = x.
Proof. 
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  assert (P_AndL : forall l : list B, AndL l (repeat I (length l)) = l).
  {
    assert (P_And : forall b : B, And b I = b).
    {
      destruct b; reflexivity.
    }
    intros. induction l.
    - simpl. reflexivity.
    - simpl. rewrite IHl. rewrite P_And. reflexivity.
  }
  intros H. simpl. rewrite <- H. rewrite P_NotL. rewrite P_AndL. reflexivity.
Qed.

Lemma ALU_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O O = y.
Proof. 
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - reflexivity.
    - simpl. rewrite <- IHn ; reflexivity.
  }
  assert (P_AndL : forall l : list B, AndL (repeat I (length l)) l = l).
  {
    intros. induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.
  }
  intros H. induction y.
  - simpl. rewrite H. simpl. reflexivity.
  - simpl. rewrite H. simpl. rewrite P_NotL. rewrite P_AndL. reflexivity. 
Qed.

Lemma ALU_Not_x (x y : list B) : 
  length x = length y -> ALU x y O O I I O I = NotL x.
Proof. 
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  assert (P_AndL : forall l : list B, AndL l (repeat I (length l)) = l).
  {
    assert (P_And : forall b : B, And b I = b).
    {
      destruct b; reflexivity.
    }
    intros. induction l.
    - reflexivity.
    - simpl. rewrite IHl, P_And. reflexivity.
  }
  intros H. simpl. rewrite <- H, P_NotL, P_AndL. reflexivity.
Qed.

Lemma ALU_Not_y (x y : list B) : 
  length x = length y -> ALU x y I I O O O I = NotL y.
Proof. 
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n.
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  }
  assert (P_AndL : forall l : list B, AndL (repeat I (length l)) l = l).
  {
    intros. induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.
  }
  intros H. simpl. rewrite H, P_NotL, P_AndL. reflexivity.
Qed.

Lemma ALU_Add (x y : list B) : 
  length x = length y -> ALU x y O O O O I O = AddL x y.
Proof. 
  intros H. simpl. reflexivity.
Qed.

Lemma ALU_And (x y : list B) : 
  length x = length y -> ALU x y O O O O O O = AndL x y.
Proof. 
auto.
Qed.

Lemma ALU_Or (x y : list B) : 
  length x = length y -> ALU x y O I O I O I = OrL x y.
Proof. 
  assert (M : forall a b : list B, NotL (AndL a b) = OrL (NotL a) (NotL b)).
  {
    intros a. induction a.
    - reflexivity.
    - destruct b.
      -- reflexivity.
      -- simpl. rewrite IHa. destruct a,b; reflexivity.
  }
  assert (U : forall a : list B, NotL (NotL a) = a).
  {
    intros. induction a.
    - reflexivity.
    - simpl. rewrite IHa. destruct a; reflexivity.
  }
  intros H. simpl. rewrite M, U, U. reflexivity.
Qed.

Lemma ALU_One (n : nat) (x y : list B) :
  length x = n /\ length y = n /\ n <> 0 -> ALU x y I I I I I I = repeat O (pred n) ++ [I].
Proof. 
  intros [a b]. simpl. destruct b.
  assert (P_NotL : forall (n : nat), NotL (repeat O n) = repeat I n).
  {
    intros. induction n0.
    - reflexivity.
    - simpl. rewrite IHn0. reflexivity.
  }
  assert (P_AndL : forall l : list B, AndL (repeat I (length l)) l = l).
  {
    intros. induction l.
    - reflexivity.
    - simpl. rewrite IHl. reflexivity.
  }
  rewrite P_NotL. rewrite <- P_AndL. rewrite a, H. rewrite P_NotL. 
  assert (P : forall (n : nat), AddL (repeat I n) (repeat I n) = repeat I n).
    {
      assert (P_rev_1 : forall (b : B) (n : nat), repeat b n ++ [b] = b :: repeat b n).
      {
        intros. induction b.
        - induction n0.
          -- simpl. reflexivity.
          -- simpl. rewrite IHn0. reflexivity.
        - induction n0. 
          -- simpl. reflexivity.
          -- simpl. rewrite IHn0. reflexivity.
      }
    intros. induction n0.
    - simpl. reflexivity.
    - simpl. unfold AddL. rewrite IHn0. rewrite <- P_rev_1. rewrite <- IHn0. f_equal. induction n0.
      -- simpl. reflexivity.  
    }
        - simpl. rewrite IHn. reflexivity.
      }
      assert (P_rev_2 : forall (b : B) (n : nat), rev (repeat b n) = repeat b n).
      {
        intros. induction n.
        - reflexivity.
        - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
      }
      intros. unfold AddL.
      rewrite P_rev_2. 
      induction n.
      - reflexivity.
      - simpl. rewrite IHn. rewrite P_rev_1. reflexivity.
    } simpl.
  
Admitted.







