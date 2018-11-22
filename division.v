(* Copyright (C) 2005-2008 Sebastien Briais *)
(* http://lamp.epfl.ch/~sbriais/ *)

(* This library is free software; you can redistribute it and/or modify *)
(* it under the terms of the GNU Lesser General Public License as *)
(* published by the Free Software Foundation; either version 2.1 of the *)
(* License, or (at your option) any later version. *)

(* This library is distributed in the hope that it will be useful, but *)
(* WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA *)
(* 02110-1301 USA *)

Require Import missing.
Require Import Wf_nat.

(** b | a if there is q such that a = b * q*)
Definition divides (b a : Z) := exists q : Z, a = (b * q).

(** 1 divides every integer number *)
Lemma one_min_div_Z : forall (n : Z),(divides 1 n).
Proof.
  intros.
  unfold divides.
  exists n.
  symmetry.
  apply Z.mul_1_l.
Qed.

(** - 1 divides every integer number *)
Lemma minus_one_min_div_Z : forall (n : Z),(divides (- 1) n).
Proof.
  intros.
  unfold divides.
  exists (- n).
  destruct n.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(** 0 is divided by every integer number *)
Lemma zero_max_div : forall (n : Z), (divides n 0).
Proof.
  intros.
  red.
  exists 0.
  symmetry.
  apply Z.mul_0_r.
Qed.

Lemma zero_not_divides : forall (a : Z), divides 0 a <-> a = 0.
Proof.
  intros.
  split.
  - unfold divides.
    intros.
    destruct H.
    simpl in H.
    apply H.
  - intros.
    unfold divides.
    exists 0.
    apply H.
Qed.

(** the relation of divisibility is reflexive *)
Lemma divides_refl : forall (a : Z), (divides a a).
Proof.
  intros.
  red.
  exists 1.
  symmetry.
  apply Z.mul_1_r.
Qed.

(** the relation of divisibility is transitive *)
Lemma divides_trans : forall (a b c : Z), (divides a b)->(divides b c)->(divides a c).
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  exists (x * x0).
  rewrite H in H0.
  rewrite H0.
  symmetry.
  apply Z.mul_assoc.
Qed.

(** the relation of divisibility is not antisymmetric in Z, but it only give two options to two related numbers *)
Lemma divides_antisym_partially : forall (a b : Z), (divides a b) -> (divides b a) -> a = b \/ a = -b.
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  rewrite H.
  destruct a.
  - left.
    reflexivity.
  - destruct b.
    * inversion H0.
    * destruct x.
      {
         inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.pos p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.pos p1 * Z.pos p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.pos p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          left.
          symmetry.
          apply Z.mul_1_r.
        - inversion H0.
      }
      {
        inversion H.
      }
    * destruct x.
      {
         inversion H.
      }
      {
        inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - inversion H0.
        - simpl in H.
          rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.pos p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.pos p1 * Z.pos p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.pos p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          right.
          simpl.
          symmetry.
          rewrite Pos.mul_1_r.
          reflexivity.
      }
  - destruct b.
    * inversion H0.
    * destruct x.
      {
         inversion H.
      }
      {
        inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - inversion H0.
        - rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.neg p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.neg p1 * Z.neg p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.neg p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          right.
          simpl.
          symmetry.
          rewrite Pos.mul_1_r.
          reflexivity.
      }
    * destruct x.
      {
         inversion H.
      }
      {
        destruct x0.
        - inversion H0.
        - simpl in H.
          rewrite H in H0.
          simpl in H0.
          assert (H1: forall (p : positive), Z.neg p <> 0).
          {
            intros p3. intuition. inversion H1.
          }
          assert (H2: Z.neg p1 * Z.neg p2 = 1).
          {
            apply mult_lemma6_Z with (n:=Z.neg p).
            apply H1.
            rewrite Z.mul_assoc. simpl. symmetry.
            rewrite Pos.mul_1_r.
            apply H0.
          }
          simpl in H2.
          apply Pos2Z.inj_pos in H2.
          apply Pos.mul_eq_1_l in H2.
          rewrite H2.
          left.
          simpl.
          symmetry.
          rewrite Pos.mul_1_r.
          reflexivity.
        - inversion H0.
      }
      {
        inversion H.
      }
Qed.

(** corollary: forall a <> 1 and a <> -1, not(a | 1) *)
Lemma non_div_1 : forall (a : Z), (a <> 1) /\ (a <> -1) -> ~ (divides a 1).
Proof.
  intros.
  red.
  intros.
  destruct H as [H1 Hm1].
  unfold divides in H0.
  destruct H0 as [q Hq].
  symmetry in Hq.
  apply mult_lemma5_Z in Hq.
  destruct Hq as [Hq1 | Hq2].
  - destruct Hq1 as [Hq1' Hq2']. apply H1. apply Hq1'.
  - destruct Hq2 as [Hq1' Hq2']. apply Hm1. apply Hq1'.
Qed.

(** if d | a and d | b then d | (a+b) *)
Lemma divides_plus : forall (d a b : Z), (divides d a) -> (divides d b) -> (divides d (a + b)).
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  exists (x + x0).
  ring.
Qed.

(** if d | a then d | a*b *)
Lemma divides_mult : forall (d a b : Z), (divides d a)->(divides d (a * b)).
Proof.
  unfold divides.
  intros.
  destruct H.
  rewrite H.
  exists (x * b).
  ring.
Qed.

(** if d | a and d | b then d | (b-a) *)
Lemma divides_minus : forall (d a b : Z), (divides d a)->(divides d b)->(divides d (b-a)).
Proof.
  unfold divides.
  intros.
  destruct H.
  destruct H0.
  rewrite H.
  rewrite H0.
  exists (x0 - x).
  ring.
Qed.

(** uniquiness of quocient -> b | a -> exists unique q -> a = b * q *)
Lemma quocient_uniquiness : forall (a b : Z), 
  divides b a -> exists q : Z, a = b * q /\ exists q0 : Z, a = b * q0
    -> q = q0.
Proof.
  intros.
  unfold divides in H.
  destruct H.
  exists x.
  split.
  - apply H.
  - exists x.
    intros.
    reflexivity.
Qed.

(** if a > 0 and b > 0 and b | a -> q > 0, where (a = b * q) *)
Lemma same_signal_pos : forall (a b : Z),
  a > 0 -> b > 0 -> divides b a -> exists q : Z, q > 0 -> a = b * q.
Proof.
  intros.
  unfold divides in H1.
  destruct H1.
  destruct a.
  - inversion H.
  - destruct b.
    + inversion H0.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * apply H1.
      * inversion H2.
    + inversion H0.
  - destruct b.
    + inversion H0.
    + inversion H.
    + inversion H0.
Qed.

(** if a < 0 and b < 0 and b | a -> q > 0, where (a = b * q) *)
Lemma same_signal_neg : forall (a b : Z),
  a < 0 -> b < 0 -> divides b a -> exists q : Z, q > 0 -> a = b * q.
Proof.
  intros.
  unfold divides in H1.
  destruct H1.
  destruct a.
  - inversion H.
  - destruct b.
    + inversion H0.
    + inversion H0.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * apply H1.
      * inversion H2.
  - destruct b.
    + inversion H0.
    + inversion H0.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * apply H1.
      * inversion H2.
Qed.

(** if a < 0 and b < 0 and b | a -> q > 0, where (a = b * q) *)
Lemma dif_signal : forall (a b : Z),
  (a > 0 /\ b < 0) \/ (a < 0 /\ b > 0) -> divides b a -> exists q : Z, q < 0 -> a = b * q.
Proof.
  intros.
  unfold divides in H0.
  destruct H0.
  destruct H as [H1 | H2].
  - destruct H1.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * inversion H2.
      * apply H0.
  - destruct H2.
    + exists x.
      intros.
      destruct x.
      * inversion H2.
      * inversion H2.
      * apply H0.
Qed.

Lemma div_comb_linear : forall (a b c : Z), (divides a b) /\ (divides a c) -> 
  forall (x y : Z), (divides a (b * x + c * y) ).
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  unfold divides.
  rewrite H.
  rewrite H0.
  exists (x0 * x + x1 * y).
  rewrite Z.mul_add_distr_l.
  rewrite Zmult_assoc_reverse.
  rewrite Zmult_assoc_reverse.
  reflexivity.
Qed.

(** lemma about divisibility *)
Lemma divides_le : forall (a b : Z), (a<>0) -> (divides b a) -> (Z.abs b <= Z.abs a).
Proof.
  intros.
  destruct H0.
  destruct b.
  - destruct a.
    + intuition.
    + intuition.
    + intuition.
  - destruct a.
    + intuition.
    + simpl.
      destruct x.
      * intuition.
      * simpl in H0.
        rewrite H0.
        apply mult_cresc_positive.
      * inversion H0.
    + simpl.
      destruct x.
      * intuition.
      * simpl in H0.
        inversion H0.
      * simpl in H0.
        apply Pos2Z.inj_neg in H0.
        rewrite H0.
        apply mult_cresc_positive.
   - destruct a.
    + intuition.
    + simpl.
      destruct x.
      * intuition.
      * inversion H0.
      * rewrite H0.
        apply mult_cresc_positive.
    + simpl.
      destruct x.
      * intuition.
      * simpl in H0.
        apply Pos2Z.inj_neg in H0.
        rewrite H0.
        apply mult_cresc_positive.
      * inversion H0. 
Qed.

(** here we show that if b | a then it is possible to compute q such that a = b*q *)
Lemma quo_dec : forall (a b : Z), (divides b a)-> {q : Z | a = b * q}.
Proof.
  intros.
  destruct a.
  - destruct b.
    + exists 0. reflexivity.
    + exists 0. reflexivity.
    + exists 0. reflexivity.
  - destruct b.
    + exists 0.
      destruct H.
      inversion H.
    + unfold divides in H.
Admitted.

(** we can now define the quotient of a by b in case of b | a *)
Definition quo (a b : Z) (H:(divides b a)) := let (q,_):=(quo_dec a b H) in q.
