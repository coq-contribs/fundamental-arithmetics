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
Require Import division.
Require Import Wf_nat.

Unset Standard Proposition Elimination Names.

Open Scope positive_scope.

Lemma never_lesser_mult_positive_1 : forall (a b : positive), ~ (a * b < a * 1).
Proof.
  intros.
  unfold not.
  intros.
  apply Pos.mul_lt_mono_l in H.
  apply Pos.nlt_1_r in H.
  intuition.
Qed.

Lemma never_lesser_mult_positive_eq : forall (a b : positive), ~ (a * b < a * 1) <-> ~ (a * b < a).
Proof.
  intros.
  unfold not.
  intros.
  split.
  - intros.
    unfold not in H.
    destruct H.
    rewrite Pos.mul_1_r.
    apply H0.
  - intros.
    apply never_lesser_mult_positive_1 in H0; intuition.
Qed.

Lemma never_lesser_mult_positive : forall (a b : positive), ~ (a * b < a).
Proof.
  intros.
  apply never_lesser_mult_positive_eq.
  apply never_lesser_mult_positive_1.
Qed.

Open Scope Z_scope.

Lemma divides_zero_module : forall (a b : Z), divides b a /\ Z.abs a < Z.abs b -> a = 0.
Proof.
  intros.
  destruct H.
  unfold divides in H.
  destruct H.
  - destruct a.
    + reflexivity.
    + destruct b.
      * inversion H.
      * destruct x.
        { inversion H. }
        {
          rewrite H in H0.
          simpl in H0.
          apply never_lesser_mult_positive in H0.
          inversion H0.
        }
        {
          inversion H.
        }
      * destruct x.
        { inversion H. }
        { inversion H. }
        {
           rewrite H in H0.
           simpl in H0.
           apply never_lesser_mult_positive in H0.
           inversion H0.
        }
   + destruct b.
     * inversion H.
     * destruct x.
       { inversion H. }
       { inversion H. }
       {
          rewrite H in H0.
          simpl in H0.
          apply never_lesser_mult_positive in H0.
          inversion H0.
       }
     * destruct x.
       { inversion H. }
       { rewrite H in H0.
          simpl in H0.
          apply never_lesser_mult_positive in H0.
          inversion H0.
       }
       { inversion H. }
Qed.

Lemma impossible_Zneg : forall (p : positive), ~ (0 <= Z.neg p).
Proof.
  intros.
  unfold not.
  intros.
  auto.
Qed.

Lemma smaller_number_div : forall (b x x0 : Z), (0 <= x < Z.abs b) /\ (0 <= x0 < Z.abs b)
  -> Z.abs (x - x0) < b.
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  destruct b.
  - simpl in H2.
    intuition.
  - simpl in H2.
    simpl in H1.
    destruct x.
    + destruct x0.
      * simpl. intuition.
      * simpl. apply H2.
      * simpl. apply impossible_Zneg in H0. intuition.
    + destruct x0.
      * simpl. apply H1.
      * simpl.
Admitted.

Lemma less_then_floor_mult : forall (x y : Z), y > 0 -> x - y * (x/y) < y.
Proof.
Admitted.

Definition ceil_div (a b : Z) : Z :=
  if (a/b =? 0) then a / b
  else a / b + 1.

Definition quotient (q a b : Z) := exists (r : Z), 0 <= r < Z.abs b /\ a = b * q + r.

Definition remainder (r a b : Z) := exists (q : Z), a = b * q + r /\ (0 <= r < Z.abs b).

Lemma greater_then_ceil_neg : forall (a b : Z), (b < 0) ->  b * (ceil_div a b) <= a.
Proof.
Admitted.

Lemma less_then_ceil_mult : forall (x y : Z), y < 0 -> x - y * (ceil_div x y) < Z.abs (y).
Proof.
Admitted.

Theorem euclide : forall (a b : Z), (b <> 0) -> exists (q r : Z), quotient q a b /\ remainder r a b.
Proof.
  intros.
  destruct b.
  - unfold not in H. intuition.
  - destruct a.
    + unfold not in H.
      exists 0.
      exists 0.
      split.
      * unfold quotient.
        exists 0.
        split.
        {
           simpl.
           intuition.
        }
        {
           reflexivity.
        }
      * unfold remainder.
        exists 0.
        split.
        {
          reflexivity.
        }
        {
           simpl.
           intuition.
        }
   + exists (Z.pos p0 / Z.pos p).
     exists (Z.pos p0 - (Z.pos p * (Z.pos p0 / Z.pos p))).
     split.
     * unfold quotient.
       exists (Z.pos p0 - (Z.pos p * (Z.pos p0 / Z.pos p))).
       split.
       {
           assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           split.
          {
             apply H1.
             intuition.
          }
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
       }
       {
         intuition.
       }
    * unfold remainder.
      exists (Z.pos p0 / Z.pos p).
      split.
      {
        intuition.
      }
      {
        split.
        {
          assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           apply H1.
           intuition.
        }
        {
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
        }
      }
  + exists (Z.neg p0 / Z.pos p).
    exists (Z.neg p0 - (Z.pos p * (Z.neg p0 / Z.pos p))).
    split.
    * unfold quotient.
      exists (Z.neg p0 - (Z.pos p * (Z.neg p0 / Z.pos p))).
      split.
      {
        split.
        {
          assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           apply H1.
           intuition.
        }
        {
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
        }
      }
      {
        intuition.
      }
   * unfold remainder.
     exists (Z.neg p0 / Z.pos p).
     split.
     {
       intuition.
     }
     {
        split.
        {
          assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           apply H1.
           intuition.
        }
        {
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
        }
     }
  - destruct a.
    + exists 0.
      exists 0.
      split.
      * unfold quotient.
        exists 0.
        intuition.
        simpl.
        intuition.
      * unfold remainder.
        exists 0.
        intuition.
        simpl.
        intuition.
    + exists (ceil_div (Z.pos p0) (Z.neg p)).
      exists (Z.pos p0 - Z.neg p * (ceil_div (Z.pos p0) (Z.neg p))).
      split.
      * unfold quotient.
        exists (Z.pos p0 - Z.neg p * (ceil_div (Z.pos p0) (Z.neg p))).
        split.
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
        intuition.
      * unfold remainder.
        exists (ceil_div (Z.pos p0) (Z.neg p)).
        split.
        {
          intuition.
        }
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
    + exists (ceil_div (Z.neg p0) (Z.neg p)).
      exists (Z.neg p0 - Z.neg p * (ceil_div (Z.neg p0) (Z.neg p))).
      split.
      * unfold quotient.
        exists (Z.neg p0 - Z.neg p * (ceil_div (Z.neg p0) (Z.neg p))).
        split.
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
        intuition.
      * unfold remainder.
        exists (ceil_div (Z.neg p0) (Z.neg p)).
        split.
        {
          intuition.
        }
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
Qed.

Theorem quotient_uniquiness : forall (a b q q1 : Z), (quotient q a b) /\ (quotient q1 a b) -> q = q1.
Proof.
  intros.
  destruct H as [H1 H2].
  unfold quotient in H1.
  unfold quotient in H2.
  destruct H1.
  destruct H2.
  destruct H.
  destruct H0.
  rewrite H1 in H2.
  rewrite Z.add_move_l in H2.
  rewrite Z.add_sub_swap in H2.
  rewrite <- Z.mul_sub_distr_l in H2.
  symmetry in H2.
  rewrite Zeq_plus_swap in H2.
Admitted.