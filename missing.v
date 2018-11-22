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

Require Export ZArith.
Require Export Arith.
Require Export ArithRing.
Require Export Omega.

Unset Standard Proposition Elimination Names.

Open Scope nat_scope.
Search(_ <= _ + _).

Open Scope positive_scope.

Lemma add_cresc_positive : forall (n m : positive), n <= n + m.
Proof.
  intros.
  rewrite Pos2Nat.inj_le.
  rewrite Pos2Nat.inj_add.
  apply le_plus_l.
Qed.

Open Scope nat_scope.

Lemma to_nat_pos : forall (n : positive), 1 <= Pos.to_nat n.
Proof.
  intros.
  induction n.
  - rewrite Pos.xI_succ_xO, Pos2Nat.inj_succ.
    apply Peano.le_n_S, Peano.le_0_n.
  - Search "inj_xO".
    rewrite Pos2Nat.inj_xO. simpl.
    apply Nat.le_trans with (m := Pos.to_nat n).
    * apply IHn.
    * apply Nat.le_add_r.
  - rewrite Pos2Nat.inj_1. 
    apply Peano.le_n_S, Peano.le_0_n.
Qed.

Lemma to_nat_pos_S_n : forall (n : positive), exists m,  Pos.to_nat n = S m.
Proof.
  intros n.
  destruct (Pos.to_nat n) eqn:H.
  - assert (H1: 1 <= Pos.to_nat n). {apply to_nat_pos. } rewrite H in H1. inversion H1.
  - exists n0. reflexivity.
Qed.

Lemma mult_cresc_positive : forall (n m :positive), (n <= n * m)%positive.
Proof.
  intros.
  rewrite Pos2Nat.inj_le, Pos2Nat.inj_mul.
  assert (H1: exists n' , Pos.to_nat n = S n'). apply to_nat_pos_S_n.
  assert (H2: exists m' , Pos.to_nat m = S m'). apply to_nat_pos_S_n.
  inversion H1.
  inversion H2.
  rewrite H, H0.
  simpl.
  apply le_n_S.
  rewrite <- mult_n_Sm, Nat.add_comm.
  assert ((x * x0) + x = x + (x * x0)). {apply Nat.add_comm. } rewrite H3.
  rewrite plus_assoc_reverse. apply le_plus_l.
Qed.
  
Lemma mult_cresc_positive_gt_1 : forall (n m : positive), ((m > 1) -> n < n * m)%positive.
Proof.
  intros.
  rewrite Pos2Nat.inj_lt.
  rewrite Pos2Nat.inj_mul.
  rewrite Pos2Nat.inj_gt in H.
  rewrite Pos2Nat.inj_1 in H.
  assert (H1: exists n' , Pos.to_nat n = S n'). apply to_nat_pos_S_n.
  assert (H2: exists m' , Pos.to_nat m = S m'). apply to_nat_pos_S_n.
  inversion H1.
  inversion H2.
  rewrite H0, H3.
  rewrite H3 in H.
  simpl. apply lt_n_S.
  rewrite Nat.mul_comm.
  simpl.
  apply gt_S_n in H.
  apply gt_le_S in H.
  destruct x0.
  - inversion H.
  - simpl. apply le_lt_n_Sm. rewrite plus_comm, plus_assoc_reverse. apply le_plus_l. 
Qed.

Open Scope positive_scope.

Lemma mult_positive_l : forall (n m : positive), (n = n * m -> m = 1)%positive.
Proof.
  intros.
  Search( _ * ?x = ?x).
  destruct m.
  - 
    apply Pos.eqb_eq in H.
    rewrite Pos.xI_succ_xO in H. 
    rewrite Pos.mul_succ_r in H.
    assert (H1: n <> n + n*m~0). { apply not_eq_sym. rewrite Pos.add_comm. apply Pos.add_no_neutral. }
    apply Pos.eqb_neq in H1.
    rewrite H in H1. inversion H1.
  - assert(H1: m~0 > 1). {
      rewrite <- Pos.add_diag.
      rewrite Pos2Nat.inj_gt.
      rewrite Pos2Nat.inj_add.
      rewrite Pos2Nat.inj_1.
      assert (H2: exists m' , Pos.to_nat m = S m'). apply to_nat_pos_S_n.
      inversion H2.
      rewrite H0. simpl. rewrite plus_comm. simpl. auto with arith.
    }
    
    assert (H2: n < n * m~0). { 
      apply mult_cresc_positive_gt_1, H1.
    }
    symmetry  in H.
    rewrite H in H2. 
    apply Pos.lt_irrefl in H2. inversion H2.
  - reflexivity.
Qed.

Open Scope Z_scope.

Lemma mult_symm_0 : forall (m : Z), m * 0 = 0.
Proof.
  intros m.
  induction m.
  + reflexivity.
  + reflexivity.
  + reflexivity.
Qed.

Lemma mult_comm_Z : forall (n m : Z), n * m = m * n.
Proof.
  intros n.
  induction n.
  + intros m. simpl. rewrite mult_symm_0. reflexivity.
  + intros m. destruct m.
    - reflexivity.
    - simpl. rewrite Pos.mul_comm. reflexivity.
    - simpl. rewrite Pos.mul_comm. reflexivity.
  + intros m. destruct m.
    - reflexivity.
    - simpl. rewrite Pos.mul_comm. reflexivity.
    - simpl. rewrite Pos.mul_comm. reflexivity.
Qed. 

Lemma mult_lemma1_Z : forall (n m : Z), (n > 0) -> (m > 0) -> (n <= n*m).
Proof.
  intros.
  rewrite mult_comm_Z. 
  induction m.
  - inversion H0.
  - destruct n.
     + inversion H.
     + rewrite mult_comm_Z. simpl. apply mult_cresc_positive.
     + inversion H.
  - inversion H0.
Qed.

Lemma mult_lemma2_Z : forall (n m : Z),(n*m = 0) -> (n=0)\/(m=0).
Proof.  
  intros.
  induction n.
  - tauto.
  - destruct m.
    + tauto.
    + inversion H.
    + inversion H.
  - destruct m.
    + tauto.
    + inversion H.
    + inversion H.
Qed.

Lemma mult_lemma3_Z : forall (n m : Z),(n > 0)->(m > 1)->(n < n*m).
Proof.
  intros.
  induction n.
  - inversion H.
  - destruct m.
    + inversion H0.
    + simpl. apply mult_cresc_positive_gt_1. apply H0.
    + inversion H0.
  - inversion H.
Qed.

Lemma mult_lemma4_Z : forall (n m : Z), n = n*m -> n = 0 \/ m = 1.
Proof.
  intros n m H.
  destruct n.
  + tauto.
  + right.
    destruct m.
    - inversion H.
    - simpl in H. inversion H. apply mult_positive_l in H1. rewrite H1. reflexivity.
    - inversion H.
  + right.
    destruct m.
    - inversion H.
    - simpl in H. inversion H. apply mult_positive_l in H1. rewrite H1. reflexivity.
    - inversion H.
Qed.

Lemma mult_lemma5_Z : forall (n m : Z),((n * m) =1)-> ((n=1)/\(m=1)) \/ ((n=-1)/\(m=-1)).
Proof.
  intros n.
  induction n.
  + intros m H. inversion H.
  + left.
    split.
    - destruct m.
      * inversion H.
      * simpl in H. 
        inversion H. 
        apply Pos.mul_eq_1_r in H1.
        rewrite H1.
        symmetry. 
        rewrite Pos.mul_comm. 
        rewrite Pos.mul_1_l.
        reflexivity.
      * inversion H.
    - destruct m.
      * inversion H.
      * simpl in H. inversion H.
        apply Pos.mul_eq_1_r in H1.
        rewrite H.
        rewrite H1.
        reflexivity.
      * simpl in H. inversion H.
    + right. split.
        - destruct m.
          * inversion H.
          * inversion H.
          * simpl in H. inversion H. 
            apply Pos.mul_eq_1_l in H1.
            rewrite H1. simpl. symmetry. inversion H.
            apply Pos.mul_eq_1_r in H2.
            rewrite H1. simpl. reflexivity.
        - destruct m.
          * inversion H.
          * inversion H.
          * simpl in H. inversion H. 
            apply Pos.mul_eq_1_l in H1.
            rewrite H1. simpl. symmetry. inversion H.
            apply Pos.mul_eq_1_r in H2. reflexivity.
Qed.

Lemma minus_same_number_Z : forall (y : Z), y - y = 0.
Proof.
  intros y.
  destruct y.
  + reflexivity.
  + simpl. apply Z.pos_sub_diag.
  + simpl. apply Z.pos_sub_diag.
Qed.

Lemma plus_minus_lemma1 : forall (y x : Z),(x+y-y=x).
Proof.
  intros.
  induction x.
  + simpl. apply minus_same_number_Z.
  + apply Z.add_simpl_r.
  + apply Z.add_simpl_r.
Qed.

Lemma mult_minus_lemma1_Z : forall (a n : Z),a*n-n = (a-1)*n.
Proof.
  intros.
  symmetry.
  rewrite Z.mul_sub_distr_r.
  assert (H: 1 * n = n).
  {
    destruct n.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.

Lemma mult_lemma6_Z : forall (a b n : Z),(n <> 0)->(n*a=n*b)->(a=b).
Proof.
  intros.
  induction a.
  - destruct b.
    + reflexivity.
    + rewrite mult_symm_0 in H0.
      symmetry in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
    + rewrite mult_symm_0 in H0.
      symmetry in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
  - destruct b.
    + rewrite mult_symm_0 in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Zpos_eq in H2.
        apply H2.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Zpos_eq in H2.
        apply H2.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
  - destruct b.
    + rewrite mult_symm_0 in H0.
      apply mult_lemma2_Z in H0. 
      destruct H0 as [Hn | Hz].
        * unfold not in H. apply H in Hn. inversion Hn.
        * inversion Hz.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
    + destruct n.
      * rewrite Z.mul_0_l in H0.
        symmetry in H0.
        rewrite Z.mul_0_l in H0.
        unfold not in H.
        apply H in H0.
        inversion H0.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Pos2Z.inj_neg_iff in H2.
        apply H2.
      * simpl in H0.
        inversion H0.
        apply Pos.mul_reg_l in H2.
        apply Pos2Z.inj_neg_iff in H2.
        apply H2.
Qed.

Lemma minus_distributive_Z : forall (x y z : Z), - x - y = - (x + y).
Proof.
  intros.
  destruct x.
  + simpl. reflexivity.
  + destruct y.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. symmetry. apply Z.pos_sub_opp.
  + destruct y.
    * simpl. reflexivity.
    * simpl. symmetry. apply Z.pos_sub_opp.
    * simpl. reflexivity.
Qed.

Lemma minus_minus_lemma2_Z : forall (x y z : Z), (x - y - z)=(x - (y + z)).
Proof.  
  intros.
  induction x.
  - simpl. destruct y.
    + simpl. reflexivity.
    + destruct z.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. symmetry. apply Z.pos_sub_opp.
    + destruct z.
      * simpl. reflexivity.
      * simpl. symmetry. apply Z.pos_sub_opp.
      * simpl. reflexivity.
  - destruct y.
    + simpl. reflexivity.
    + destruct z.
      * simpl. rewrite Z.sub_0_r. reflexivity.
      * symmetry. apply Z.sub_add_distr.
      * symmetry. apply Z.sub_add_distr.
    + destruct z.
      * simpl. reflexivity.
      * symmetry. apply Z.sub_add_distr.
      * symmetry. apply Z.sub_add_distr.
  - destruct y.
    + reflexivity.
    + destruct z.
      * simpl. reflexivity.
      * simpl. apply Pos2Z.inj_neg_iff.
        symmetry.
        apply Pos.add_assoc.
      * symmetry. apply Z.sub_add_distr.
    + destruct z.
      * simpl. rewrite Z.sub_0_r. reflexivity.
      * symmetry. apply Z.sub_add_distr.
      * symmetry. apply Z.sub_add_distr.
Qed.

Lemma mult_lemma7_Z : forall (x y z t : Z), x * y * (z * t) = z * (x * y * t).
Proof.
  intros.
  ring.
Qed.

Lemma minus_lt_lemma1 : forall (b a : Z),(a < b) -> (0 < b - a).
Proof.
  intros.
  omega.
Qed.

Lemma different_from_zero_pos : forall (p : positive), Z.pos p <> 0.
Proof.
  intros.
  unfold not.
  intros H.
  inversion H.
Qed.

Lemma different_from_zero_neg : forall (p : positive), Z.neg p <> 0.
Proof.
  intros.
  unfold not.
  intros H.
  inversion H.
Qed.