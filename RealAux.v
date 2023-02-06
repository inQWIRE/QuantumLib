(** Supplement to Coq's axiomatized Reals *)
  
Require Export Reals.
Require Import Psatz.
Require Export Program.
Require Export Summation.
 
(** * Basic lemmas *)

(** Relevant lemmas from Coquelicot's Rcomplements.v **)

Open Scope R_scope.
Local Coercion INR : nat >-> R.

Lemma Rle_minus_l : forall a b c,(a - c <= b <-> a <= b + c). Proof. intros. lra. Qed.
Lemma Rlt_minus_r : forall a b c,(a < b - c <-> a + c < b). Proof. intros. lra. Qed.
Lemma Rlt_minus_l : forall a b c,(a - c < b <-> a < b + c). Proof. intros. lra. Qed.
Lemma Rle_minus_r : forall a b c,(a <= b - c <-> a + c <= b). Proof. intros. lra. Qed.
Lemma Rminus_le_0 : forall a b, a <= b <-> 0 <= b - a. Proof. intros. lra. Qed.
Lemma Rminus_lt_0 : forall a b, a < b <-> 0 < b - a. Proof. intros. lra. Qed.

(* Automation *)

Lemma Rminus_unfold : forall r1 r2, (r1 - r2 = r1 + -r2). Proof. reflexivity. Qed.
Lemma Rdiv_unfold : forall r1 r2, (r1 / r2 = r1 */ r2). Proof. reflexivity. Qed.

Hint Rewrite Rminus_unfold Rdiv_unfold Ropp_0 Ropp_involutive Rplus_0_l 
             Rplus_0_r Rmult_0_l Rmult_0_r Rmult_1_l Rmult_1_r : R_db.
Hint Rewrite <- Ropp_mult_distr_l Ropp_mult_distr_r : R_db.
Hint Rewrite Rinv_l Rinv_r sqrt_sqrt using lra : R_db.

Notation "√ n" := (sqrt n) (at level 20) : R_scope.

(** Other useful facts *)

Lemma Rmult_div_assoc : forall (x y z : R), x * (y / z) = x * y / z.
Proof. intros. unfold Rdiv. rewrite Rmult_assoc. reflexivity. Qed.

Lemma Rmult_div : forall r1 r2 r3 r4 : R, r2 <> 0 -> r4 <> 0 -> 
  r1 / r2 * (r3 / r4) = r1 * r3 / (r2 * r4). 
Proof. intros. unfold Rdiv. rewrite Rinv_mult_distr; trivial. lra. Qed.

Lemma Rdiv_cancel :  forall r r1 r2 : R, r1 = r2 -> r / r1 = r / r2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Rsum_nonzero : forall r1 r2 : R, r1 <> 0 \/ r2 <> 0 -> r1 * r1 + r2 * r2 <> 0. 
Proof.
  intros.
  replace (r1 * r1)%R with (r1 ^ 2)%R by lra.
  replace (r2 * r2)%R with (r2 ^ 2)%R by lra.
  specialize (pow2_ge_0 (r1)). intros GZ1.
  specialize (pow2_ge_0 (r2)). intros GZ2.
  destruct H.
  - specialize (pow_nonzero r1 2 H). intros NZ. lra.
  - specialize (pow_nonzero r2 2 H). intros NZ. lra.
Qed.

Lemma Rpow_le1: forall (x : R) (n : nat), 0 <= x <= 1 -> x ^ n <= 1.
Proof.
  intros; induction n.
  - simpl; lra.
  - simpl.
    rewrite <- Rmult_1_r.
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
Qed.
    
(* The other side of Rle_pow, needed below *)
Lemma Rle_pow_le1: forall (x : R) (m n : nat), 
  0 <= x <= 1 -> (m <= n)%nat -> x ^ n <= x ^ m.
Proof.
  intros x m n [G0 L1] L.
  remember (n - m)%nat as p.
  replace n with (m+p)%nat in * by lia.
  clear -G0 L1.
  rewrite pow_add.
  rewrite <- Rmult_1_r.
  apply Rmult_le_compat; try lra.
  apply pow_le; trivial.
  apply pow_le; trivial.
  apply Rpow_le1; lra.
Qed.


(** * Square roots *)

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x.
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma sqrt_pow : forall (r : R) (n : nat), (0 <= r)%R -> (√ (r ^ n) = √ r ^ n)%R.
Proof.
  intros r n Hr.
  induction n.
  simpl. apply sqrt_1.
  rewrite <- 2 tech_pow_Rmult.
  rewrite sqrt_mult_alt by assumption.
  rewrite IHn. reflexivity.
Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt; lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat), 
  0 <= x -> √ x ^ (S (S n)) = x * √ x ^ n.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.  

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> √ r <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.  

Lemma sqrt2_div2 : (√ 2 / 2)%R = (1 / √ 2)%R.
Proof.
   field_simplify_eq; try (apply sqrt_neq_0_compat; lra).
   rewrite pow2_sqrt2; easy.
Qed.

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof. apply sqrt_inv; lra. Qed.  

Lemma sqrt_sqrt_inv : forall (r : R), 0 < r -> (√ r * √ / r)%R = 1.
Proof. 
  intros. 
  rewrite sqrt_inv; trivial. 
  rewrite Rinv_r; trivial. 
  apply sqrt_neq_0_compat; easy.
Qed.

Lemma sqrt2_sqrt2_inv : (√ 2 * √ / 2)%R = 1.
Proof. apply sqrt_sqrt_inv. lra. Qed.

Lemma sqrt2_inv_sqrt2 : ((√ / 2) * √ 2)%R = 1.
Proof. rewrite Rmult_comm. apply sqrt2_sqrt2_inv. Qed.

Lemma sqrt2_inv_sqrt2_inv : ((√ / 2) * (√ / 2) = /2)%R.
Proof. 
  rewrite sqrt2_inv. field_simplify. 
  rewrite pow2_sqrt2. easy. 
  apply sqrt_neq_0_compat; lra. 
Qed.

Lemma sqrt_1_unique : forall x, 1 = √ x -> x = 1.
Proof. intros. assert (H' := H). unfold sqrt in H. destruct (Rcase_abs x).
       - apply R1_neq_R0 in H; easy. 
       - rewrite <- (sqrt_def x); try rewrite <- H'; lra.
Qed.

Lemma lt_ep_helper : forall (ϵ : R),
  ϵ > 0 <-> ϵ / √ 2 > 0.
Proof. intros; split; intros. 
       - unfold Rdiv. 
         apply Rmult_gt_0_compat; auto; 
           apply Rinv_0_lt_compat; apply Rlt_sqrt2_0.
       - rewrite <- (Rmult_1_r ϵ).
         rewrite <- (Rinv_l (√ 2)), <- Rmult_assoc.
         apply Rmult_gt_0_compat; auto. 
         apply Rlt_sqrt2_0.
         apply sqrt2_neq_0.
Qed.




(** Defining 2-adic valuation of an integer and properties *)

Open Scope Z_scope.

(* could return nat, but int seem better *)
Fixpoint two_val_pos (p : positive) : Z :=
  match p with 
  | xO p' => 1 + (two_val_pos p')
  | _ => 0
  end.

Fixpoint odd_part_pos (p : positive) : positive :=
  match p with 
  | xO p' => odd_part_pos p'
  | _ => p
  end.


Lemma two_val_pos_mult : forall (p1 p2 : positive),
  two_val_pos (p1 * p2) = two_val_pos p1 + two_val_pos p2.
Proof. induction p1; try easy; intros. 
       - replace (two_val_pos p1~1) with 0 by easy.
         induction p2; try easy.
         replace ((xI p1) * (xO p2))%positive with (xO ((xI p1) * p2))%positive by lia.
         replace (two_val_pos (xO ((xI p1) * p2))%positive) with 
           (1 + (two_val_pos ((xI p1) * p2)%positive)) by easy.
         rewrite IHp2; easy.
       - replace (two_val_pos (xO p1)) with (1 + two_val_pos p1) by easy.
         rewrite <- Z.add_assoc, <- IHp1.
         replace ((xO p1) * p2)%positive with (xO (p1 * p2))%positive by lia.
         easy.
Qed.

(* TODO: prove at some point, don't actually need this now though. *)
(*
Lemma two_val_pos_plus : forall (p1 p2 : positive),
  two_val_pos (p1 + p2) >= Z.min (two_val_pos p1) (two_val_pos p2).
Proof. induction p1; try easy; intros.
       - replace (two_val_pos p1~1) with 0 by easy.
         induction p2; try easy.
         replace ((xI p1) * (xO p2))%positive with (xO ((xI p1) * p2))%positive by lia.
         replace (two_val_pos (xO ((xI p1) * p2))%positive) with 
           (1 + (two_val_pos ((xI p1) * p2)%positive)) by easy.
         rewrite IHp2; easy.
       - replace (two_val_pos (xO p1)) with (1 + two_val_pos p1) by easy.
         rewrite <- Z.add_assoc, <- IHp1.
         replace ((xO p1) * p2)%positive with (xO (p1 * p2))%positive by lia.
         easy.
Qed. *)




(* CHECK: maybe only need these for positives since we split on 0, pos, neg, anyways *)

Definition two_val (z : Z) : Z :=
  match z with 
  | Z0 => 0 (* poorly defined on 0 *)
  | Zpos p => two_val_pos p
  | Zneg p => two_val_pos p
  end.


Definition odd_part (z : Z) : Z :=
  match z with 
  | Z0 => 0  (* poorly defined on 0 *)
  | Zpos p => Zpos (odd_part_pos p)
  | Zneg p => Zneg (odd_part_pos p)
  end.


(* useful for below since its easier to induct on nats rather than ints *)
Coercion Z.of_nat : nat >-> Z.

(* helper for the next section to go from nats to ints *)
Lemma Z_plusminus_nat : forall z : Z, 
  (exists n : nat, z = n \/ z = - n)%Z.
Proof. intros. 
       destruct z.
       - exists O; left; easy.
       - exists (Pos.to_nat p); left; lia.
       - exists (Pos.to_nat p); right; lia.
Qed.

Lemma two_val_mult : forall (z1 z2 : Z),
  z1 <> 0 -> z2 <> 0 ->
  two_val (z1 * z2) = two_val z1 + two_val z2.
Proof. intros.
       destruct z1; destruct z2; simpl; try easy.
       all : rewrite two_val_pos_mult; easy.
Qed.
         
(* TODO: should prove this, but don't actually need it. 
Lemma two_val_plus : forall (z1 z2 : Z),
  z1 <> 0 -> z2 <> 0 -> 
  z1 + z2 <> 0 ->
  two_val (z1 + z2) >= Z.min (two_val z1) (two_val z2).
Proof. intros.
       destruct z1; destruct z2; try easy.
*)
       


Lemma two_val_odd_part : forall (z : Z),
  two_val (2 * z + 1) = 0.
Proof. intros. 
       destruct z; auto.
       destruct p; auto.
Qed.

Lemma two_val_even_part : forall (a : Z),
  a >= 0 -> two_val (2 ^ a) = a.
Proof. intros.
       destruct (Z_plusminus_nat a) as [x [H0 | H0]]; subst.
       induction x; auto.
       replace (S x) with (1 + x)%nat by lia.
       rewrite Nat2Z.inj_add, Z.pow_add_r, two_val_mult; try lia.
       rewrite IHx; auto; try lia.
       try (apply (Z.pow_nonzero 2 x); lia).
       induction x; auto.
       replace (S x) with (1 + x)%nat by lia.
       rewrite Nat2Z.inj_add, Z.opp_add_distr, Z.pow_add_r, two_val_mult; try lia.
Qed.

Lemma twoadic_nonzero : forall (a b : Z),
  a >= 0 -> 2^a * (2 * b + 1) <> 0.
Proof. intros. 
       apply Z.neq_mul_0; split; try lia;
       try (apply Z.pow_nonzero; lia).
Qed.

Lemma get_two_val : forall (a b : Z),
  a >= 0 -> 
  two_val (2^a * (2 * b + 1)) = a.
Proof. intros. 
       rewrite two_val_mult; auto.
       rewrite two_val_odd_part, two_val_even_part; try lia.
       apply Z.pow_nonzero; try lia.
       lia.
Qed.       

Lemma odd_part_reduce : forall (a : Z),
  odd_part (2 * a) = odd_part a.
Proof. intros.
       induction a; try easy.
Qed.

Lemma get_odd_part : forall (a b : Z),
  a >= 0 -> 
  odd_part (2^a * (2 * b + 1)) = 2 * b + 1.
Proof. intros. 
       destruct (Z_plusminus_nat a) as [x [H0 | H0]]; subst.
       induction x; try easy.
       - replace (2 ^ 0%nat * (2 * b + 1)) with (2 * b + 1) by lia.
         destruct b; simpl; auto.
         induction p; simpl; easy.
       - replace (2 ^ S x * (2 * b + 1)) with (2 * (2 ^ x * (2 * b + 1))).
         rewrite odd_part_reduce, IHx; try lia.
         replace (S x) with (1 + x)%nat by lia.
         rewrite Nat2Z.inj_add, Z.pow_add_r; try lia.
       - destruct x; try easy.
         replace (2 ^ (- 0%nat) * (2 * b + 1)) with (2 * b + 1) by lia.
         destruct b; simpl; auto.
         induction p; simpl; easy.
Qed.       

Lemma break_into_parts : forall (z : Z),
  z <> 0 -> exists a b, a >= 0 /\ z = (2^a * (2 * b + 1)).
Proof. intros. 
       destruct z; try easy.
       - induction p.
         + exists 0, (Z.pos p); try easy.
         + destruct IHp as [a [b [H0 H1]]]; try easy.
           exists (1 + a), b.
           replace (Z.pos (xO p)) with (2 * Z.pos p) by easy.
           split; try lia.
           rewrite H1, Z.pow_add_r; try lia.
         + exists 0, 0; split; try lia.
       - induction p.
         + exists 0, (Z.neg p - 1); try easy; try lia.
         + destruct IHp as [a [b [H0 H1]]]; try easy.
           exists (1 + a), b.
           replace (Z.neg (xO p)) with (2 * Z.neg p) by easy.
           split; try lia.
           rewrite H1, Z.pow_add_r; try lia.
         + exists 0, (-1); split; try lia.
Qed.

Lemma twoadic_breakdown : forall (z : Z),
  z <> 0 -> z = (2^(two_val z)) * (odd_part z).
Proof. intros. 
       destruct (break_into_parts z) as [a [b [H0 H1]]]; auto.
       rewrite H1, get_two_val, get_odd_part; easy.
Qed.

Lemma odd_part_pos_odd : forall (p : positive),
  (exists p', odd_part_pos p = xI p') \/ (odd_part_pos p = xH).
Proof. intros.
       induction p.
       - left; exists p; easy. 
       - destruct IHp.
         + left. 
           destruct H.
           exists x; simpl; easy.
         + right; simpl; easy.
       - right; easy.
Qed.

Lemma odd_part_0 : forall (z : Z),
  odd_part z = 0 -> z = 0.
Proof. intros.
       destruct z; simpl in *; easy.
Qed.

Lemma odd_part_odd : forall (z : Z),
  z <> 0 -> 
  2 * ((odd_part z - 1) / 2) + 1 = odd_part z.
Proof. intros. 
       rewrite <- (Zdiv.Z_div_exact_full_2 _ 2); try lia.
       destruct z; try easy; simpl;
         destruct (odd_part_pos_odd p).
       - destruct H0; rewrite H0; simpl.
         rewrite Pos2Z.pos_xO, Zmult_comm, Zdiv.Z_mod_mult.
         easy.
       - rewrite H0; easy.
       - destruct H0; rewrite H0; simpl.
         rewrite (Pos2Z.neg_xO (Pos.succ x)), Zmult_comm, Zdiv.Z_mod_mult. 
         easy.
       - rewrite H0; easy. 
Qed.

Lemma two_val_ge_0 : forall (z : Z),
  two_val z >= 0.
Proof. intros. 
       destruct z; simpl; try lia.
       - induction p; try (simpl; lia). 
         replace (two_val_pos p~0) with (1 + two_val_pos p) by easy.
         lia. 
       - induction p; try (simpl; lia). 
         replace (two_val_pos p~0) with (1 + two_val_pos p) by easy.
         lia. 
Qed.
     



(*
 *
 *
 *)


Close Scope Z_scope.


(** proving that sqrt2 is irrational! *)


(* note that the machinery developed in the previous section makes this super easy, 
   although does not generalize for other primes *)
Lemma two_not_square : forall (a b : Z),
  (b <> 0)%Z -> 
  ~ (a*a = b*b*2)%Z.
Proof. intros.  
       unfold not; intros. 
       destruct (Z.eq_dec a 0); try lia. 
       apply (f_equal_gen two_val two_val) in H0; auto.
       do 3 (rewrite two_val_mult in H0; auto); try lia.
       replace (two_val 2) with 1%Z in H0 by easy.
       lia. 
Qed.


Theorem sqrt2_irrational : forall (a b : Z),
  (b <> 0)%Z -> ~ (IZR a = (IZR b) * √ 2).
Proof. intros. 
       apply (two_not_square a b) in H.
       unfold not; intros; apply H.
       apply (f_equal_gen (fun x => x * x) (fun x => x * x)) in H0; auto.
       rewrite Rmult_assoc, (Rmult_comm (√ 2)), Rmult_assoc, 
         sqrt_def, <- Rmult_assoc in H0; try lra.
       repeat rewrite <- mult_IZR in H0.
       apply eq_IZR in H0.
       easy.
Qed.


Corollary one_sqrt2_Rbasis : forall (a b : Z),
  (IZR a) + (IZR b) * √2 = 0 -> 
  (a = 0 /\ b = 0)%Z.
Proof. intros. 
       destruct (Req_dec (IZR b) 0); subst.
       split.
       rewrite H0, Rmult_0_l, Rplus_0_r in H.
       all : try apply eq_IZR; auto.
       apply Rplus_opp_r_uniq in H; symmetry in H.
       assert (H' : b <> 0%Z).
       unfold not; intros; apply H0.
       rewrite H1; auto.
       apply (sqrt2_irrational (-a) b) in H'.
       rewrite Ropp_Ropp_IZR in H'.
       easy.
Qed.



(* Automation *)
Ltac R_field_simplify := repeat field_simplify_eq [pow2_sqrt2 sqrt2_inv].
Ltac R_field := R_field_simplify; easy.

(** * Trigonometry *)

Lemma sin_upper_bound_aux : forall x : R, 0 < x < 1 -> sin x <= x.
Proof.
  intros x H.
  specialize (SIN_bound x) as B.
    destruct (SIN x) as [_ B2]; try lra.
    specialize PI2_1 as PI1. lra.
    unfold sin_ub, sin_approx in *.
    simpl in B2.
    unfold sin_term at 1 in B2.
    simpl in B2.
    unfold Rdiv in B2.
    rewrite Rinv_1, Rmult_1_l, !Rmult_1_r in B2.
    (* Now just need to show that the other terms are negative... *)
    assert (sin_term x 1 + sin_term x 2 + sin_term x 3 + sin_term x 4 <= 0); try lra.
    unfold sin_term.
    remember (INR (fact (2 * 1 + 1))) as d1.
    remember (INR (fact (2 * 2 + 1))) as d2.
    remember (INR (fact (2 * 3 + 1))) as d3.
    remember (INR (fact (2 * 4 + 1))) as d4.
    assert (0 < d1) as L0.
    { subst. apply lt_0_INR. apply lt_O_fact. }
    assert (d1 <= d2) as L1.
    { subst. apply le_INR. apply fact_le. simpl; lia. }
    assert (d2 <= d3) as L2.
    { subst. apply le_INR. apply fact_le. simpl; lia. }
    assert (d3 <= d4) as L3.
    { subst. apply le_INR. apply fact_le. simpl; lia. }
    simpl.    
    ring_simplify.
    assert ( - (x * (x * (x * 1)) / d1) + x * (x * (x * (x * (x * 1)))) / d2 <= 0).
    rewrite Rplus_comm.
    apply Rle_minus.
    field_simplify; try lra.
    assert (x ^ 5 <= x ^ 3).
    { apply Rle_pow_le1; try lra; try lia. }
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
    left. apply Rinv_0_lt_compat. lra.
    apply Rinv_le_contravar; lra.
    unfold Rminus.
    assert (- (x * (x * (x * (x * (x * (x * (x * 1)))))) / d3) +
            x * (x * (x * (x * (x * (x * (x * (x * (x * 1)))))))) / d4 <= 0).
    rewrite Rplus_comm.
    apply Rle_minus.
    field_simplify; try lra.
    assert (x ^ 9 <= x ^ 7).
    { apply Rle_pow_le1; try lra; try lia. }
    apply Rmult_le_compat; try lra.
    apply pow_le; lra.
    left. apply Rinv_0_lt_compat. lra.
    apply Rinv_le_contravar; lra.
    lra.
Qed.

Lemma sin_upper_bound : forall x : R, Rabs (sin x) <= Rabs x.
Proof.
  intros x.  
  specialize (SIN_bound x) as B.
  destruct (Rlt_or_le (Rabs x) 1).
  (* abs(x) > 1 *)
  2:{ apply Rabs_le in B. lra. }
  destruct (Rtotal_order x 0) as [G | [E| L]].
  - (* x < 0 *)
    rewrite (Rabs_left x) in * by lra.
    rewrite (Rabs_left (sin x)).
    2:{ apply sin_lt_0_var; try lra.
        specialize PI2_1 as PI1.
        lra. }
    rewrite <- sin_neg.
    apply sin_upper_bound_aux.
    lra.
  - (* x = 0 *)
    subst. rewrite sin_0. lra.
  - rewrite (Rabs_right x) in * by lra.
    rewrite (Rabs_right (sin x)).
    2:{ apply Rle_ge.
        apply sin_ge_0; try lra.
        specialize PI2_1 as PI1. lra. }
    apply sin_upper_bound_aux; lra.
Qed.    

Hint Rewrite sin_0 sin_PI4 sin_PI2 sin_PI cos_0 cos_PI4 cos_PI2 
             cos_PI sin_neg cos_neg : trig_db.

(** * glb support *) 

Definition is_lower_bound (E:R -> Prop) (m:R) := forall x:R, E x -> m <= x.

Definition bounded_below (E:R -> Prop) := exists m : R, is_lower_bound E m.

Definition is_glb (E:R -> Prop) (m:R) :=
  is_lower_bound E m /\ (forall b:R, is_lower_bound E b -> b <= m).

Definition neg_Rset (E : R -> Prop) :=
  fun r => E (-r).

Lemma lb_negset_ub : forall (E : R -> Prop) (b : R),
  is_lower_bound E b <-> is_upper_bound (neg_Rset E) (-b).
Proof. unfold is_lower_bound, is_upper_bound, neg_Rset; split; intros.
       - apply H in H0; lra. 
       - rewrite <- Ropp_involutive in H0. 
         apply H in H0; lra.
Qed.

Lemma ub_negset_lb : forall (E : R -> Prop) (b : R),
  is_upper_bound E b <-> is_lower_bound (neg_Rset E) (-b).
Proof. unfold is_lower_bound, is_upper_bound, neg_Rset; split; intros.
       - apply H in H0; lra. 
       - rewrite <- Ropp_involutive in H0. 
         apply H in H0; lra.
Qed.

Lemma negset_bounded_above : forall (E : R -> Prop),
  bounded_below E -> (bound (neg_Rset E)).
Proof. intros. 
       destruct H.
       exists (-x).
       apply lb_negset_ub; easy.
Qed.

Lemma negset_glb : forall (E : R -> Prop) (m : R),
  is_lub (neg_Rset E) m -> is_glb E (-m).
Proof. intros.  
       destruct H; split. 
       - apply lb_negset_ub.
         rewrite Ropp_involutive; easy. 
       - intros. 
         apply lb_negset_ub in H1.
           apply H0 in H1; lra.
Qed.

Lemma glb_completeness :
  forall E:R -> Prop,
    bounded_below E -> (exists x : R, E x) -> { m:R | is_glb E m }.
Proof. intros.  
       apply negset_bounded_above in H.
       assert (H' : exists x : R, (neg_Rset E) x).
       { destruct H0; exists (-x).
         unfold neg_Rset; rewrite Ropp_involutive; easy. }
       apply completeness in H'; auto.
       destruct H' as [m [H1 H2] ].
       exists (-m).
       apply negset_glb; easy.
Qed.



(** * Showing that R is a field, and a vector space over itself *)

Global Program Instance R_is_monoid : Monoid R := 
  { Gzero := 0
  ; Gplus := Rplus
  }.
Solve All Obligations with program_simpl; try lra.

Global Program Instance R_is_group : Group R :=
  { Gopp := Ropp }.
Solve All Obligations with program_simpl; try lra.

Global Program Instance R_is_comm_group : Comm_Group R.
Solve All Obligations with program_simpl; lra. 

Global Program Instance R_is_ring : Ring R :=
  { Gone := 1
  ; Gmult := Rmult
  }.
Solve All Obligations with program_simpl; try lra. 
Next Obligation. try apply Req_EM_T. Qed.


Global Program Instance R_is_comm_ring : Comm_Ring R.
Solve All Obligations with program_simpl; lra. 
                                                     
Global Program Instance R_is_field : Field R :=
  { Ginv := Rinv }.
Next Obligation. 
  rewrite Rinv_r; easy.
Qed.

Global Program Instance R_is_module_space : Module_Space R R :=
  { Vscale := Rmult }.
Solve All Obligations with program_simpl; lra. 


Global Program Instance R_is_vector_space : Vector_Space R R.  



(** * some big_sum lemmas specific to R *)

Lemma Rsum_le : forall (f g : nat -> R) (n : nat),
  (forall i, (i < n)%nat -> f i <= g i) ->
  (big_sum f n) <= (big_sum g n).
Proof. induction n as [| n']; simpl; try lra.  
       intros.
       apply Rplus_le_compat.
       apply IHn'; intros. 
       all : apply H; try lia. 
Qed.

Lemma Rsum_ge_0 : forall (f : nat -> R) (n : nat),
  (forall i, (i < n)%nat -> 0 <= f i) ->
  0 <= big_sum f n.
Proof. induction n as [| n'].
       - intros; simpl; lra. 
       - intros. simpl; apply Rplus_le_le_0_compat.
         apply IHn'; intros; apply H; lia. 
         apply H; lia. 
Qed.
