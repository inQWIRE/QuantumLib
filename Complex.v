(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either 
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.

---------------------------------------------------------------

This version modified to work without SSReflect,
or any other dependencies, as part of the QWIRE project
by Robert Rand and Jennifer Paykin (June 2017).

---------------------------------------------------------------

Additional lemmas added as part of work on projects in inQWIRE 
(https://github.com/inQWIRE) 2019-2021.
*)

Require Export Prelim. 
Require Export RealAux.
Require Export Summation. 

(** This file defines complex numbers [C] as [R * R]. Operations are
given, and [C] is proved to be a field, a normed module, and a
complete space. *)

(** * The set of complex numbers *)

Definition C := (R * R)%type.

Declare Scope C_scope.
Delimit Scope C_scope with C.
 
Open Scope nat_scope.
Open Scope R_scope.
Open Scope C_scope.
Bind Scope nat_scope with nat.
Bind Scope R_scope with R.
Bind Scope C_scope with C.

Definition RtoC (x : R) : C := (x,0).
Coercion RtoC : R >-> C.

Lemma RtoC_inj : forall (x y : R),
  RtoC x = RtoC y -> x = y.
Proof.
  intros x y H.
  now apply (f_equal (@fst R R)) in H.
Qed.

Lemma Ceq_dec (z1 z2 : C) : { z1 = z2 } + { z1 <> z2 }.
Proof.
  destruct z1 as [x1 y1].
  destruct z2 as [x2 y2].
  destruct (Req_EM_T x1 x2) as [Eqx | Neqx]; [| right; congruence].
  destruct (Req_EM_T y1 y2) as [Eqy | Neqy]; [subst; auto | right; congruence].
Qed.

(* lca, a great tactic for solving computations or basic equality checking *)
Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

(* essentially, we just bootsrap coq's lra *)
Ltac lca := eapply c_proj_eq; simpl; lra.


(** ** Constants and usual functions *)

(** 0 and 1 for complex are defined as [RtoC 0] and [RtoC 1] *)
Definition Ci : C := (0,1).
Notation C0 := (RtoC 0). 
Notation C1 := (RtoC 1).
Notation C2 := (RtoC 2).

(** *** Arithmetic operations *)

Definition Cplus (x y : C) : C := (fst x + fst y, snd x + snd y).
Definition Copp (x : C) : C := (-fst x, -snd x).
Definition Cminus (x y : C) : C := Cplus x (Copp y).
Definition Cmult (x y : C) : C := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
Definition Cinv (x : C) : C := (fst x / (fst x ^ 2 + snd x ^ 2), - snd x / (fst x ^ 2 + snd x ^ 2)).
Definition Cdiv (x y : C) : C := Cmult x (Cinv y).

(* Added exponentiation *)
Fixpoint Cpow (c : C) (n : nat) : C :=  
  match n with
  | 0%nat => 1
  | S n' => Cmult c (Cpow c n')
  end.


Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.
Infix "^" := Cpow : C_scope.

(** * Showing that C is a field, and a vector space over itself *)
            
Global Program Instance C_is_monoid : Monoid C := 
  { Gzero := C0
  ; Gplus := Cplus
  }.
Solve All Obligations with program_simpl; try lca.

Global Program Instance C_is_group : Group C :=
  { Gopp := Copp }.
Solve All Obligations with program_simpl; try lca.
        
Global Program Instance C_is_comm_group : Comm_Group C.
Solve All Obligations with program_simpl; lca. 
                                             
Global Program Instance C_is_ring : Ring C :=
  { Gone := C1
  ; Gmult := Cmult
  }.
Solve All Obligations with program_simpl; try lca; apply Ceq_dec. 

Global Program Instance C_is_comm_ring : Comm_Ring C.
Solve All Obligations with program_simpl; lca. 

Global Program Instance C_is_field : Field C :=
  { Ginv := Cinv }.
Next Obligation.
  assert (H := R1_neq_R0).
  contradict H.  
  apply (f_equal_gen fst fst) in H; simpl in H; easy. 
Qed.
Next Obligation.
  apply injective_projections ; simpl ; field; 
  contradict H; apply Rplus_sqr_eq_0 in H;
  apply injective_projections ; simpl ; apply H.
Qed.

Global Program Instance C_is_module_space : Module_Space C C :=
  { Vscale := Cmult }.
Solve All Obligations with program_simpl; lca. 

Global Program Instance C_is_vector_space : Vector_Space C C.



(** *** Other usual functions *)

Definition Re (z : C) : R := fst z.

Definition Im (z : C) : R := snd z.

Definition Cmod (x : C) : R := sqrt (fst x ^ 2 + snd x ^ 2).

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).

Notation "a ^*" := (Cconj a) (at level 10) : C_scope.

Lemma Cmod_0 : Cmod 0 = R0.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l, Rplus_0_l.
apply sqrt_0.
Qed.

Lemma Cmod_1 : Cmod 1 = R1.
Proof.
unfold Cmod.
simpl.
rewrite Rmult_0_l, Rplus_0_r, 2!Rmult_1_l.
apply sqrt_1.
Qed.

Lemma Cmod_opp : forall x, Cmod (-x) = Cmod x.
Proof.
unfold Cmod.
simpl.
intros x.
apply f_equal.
ring.
Qed.

Lemma Cmod_triangle : forall x y, Cmod (x + y) <= Cmod x + Cmod y.
Proof.
  intros x y ; unfold Cmod.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr ; simpl ; ring_simplify.
  unfold pow. 
  rewrite ?Rmult_1_r.
  rewrite ?sqrt_sqrt ; ring_simplify.
  replace (-2 * fst x * fst y - 2 * snd x * snd y)%R with (- (2 * (fst x * fst y + snd x * snd y)))%R by ring.
  rewrite Rmult_assoc, <- sqrt_mult.
  rewrite Rplus_comm.
  apply -> Rminus_le_0.
  apply Rmult_le_compat_l.
  apply Rlt_le, Rlt_0_2.
  apply Rsqr_incr_0_var.
  apply Rminus_le_0.
  unfold Rsqr; rewrite ?sqrt_sqrt ; ring_simplify.
  replace (fst x ^ 2 * snd y ^ 2 - 2 * fst x * snd x * fst y * snd y +
    snd x ^ 2 * fst y ^ 2)%R with ( (fst x * snd y - snd x * fst y)^2)%R
    by ring.
  apply pow2_ge_0.
  repeat apply Rplus_le_le_0_compat ; apply Rmult_le_pos ; apply pow2_ge_0.
  apply sqrt_pos.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  replace (fst x ^ 2 + 2 * fst x * fst y + fst y ^ 2 + snd x ^ 2 + 2 * snd x * snd y + snd y ^ 2)%R
    with ((fst x + fst y)^2 + (snd x + snd y)^2)%R by ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply sqrt_pos.
Qed.

Lemma Cmod_mult : forall x y, Cmod (x * y) = (Cmod x * Cmod y)%R.
Proof.
  intros x y.
  unfold Cmod.
  rewrite <- sqrt_mult.
  apply f_equal ; simpl ; ring.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
  apply Rplus_le_le_0_compat ; apply pow2_ge_0.
Qed.

Lemma Rmax_Cmod : forall x,
  Rmax (Rabs (fst x)) (Rabs (snd x)) <= Cmod x.
Proof.
  intros [x y]; simpl.
  rewrite <- !sqrt_Rsqr_abs.
  apply Rmax_case ; apply sqrt_le_1_alt, Rminus_le_0 ;
  unfold Rsqr; simpl ; ring_simplify ; try apply pow2_ge_0; auto.
Qed.

Lemma Cmod_2Rmax : forall x,
  Cmod x <= sqrt 2 * Rmax (Rabs (fst x)) (Rabs (snd x)).
Proof.
  intros [x y]; apply Rmax_case_strong; intros H0;
  rewrite <- !sqrt_Rsqr_abs ;
  rewrite <- ?sqrt_mult ;
  try (apply Rle_0_sqr; auto);
  try (apply Rlt_le, Rlt_0_2; auto) ;
  apply sqrt_le_1_alt ; simpl ; [ rewrite Rplus_comm | ] ;
  unfold Rsqr ; apply Rle_minus_r ; ring_simplify ;
  apply Rsqr_le_abs_1 in H0 ; unfold pow; rewrite !Rmult_1_r; auto.
Qed.

Lemma Cmod_ge_fst z : 
  fst z <= Cmod z.
Proof.
  unfold Cmod.
  apply sqrt_ge.
  pose proof (pow2_ge_0 (snd z)).
  lra.
Qed.

Lemma Cmod_ge_snd z : 
  snd z <= Cmod z.
Proof.
  unfold Cmod.
  apply sqrt_ge.
  pose proof (pow2_ge_0 (fst z)).
  lra.
Qed.

Lemma Cmod_ge_abs_fst z : 
  Rabs (fst z) <= Cmod z.
Proof.
  unfold Cmod.
  apply sqrt_ge_abs.
  pose proof (pow2_ge_0 (snd z)).
  lra.
Qed.

Lemma Cmod_ge_abs_snd z : 
  Rabs (snd z) <= Cmod z.
Proof.
  unfold Cmod.
  apply sqrt_ge_abs.
  pose proof (pow2_ge_0 (fst z)).
  lra.
Qed.

Lemma Cmod_plus_fst_ge_0 z : 
  0 <= Cmod z + fst z.
Proof.
  rewrite Rplus_comm.
  apply Rplus_ge_0_of_ge_Rabs.
  apply Cmod_ge_abs_fst.
Qed.

Lemma Cmod_plus_snd_ge_0 z : 
  0 <= Cmod z + snd z.
Proof.
  rewrite Rplus_comm.
  apply Rplus_ge_0_of_ge_Rabs.
  apply Cmod_ge_abs_snd.
Qed.

Lemma C_neq_iff : forall c d : C, c <> d <-> (fst c <> fst d \/ snd c <> snd d).
Proof.
  intros [cr ci] [dr di].
  split.
  - intros Hne.
    destruct (Req_dec cr dr); [|now left].
    destruct (Req_dec ci di); [|now right].
    subst; easy.
  - simpl.
    intros []; congruence.
Qed.

Lemma C_neq_0 : forall c : C, c <> 0 -> (fst c) <> 0 \/ (snd c) <> 0.
Proof.
  intros c.
  apply C_neq_iff.
Qed.

Lemma Cinv_0 : / 0 = 0.
Proof.
  lca.
Qed.

Lemma Cdiv_0_r z : z / 0 = 0.
Proof.
  lca.
Qed.

(* some lemmas to help simplify addition/multiplication scenarios *)
Lemma Cplus_simplify : forall (a b c d : C),
    a = b -> c = d -> (a + c = b + d)%C.
Proof. intros. 
       rewrite H, H0; easy.
Qed.

Lemma Cmult_simplify : forall (a b c d : C),
    a = b -> c = d -> (a * c = b * d)%C.
Proof. intros. 
       rewrite H, H0; easy.
Qed.

(** ** C is a field *)

Lemma RtoC_plus (x y : R) : RtoC (x + y) = RtoC x + RtoC y.
Proof.
  unfold RtoC, Cplus ; simpl.
  rewrite Rplus_0_r; auto.
Qed.

Lemma RtoC_opp (x : R) : RtoC (- x) = - RtoC x.
Proof.
  unfold RtoC, Copp ; simpl.
  rewrite Ropp_0; auto.
Qed.

Lemma RtoC_minus (x y : R) : RtoC (x - y) = RtoC x - RtoC y.
Proof. unfold Cminus; rewrite <- RtoC_opp, <- RtoC_plus; auto. Qed.

Lemma RtoC_mult (x y : R) : RtoC (x * y) = RtoC x * RtoC y.
Proof.
  unfold RtoC, Cmult ; simpl.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma RtoC_inv (x : R) : RtoC (/ x) = / RtoC x.
Proof. destruct (Req_dec x 0).
  - subst; now rewrite Cinv_0, Rinv_0.
  - apply injective_projections ; simpl ; field ; auto. 
Qed.

Lemma RtoC_div (x y : R) : RtoC (x / y) = RtoC x / RtoC y.
Proof. destruct (Req_dec y 0).
  - subst; unfold Rdiv; now rewrite Cdiv_0_r, Rinv_0, Rmult_0_r.
  - apply injective_projections ; simpl ; field ; auto. 
Qed.

Lemma Cplus_comm (x y : C) : x + y = y + x.
Proof. apply injective_projections ; simpl ; apply Rplus_comm. Qed.

Lemma Cplus_assoc (x y z : C) : x + (y + z) = (x + y) + z.
Proof. apply injective_projections ; simpl ; apply sym_eq, Rplus_assoc. Qed.

Lemma Cplus_0_r (x : C) : x + 0 = x.
Proof. apply injective_projections ; simpl ; apply Rplus_0_r. Qed.

Lemma Cplus_0_l (x : C) : 0 + x = x.
Proof. apply injective_projections ; simpl ; apply Rplus_0_l. Qed.

Lemma Cplus_opp_r (x : C) : x + -x = 0.
Proof. apply injective_projections ; simpl ; apply Rplus_opp_r. Qed.

Lemma Copp_plus_distr (z1 z2 : C) : - (z1 + z2) = (- z1 + - z2).
Proof. apply injective_projections ; apply Ropp_plus_distr; auto. Qed.

Lemma Copp_minus_distr (z1 z2 : C) : - (z1 - z2) = z2 - z1.
Proof. apply injective_projections ; apply Ropp_minus_distr; auto. Qed.

Lemma Cmult_comm (x y : C) : x * y = y * x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_assoc (x y z : C) : x * (y * z) = (x * y) * z.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_0_r (x : C) : x * 0 = 0.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_0_l (x : C) : 0 * x = 0.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_1_r (x : C) : x * 1 = x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cmult_1_l (x : C) : 1 * x = x.
Proof. apply injective_projections ; simpl ; ring. Qed.

Lemma Cinv_r (r : C) : r <> 0 -> r * /r = 1.
Proof.
  intros H.
  apply injective_projections ; simpl ; field.
  contradict H.
  apply Rplus_sqr_eq_0 in H.
  apply injective_projections ; simpl ; apply H.
  contradict H.
  apply Rplus_sqr_eq_0 in H.
  apply injective_projections ; simpl ; apply H.
Qed.

Lemma Cinv_l (r : C) : r <> 0 -> /r * r = 1.
Proof.
intros Zr.
rewrite Cmult_comm.
now apply Cinv_r.
Qed.

Lemma Cdiv_mult_r (c d : C) : d <> 0%R ->
  c / d * d = c.
Proof.
  intros.
  unfold Cdiv.
  rewrite <- Cmult_assoc, Cinv_l by easy.
  apply Cmult_1_r.
Qed.

Lemma Cdiv_mult_l (c d : C) : d <> 0%R ->
  d * c / d = c.
Proof.
  intros.
  unfold Cdiv.
  rewrite (Cmult_comm d c), <- Cmult_assoc, (Cmult_comm d), Cmult_assoc.
  apply Cdiv_mult_r.
  easy.
Qed.

Lemma Cdiv_mult_l' (c d : C) : d <> 0%R ->
  d * (c / d) = c.
Proof.
  intros.
  rewrite Cmult_comm.
  apply Cdiv_mult_r.
  easy.
Qed.

Lemma Cdiv_1_r : forall c, c / C1 = c.
Proof. intros. lca. Qed.

Lemma Cmult_plus_distr_l (x y z : C) : x * (y + z) = x * y + x * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma Cmult_plus_distr_r (x y z : C) : (x + y) * z = x * z + y * z.
Proof.
  apply injective_projections ; simpl ; ring.
Qed.

Lemma Copp_0 : Copp 0 = 0.
Proof. apply injective_projections; simpl ; ring. Qed.

Lemma Cmod_m1 : Cmod (Copp 1) = 1.
Proof. rewrite Cmod_opp. apply Cmod_1. Qed.

Lemma Cmod_eq_0 : forall x, Cmod x = 0 -> x = 0.
Proof.
  intros x H.
  unfold Cmod, pow in H.
  rewrite 2!Rmult_1_r, <- sqrt_0 in H.
  apply sqrt_inj in H.
  apply Rplus_sqr_eq_0 in H.
  now apply injective_projections.
  apply Rplus_le_le_0_compat ; apply Rle_0_sqr.
  apply Rle_refl.
Qed.

Lemma Cmod_ge_0 : forall x, 0 <= Cmod x.
Proof.
  intros x.
  apply sqrt_pos.
Qed.

Lemma Cmod_gt_0 :
  forall (x : C), x <> 0 <-> 0 < Cmod x.
Proof.
  intros x ; split; intro Hx.
  destruct (Cmod_ge_0 x); auto.
  apply sym_eq, Cmod_eq_0 in H. tauto.
  contradict Hx.
  apply Rle_not_lt, Req_le.
  rewrite Hx, Cmod_0; auto.
Qed.

Lemma Cmod_R : forall x : R, Cmod x = Rabs x.
Proof.
  intros x.
  unfold Cmod.
  simpl.
  rewrite Rmult_0_l, Rplus_0_r, Rmult_1_r.
  apply sqrt_Rsqr_abs.
Qed.

Lemma Cmod_inv : forall x : C, x <> 0 -> Cmod (/ x) = Rinv (Cmod x).
Proof.
  intros x Zx.
  apply Rmult_eq_reg_l with (Cmod x).
  rewrite <- Cmod_mult.
  rewrite Rinv_r.
  rewrite Cinv_r.
  rewrite Cmod_R.
  apply Rabs_R1.
  exact Zx.
  contradict Zx.
  now apply Cmod_eq_0.
  contradict Zx.
  now apply Cmod_eq_0.
Qed.

Lemma Cmod_div (x y : C) : y <> 0 -> Cmod (x / y) = Rdiv (Cmod x) (Cmod y).
Proof.
  intro Hy.
  unfold Cdiv.
  rewrite Cmod_mult.
  rewrite Cmod_inv; auto.
Qed.

Lemma Cmod_real : forall (c : C), 
  fst c >= 0 -> snd c = 0 -> Cmod c = fst c. 
Proof. intros. 
       unfold Cmod. 
       rewrite H0.
       simpl. 
       autorewrite with R_db.
       apply sqrt_square.
       lra. 
Qed.

Lemma Cmod_eq_0_iff x : Cmod x = 0 <-> x = 0.
Proof.
  split; [apply Cmod_eq_0|intros ->; apply Cmod_0].
Qed.

Lemma Cmod_eq_C0_iff x : @eq C (Cmod x) 0 <-> x = 0.
Proof.
  split; [intros H; apply Cmod_eq_0
  |intros ->; now rewrite Cmod_0].
  apply (f_equal fst) in H.
  apply H.
Qed.

Lemma Cmod_real_abs z : snd z = 0 -> Cmod z = Rabs (fst z).
Proof.
  intros Hreal.
  unfold Cmod.
  rewrite Hreal.
  rewrite Rpow_0_l, Rplus_0_r by easy.
  rewrite <- pow2_abs.
  now rewrite sqrt_pow2 by (apply Rabs_pos).
Qed.

Lemma Cmult_neq_0 (z1 z2 : C) : z1 <> 0 -> z2 <> 0 -> z1 * z2 <> 0.
Proof.
  intros Hz1 Hz2 Hz.
  assert (Cmod (z1 * z2) = 0).
  rewrite Hz, Cmod_0; auto.
  rewrite Cmod_mult in H.
  apply Rmult_integral in H ; destruct H.
  now apply Hz1, Cmod_eq_0.
  now apply Hz2, Cmod_eq_0.
Qed.

Lemma Cmult_integral : forall c1 c2 : C, c1 * c2 = 0 -> c1 = 0 \/ c2 = 0.
Proof. intros. 
       destruct (Ceq_dec c1 0); try (left; easy).
       destruct (Ceq_dec c2 0); try (right; easy).
       apply (Cmult_neq_0 c1 c2) in n0; auto.
       easy. 
Qed.

Lemma Cmult_integral_iff (a b : C) : 
  a * b = 0 <-> (a = 0 \/ b = 0).
Proof.
  split; [apply Cmult_integral|].
  intros [-> | ->]; lca.
Qed.

Lemma Cminus_eq_contra : forall r1 r2 : C, r1 <> r2 -> r1 - r2 <> 0.
Proof.
  intros ; contradict H ; apply injective_projections ;
  apply Rminus_diag_uniq.
  now apply (f_equal (@fst R R)) in H.
  now apply (f_equal (@snd R R)) in H.
Qed.

Lemma Cminus_diag : forall r1 r2, r1 = r2 -> r1 - r2 = C0.
Proof. intros; subst; lca. 
Qed.


Lemma Cminus_eq_0 : forall r1 r2 : C, r1 - r2 = C0 -> r1 = r2.
Proof. intros.
       apply injective_projections; 
         apply Rminus_diag_uniq. 
       now apply (f_equal (@fst R R)) in H.
       now apply (f_equal (@snd R R)) in H.
Qed.


Lemma Cmult_cancel_l : forall a c1 c2 : C,
  a <> C0 ->
  a * c1 = a * c2 -> c1 = c2.
Proof. intros. 
       apply (f_equal_gen (Cmult (/ a)) (Cmult (/ a))) in H0; auto.
       do 2 rewrite Cmult_assoc in H0.
       rewrite Cinv_l in H0; auto.
       do 2 rewrite Cmult_1_l in H0.
       easy.
Qed.

Lemma Cmult_cancel_r : forall a c1 c2 : C,
  a <> C0 ->
  c1 * a = c2 * a -> c1 = c2.
Proof. intros. 
       apply (Cmult_cancel_l a); auto.
       rewrite Cmult_comm, H0; lca.
Qed.


Lemma C_field_theory : field_theory (RtoC 0) (RtoC 1) Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof. apply (@G_field_theory C _ _ _ _ _ C_is_field). Qed.

Add Field C_field_field : C_field_theory.


(** * Content added as part of inQWIRE  **)


Lemma Ci2 : Ci * Ci = -C1. Proof. lca. Qed.
Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros; lca. Qed.
Lemma Cdouble : forall c : C, 2 * c = c + c. Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.

Lemma C0_imp : forall c : C, c <> 0 -> (fst c <> 0 \/ snd c <> 0)%R.  
Proof. intros c H. destruct c. simpl.
       destruct (Req_EM_T r 0), (Req_EM_T r0 0); subst; intuition. Qed.
Lemma C0_fst_neq : forall (c : C), fst c <> 0 -> c <> 0. 
Proof. intros c. intros N E. apply N. rewrite E. reflexivity. Qed.
Lemma C0_snd_neq : forall (c : C), snd c <> 0 -> c <> 0. 
Proof. intros c. intros N E. apply N. rewrite E. reflexivity. Qed.
Lemma RtoC_neq : forall (r : R), r <> 0 -> RtoC r <> 0. 
Proof. intros. apply C0_fst_neq. easy. Qed.

(** Other useful facts *)

Lemma Cmult_if_l (b : bool) (c d : C) : 
  (if b then c else 0%R) * d = 
  if b then c * d else 0%R.
Proof.
  destruct b; lca.
Qed.

Lemma Cmult_if_r (b : bool) (c d : C) : 
  d * (if b then c else 0%R) = 
  if b then d * c else 0%R.
Proof.
  destruct b; lca.
Qed.

Lemma Cmult_if_andb (b c : bool) (x y : C) : 
  (if b then x else 0%R) * (if c then y else 0%R) = 
  if b && c then x * y else 0%R.
Proof.
  destruct b,c; lca.
Qed.

Lemma Cmult_if_1_l (b : bool) (d : C) : 
  (if b then C1 else 0%R) * d = 
  if b then d else 0%R.
Proof.
  destruct b; lca.
Qed.

Lemma Cmult_if_1_r (b : bool) (d : C) : 
  d * (if b then C1 else 0%R) = 
  if b then d else 0%R.
Proof.
  destruct b; lca.
Qed.

Lemma Cmult_if_if_1_l (b c : bool) (x : C) : 
  (if b then C1 else 0%R) * (if c then x else 0%R) = 
  if b && c then x else 0%R.
Proof.
  destruct b; lca.
Qed.

Lemma Cmult_if_if_1_r (b c : bool) (x : C) : 
  (if b then x else 0%R) * (if c then C1 else 0%R) = 
  if b && c then x else 0%R.
Proof.
  destruct b,c; lca.
Qed.

Lemma Copp_neq_0_compat: forall c : C, c <> 0 -> (- c)%C <> 0.
Proof.
 intros c H.
 apply C0_imp in H as [H | H].
 apply C0_fst_neq.
 apply Ropp_neq_0_compat.
 assumption.
 apply C0_snd_neq.
 apply Ropp_neq_0_compat.
 assumption.
Qed.

Lemma C1_neq_C0 : C1 <> C0.
Proof. apply C0_fst_neq.
       simpl. 
       apply R1_neq_R0.
Qed.

Lemma C1_nonzero : C1 <> 0.
Proof.
  apply RtoC_neq.
  lra.
Qed.

Lemma C2_nonzero : C2 <> 0.
Proof.
  apply RtoC_neq.
  lra.
Qed.

Lemma Cconj_neq_0 : forall c : C, c <> 0 -> c^* <> 0.
Proof.
  intros.
  unfold Cconj.
  apply C_neq_0 in H.
  destruct H.
  - apply C0_fst_neq.
    simpl.
    assumption.
  - apply C0_snd_neq.
    simpl.
    apply Ropp_neq_0_compat.
    assumption.
Qed.

Lemma nonzero_div_nonzero : forall c : C, c <> C0 -> / c <> C0.
Proof. intros. 
       unfold not; intros. 
        assert (H' : (c * (/ c) = c * C0)%C). 
        { rewrite H0; easy. } 
        rewrite Cinv_r in H'; try easy.
        rewrite Cmult_0_r in H'.
        apply C1_neq_C0; easy.
Qed.

Lemma Cinv_eq_0_iff (a : C) : / a = C0 <-> a = 0.
Proof.
  split.
  - destruct (Ceq_dec a C0) as [? | H%nonzero_div_nonzero]; easy.
  - intros ->.
    lca.
Qed.

Lemma Cdiv_integral_iff (a b : C) : 
  a / b = C0 <-> (a = C0 \/ b = C0).
Proof.
  unfold Cdiv.
  rewrite Cmult_integral_iff, Cinv_eq_0_iff.
  reflexivity.
Qed.

Lemma Cdiv_integral (a b : C) : 
  a / b = C0 -> (a = C0 \/ b = C0).
Proof.
  rewrite Cdiv_integral_iff.
  easy.
Qed.

Lemma Cdiv_integral_dec (a b : C) : 
  a / b = C0 -> ({a = C0} + {b = C0}).
Proof.
  intros H%Cdiv_integral.
  destruct (Ceq_dec a 0); [now left |].
  destruct (Ceq_dec b 0); [now right |].
  exfalso.
  destruct H; easy.
Defined.

Lemma Cdiv_nonzero (c d : C) : c <> 0%R -> d <> 0%R ->
  c / d <> 0%R.
Proof.
  intros Hc Hd Hf; apply Hc.
  apply (f_equal (Cmult d)) in Hf.
  rewrite Cdiv_mult_l' in Hf; [|easy].
  rewrite Hf.
  lca.
Qed.

Lemma div_real : forall (c : C),
  snd c = 0 -> snd (/ c) = 0.
Proof. intros. 
       unfold Cinv. 
       simpl. 
       rewrite H. lra. 
Qed.

Lemma eq_neg_implies_0 : forall (c : C), 
  (-C1 * c)%C = c -> c = C0.
Proof.  intros. 
        assert (H' : (- C1 * c + c = c + c)%C).
        { rewrite H; easy. }
        assert (H'' : (- C1 * c + c = C0)%C).
        { lca. }
        rewrite H'' in H'.
        assert (H0 : (c + c = C2 * c)%C). lca.  
        rewrite H0 in H'. 
        destruct (Ceq_dec c C0); try easy.
        assert (H1 : C2 <> C0).
        apply C0_fst_neq.
        simpl. lra. 
        assert (H2 : (C2 * c)%C <> C0).
        apply Cmult_neq_0; try easy.
        rewrite <- H' in H2. easy.
Qed.

Lemma Cinv_mult_distr : forall c1 c2 : C, / (c1 * c2) = / c1 * / c2.
Proof.
  intros.
  destruct (Ceq_dec c1 0) as [?|H]; 
    [subst; now rewrite Cmult_0_l, !Cinv_0, Cmult_0_l|].
  destruct (Ceq_dec c2 0) as [?|H0]; 
    [subst; now rewrite Cmult_0_r, !Cinv_0, Cmult_0_r|].
  apply c_proj_eq.
  - simpl.
    repeat rewrite Rmult_1_r.
    rewrite Rmult_div.
    rewrite Rmult_div.
    rewrite Rmult_opp_opp.
    unfold Rminus.
    rewrite <- Ropp_div.
    rewrite <- Rdiv_plus_distr.
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_l.
    apply Rdiv_cancel.
    lra.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
  - simpl.    
    repeat rewrite Rmult_1_r.
    rewrite Rmult_div.
    rewrite Rmult_div.
    unfold Rminus.
    rewrite <- Rdiv_plus_distr.
    repeat rewrite Rmult_plus_distr_r.
    repeat rewrite Rmult_plus_distr_l.
    repeat rewrite <- Ropp_mult_distr_r.
    repeat rewrite <- Ropp_mult_distr_l.
    repeat rewrite <- Ropp_plus_distr.
    apply Rdiv_cancel.
    lra.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
    * apply Rsum_nonzero. apply C0_imp in H. assumption.
    * apply Rsum_nonzero. apply C0_imp in H0. assumption.
Qed.


Lemma Cinv_inv : forall c : C, / / c = c.
Proof. 
  intros.
  destruct (Ceq_dec c C0).
  - subst. now rewrite 2!Cinv_0.
  - apply (Cmult_cancel_l (/ c)).
    apply nonzero_div_nonzero; auto.
    rewrite Cinv_l, Cinv_r; auto.
    apply nonzero_div_nonzero; auto.
Qed.

Lemma Cconj_eq_implies_real : forall c : C, c = Cconj c -> snd c = 0%R.
Proof. intros. 
       unfold Cconj in H.
       apply (f_equal snd) in H.
       simpl in H.
       assert (H' : (2 * snd c = 0)%R).
       replace (2 * snd c)%R with (snd c + (- snd c))%R by lra.
       lra.
       replace (snd c) with (/2 * (2 * snd c))%R by lra.
       rewrite H'; lra.
Qed.

(** * some C big_sum specific lemmas *)

Lemma times_n_C : forall n (c : C), 
  times_n c n = c * INR n.
Proof.
  intros n c.
  induction n; [lca|].
  cbn [times_n].
  rewrite S_INR, IHn.
  lca.
Qed.


Local Open Scope nat_scope. 

Lemma Rsum_big_sum : forall n (f : nat -> R),
  fst (big_sum (fun i => RtoC (f i)) n) = big_sum f n.
Proof.
  intros. induction n.
  - easy.
  - simpl. rewrite IHn.
    easy. 
Qed.

Lemma Re_big_sum (n : nat) (f : nat -> C) : 
  fst (big_sum (fun i => f i) n) = big_sum (fun i => fst (f i)) n.
Proof.
  induction n; [easy|].
  simpl; f_equal; easy.
Qed. 

Lemma Im_big_sum (n : nat) (f : nat -> C) : 
  snd (big_sum (fun i => f i) n) = big_sum (fun i => snd (f i)) n.
Proof.
  induction n; [easy|].
  simpl; f_equal; easy.
Qed.

Lemma big_sum_real n (f : nat -> C)
  (Hf : forall i, (i < n)%nat -> snd (f i) = 0%R) :
  big_sum f n = big_sum (fun i => fst (f i)) n.
Proof.
  rewrite (big_sum_eq_bounded _ (fun i => RtoC (fst (f i)))).
  - apply c_proj_eq.
    + rewrite Rsum_big_sum; easy.
    + rewrite Im_big_sum.
      simpl.
      clear Hf.
      induction n; [easy|].
      simpl; lra.
  - intros i Hi.
    apply c_proj_eq; [easy|]. 
    apply Hf; easy.
Qed.

(* TODO: these should all probably have better names *)
Lemma big_sum_rearrange : forall (n : nat) (f g : nat -> nat -> C),
  (forall x y, x <= y -> f x y = (-C1) * (g (S y) x))%G ->
  (forall x y, y <= x -> f (S x) y = (-C1) * (g y x))%G ->
  big_sum (fun i => big_sum (fun j => f i j) n) (S n) = 
  (-C1 * (big_sum (fun i => big_sum (fun j => g i j) n) (S n)))%G.
Proof. induction n as [| n'].
       - intros. lca. 
       - intros. 
         do 2 rewrite big_sum_extend_double.
         rewrite (IHn' f g); try easy.
         repeat rewrite Cmult_plus_distr_l.
         repeat rewrite <- Cplus_assoc.
         apply Cplus_simplify; try easy.
         assert (H' : forall a b c, (a + (b + c) = (a + c) + b)%G). 
         intros. lca. 
         do 2 rewrite H'.
         rewrite <- Cmult_plus_distr_l.
         do 2 rewrite (@big_sum_extend_r C C_is_monoid). 
         do 2 rewrite (@big_sum_mult_l C _ _ _ C_is_ring).  
         rewrite Cplus_comm.
         apply Cplus_simplify.
         all : apply big_sum_eq_bounded; intros. 
         apply H; lia. 
         apply H0; lia. 
Qed.

Local Close Scope nat_scope.

Lemma big_sum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> (0 <= fst (big_sum f n))%R.
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.

Lemma big_sum_gt_0 : forall f n, (forall x, 0 <= fst (f x)) -> 
                              (exists y : nat, (y < n)%nat /\ 0 < fst (f y)) ->
                              0 < fst (big_sum f n).
Proof.
  intros f n H [y [H0 H1]].
  induction n.
  - simpl. lia. 
  - simpl in *.
    bdestruct (y <? n)%nat; bdestruct (y =? n)%nat; try lia. 
    + assert (H' : 0 <= fst (f n)). { apply H. } 
      apply IHn in H2. lra. 
    + apply (big_sum_ge_0 f n) in H.
      rewrite H3 in H1.
      lra. 
Qed.

Lemma big_sum_member_le : forall (f : nat -> C) (n : nat), (forall x, 0 <= fst (f x)) ->
                      (forall x, (x < n)%nat -> fst (f x) <= fst (big_sum f n)).
Proof.
  intros f.
  induction n.
  - intros H x Lt. inversion Lt.
  - intros H x Lt.
    bdestruct (Nat.ltb x n).
    + simpl.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat.
      apply IHn; easy.
      apply H.
    + assert (E: x = n) by lia.
      rewrite E.
      simpl.
      rewrite <- Rplus_0_l at 1.
      apply Rplus_le_compat.
      apply big_sum_ge_0; easy.
      lra.
Qed.  

Lemma big_sum_squeeze : forall (f : nat -> C) (n : nat), 
  (forall x, (0 <= fst (f x)))%R -> big_sum f n = C0 ->
  (forall x, (x < n)%nat -> fst (f x) = fst C0).
Proof. intros. 
       assert (H2 : (forall x, (x < n)%nat -> (fst (f x) <= 0)%R)).
       { intros. 
         replace 0%R with (fst (C0)) by easy.
         rewrite <- H0.
         apply big_sum_member_le; try easy. }
       assert (H3 : forall r : R, (r <= 0 -> 0 <= r -> r = 0)%R). 
       intros. lra. 
       simpl. 
       apply H3.
       apply H2; easy.
       apply H.
Qed.

Lemma big_sum_snd_0 : forall n f, (forall x, snd (f x) = 0) -> snd (big_sum f n) = 0.       
Proof. intros. induction n.
       - reflexivity.
       - rewrite <- big_sum_extend_r.
         unfold Cplus. simpl. rewrite H, IHn.
         simpl; lra.
Qed.


Lemma big_sum_Cmod_0_all_0 : forall (f : nat -> C) (n : nat),
  big_sum (fun i => Cmod (f i)) n = 0 -> 
  forall i, (i < n)%nat -> f i = C0.
Proof. induction n as [| n']; try nia.   
       intros; simpl in H.
       assert (H' := H).
       rewrite Rplus_comm in H; apply Rplus_eq_0_l in H. 
       apply Rplus_eq_0_l in H'.
       all : try apply Rsum_ge_0; intros.
       all : try apply Cmod_ge_0.
       bdestruct (i <? n')%nat.
       - apply IHn'; easy. 
       - bdestruct (i =? n')%nat; try lia; subst. 
         apply Cmod_eq_0; try easy.
Qed.

Lemma big_sum_triangle : forall f n,
  Cmod (big_sum f n) <= big_sum (fun i => Cmod (f i)) n.
Proof. induction n as [| n'].
       - simpl. rewrite Cmod_0; lra.
       - simpl.
         eapply Rle_trans; try apply Cmod_triangle.
         apply Rplus_le_compat_r.
         easy. 
Qed. 

Lemma Cmod_real_nonneg_sum_ge_any n (f : nat -> C) k (Hk : (k < n)%nat) 
  (Hf_re : forall i, (i < n)%nat -> snd (f i) = 0) 
  (Hf_nonneg : forall i, (i < n)%nat -> 0 <= fst (f i)):
  Cmod (f k) <= Cmod (big_sum (fun i => f i) n).
Proof.
  rewrite big_sum_real by easy.
  rewrite 2!Cmod_real; try apply Hf_re; 
  try apply Rle_ge;
  try apply (Hf_nonneg k Hk); try easy.
  - simpl.
    apply (Rsum_nonneg_ge_any n (fun i => fst (f i))); easy.
  - apply Rsum_ge_0_on.
    easy.
Qed.

Lemma big_sum_if_eq_C (f : nat -> C) n k :
  big_sum (fun x => if (x =? k)%nat then f x else 0%R) n =
  (if (k <? n)%nat then f k else 0%R).
Proof. 
  apply (@big_sum_if_eq C).
Qed.

Lemma big_sum_if_eq_C' (f : nat -> C) n k :
  big_sum (fun x => if (k =? x)%nat then f x else 0%R) n =
  (if (k <? n)%nat then f k else 0%R).
Proof. 
  apply (@big_sum_if_eq' C).
Qed.

Lemma add_if_exclusive_join_C (b c : bool) (v : C) : 
  (b = true -> c = false) -> (c = true -> b = false) -> 
  ((if b then v else 0%R) + (if c then v else 0%R) = 
  if b || c then v else 0%R)%C.
Proof.
  destruct b, c; simpl; intros; lca.
Qed.


(** * Lemmas about Cpow *)


Lemma RtoC_pow : forall r n, (RtoC r) ^ n = RtoC (r ^ n).
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite RtoC_mult.
    reflexivity.
Qed.

Lemma Re_Cpow (c : C) (Hc : snd c = 0) n : 
  fst (Cpow c n) = pow (fst c) n.
Proof.
  induction n; [easy|].
  simpl.
  rewrite Hc, IHn.
  lra.
Qed.

Lemma Cpow_nonzero_real : forall (r : R) (n : nat), (r <> 0 -> r ^ n <> C0)%C. 
Proof.
  intros.
  rewrite RtoC_pow. 
  apply C0_fst_neq. 
  apply pow_nonzero. 
  lra.
Qed.

Lemma Cpow_nonzero : forall (c : C) (n : nat), (c <> C0 -> c ^ n <> C0)%C. 
Proof.
  intros.
  induction n.
  - simpl; apply C1_neq_C0.
  - simpl. 
    apply Cmult_neq_0; easy.
Qed.

Lemma Cpow_0_l : forall n, n <> O -> C0 ^ n = C0.
Proof.
  intros n.
  destruct n; [easy|].
  simpl.
  rewrite Cmult_0_l.
  reflexivity.
Qed.

Lemma Cpow_add : forall (c : C) (n m : nat), (c ^ (n + m) = c^n * c^m)%C.
Proof.
  intros. induction n. simpl. lca.
  simpl. rewrite IHn. lca.
Qed.

Lemma Cpow_mult : forall (c : C) (n m : nat), (c ^ (n * m) = (c ^ n) ^ m)%C.
Proof.
  intros. induction m. rewrite Nat.mul_0_r. easy.
  replace (n * (S m))%nat with (n * m + n)%nat by lia.
  simpl. rewrite Cpow_add. rewrite IHm. lca.
Qed.

Lemma Cpow_inv : forall (c : C) (n : nat), (forall n', (n' <= n)%nat -> c ^ n' <> 0) -> (/ c) ^ n = / (c ^ n).
Proof.
  intros.
  induction n.
  - lca.
  - simpl.
    rewrite IHn.
    + rewrite Cinv_mult_distr.
      reflexivity.
    + intros.
      apply H.
      apply le_S.
      assumption.
Qed.  

Lemma Cpow_add_r : forall (c : C) (a b : nat), c ^ (a + b) = c ^ a * c ^ b.
Proof. induction a as [| a']; intros. 
       - lca.
       - simpl; rewrite IHa'; lca.
Qed.

Lemma Cpow_mul_l : forall (c1 c2 : C) (n : nat), (c1 * c2) ^ n = c1 ^ n * c2 ^ n.
Proof. induction n as [| n']; intros. 
       - lca.
       - simpl; rewrite IHn'; lca.
Qed.


Lemma Cmod_pow : forall x n, Cmod (x ^ n) = ((Cmod x) ^ n)%R.
Proof.
  intros x n.
  induction n; simpl.
  apply Cmod_1.
  rewrite Cmod_mult, IHn.
  reflexivity.
Qed.


(** * Lemmas about Cmod *)

Lemma Cmod_Cconj : forall c : C, Cmod (c^*) = Cmod c.
Proof.
  intro. unfold Cmod, Cconj. simpl.
  replace (- snd c * (- snd c * 1))%R with (snd c * (snd c * 1))%R by lra. 
  easy.
Qed.

Lemma Cmod_real_pos :
  forall x : C,
    snd x = 0 ->
    fst x >= 0 ->
    x = Cmod x.
Proof.
  intros. 
  unfold Cmod. 
  rewrite H. 
  replace (fst x ^ 2 + 0 ^ 2)%R with (fst x ^ 2)%R by lra. 
  rewrite sqrt_pow2 by lra.
  destruct x; simpl in *.
  rewrite H.
  reflexivity.
Qed.

Lemma Cmod_sqr : forall c : C, (Cmod c ^2 = c^* * c)%C.
Proof.
  intro.
  rewrite RtoC_pow.
  simpl.
  rewrite Rmult_1_r.
  rewrite <- Cmod_Cconj at 1. 
  rewrite <- Cmod_mult.
  rewrite Cmod_real_pos; auto.
  destruct c. simpl. lra.
  destruct c. simpl. nra.
Qed.

Lemma Cmod_switch : forall (a b : C),
  Cmod (a - b) = Cmod (b - a).
Proof. intros. 
       replace (b - a) with (- (a - b)) by lca. 
       rewrite Cmod_opp; easy.
Qed.

Lemma Cmod_triangle_le : forall (a b : C) (ϵ : R),
  Cmod a + Cmod b < ϵ -> Cmod (a + b) < ϵ.
Proof. intros. 
       assert (H0 := Cmod_triangle a b).
       lra. 
Qed.

Lemma Cmod_triangle_diff : forall (a b c : C) (ϵ : R),
  Cmod (c - b) + Cmod (b - a) < ϵ -> Cmod (c - a) < ϵ.
Proof. intros. 
       replace (c - a) with ((c - b) + (b - a)) by lca. 
       apply Cmod_triangle_le.
       easy. 
Qed.

(** * Lemmas about Cconj *)

Lemma Cconj_R : forall r : R, r^* = r.         Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0.                  Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ √2)^* = / √2.       Proof. lca. Qed.
Lemma Cplus_div2 : /2 + /2 = 1.           Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.
Lemma Cconj_minus_distr :  forall (x y : C), (x - y)^* = x^* - y^*. Proof. intros; lca. Qed.
                
Lemma Cinv_Cconj : forall c : C, (/ (c ^*) = (/ c) ^*)%C.
Proof. intros. 
       unfold Cinv, Cconj; simpl.
       apply c_proj_eq; simpl; try lra.
       apply f_equal. lra.
       (* this is just Ropp_div or Ropp_div_l, depending on Coq version *) 
       assert (H' : forall x y : R, (- x / y)%R = (- (x / y))%R).
       { intros. lra. }
       rewrite <- H'.
       apply f_equal. lra.
Qed.
                                    
Lemma Cmult_conj_real : forall (c : C), snd (c * c^*) = 0.
Proof.
  intros c.
  unfold Cconj.
  unfold Cmult.
  simpl.
  rewrite <- Ropp_mult_distr_r.
  rewrite Rmult_comm.
  rewrite Rplus_opp_l.
  reflexivity.
Qed.

Lemma Cmult_conj_nonneg (c : C) : 
  0 <= fst (c ^* * c)%C.
Proof.
  rewrite <- Cmod_sqr, RtoC_pow.
  apply pow2_ge_0.
Qed.


Lemma Cconj_simplify : forall (c1 c2 : C), c1^* = c2^* -> c1 = c2.
Proof. intros. 
       assert (H1 : c1 ^* ^* = c2 ^* ^*). { rewrite H; easy. }
       do 2 rewrite Cconj_involutive in H1.   
       easy. 
Qed.

               
(** * Lemmas about complex Square roots **)

Lemma Csqrt_sqrt : forall x : R, 0 <= x -> √ x * √ x = x.
Proof. intros. eapply c_proj_eq; simpl; try rewrite sqrt_sqrt; lra. Qed.

Lemma Csqrt2_sqrt : √ 2 * √ 2 = 2.
Proof. apply Csqrt_sqrt; lra. Qed.

Lemma Cinv_sqrt2_sqrt : /√2 * /√2 = /2. 
Proof. 
  eapply c_proj_eq; simpl; try lra.
  autorewrite with R_db. 
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (/2) _).
  repeat rewrite <- Rmult_assoc.
  rewrite sqrt_def; lra.
Qed.

Lemma Csqrt_inv : forall (r : R), 0 < r -> RtoC (√ (/ r)) = (/ √ r).
Proof.
  intros r H.
  apply c_proj_eq; simpl.
  field_simplify_eq. 
  rewrite sqrt_inv; auto.
  field_simplify_eq; auto.
  apply sqrt_neq_0_compat; lra.
  apply sqrt_neq_0_compat; lra.
  field. apply sqrt_neq_0_compat; lra.
Qed.

Lemma Csqrt2_inv : RtoC (√ (/ 2)) = (/ √ 2).
Proof. apply Csqrt_inv; lra. Qed.  

Lemma Csqrt_sqrt_inv : forall (r : R), 0 < r -> (√ r * √ / r) = 1.
Proof. 
  intros. 
  rewrite Csqrt_inv; trivial. 
  rewrite Cinv_r; trivial. 
  apply RtoC_neq.
  apply sqrt_neq_0_compat; easy.
Qed.

Lemma Csqrt2_sqrt2_inv : (√ 2 * √ / 2) = 1.
Proof. apply Csqrt_sqrt_inv. lra. Qed.

Lemma Csqrt2_inv_sqrt2 : ((√ / 2) * √ 2) = 1.
Proof. rewrite Cmult_comm. apply Csqrt2_sqrt2_inv. Qed.

Lemma Csqrt2_inv_sqrt2_inv : ((√ / 2) * (√ / 2)) = /2.
Proof. 
  rewrite Csqrt2_inv. field_simplify. 
  rewrite Csqrt2_sqrt. easy. 
  apply RtoC_neq; lra.
  apply RtoC_neq; apply sqrt_neq_0_compat; lra. 
Qed.

Lemma Csqrt2_neq_0 : (RtoC (√ 2) <> 0)%C.
Proof.
  unfold RtoC.
  unfold not.
  intro Hcontra.
  apply pair_equal_spec in Hcontra.
  destruct Hcontra.
  contradict H.
  apply sqrt2_neq_0.
Qed.


Lemma Cinv_sqrt2_proper : / RtoC (√ 2) = RtoC (√ 2) / 2.
Proof. rewrite <- Csqrt2_sqrt.
       unfold Cdiv.
       rewrite Cinv_mult_distr, Cmult_assoc, Cinv_r. 
       lca.
       all : apply RtoC_neq; apply sqrt2_neq_0.
Qed.


Corollary one_sqrt2_Cbasis : forall (a b : Z),
  (RtoC (IZR a)) + (RtoC (IZR b)) * √2 = 0 -> 
  (a = 0 /\ b = 0)%Z.
Proof. intros. 
       apply one_sqrt2_Rbasis.
       apply RtoC_inj. 
       rewrite RtoC_plus, RtoC_mult.
       easy.
Qed.

Definition Csqrt (z : C) : C :=
	match z with
	| (a, b) => sqrt ((Cmod z + a) / 2) + Ci * (b / Rabs b) * sqrt((Cmod z - a) / 2)
	end.

(* TODO: Remove; this is in Reals past coq 8.16 *)
Lemma Req_dec_T : forall r1 r2:R, {r1 = r2} + {r1 <> r2}.
Proof.
  intros r1 r2; destruct (total_order_T r1 r2) as [[H | ] | H].
  - now right; intros ->; apply (Rlt_irrefl r2).
  - now left.
  - now right; intros ->; apply (Rlt_irrefl r2 H).
Qed.

Definition Csqrt_alt z :=
  if Req_dec_T (snd z) 0 then 
    if Rcase_abs (fst z) 
    then Ci * (√ (- fst z)) 
    else √ (fst z)
  else 
    √ Cmod z * (z + Cmod z) / (Cmod (z + Cmod z)).

Lemma Csqrt_Csqrt_alt (z : C) : 
  Csqrt_alt z * Csqrt_alt z = z.
Proof.
  unfold Csqrt_alt.
  destruct z as [a b].
  cbn [fst snd].
  destruct (Req_dec_T b 0).
  - destruct (Rcase_abs a).
    + field_simplify.
      rewrite Ci2.
      rewrite <- Cmult_assoc.
      rewrite <- RtoC_mult.
      rewrite sqrt_sqrt by lra.
      lca.
    + rewrite <- RtoC_mult, sqrt_sqrt by lra.
      lca.
  - assert (Hnz: RtoC (Cmod ((a,b) + Cmod (a,b))) <> 0). 1: {
      rewrite Cmod_eq_C0_iff.
      intros Heq.
      apply (f_equal snd) in Heq.
      simpl in Heq.
      lra.
    }
    field_simplify.
    2: { easy. }
    rewrite <- !RtoC_mult, sqrt_sqrt by apply Cmod_ge_0.
    field_simplify.
    2: { intros Heq; apply (f_equal fst) in Heq; simpl in Heq; apply Hnz.
      apply Rmult_integral in Heq.
      now destruct Heq as [-> | ->].
    }
    rewrite <- 2!Cmult_assoc, <- RtoC_mult, sqrt_sqrt by apply Cmod_ge_0.
    field_simplify.
    2: { intros Heq; apply (f_equal fst) in Heq; simpl in Heq; apply Hnz.
      apply Rmult_integral in Heq.
      now destruct Heq as [-> | ->].
    }
    generalize Hnz; intros Hnz'.
    rewrite Cmod_eq_C0_iff in Hnz'.
    unfold Cmod in *.
    pose proof (pow2_ge_0 a).
    pose proof (pow2_ge_0 b).
    cbn [fst snd] in *.
    rewrite <- RtoC_mult, !sqrt_sqrt in * by lra.
    cbn [fst snd RtoC Cplus] in *.
    rewrite sqrt_sqrt by (pose proof (pow2_ge_0 (a+√(a^2+b^2))); 
      pose proof (pow2_ge_0 (b+0)); lra).
    
    field_simplify_eq.
    2: {intros Hrw. apply (f_equal fst) in Hrw. cbn [fst RtoC] in Hrw. 
      rewrite Hrw in *. now rewrite sqrt_0 in *. }
    apply c_proj_eq.
    + simpl in *. 
      field_simplify.
      simpl.
      rewrite !Rmult_1_r.
      rewrite sqrt_sqrt by lra.
      lra.
    + simpl.
      field_simplify.
      simpl.
      rewrite !Rmult_1_r.
      rewrite sqrt_sqrt by lra.
      lra.
Qed.
(** * Complex exponentiation **)


(** Compute e^(iθ) *)
Definition Cexp (θ : R) : C := (cos θ, sin θ).

Lemma Cexp_spec : forall α, Cexp α = cos α + Ci * sin α.
Proof. intros; lca. Qed.

Lemma Cexp_0 : Cexp 0 = 1.
Proof. unfold Cexp. autorewrite with trig_db; easy. Qed.

Lemma Cexp_add: forall (x y : R), Cexp (x + y) = Cexp x * Cexp y.
Proof.
  intros.
  unfold Cexp.
  apply c_proj_eq; simpl.
  - apply cos_plus.
  - rewrite sin_plus. field.
Qed.

Lemma Cexp_neg : forall θ, Cexp (- θ) = / Cexp θ.
Proof.
  intros θ.
  unfold Cexp.
  rewrite sin_neg, cos_neg.
  apply c_proj_eq; simpl.
  - replace (cos θ * (cos θ * 1) + sin θ * (sin θ * 1))%R with 
        (cos θ ^ 2 + sin θ ^ 2)%R by reflexivity.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    field.
  - replace ((cos θ * (cos θ * 1) + sin θ * (sin θ * 1)))%R with 
        (cos θ ^ 2 + sin θ ^ 2)%R by reflexivity.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    rewrite sin2_cos2.
    field.
Qed.

Lemma Cexp_minus : forall θ,
	Cexp θ + Cexp (-θ) = 2 * cos θ.
Proof.
	intros.
	unfold Cexp.
	rewrite cos_neg.
	rewrite sin_neg.
	lca.
Qed.

Lemma Cexp_plus_PI : forall x,
  Cexp (x + PI) = (- (Cexp x))%C.
Proof.
  intros.
  unfold Cexp.
  rewrite neg_cos, neg_sin.
  lca.
Qed.

Lemma Cexp_minus_PI: forall x : R, Cexp (x - PI) = (- Cexp x)%C.
Proof.
  intros x.
  unfold Cexp.
  rewrite cos_sym.
  rewrite Ropp_minus_distr.
  rewrite Rtrigo_facts.cos_pi_minus.
  rewrite <- Ropp_minus_distr.
  rewrite sin_antisym.
  rewrite Rtrigo_facts.sin_pi_minus.
  lca.
Qed.

Lemma Cexp_nonzero : forall θ, Cexp θ <> 0.
Proof. 
  intro θ. unfold Cexp.
  specialize (cos_sin_0_var θ) as [? | ?].
  apply C0_fst_neq; auto. 
  apply C0_snd_neq; auto.
Qed.

Lemma Cexp_mul_neg_l : forall θ, Cexp (- θ) * Cexp θ = 1.
Proof.  
  unfold Cexp. intros θ.
  eapply c_proj_eq; simpl.
  - autorewrite with R_db trig_db.
    field_simplify_eq.
    repeat rewrite <- Rsqr_pow2.
    rewrite Rplus_comm.
    apply sin2_cos2.
  - autorewrite with R_db trig_db. field.
Qed.

Lemma Cexp_mul_neg_r : forall θ, Cexp θ * Cexp (-θ) = 1.
Proof. intros. rewrite Cmult_comm. apply Cexp_mul_neg_l. Qed.

Lemma Cexp_pow : forall θ k, Cexp θ ^ k = Cexp (θ * INR k).
Proof.
  intros.
  induction k. 
  simpl. rewrite Rmult_0_r, Cexp_0. reflexivity.
  Local Opaque INR.
  simpl. rewrite IHk.
  rewrite <- Cexp_add.
  replace (S k) with (k + 1)%nat by lia.
  Local Transparent INR.
  rewrite plus_INR; simpl.
  apply f_equal. lra.
Qed.

Lemma Cexp_conj_neg : forall θ, (Cexp θ)^* = Cexp (-θ)%R.
Proof.
  intros.
  unfold Cexp.
  unfold Cconj.
  simpl.
  apply c_proj_eq; simpl.
  - rewrite cos_neg.
    reflexivity.
  - rewrite sin_neg.
    reflexivity.
Qed.

Lemma Cmod_Cexp : forall θ, Cmod (Cexp θ) = 1.
Proof.
  intro. unfold Cexp, Cmod. simpl. 
  replace ((cos θ * (cos θ * 1) + sin θ * (sin θ * 1)))%R 
    with (cos θ * cos θ + sin θ * sin θ)%R by lra. 
  specialize (sin2_cos2 θ) as H. 
  unfold Rsqr in H. 
  rewrite Rplus_comm in H. 
  rewrite H. apply sqrt_1.
Qed.

Lemma Cmod_Cexp_alt : forall θ, Cmod (1 - Cexp (2 * θ)) = Cmod (2 * (sin θ)).
Proof.
  intro θ.
  unfold Cexp, Cminus, Cplus.
  simpl.
  unfold Cmod. simpl. 
  apply f_equal.
  field_simplify_eq.
  unfold Rminus.
  rewrite (Rplus_assoc (_ ^ 2)).
  rewrite (Rplus_comm (- _)).
  rewrite <- Rplus_assoc.
  rewrite (Rplus_comm (_ ^ 2)).
  rewrite <- 2 Rsqr_pow2.
  rewrite sin2_cos2.
  rewrite cos_2a_sin.
  lra.
Qed.


(** Cexp of multiples of PI **)

(* Euler's Identity *) 
Lemma Cexp_PI : Cexp PI = -1.
Proof. unfold Cexp. autorewrite with trig_db; easy. Qed.

Lemma Cexp_PI2 : Cexp (PI/2) = Ci.
Proof. unfold Cexp. autorewrite with trig_db; easy. Qed.

Lemma Cexp_2PI : Cexp (2 * PI) = 1.
Proof.
  unfold Cexp. rewrite sin_2PI, cos_2PI. reflexivity.
Qed.

Lemma Cexp_3PI2: Cexp (3 * PI / 2) = - Ci.
Proof.
  unfold Cexp.
  replace (3 * PI / 2)%R with (3 * (PI/2))%R by lra.  
  rewrite cos_3PI2, sin_3PI2.
  lca.
Qed.

Lemma Cexp_PI4 : Cexp (PI / 4) = /√2 + /√2 * Ci.
Proof.
  unfold Cexp.
  rewrite sin_PI4, cos_PI4.
  eapply c_proj_eq; simpl.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
Qed.

Lemma Cexp_PIm4 : Cexp (- PI / 4) = /√2 - /√2 * Ci.
Proof.
  unfold Cexp. 
  rewrite Ropp_div.
  rewrite sin_antisym.
  rewrite cos_neg.
  rewrite sin_PI4, cos_PI4.
  eapply c_proj_eq; simpl.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
  field_simplify_eq; trivial; apply sqrt2_neq_0.
Qed.

Lemma Cexp_0PI4 : Cexp (0 * PI / 4) = 1.
Proof. rewrite <- Cexp_0. apply f_equal. lra. Qed.

Lemma Cexp_1PI4 : Cexp (1 * PI / 4) = /√2 + /√2 * Ci.
Proof. rewrite <- Cexp_PI4. apply f_equal. lra. Qed.

Lemma Cexp_2PI4 : Cexp (2 * PI / 4) = Ci.
Proof. rewrite <- Cexp_PI2. apply f_equal. lra. Qed.

Lemma Cexp_3PI4 : Cexp (3 * PI / 4) = -/√2 + /√2 * Ci.
Proof.
  unfold Cexp.
  rewrite <- Rmult_div_assoc.
  rewrite cos_3PI4, sin_3PI4.
  eapply c_proj_eq; simpl.
  R_field_simplify; trivial. apply sqrt2_neq_0.
  R_field_simplify; trivial. apply sqrt2_neq_0.
Qed.

Lemma Cexp_4PI4 : Cexp (4 * PI / 4) = -1.
Proof. rewrite <- Cexp_PI. apply f_equal. lra. Qed.
  
Lemma Cexp_5PI4 : Cexp (5 * PI / 4) = -/√2 - /√2 * Ci.
Proof.
  unfold Cexp.
  rewrite <- Rmult_div_assoc.
  rewrite cos_5PI4, sin_5PI4.
  eapply c_proj_eq; simpl.
  R_field_simplify; trivial. apply sqrt2_neq_0.
  R_field_simplify; trivial. apply sqrt2_neq_0.
Qed.

Lemma Cexp_6PI4 : Cexp (6 * PI / 4) = -Ci.
Proof.
Proof. rewrite <- Cexp_3PI2. apply f_equal. lra. Qed.
  
Lemma Cexp_7PI4 : Cexp (7 * PI / 4) = /√2 - /√2 * Ci.
Proof.
  unfold Cexp.
  replace (7 * PI / 4)%R with (- PI / 4 + 2 * INR 1 * PI)%R.
  2:{ R_field_simplify. rewrite Rmult_1_r. lra. }
  rewrite cos_period, sin_period.
  rewrite Ropp_div.
  rewrite cos_neg, sin_neg.
  rewrite sin_PI4, cos_PI4.
  eapply c_proj_eq; simpl.
  R_field_simplify; trivial. apply sqrt2_neq_0.
  R_field_simplify; trivial. apply sqrt2_neq_0.
Qed.    

Lemma Cexp_8PI4 : Cexp (8 * PI / 4) = 1.
Proof. rewrite <- Cexp_2PI. apply f_equal. lra. Qed.

(* This is a dramatically simplified version of Cexp_mod_2PI and we
   can probably get rid of it. *)
Lemma Cexp_PI4_m8 : forall (k : Z), Cexp (IZR (k - 8) * PI / 4) = Cexp (IZR k * PI / 4).
Proof.
  intros.
  unfold Rdiv.
  rewrite minus_IZR.
  unfold Rminus.
  repeat rewrite Rmult_plus_distr_r.
  replace (- (8) * PI * / 4)%R with (-(2 * PI))%R by lra.
  rewrite Cexp_add, Cexp_neg, Cexp_2PI.
  lca.
Qed.

Lemma Cexp_2nPI : forall (k : Z), Cexp (IZR (2 * k) * PI) = 1.
Proof.
  induction k using Z.peano_ind.
  - simpl. rewrite Rmult_0_l. apply Cexp_0.
  - rewrite Z.mul_succ_r.
    rewrite plus_IZR.
    rewrite Rmult_plus_distr_r.
    rewrite Cexp_add, Cexp_2PI.
    rewrite IHk.
    lca.
  - rewrite Z.mul_pred_r.
    rewrite minus_IZR.
    unfold Rminus.
    rewrite Rmult_plus_distr_r.
    rewrite <- Ropp_mult_distr_l.
    rewrite Cexp_add, Cexp_neg, Cexp_2PI.
    rewrite IHk.
    lca.
Qed.

Lemma Cexp_mod_2PI : forall (k : Z), Cexp (IZR k * PI) = Cexp (IZR (k mod 2) * PI). 
Proof.
  intros.
  rewrite (Z.div_mod k 2) at 1 by lia.
  remember (k/2)%Z as k'.
  rewrite plus_IZR.
  rewrite Rmult_plus_distr_r.
  rewrite Cexp_add.
  rewrite Cexp_2nPI.
  lca.
Qed.  

Lemma Cexp_mod_2PI_scaled : forall (k sc : Z), 
  Cexp (IZR k * PI / IZR sc) = Cexp (IZR (k mod (2 * sc)) * PI / IZR sc). 
Proof.
  intros k sc.
  destruct (Z.eq_dec sc 0) as [?|H];
  [subst; simpl; now rewrite 2!Rdiv_0_r|].
  rewrite (Z.div_mod k (2 * sc)) at 1 by lia.
  repeat rewrite plus_IZR.
  unfold Rdiv.
  repeat rewrite Rmult_plus_distr_r.
  rewrite Cexp_add.
  replace (IZR (2 * sc * (k / (2 * sc))) * PI * Rinv (IZR sc))%R with
      (IZR (2 * (k / (2 * sc))) * PI)%R.
  2:{ repeat rewrite mult_IZR. 
      R_field_simplify.
      reflexivity. 
      apply not_0_IZR; assumption. }
  rewrite Cexp_2nPI.
  lca.
Qed.

#[global] Hint Rewrite Cexp_0 Cexp_PI Cexp_PI2 Cexp_2PI Cexp_3PI2 Cexp_PI4 Cexp_PIm4
  Cexp_1PI4 Cexp_2PI4 Cexp_3PI4 Cexp_4PI4 Cexp_5PI4 Cexp_6PI4 Cexp_7PI4 Cexp_8PI4
  Cexp_add Cexp_neg Cexp_plus_PI Cexp_minus_PI : Cexp_db.

Lemma INR_pi_exp : forall (r : nat),
	Cexp (INR r * PI) = 1 \/ Cexp (INR r * PI) = -1.
Proof.
	intros.
	dependent induction r.
	- simpl.
		rewrite Rmult_0_l.
		left.
		apply Cexp_0.
	-	rewrite S_O_plus_INR.
		rewrite Rmult_plus_distr_r.
		rewrite Rmult_1_l.
		rewrite Rplus_comm.
		rewrite Cexp_plus_PI.
		destruct IHr.
		+ rewrite H; right; lca.
		+ rewrite H; left; lca.
Qed.

Lemma Cexp_2_PI : forall a, Cexp (INR a * 2 * PI) = 1.
Proof.
	intros.
	induction a.
	- simpl.
		rewrite 2 Rmult_0_l.
		rewrite Cexp_0.
		easy.
	- rewrite S_INR.
		rewrite 2 Rmult_plus_distr_r.
		rewrite Rmult_1_l.
		rewrite double.
		rewrite <- Rplus_assoc.
		rewrite 2 Cexp_plus_PI.
		rewrite IHa.
		lca.
Qed.

Lemma sin_sin_PI8 : 
  sin (PI / 8) * sin (PI / 8) = 
  cos (PI / 8) * cos (PI / 8) - cos (PI / 4).
Proof.
  replace (PI / 4)%R with (2 * (PI / 8))%R by lra.
  rewrite cos_2a.
  lca.
Qed.


Definition CexpC (c : C) :=
  exp (Re c) * Cexp (Im c).

Lemma CexpC_def (c : C) : 
  CexpC c = exp (Re c) * Cexp (Im c).
Proof. reflexivity. Qed.

Lemma CexpC_add (c d : C) : 
  CexpC (c + d) = CexpC c * CexpC d.
Proof.
  unfold CexpC, Im, Re.
  cbn.
  rewrite exp_plus, Cexp_add.
  lca.
Qed.

Lemma CexpC_neg (c : C) : 
  CexpC (-c) = / CexpC c.
Proof.
  unfold CexpC, Im, Re.
  cbn.
  pose proof (exp_pos (fst c)).
  rewrite exp_Ropp, Cexp_neg, RtoC_inv, Cinv_mult_distr.
  reflexivity.
Qed.

Lemma CexpC_minus (c d : C) : 
  CexpC (c - d) = CexpC c / CexpC d.
Proof.
  unfold Cminus.
  rewrite CexpC_add, CexpC_neg.
  reflexivity.
Qed.

Lemma CexpC_zero : CexpC 0 = 1.
Proof.
  unfold CexpC.
  cbn.
  rewrite exp_0, Cexp_0.
  lca.
Qed.

Lemma Cmod_CexpC c : Cmod (CexpC c) = exp (Re c).
Proof.
  unfold CexpC.
  rewrite Cmod_mult, Cmod_Cexp, Rmult_1_r.
  apply Cmod_real; [cbn | reflexivity].
  pose proof (exp_pos (Re c)).
  lra.
Qed.

Lemma Cexp_CexpC (r : R) : 
  Cexp r = CexpC (0, r).
Proof.
  unfold CexpC.
  cbn.
  rewrite exp_0.
  lca.
Qed.

Lemma RtoC_exp (x : R) : 
  RtoC (exp x) = CexpC x.
Proof.
  apply c_proj_eq; simpl;
  autorewrite with trig_db; lra.
Qed.

Lemma Cmod_1_plus_Cexp (r : R) : 
  Cmod (1 + Cexp r) = √ (2 + 2 * cos r)%R.
Proof.
  unfold Cmod.
  f_equal.
  simpl.
  pose proof sin2_cos2 r as H.
  rewrite 2!Rsqr_pow2 in H.
  field_simplify.
  rewrite (Rplus_comm _ (_ ^ 2)), <- Rplus_assoc.
  rewrite H.
  lra.
Qed.

Opaque C.



(** * Automation **)


Lemma Cminus_unfold : forall c1 c2, (c1 - c2 = c1 + -c2)%C. Proof. reflexivity. Qed.
Lemma Cdiv_unfold : forall c1 c2, (c1 / c2 = c1 */ c2)%C. Proof. reflexivity. Qed.

(* For proving goals of the form x <> 0 or 0 < x *)
Ltac nonzero :=
  repeat split;
  repeat
    match goal with
    | |- not (@eq _ (Copp _) (RtoC (IZR Z0))) => apply Copp_neq_0_compat
    | |- not (@eq _ (Cpow _ _) (RtoC (IZR Z0))) => apply Cpow_nonzero
    | |- not (@eq _ Ci (RtoC (IZR Z0))) => apply C0_snd_neq; simpl
    | |- not (@eq _ (Cexp _) (RtoC (IZR Z0))) => apply Cexp_nonzero
    | |- not (@eq _ _ (RtoC (IZR Z0))) => apply RtoC_neq
    end;
  repeat
    match goal with
    | |- not (@eq _ (sqrt (pow _ _)) (IZR Z0)) => rewrite sqrt_pow
    | |- not (@eq _ (pow _ _) (IZR Z0)) => apply pow_nonzero; try apply RtoC_neq
    | |- not (@eq _ (sqrt _) (IZR Z0)) => apply sqrt_neq_0_compat
    | |- not (@eq _ (Rinv _) (IZR Z0)) => apply Rinv_neq_0_compat
    | |- not (@eq _ (Rmult _ _) (IZR Z0)) => apply Rmult_integral_contrapositive_currified
    end;
  repeat
    match goal with
    | |- Rlt (IZR Z0) (Rmult _ _) => apply Rmult_lt_0_compat
    | |- Rlt (IZR Z0) (Rinv _) => apply Rinv_0_lt_compat
    | |- Rlt (IZR Z0) (pow _ _) => apply pow_lt
    end;
  match goal with
  | |- not (@eq _ _ _) => lra
  | |- Rlt _ _ => lra
  | |- Rle _ _ => lra
  end.

#[global] Hint Rewrite Cminus_unfold Cdiv_unfold Ci2 Cconj_R Cconj_opp Cconj_rad2 
     Cinv_sqrt2_sqrt Cplus_div2
     Cplus_0_l Cplus_0_r Cplus_opp_r Cplus_opp_l Copp_0  Copp_involutive
     Cmult_0_l Cmult_0_r Cmult_1_l Cmult_1_r : C_db.

#[global] Hint Rewrite <- Copp_mult_distr_l Copp_mult_distr_r Cdouble : C_db.
#[global] Hint Rewrite Csqrt_sqrt using Psatz.lra : C_db.
#[global] Hint Rewrite Cinv_l Cinv_r using nonzero : C_db.
(* Previously in the other direction *)
#[global] Hint Rewrite Cinv_mult_distr : C_db.

(* Light rewriting db *)
#[global] Hint Rewrite Cplus_0_l Cplus_0_r Cmult_0_l Cmult_0_r Copp_0 
             Cconj_R Cmult_1_l Cmult_1_r : C_db_light.

(* Distributing db *)
#[global] Hint Rewrite Cmult_plus_distr_l Cmult_plus_distr_r 
  Copp_plus_distr Copp_mult_distr_l Copp_involutive : Cdist_db.

#[global] Hint Rewrite RtoC_opp RtoC_mult RtoC_minus RtoC_plus : RtoC_db.
#[global] Hint Rewrite RtoC_inv using nonzero : RtoC_db.
#[global] Hint Rewrite RtoC_pow : RtoC_db.

Lemma Copp_Ci : / Ci = - Ci.
Proof. field_simplify_eq; lca + nonzero. Qed.

#[global] Hint Rewrite Copp_Ci : C_db.


Ltac Csimpl := 
  repeat match goal with
  | _ => rewrite Cmult_0_l
  | _ => rewrite Cmult_0_r
  | _ => rewrite Cplus_0_l
  | _ => rewrite Cplus_0_r
  | _ => rewrite Cmult_1_l
  | _ => rewrite Cmult_1_r
  | _ => rewrite Cconj_R
  end.

Ltac Csimpl_in H := 
  repeat
  match goal with
  | _ => rewrite Cmult_0_l in H
  | _ => rewrite Cmult_0_r in H
  | _ => rewrite Cplus_0_l in H
  | _ => rewrite Cplus_0_r in H
  | _ => rewrite Cmult_1_l in H
  | _ => rewrite Cmult_1_r in H
  | _ => rewrite Cconj_R in H
  end.

Ltac C_field_simplify := repeat field_simplify_eq [ Csqrt2_sqrt Csqrt2_inv Ci2].
Ltac C_field := C_field_simplify; nonzero || trivial; try trivial.

Ltac has_term t exp  := 
  match exp with
    | context[t] => idtac 
  end.

Ltac group_radicals :=
  repeat rewrite Cconj_opp;
  repeat rewrite Cconj_rad2;
  repeat rewrite <- Copp_mult_distr_l;
  repeat rewrite <- Copp_mult_distr_r;
  repeat match goal with
  | _ => rewrite Cinv_sqrt2_sqrt
  | |- context [ ?x * ?y ] => tryif has_term (√ 2) x then fail 
                            else (has_term (√ 2) y; rewrite (Cmult_comm x y)) 
  | |- context [ ?x * ?y * ?z ] =>
    tryif has_term (√ 2) y then fail 
    else (has_term (√ 2) x; has_term (√ 2) z; rewrite <- (Cmult_assoc x y z)) 
  | |- context [ ?x * (?y * ?z) ] => 
    has_term (√ 2) x; has_term (√ 2) y; rewrite (Cmult_assoc x y z)
  end.    

Ltac cancel_terms t := 
  repeat rewrite Cmult_plus_distr_l;
  repeat rewrite Cmult_plus_distr_r; 
  repeat match goal with
  | _ => rewrite Cmult_1_l
  | _ => rewrite Cmult_1_r
  | _ => rewrite Cinv_r; try nonzero  
  | _ => rewrite Cinv_l; try nonzero
  | |- context[(?x * ?y)%C]        => tryif has_term (/ t)%C y then fail else has_term (/ t)%C x; has_term t y; 
                                    rewrite (Cmult_comm x y)
  | |- context[(?x * (?y * ?z))%C] => has_term t x; has_term (/ t)%C y; 
                                    rewrite (Cmult_assoc x y z)
  | |- context[(?x * (?y * ?z))%C] => tryif has_term t y then fail else has_term t x; has_term (/ t)%C z; 
                                    rewrite (Cmult_comm y z)
  | |- context[(?x * ?y * ?z)%C]   => tryif has_term t x then fail else has_term t y; has_term (/ t)%C z; 
                                    rewrite <- (Cmult_assoc x y z)
  end. 

Ltac group_Cexp :=
  repeat rewrite <- Cexp_neg;
  repeat match goal  with
  | _ => rewrite <- Cexp_add
  | _ => rewrite <- Copp_mult_distr_l
  | _ => rewrite <- Copp_mult_distr_r
  | |- context [ ?x * ?y ] => tryif has_term Cexp x then fail 
                            else (has_term Cexp y; rewrite (Cmult_comm x y)) 
  | |- context [ ?x * ?y * ?z ] =>
    tryif has_term Cexp y then fail 
    else (has_term Cexp x; has_term Cexp z; rewrite <- (Cmult_assoc x y z)) 
  | |- context [ ?x * (?y * ?z) ] => 
    has_term Cexp x; has_term Cexp y; rewrite (Cmult_assoc x y z)
  end.    
