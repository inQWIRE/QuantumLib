Require Import Polar.
Require Export Ctopology.
Require Import Setoid.

(*********************************************************************)
(* defining poly_coef_norm and showing how it can be used as a bound *)
(*********************************************************************)

Definition poly_coef_norm (p : Polynomial) : R :=
  big_sum (fun i => Cmod (nth i p C0)) (length p).

Lemma poly_coef_norm_ge_0 : forall (p : Polynomial),
  0 <= poly_coef_norm p.
Proof. intros. 
       apply Rsum_ge_0; intros. 
       apply Cmod_ge_0.
Qed.

Lemma norm_0_iff_0 : forall (p : Polynomial),
  p ≅ [] <-> poly_coef_norm p = 0.
Proof. split; intros.
       - apply Peq_0_eq_repeat_0 in H.
         rewrite H.
         unfold poly_coef_norm.
         apply (@big_sum_0_bounded R R_is_monoid); intros. 
         rewrite nth_repeat, Cmod_0; easy.
       - unfold poly_coef_norm in H.
         assert (H' := (big_sum_Cmod_0_all_0 (fun i : nat => nth i p 0) (length p))).
         simpl in H'. 
         assert (H'' : forall i : nat, (i < length p)%nat -> nth i p 0 = 0). 
         apply H'; apply H.
         unfold Peq.
         apply functional_extensionality; intros.
         unfold Peval; simpl.
         apply (@big_sum_0_bounded C C_is_monoid); intros.
         rewrite H''; try lca; easy.
Qed.

Lemma poly_coef_norm_compactify : forall (p : Polynomial),
  poly_coef_norm p = poly_coef_norm (compactify p).
Proof. intros. 
       destruct (Peq_0_dec p).
       - rewrite Peq_0_compactify_0; auto.
         apply norm_0_iff_0 in p0; rewrite p0.
         easy.
       - apply C0_end_breakdown in n.
         destruct n as [n [a [p' [H H0] ] ] ].
         rewrite H0, app_C0_compactify_reduce, app_nonzero_compactify_reduce; auto.
         unfold poly_coef_norm.
         rewrite app_length, big_sum_sum, <- (Rplus_0_r).
         apply f_equal_gen. 
         apply f_equal_gen; auto.
         apply big_sum_eq_bounded; intros. 
         apply f_equal_gen; auto.
         rewrite app_nth1; easy.
         apply (@big_sum_0_bounded R R_is_monoid); intros. 
         rewrite app_nth2, nth_repeat, Cmod_0; try lia. simpl; lra.
Qed.

Add Parametric Morphism : poly_coef_norm
  with signature Peq ==> eq as polycoefnorm_mor.
Proof. intros p1 p2 H. 
       rewrite poly_coef_norm_compactify, (poly_coef_norm_compactify p2).
       apply Peq_compactify_eq in H; rewrite H; easy.
Qed.

Lemma poly_bound_ge_1 : forall (p : Polynomial) (z : C),
  1 <= Cmod z ->
  Cmod (p[[z]]) <= (poly_coef_norm p) * (Cmod z)^(length p - 1).
Proof. intros. 
       destruct p as [| a].
       - assert (H' : [] ≅ []). easy.
         apply norm_0_iff_0 in H'; rewrite H'.
         unfold Peval; simpl.
         rewrite Cmod_0; lra.
       - unfold Peval.
         eapply Rle_trans.
         apply big_sum_triangle.
         unfold poly_coef_norm.
         rewrite (@big_sum_mult_r R _ _ _ R_is_ring).
         apply Rsum_le; intros. 
         rewrite Cmod_mult.
         apply Rmult_le_compat_l; try apply Cmod_ge_0.
         rewrite Cmod_pow. 
         apply Rle_pow; auto; lia.
Qed.

Lemma poly_bound_le_1 : forall (p : Polynomial) (z : C),
  Cmod z <= 1 ->
  Cmod ((C0 :: p)[[z]]) <= (poly_coef_norm p) * (Cmod z).
Proof. intros. 
       unfold Peval, poly_coef_norm; simpl length.
       rewrite <- big_sum_extend_l, (@big_sum_mult_r R _ _ _ R_is_ring); simpl. 
       rewrite Cmult_0_l, Cplus_0_l.
       eapply Rle_trans; try apply big_sum_triangle.
       apply Rsum_le; intros. 
       repeat rewrite Cmod_mult.
       apply Rmult_le_compat_l.
       apply Cmod_ge_0.
       rewrite Cmod_pow.
       rewrite <- Rmult_1_r.
       apply Rmult_le_compat_l.
       apply Cmod_ge_0.
       apply Rpow_le1; split; auto.
       apply Cmod_ge_0.
Qed.

Lemma half_norm_bound : forall (c z : C),
  (Cmod c < (Cmod z) * /2)%R ->
  ((Cmod z) * /2 < Cmod (z + c))%R.
Proof. intros. 
       assert (H0 := Cmod_triangle (z + c) (-c)).
       replace (z + c + - c) with z in H0 by lca.
       rewrite Cmod_opp in H0.
       apply Rle_minus_l in H0.
       eapply Rlt_le_trans; try apply H0.
       apply Rlt_minus_r.
       rewrite Rplus_comm.
       apply Rlt_minus_r.
       replace (Cmod z - Cmod z * / 2)%R with (Cmod z /2 + Cmod z /2 - Cmod z * / 2)%R.
       lra.
       rewrite <- (double_var (Cmod z)); easy.
Qed.

Lemma leading_term_dom : forall (p : Polynomial) (a c : C),
  a <> C0 -> 
  Cmod c > (2 * poly_coef_norm p / (Cmod a))%R -> Cmod c > 1 ->
  Cmod p[[c]] < Cmod (a * c^(length p)) /2.
Proof. intros. 
       destruct p as [| a0].
       - unfold Peval; simpl.
         rewrite Cmult_1_r, Cmod_0.
         apply Rdiv_lt_0_compat; try lra. 
         apply Cmod_gt_0; easy.
       - eapply Rle_lt_trans; try (apply poly_bound_ge_1; lra).
         replace (length (a0 :: p) - 1)%nat with (length p) by (simpl; lia).
         unfold Rdiv; simpl. 
         rewrite Cmod_mult, Cmod_mult; simpl.         
         rewrite Rmult_assoc, Rmult_assoc, 
           (Rmult_comm _ (/ 2)), Cmod_pow; repeat rewrite <- Rmult_assoc.
         apply Rmult_lt_compat_r; try (apply pow_lt; lra).
         apply (Rmult_lt_reg_r 2 _ _); try lra.
         repeat rewrite Rmult_assoc; rewrite Rinv_l, Rmult_1_r; try lra. 
         apply (Rmult_lt_reg_l (/ Cmod a) _ _);
           try (apply Rinv_0_lt_compat; apply Cmod_gt_0; easy).
         do 2 rewrite <- Rmult_assoc; rewrite Rinv_l, Rmult_1_l; try lra.
         unfold not; intros; apply H.
         apply Cmod_eq_0; easy. 
Qed.

Lemma poly_bound_leading_term : forall (p : Polynomial) (a : C),
  a <> C0 -> 
  exists r, (forall c, Cmod c > r -> Cmod (p ++ [a])[[c]] > Cmod (a * c^(length p)) * /2).
Proof. intros. 
       exists (Rmax (2 * poly_coef_norm p / (Cmod a))%R 1); intros.        
       apply Rmax_Rlt in H0; destruct H0.
       rewrite app_eval_to_mul.
       replace (c ^ length p * ([a]) [[c]]) with (a * c ^ (length p)).
       rewrite Cplus_comm.
       apply half_norm_bound.
       apply leading_term_dom; auto; lra.
       unfold Peval; simpl; lca.
Qed.

Lemma x_to_n_bounded_below : forall (a c : C) (M : R) (n : nat),
  a <> C0 -> n <> 0%nat -> 
  Cmod c > Rmax (2 * (M / Cmod a)) 1 -> 
  Cmod (a * c^n) * /2 > M.
Proof. intros. 
       apply (Rmult_lt_reg_r 2 _ _); try lra.
       rewrite Rmult_assoc, Rinv_l, Rmult_1_r, Cmod_mult; try lra. 
       apply (Rmult_lt_reg_l (/ Cmod a) _ _);
           try (apply Rinv_0_lt_compat; apply Cmod_gt_0; easy).
       do 2 rewrite <- Rmult_assoc; rewrite Rinv_l, Rmult_1_l, Cmod_pow; try lra.
       apply Rmax_Rlt in H1; destruct H1.
       eapply Rlt_le_trans; try apply (Rle_pow _ 1 n); simpl; try lra.
       destruct n; try easy; lia.
       unfold not; intros; apply H.
       apply Cmod_eq_0; easy.
Qed.       

Lemma poly_to_inf_uniformly : forall (p : Polynomial) (M : R),
  (Polynomial.degree p > 0)%nat -> 
  exists r, r > 0 /\ (forall c, Cmod c > r -> Cmod p[[c]] > M).
Proof. intros. 
       destruct (Peq_0_dec p).
       - rewrite p0 in H; easy.
       - assert (H0 := p_Peq_compactify_p p); simpl in H0.
         apply compactify_breakdown in n.
         destruct n as [a [p' [H1 H2] ] ].
         destruct (poly_bound_leading_term p' a) as [r1 H3]; auto.
         exists (Rmax r1 (Rmax (2 * (M / Cmod a)) 1)); split.
         assert (H' : 1 <= Rmax r1 (Rmax (2 * (M / Cmod a)) 1)).
         { apply Rmax_Rle; right.
           apply Rmax_r. }
         lra.
         intros. 
         apply Rmax_Rlt in H4; destruct H4.
         rewrite H0, H2.
         eapply Rgt_trans; try (apply H3; lra).
         apply x_to_n_bounded_below; auto; try lra.
         destruct p'; try easy.
         unfold degree in H.
         rewrite H2 in H; easy.
Qed.



(* We finally can show that polynomial take on a minimum value and use this to prove FTA *)

Lemma poly_compact_closed_ball : forall (p : Polynomial) (r : R),
  compact ((Peval p) @ (fun c' => Cmod (c') <= r)).
Proof. intros. 
       apply continuous_image_compact. 
       unfold continuous_on, C_; intros. 
       apply polynomial_continuous. 
       apply Heine_Borel; split.  
       assert (H : (fun c' : C => Cmod c' <= r) = (fun c' : C => Cmod (c' - 0) <= r)).
       { apply functional_extensionality; intros. 
         replace (x - 0) with x by lca; easy. }
       rewrite H.
       apply closed_ball_closed. 
       exists (r + 1)%R; unfold subset, ϵ_disk; intros. 
       replace (c - 0) with c by lca; lra.
Qed.       

(* we finally prove poly_min! is there a way to show this without compactness? *) 
Lemma poly_min : forall (p : Polynomial), 
  exists m, (forall c, Cmod p[[m]] <= Cmod p[[c]]).
Proof. intros. 
       destruct (Polynomial.degree p) as [| n] eqn:E.
       - unfold degree in E.
         exists 0; intros.  
         destruct (compactify p) as [| a0] eqn:E0; 
           rewrite p_Peq_compactify_p, E0; unfold Peval; simpl; try lra. 
         destruct p0; try easy; simpl; lra. 
       - assert (H' : compact ((Peval p) @ (fun c' => Cmod (c') <= 1))).
         { apply poly_compact_closed_ball. } 
         apply compact_contains_min_norn_elem in H'.
         destruct H' as [mne [H H0] ].
         assert (H' : (Polynomial.degree p > 0)%nat).
         { rewrite E; lia. }
         apply (poly_to_inf_uniformly _ (Cmod mne)) in H'.
         destruct H' as [r [rgt0 H1] ]. 
         assert (H' : compact ((Peval p) @ (fun c' => Cmod (c') <= (r + 1)))).
         { apply poly_compact_closed_ball. }
         apply compact_contains_min_norn_elem in H'.
         all : try (exists p[[0]]; exists 0; split; try easy;
                      rewrite Cmod_0; lra).
         destruct H' as [mne' [H2 H3] ].
         destruct H2 as [m [H2 H4] ].
         exists m; intros; rewrite H4.
         destruct (Rle_lt_dec (Cmod c) r).
         + apply H3.
           exists c; split; try lra; easy. 
         + destruct H as [m' [H H5] ].
           assert (H6 : Cmod mne' <= Cmod mne).
           { apply H3.
             exists m'; split; try lra; easy. }
           left.
           eapply Rle_lt_trans; try apply H6.
           apply H1; lra.
Qed.      

Lemma first_nonzero_coef : forall (p : Polynomial),
  Peval p <> Peval [] -> 
  exists a n p', a <> C0 /\ p = (repeat C0 n) ++ [a] ++ p'.
Proof. induction p as [| a0]; try easy.
       intros. 
       destruct (Ceq_dec a0 C0); subst.
       - destruct (Peq_0_dec p).
         + assert (H' : (C0 :: p) ≅ []).
           rewrite p0; apply C0_Peq_nil.
           easy.
         + apply IHp in n.
           destruct n as [a [n [p' [H0 H1] ] ] ].
           exists a, (S n), p'; split; auto.
           rewrite H1; easy.
       - exists a0, O, p; split; easy.
Qed.
  
Lemma eval_x_to_n_plus_a : forall (z a0 ak : C) (ϵ : R) (k : nat),
  a0 <> C0 -> ak <> C0 -> 0 < ϵ < 1 ->
  z ^ (k + 1) = (-a0 / ak) -> 
  Cmod ((a0 :: repeat C0 k) ++ [ak]) [[ϵ * z]] = ((Cmod a0) * (1 - ϵ ^ (k + 1)))%R.
Proof. intros.  
       rewrite <- (Rabs_pos_eq (1 - ϵ ^ (k + 1))), <- Cmod_R, <- Cmod_mult.
       apply f_equal_gen; auto.
       rewrite app_eval_to_mul.
       assert (H3 := p_Peq_compactify_p (a0 :: repeat C0 k)).
       simpl in H3.
       replace (a0 :: repeat C0 k) with ([a0] ++ repeat C0 k) in * by easy.
       rewrite app_C0_compactify_reduce in H3.
       rewrite H3.
       unfold compactify, prune; simpl.
       destruct (Ceq_dec a0 0); try easy; simpl. 
       unfold Peval; simpl.
       rewrite repeat_length.
       rewrite Cpow_mul_l.
       replace (ϵ * z * (ϵ ^ k * z ^ k)) with (z ^ k * z * ϵ * ϵ ^k) by lca.
       rewrite Cpow_add_r in H2; simpl in H2; rewrite Cmult_1_r in H2.
       do 2 rewrite Cmult_1_r, Cplus_0_l.
       rewrite H2, Cmult_comm.
       rewrite <- Cmult_assoc. 
       replace (ϵ * ϵ ^ k) with (ϵ ^ (k + 1)).
       rewrite Cmult_assoc.
       replace (ak * (- a0 / ak)) with (- a0).
       replace (RtoC (Rminus (IZR (Zpos xH)) (pow ϵ (Init.Nat.add k (S O))))) with
         (Cminus (RtoC (IZR (Zpos xH))) (pow ϵ (Init.Nat.add k (S O)))) by lca.
       rewrite RtoC_pow; lca.
       unfold Cdiv.
       rewrite Cmult_comm, <- Cmult_assoc, Cinv_l; try lca; easy.
       rewrite Cpow_add_r; lca.
       apply Rle_minus_r.
       rewrite Rplus_0_l.
       apply Rpow_le1; lra.
Qed.    

(* here ak is really a(k+1) *)
Lemma bound_lemma1 : forall (z a0 ak : C) (ϵ : R) (k : nat) (p : Polynomial),
  a0 <> C0 -> ak <> C0 -> 0 < ϵ < 1 ->
  z ^ (k + 1) = (-a0 / ak) ->  
  ϵ * Cmod z <= 1 -> 
  Cmod (a0 :: (repeat C0 k) ++ [ak] ++ p)[[ϵ * z]] <= 
    (Cmod a0) * (1 - ϵ^(k + 1)) + (poly_coef_norm p) * Cmod (z ^ (k + 2)) * ϵ^(k + 2).
Proof. intros. 
       destruct H1.
       rewrite app_comm_cons, app_assoc, app_eval.
       eapply Rle_trans; try apply Cmod_triangle.
       rewrite eval_x_to_n_plus_a; try easy.
       apply Rplus_le_compat_l.
       assert (H5 : (repeat C0 (length ((a0 :: repeat C0 k) ++ [ak])) ++ p) = 
                      (repeat C0 (k + 1)) ++ (C0 :: p)).
       { replace (C0 :: p) with ([C0] ++ p) by easy.
         rewrite app_assoc, <- repeat_cons; simpl. 
         rewrite app_length, repeat_length; simpl; easy. }
       rewrite H5, mul_by_x_to_n, Cpow_mul_l, (Cmult_comm (ϵ ^ (k + 1))), Cmult_assoc.
       repeat rewrite Cmod_mult.
       rewrite RtoC_pow, Cmod_R, Rabs_pos_eq; try (apply pow_le; lra).
       replace (k + 2)%nat with (1 + (k + 1))%nat by lia.
       rewrite (pow_add _ 1 (k + 1)).
       repeat rewrite <- Rmult_assoc.
       apply Rmult_le_compat_r; try (apply pow_le; lra).
       rewrite Rmult_assoc, (Rmult_comm _ (ϵ ^ 1)), <- Rmult_assoc.
       rewrite (Cpow_add_r _ 1), Cmod_mult, <- Rmult_assoc.
       apply Rmult_le_compat_r; try (apply Cmod_ge_0). 
       eapply Rle_trans; try apply poly_bound_le_1.
       rewrite Cmod_mult, Cmod_R, Rabs_pos_eq; lra.
       rewrite Cmod_mult, Cmod_R, Rabs_pos_eq; simpl; try lra.
       rewrite Cmult_1_r; lra.
Qed.

Lemma bound_lemma2 : forall (z a0 ak : C) (ϵ : R) (k : nat) (p : Polynomial),
  a0 <> C0 -> ak <> C0 -> 0 < ϵ < 1 ->
  Peval p <> Peval [] -> 
  z ^ (k + 1) = (-a0 / ak) ->  
  ϵ <= 1 * / Cmod z ->
  ϵ < (Cmod a0) / ((poly_coef_norm p) * (Cmod z) ^ (k + 2)) ->
  (Cmod a0) * (1 - ϵ^(k + 1)) + (poly_coef_norm p) * Cmod (z ^ (k + 2)) * ϵ^(k + 2) <
   Cmod a0.
Proof. intros. 
       assert (Hz : z <> C0).
       { apply (nonzero_nth_root (-a0 / ak) z (k+1)); try lia; try easy.
         unfold not; intros; apply H.
         apply (Cmult_simplify _ _ (-1) (-1)) in H6; auto.
         replace (- a0 / ak * -1) with (a0 * / ak) in H6 by lca.
         apply (Cmult_simplify _ _ ak ak) in H6; auto.
         rewrite <- Cmult_assoc, Cmult_0_l, Cmult_0_l, Cinv_l in H6; auto.
         rewrite <- H6; lca. }
       destruct (Req_dec (poly_coef_norm p) 0).
       - apply norm_0_iff_0 in H6; easy.
       - rewrite <- Rplus_0_r.
         unfold Rminus.
         rewrite Rmult_plus_distr_l, Rmult_1_r.
         rewrite Rplus_assoc.
         apply Rplus_lt_compat_l.
         replace (Cmod a0 * - ϵ^(k+1) + poly_coef_norm p * Cmod (z^(k+2)) * ϵ^(k+2))%R
           with ((poly_coef_norm p * Cmod (z^(k+2)) * ϵ^(k+2)) - (Cmod a0 * ϵ^(k+1)))%R by lra.
         apply Rlt_minus_l.
         rewrite Rplus_0_l.
         replace (k + 2)%nat with (1 + (k + 1))%nat by lia.
         rewrite (pow_add _ 1).
         rewrite <- Rmult_assoc.
         apply Rmult_lt_compat_r; simpl. 
         apply pow_lt; easy.
         replace (z * z ^ (k + 1)) with (z ^ (k + 2)).
         rewrite Rmult_comm, Rmult_1_r. 
         apply (Rmult_lt_reg_r (/ (poly_coef_norm p * Cmod z ^ (k + 2)))).
         apply Rinv_0_lt_compat; apply Rmult_lt_0_compat.
         destruct (poly_coef_norm_ge_0 p); try easy.
         symmetry in H7; easy.
         apply pow_lt.
         apply Cmod_gt_0; auto.
         rewrite Rmult_assoc. 
         replace (poly_coef_norm p * Cmod (z ^ (k + 2)) * 
                    / (poly_coef_norm p * Cmod z ^ (k + 2)))%R with 1.
         rewrite Rmult_1_r; easy.
         rewrite Cmod_pow, Rinv_r; auto.
         apply Rmult_integral_contrapositive_currified; auto.
         apply pow_nonzero.
         unfold not; intros; apply Hz.
         apply Cmod_eq_0; easy.
         replace (k + 2)%nat with (1 + (k + 1))%nat by lia.
         rewrite (Cpow_add_r _ 1); lca.
Qed.

(* this proof is pretty ugly and repetative. TODO: make better *)
Lemma get_smaller_norm_output : forall (a0 ak : C) (k : nat) (p : Polynomial),
  a0 <> C0 -> ak <> C0 -> 
  exists c, Cmod (a0 :: (repeat C0 k) ++ [ak] ++ p)[[c]] < Cmod a0.
Proof. intros. 
       destruct (nth_root_C (-a0 / ak) (k+1)) as [z H1]; try lia.
       assert (H2 : z <> C0).
       { apply (nonzero_nth_root (-a0 / ak) z (k+1)); try lia; try easy.
         unfold not; intros; apply H.
         apply (Cmult_simplify _ _ (-1) (-1)) in H2; auto.
         replace (- a0 / ak * -1) with (a0 * / ak) in H2 by lca.
         apply (Cmult_simplify _ _ ak ak) in H2; auto.
         rewrite <- Cmult_assoc, Cmult_0_l, Cmult_0_l, Cinv_l in H2; auto.
         rewrite <- H2; lca. }
       destruct (Peq_0_dec p).
       - assert (H' : exists ϵ, 0 < ϵ < 1 /\ ϵ * Cmod z <= 1).
         { exists (Rmin (/ 2) (/ Cmod z)); repeat split.
           apply Rmin_glb_lt; apply Rinv_0_lt_compat; try lra.
           apply Cmod_gt_0; auto.
           eapply Rle_lt_trans; try apply Rmin_l; lra.
           assert (H' := (Rmin_r (/ 2) (/ Cmod z))).
           apply (Rmult_le_compat_r (Cmod z)) in H'.
           rewrite Rinv_l in H'; try easy.
           unfold not; intros; apply H2; apply Cmod_eq_0; easy.
           apply Cmod_ge_0. }
         destruct H' as [ϵ [H3 H4] ].
         exists (ϵ * z).
         apply (bound_lemma1 _ _ _ ϵ _ p) in H1; auto.
         apply norm_0_iff_0 in p0; rewrite p0, Rmult_0_l, Rmult_0_l, Rplus_0_r in *.
         eapply Rle_lt_trans; try apply H1.
         rewrite <- Rmult_1_r.
         apply Rmult_lt_compat_l; try (apply Cmod_gt_0; easy).
         apply Rlt_minus_l.
         assert (H' : 0 < ϵ ^ (k + 1)).
         apply pow_lt; lra. 
         lra. 
       - assert (H' : exists ϵ, 0 < ϵ < 1 /\ ϵ <= 1 * / Cmod z /\ 
                             ϵ < (Cmod a0) / ((poly_coef_norm p) * (Cmod z) ^ (k + 2))).
         { exists (Rmin ((1 * / Cmod z) * /2) 
                   (Rmin ((Cmod a0 / (poly_coef_norm p * Cmod z ^ (k + 2))) * /2) (/ 2))).
           repeat split.
           repeat apply Rmin_glb_lt; try lra.
           repeat apply Rmult_lt_0_compat; try apply Rinv_0_lt_compat; try lra.
           apply Cmod_gt_0; auto.
           repeat apply Rdiv_lt_0_compat; try lra.
           apply Cmod_gt_0; auto.
           apply Rmult_lt_0_compat.
           destruct (poly_coef_norm_ge_0 p); try easy.
           symmetry in H3; apply norm_0_iff_0 in H3; easy.
           apply pow_lt.
           apply Cmod_gt_0; auto.
           do 2 (eapply Rle_lt_trans; try apply Rmin_r); lra.
           eapply Rle_trans; try apply Rmin_l. 
           rewrite <- Rmult_1_r.
           apply Rmult_le_compat_l; try lra.
           replace (1 * / Cmod z)%R with (1 / Cmod z)%R by easy.
           left; apply Rdiv_lt_0_compat; try lra.
           apply Cmod_gt_0; auto.
           eapply Rle_lt_trans; try apply Rmin_r. 
           eapply Rle_lt_trans; try apply Rmin_l. 
           rewrite <- Rmult_1_r.
           apply Rmult_lt_compat_l; try lra.
           apply Rdiv_lt_0_compat.
           apply Cmod_gt_0; auto.
           apply Rmult_lt_0_compat.
           destruct (poly_coef_norm_ge_0 p); try easy.
           symmetry in H3; apply norm_0_iff_0 in H3; easy.
           apply pow_lt.
           apply Cmod_gt_0; auto. }
         destruct H' as [ϵ [H3 [H4 H5] ] ].
         assert (H6 := H1).
         apply (bound_lemma2 _ _ _ ϵ _ p) in H1; auto.
         exists (ϵ * z).
         eapply Rle_lt_trans; try apply H1.
         apply bound_lemma1; auto.
         apply (Rmult_le_reg_r (/ Cmod z)); try apply Rinv_0_lt_compat.
         apply Cmod_gt_0; auto.
         rewrite Rmult_assoc, Rinv_r; try lra.
         unfold not; intros; apply H2.
         apply Cmod_eq_0; easy.
Qed.

Lemma FTA_min_at_0 : forall (p : Polynomial) (a : C),
  (Polynomial.degree (a :: p) > 0)%nat -> 
  (forall c, Cmod (a :: p)[[C0]] <= Cmod (a :: p)[[c]]) ->
  a = C0.
Proof. intros. 
       destruct (Ceq_dec a C0); try easy.
       destruct (Peq_0_dec p).
       rewrite p0 in H. 
       unfold degree, compactify, prune in H; simpl in H.
       destruct (Ceq_dec a C0); easy.
       apply first_nonzero_coef in n0.
       destruct n0 as [ak [k [p' [H1 H2] ] ] ].
       destruct (get_smaller_norm_output a ak k p') as [z H3]; auto.
       rewrite <- H2 in H3.
       assert (H4 := H0 z).
       assert (H' : (a :: p) [[C0]] = a).
       { unfold Peval; simpl length.
         rewrite <- Cplus_0_r, <- big_sum_extend_l.
         apply Cplus_simplify; try lca.
         apply (@big_sum_0_bounded C C_is_monoid); intros. 
         simpl; lca. }
       rewrite H' in H4.
       lra.
Qed.

Theorem Fundamental_Theorem_Algebra : forall (p : Polynomial),
  (Polynomial.degree p > 0)%nat -> (exists c : Complex.C, p[[c]] = C0).
Proof. intros.
       destruct (poly_min p) as [min H0].
       assert (H1 : forall c, Cmod (poly_shift p (-min))[[C0]] <= Cmod (poly_shift p (-min))[[c]]).
       { intros. 
         do 2 rewrite <- poly_shift_ver.
         replace (0 - - min) with min by lca.
         apply H0. }
       assert (H2 := (poly_shift_degree p (-min))).
       destruct (poly_shift p (- min)) as [| a] eqn:E.
       rewrite H2 in H.
       unfold degree, compactify, prune in H; simpl in H; lia.
       apply FTA_min_at_0 in H1.
       exists (0 - - min).
       rewrite poly_shift_ver, E.
       unfold Peval.
       apply (@big_sum_0_bounded C C_is_monoid); intros. 
       destruct x; simpl; subst; lca.
       rewrite <- H2; easy.
Qed.


(*****)
(*****)

