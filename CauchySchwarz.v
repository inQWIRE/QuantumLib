Require Import Psatz.  
Require Import Reals.
  
Require Export VecSet.


Local Close Scope nat_scope.


(* some inner product lemmas *)
Lemma inner_product_scale_l : forall {n} (u v : Vector n) (c : C),
  ⟨c .* u, v⟩ = c^* * ⟨u,v⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mmult.
       rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_scale_r : forall {n} (u v : Vector n) (c : C),
  ⟨u, c .* v⟩ = c * ⟨u,v⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mmult.
       rewrite (@big_sum_mult_l C _ _ _ C_is_ring).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_plus_l : forall {n} (u v w : Vector n),
  ⟨u .+ v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mplus, Mmult.
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_plus_r : forall {n} (u v w : Vector n),
  ⟨u, v .+ w⟩ = ⟨u, v⟩ + ⟨u, w⟩.
Proof. intros.
       unfold inner_product, scale, adjoint, Mplus, Mmult.
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group).
       apply big_sum_eq_bounded; intros.
       lca.
Qed.       

Lemma inner_product_adjoint_r : forall {m n} (A : Matrix m n) (u : Vector m) (v : Vector n),
  ⟨u, A × v⟩ = ⟨A† × u, v⟩.
Proof. intros. 
       unfold inner_product. 
       rewrite Mmult_adjoint, adjoint_involutive, Mmult_assoc.
       easy.
Qed.

Lemma inner_product_adjoint_l : forall {m n} (A : Matrix m n) (u : Vector n) (v : Vector m),
  ⟨A × u, v⟩ = ⟨u, A† × v⟩.
Proof. intros. 
       rewrite inner_product_adjoint_r, adjoint_involutive. 
       easy.
Qed.

Lemma inner_product_big_sum_l : forall {n} (u : Vector n) (f : nat -> Vector n) (k : nat),
  ⟨big_sum f k, u⟩ = big_sum (fun i => ⟨f i, u⟩) k.
Proof. induction k.
       - unfold inner_product; simpl.
         rewrite zero_adjoint_eq, Mmult_0_l; easy.
       - simpl. 
         rewrite inner_product_plus_l, IHk.
         reflexivity.
Qed.       

Lemma inner_product_big_sum_r : forall {n} (u : Vector n) (f : nat -> Vector n) (k : nat),
  ⟨u, big_sum f k⟩ = big_sum (fun i => ⟨u, f i⟩) k.
Proof. induction k.
       - unfold inner_product; simpl.
         rewrite Mmult_0_r; easy.
       - simpl. 
         rewrite inner_product_plus_r, IHk.
         reflexivity.
Qed.       

Lemma inner_product_conj_sym : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨v, u⟩^*.
Proof. intros. 
       unfold inner_product, adjoint, Mmult.
       rewrite (@big_sum_func_distr C C _ C_is_group _ C_is_group).
       apply big_sum_eq_bounded; intros.
       lca.
       intros; lca.
Qed.

Lemma inner_product_mafe_WF_l : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨make_WF u, v⟩.
Proof. intros. 
       unfold inner_product, adjoint, Mmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.

Lemma inner_product_mafe_WF_r : forall {n} (u v : Vector n),
  ⟨u, v⟩ = ⟨u, make_WF v⟩.
Proof. intros. 
       unfold inner_product, adjoint, Mmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.

(* Useful to be able to normalize vectors *)
Definition norm {n} (ψ : Vector n) : R :=
  sqrt (fst ⟨ψ,ψ⟩).

Definition normalize {n} (ψ : Vector n) :=
  / (norm ψ) .* ψ.

Lemma WF_normalize : forall {n} (ψ : Vector n),
  WF_Matrix ψ -> WF_Matrix (normalize ψ).
Proof. intros. 
       unfold normalize.
       auto with wf_db.
Qed. 

#[export] Hint Resolve WF_normalize : wf_db.

Lemma norm_make_WF : forall {n} (v : Vector n),
  norm v = norm (make_WF v).
Proof. intros. 
       unfold norm, make_WF.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       unfold inner_product, adjoint, Mmult.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl.
       easy.
Qed.

Lemma norm_scale : forall {n} c (v : Vector n), norm (c .* v) = ((Cmod c) * norm v)%R.
Proof.
  intros n c v.
  unfold norm, inner_product.
  rewrite Mscale_adj.
  rewrite Mscale_mult_dist_l, Mscale_mult_dist_r, Mscale_assoc.
  unfold scale.
  simpl.
  replace (fst c * snd c + - snd c * fst c)%R with 0%R.
  autorewrite with R_db C_db.
  replace (fst c * fst c)%R with (fst c ^ 2)%R by lra.
  replace (snd c * snd c)%R with (snd c ^ 2)%R by lra.
  rewrite sqrt_mult_alt.
  reflexivity.
  apply Rplus_le_le_0_compat; apply pow2_ge_0.
  lra.
Qed.

Lemma normalized_norm_1 : forall {n} (v : Vector n),
  norm v <> 0 -> norm (normalize v) = 1.
Proof. intros. 
       unfold normalize.
       rewrite norm_scale.  
       rewrite Cmod_real. 
       simpl.  
       autorewrite with R_db.
       rewrite Rmult_comm.
       rewrite Rinv_mult; try easy. 
       rewrite <- Rmult_comm.
       rewrite <- Rmult_assoc.
       rewrite Rinv_r; try easy.
       autorewrite with R_db.
       reflexivity. 
       unfold Cinv.
       simpl. 
       autorewrite with R_db.
       rewrite Rinv_mult; try easy. 
       rewrite <- Rmult_assoc.
       rewrite Rinv_r; try easy.
       autorewrite with R_db.
       assert (H' : norm v >= 0).
       { assert (H'' : 0 <= norm v).
         { apply sqrt_pos. }
         lra. }
       destruct H' as [H0 | H0].
       left.
       assert (H1 : 0 < norm v). { lra. }
       apply Rinv_0_lt_compat in H1.
       lra. easy. 
       apply div_real.
       easy. 
Qed. 

Lemma rewrite_norm : forall {d} (ψ : Vector d),
    fst ⟨ψ,ψ⟩ = big_sum (fun i => Cmod (ψ i O) ^ 2)%R d.
Proof.
  intros d ψ. unfold inner_product, Mmult.
  replace (fun y : nat => (ψ† O y * ψ y O)%C) with (fun y : nat => RtoC (Cmod (ψ y O) ^ 2)).
  apply Rsum_big_sum.
  apply functional_extensionality. intros.
  unfold adjoint. rewrite <- Cmod_sqr. symmetry. apply RtoC_pow.
Qed.

Local Open Scope nat_scope.

Lemma norm_real : forall {n} (v : Vector n), snd ⟨v,v⟩ = 0%R. 
Proof. intros. unfold inner_product, Mmult, adjoint.
       rewrite big_sum_snd_0. easy.
       intros. rewrite Cmult_comm.
       rewrite Cmult_conj_real.
       reflexivity.
Qed.

Lemma inner_product_ge_0 : forall {d} (ψ : Vector d),
  (0 <= fst ⟨ψ,ψ⟩)%R.
Proof.
  intros.
  unfold inner_product, Mmult, adjoint.
  apply big_sum_ge_0.
  intro.
  rewrite <- Cmod_sqr.
  simpl.
  autorewrite with R_db.
  apply Rmult_le_pos; apply Cmod_ge_0.
Qed.


(* why does sqrt_pos exist? *)
Lemma norm_ge_0 : forall {d} (ψ : Vector d),
  (0 <= norm ψ)%R.
Proof. intros.
       unfold norm.
       apply sqrt_positivity.
       (* apply sqrt_pos *)
       apply inner_product_ge_0.
Qed.

Lemma norm_squared : forall {d} (ψ : Vector d),
  ((norm ψ) ^2)%R = fst ⟨ ψ, ψ ⟩.
Proof. intros.
       unfold norm.
       rewrite pow2_sqrt; auto.
       apply inner_product_ge_0.
Qed.

(* "Quick" proof of |x| = 0 iff x = 0 *)
Lemma inner_product_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> (⟨v,v⟩ = C0 <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         destruct (mat_equiv_dec v Zero).
         apply mat_equiv_eq; try easy.
         assert (H' : v <> Zero). 
         { unfold not; intros. 
           apply n0. rewrite H1.
           easy. }
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         unfold WF_Matrix in H.
         bdestruct (x <? n).
         assert (H0' := Rle_0_sqr).  
         unfold Rsqr in H0'. 
         assert (H' : (0 < fst (inner_product v v))%R).
         { unfold inner_product.
           unfold Mmult. 
           apply big_sum_gt_0.
           unfold adjoint. 
           intros.
           rewrite <- Cmod_sqr.
           simpl. autorewrite with R_db.
           apply H0'. 
           exists x. split; try easy.
           unfold adjoint. 
           rewrite <- Cmod_sqr.
           simpl. autorewrite with R_db.
           assert (H' : (0 <= Cmod (v x 0%nat) * Cmod (v x 0%nat))%R). 
           { apply H0'. } 
           destruct H'; try easy. 
           assert (H' := Rsqr_0_uniq).
           unfold Rsqr in H'. 
           assert (H'' : forall a b : R, a = b -> b = a). { easy. }
           apply H'' in H3. 
           apply H' in H3.
           apply Cmod_gt_0 in H1.
           rewrite H3 in H1.
           lra. }
         rewrite H0 in H'. 
         simpl in H'. lra. 
         assert (H' : v x O = C0).
         { apply H. left; easy. }
         rewrite H' in H1; easy. 
       - intros. 
         unfold inner_product.  
         rewrite H0. 
         rewrite Mmult_0_r. 
         easy.
Qed.

Lemma norm_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> (norm v = 0%R <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         unfold norm in H0.
         apply inner_product_zero_iff_zero in H.
         unfold inner_product in H. 
         apply sqrt_eq_0 in H0.
         apply H. 
         apply c_proj_eq.
         apply H0.
         apply norm_real.
         apply inner_product_ge_0.
       - intros. 
         rewrite H0. 
         unfold norm, inner_product.
         rewrite Mmult_0_r. 
         simpl. apply sqrt_0. 
Qed.     

Corollary norm_nonzero_iff_nonzero : forall {n} (v : Vector n),
  WF_Matrix v -> (norm v <> 0%R <-> v <> Zero). 
Proof. intros. 
       split; intros;
       contradict H0;
       apply norm_zero_iff_zero; auto.
Qed.

Corollary fst_inner_product_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> ((fst ⟨v,v⟩) = 0%R <-> v = Zero).
Proof. intros; split; intros. 
       apply inner_product_zero_iff_zero; auto.
       apply c_proj_eq; auto.
       rewrite norm_real; auto.
       apply inner_product_zero_iff_zero in H0; auto.
       rewrite H0; easy.
Qed.

Corollary fst_inner_product_nonzero_iff_nonzero : forall {n} (v : Vector n),
  WF_Matrix v -> ((fst ⟨v,v⟩) <> 0%R <-> v <> Zero).
Proof. intros; split; intros;
       contradict H0; apply fst_inner_product_zero_iff_zero; easy.
Qed.

Lemma nonzero_inner_product_gt_0 : forall {d} (ψ : Vector d),
  WF_Matrix ψ -> ψ <> Zero ->
  (0 < fst ⟨ψ,ψ⟩)%R.
Proof.
  intros.
  assert (H' : forall r : R, (0 <= r -> r <> 0 -> 0 < r)%R).
  intros; lra.
  apply H'.
  apply inner_product_ge_0.
  apply fst_inner_product_nonzero_iff_nonzero; easy.
Qed.

(* useful in some scenarios and also does not require WF *)
Corollary nonzero_entry_implies_nonzero_norm : forall {n} (v : Vector n) (i : nat),
  i < n -> v i 0 <> C0 -> norm v <> 0%R.
Proof. intros.   
       rewrite norm_make_WF.
       apply norm_nonzero_iff_nonzero; auto with wf_db.
       contradict H0.
       replace C0 with (@Zero n (S O) i O).
       rewrite <- H0.
       unfold make_WF; bdestruct_all; easy.
       lca.
Qed.

Local Close Scope nat_scope.

Lemma subnormal_matrix_le_1 {n m : nat} (A : Matrix n m) {i j} 
  (Hi : (i < n)%nat) (Hj : (j < m)%nat) 
  (Hnorm : forall i, (i < m)%nat -> norm (get_col A i) <= 1) :
  Cmod (A i j) <= 1.
Proof.
  apply Rle_pow_le_nonneg with 1%nat; try lra; [apply Cmod_ge_0|].
  rewrite pow1.
  specialize (Hnorm j Hj).
  revert Hnorm.
  unfold get_col, norm, inner_product. 
  autounfold with U_db.
  rewrite Nat.eqb_refl. 
  rewrite (big_sum_eq_bounded _ (fun k => RtoC (Cmod (A k j) ^ 2)))
  by (intros; rewrite <- Cmod_sqr, RtoC_pow; easy).
  rewrite Rsum_big_sum.
  intros H.
  rewrite <- sqrt_1 in H.
  apply sqrt_le_0 in H; 
  [|apply Rsum_ge_0_on;intros;apply pow2_ge_0|lra].
  refine (Rle_trans _ _ _ _ H).
  apply (Rsum_nonneg_ge_any n (fun k => Cmod (A k j) ^ 2)%R i); [easy|].
  intros; apply pow2_ge_0.
Qed.

Lemma normal_matrix_le_1 {n m : nat} (A : Matrix n m) {i j} 
  (Hi : (i < n)%nat) (Hj : (j < m)%nat) 
  (Hnorm : forall i, (i < m)%nat -> norm (get_col A i) = 1) :
  Cmod (A i j) <= 1.
Proof.
  apply subnormal_matrix_le_1; [easy..|].
  intros.
  rewrite Hnorm; easy + lra.
Qed.

(* We can now prove Cauchy-Schwartz for vectors with inner_product *)
Lemma CS_key_lemma : forall {n} (u v : Vector n),
  fst ⟨ (⟨v,v⟩ .* u .+ -1 * ⟨v,u⟩ .* v), (⟨v,v⟩ .* u .+ -1 * ⟨v,u⟩ .* v) ⟩ =
    ((fst ⟨v,v⟩) * ((fst ⟨v,v⟩)* (fst ⟨u,u⟩) - (Cmod ⟨u,v⟩)^2 ))%R.
Proof. intros. 
       replace ((fst ⟨v,v⟩) * ((fst ⟨v,v⟩)* (fst ⟨u,u⟩) - (Cmod ⟨u,v⟩)^2 ))%R with
               (fst (⟨v,v⟩ * (⟨v,v⟩ * ⟨u,u⟩ - (Cmod ⟨u,v⟩)^2))).
       - apply f_equal.
         repeat rewrite inner_product_plus_l; repeat rewrite inner_product_plus_r;
           repeat rewrite inner_product_scale_l; repeat rewrite inner_product_scale_r. 
         replace ((-1 * ⟨ v, u ⟩) ^* * (-1 * ⟨ v, u ⟩ * ⟨ v, v ⟩)) with 
           ( ⟨ v, u ⟩^* * ⟨ v, u ⟩ * ⟨ v, v ⟩ ) by lca.       
         replace ((-1 * ⟨ v, u ⟩) ^* * (⟨ v, v ⟩ * ⟨ v, u ⟩) +
                    ⟨ v, u ⟩ ^* * ⟨ v, u ⟩ * ⟨ v, v ⟩) with C0 by lca.
         rewrite (inner_product_conj_sym v u), <- (inner_product_conj_sym v v).
         rewrite <- Cmult_assoc.   
         replace (⟨ u, v ⟩ ^* * ⟨ u, v ⟩) with (Cmod ⟨ u, v ⟩ ^ 2) by apply Cmod_sqr.
         lca.
       - assert (H := norm_real v).
         assert (H0 := norm_real u).
         destruct ⟨ v, v ⟩; destruct ⟨ u, u ⟩.
         rewrite Cmod_sqr.
         replace (⟨ u, v ⟩ ^* * ⟨ u, v ⟩) with (Cmod ⟨ u, v ⟩ ^ 2,0)%R.
         simpl in *; subst; lra.
         apply c_proj_eq.
         unfold Cmod. 
         rewrite pow2_sqrt. 
         simpl; lra.
         apply Rplus_le_le_0_compat; apply pow2_ge_0.
         rewrite Cmult_comm, Cmult_conj_real; easy. 
Qed.

Lemma real_ge_0_aux : forall (a b c : R),
  0 <= a -> 0 < b -> (a = b * c)%R ->
  0 <= c.
Proof. intros. 
       replace c with (a * / b)%R.
       apply Rle_mult_inv_pos; auto.
       subst.
       replace (b * c * / b)%R with (b * /b * c)%R by lra.
       rewrite Rinv_r; try lra. 
Qed.

Lemma real_gt_0_aux : forall (a b c : R),
  0 < a -> 0 < b -> (a = b * c)%R ->
  0 < c.
Proof. intros. 
       replace c with (a * / b)%R.
       apply Rlt_mult_inv_pos; auto.
       subst.
       replace (b * c * / b)%R with (b * /b * c)%R by lra.
       rewrite Rinv_r; try lra. 
Qed.

Lemma Cauchy_Schwartz_ver1 : forall {n} (u v : Vector n),
  (Cmod ⟨u,v⟩)^2 <= (fst ⟨u,u⟩) * (fst ⟨v,v⟩).
Proof. intros.  
       destruct (Req_dec (fst ⟨v,v⟩) 0). 
       - rewrite H. 
         rewrite inner_product_mafe_WF_l, inner_product_mafe_WF_r in H.
         rewrite inner_product_mafe_WF_r.
         assert (H' : make_WF v = Zero).
         { apply norm_zero_iff_zero; auto with wf_db.
           unfold norm; rewrite H.
           apply sqrt_0. }
         unfold inner_product.
         rewrite H', Mmult_0_r.
         unfold Zero.
         rewrite Cmod_0.
         lra.
       - assert (H0 := CS_key_lemma u v).
         apply real_ge_0_aux in H0.
         lra.
         apply inner_product_ge_0.
         destruct (inner_product_ge_0 v); lra.
Qed.

Lemma Cauchy_Schwartz_ver2 : forall {n} (u v : Vector n),
  (Cmod ⟨u,v⟩) <= norm u * norm v.
Proof. intros.  
       rewrite <- (sqrt_pow2 (Cmod ⟨ u, v ⟩)), <- (sqrt_pow2 (norm v)), <- (sqrt_pow2 (norm u)).
       rewrite <- sqrt_mult.
       apply sqrt_le_1.
       all : try apply pow2_ge_0.
       apply Rmult_le_pos.
       all : try apply pow2_ge_0.
       unfold norm.
       rewrite pow2_sqrt, pow2_sqrt.
       apply Cauchy_Schwartz_ver1.
       all : try apply inner_product_ge_0; try apply norm_ge_0.
       apply Cmod_ge_0.
Qed.

Lemma Cplx_Cauchy_vector :
  forall n (u v : Vector n),
    ((big_sum (fun i => Cmod (u i O) ^ 2) n) * (big_sum (fun i => Cmod (v i O) ^ 2) n) >=
     Cmod (big_sum (fun i => ((u i O)^* * (v i O))%C) n) ^ 2)%R.
Proof. intros.
       assert (H := Cauchy_Schwartz_ver1 u v).
       replace (big_sum (fun i : nat => (Cmod (u i 0%nat) ^ 2)%R) n) with (fst ⟨ u, u ⟩).
       replace (big_sum (fun i : nat => (Cmod (v i 0%nat) ^ 2)%R) n) with (fst ⟨ v, v ⟩).
       replace (Σ (fun i : nat => (u i 0%nat) ^* * v i 0%nat) n) with (⟨ u, v ⟩).
       lra.
       all : unfold inner_product, adjoint, Mmult; try easy. 
       all : rewrite (@big_sum_func_distr C R _ C_is_group _ R_is_group).
       all : try apply big_sum_eq_bounded; intros.
       all : try rewrite <- Cmod_sqr. 
       all : try (destruct a; destruct b; simpl; easy).
       destruct (v x 0%nat); unfold Cmod, pow, Cmult; simpl; lra. 
       destruct (u x 0%nat); unfold Cmod, pow, Cmult; simpl; lra. 
Qed.

Local Open Scope nat_scope.

Lemma Cplx_Cauchy :
  forall n (u v : nat -> C),
    ((big_sum (fun i => Cmod (u i) ^ 2) n) * (big_sum (fun i => Cmod (v i) ^ 2) n) >= Cmod (big_sum (fun i => ((u i)^* * (v i))%C) n) ^ 2)%R.
Proof. intros. 
       assert (H := Cplx_Cauchy_vector n (fun i j => u i) (fun i j => v i)).
       simpl in *.
       easy. 
Qed.

Local Close Scope nat_scope.


Lemma Cauchy_Schwartz_strict_ver1 : forall {n} (u v : Vector n),
  WF_Matrix u -> WF_Matrix v ->
  (forall c d, c <> C0 \/ d <> C0 -> c .* u <> d .* v) ->
  (Cmod ⟨u,v⟩)^2 < (fst ⟨u,u⟩) * (fst ⟨v,v⟩).
Proof. intros.  
       destruct (Req_dec (fst ⟨v,v⟩) 0). 
       - apply fst_inner_product_zero_iff_zero in H2; auto.
         assert (H' : C0 .* u = C1 .* v).
         subst. lma.
         apply H1 in H'.
         easy.
         right. 
         apply C1_neq_C0.
       - assert (H3 := CS_key_lemma u v).  
         assert (H' : forall r, 0 <= r -> r <> 0 -> 0 < r). 
         intros.  
         lra.
         apply real_gt_0_aux in H3.
         lra.
         apply H'.
         apply inner_product_ge_0.
         apply fst_inner_product_nonzero_iff_nonzero; auto with wf_db.
         assert (H'' : ⟨ v, v ⟩ .* u <> ⟨ v, u ⟩ .* v).
         { apply H1. 
           left.
           contradict H2.
           rewrite H2; easy. }
         contradict H''.
         replace (⟨ v, u ⟩ .* v) with (⟨ v, u ⟩ .* v .+ Zero) by lma.
         rewrite <- H''. 
         lma. (* lma does great here! *)
         apply H'; auto.
         apply inner_product_ge_0.
Qed.

Lemma Cauchy_Schwartz_strict_ver2 : forall {n} (u v : Vector n),
  WF_Matrix u -> WF_Matrix v ->
  linearly_independent (smash u v) ->
  Cmod ⟨u,v⟩ < norm u * norm v.
Proof. intros.
       rewrite <- (sqrt_pow2 (Cmod ⟨ u, v ⟩)), <- (sqrt_pow2 (norm v)), <- (sqrt_pow2 (norm u)).
       rewrite <- sqrt_mult.
       apply sqrt_lt_1.
       all : try apply pow2_ge_0.
       apply Rmult_le_pos.
       all : try apply pow2_ge_0.
       unfold norm.
       rewrite pow2_sqrt, pow2_sqrt.
       apply Cauchy_Schwartz_strict_ver1.
       all : try apply inner_product_ge_0; try apply norm_ge_0; auto.
       intros. 
       apply Classical_Prop.or_not_and in H2.
       contradict H2.
       unfold linearly_independent in H1.
       assert (H' : list2D_to_matrix [[c]; [-d]] = Zero).
       apply H1.
       apply WF_list2D_to_matrix; try easy.
       intros. repeat (destruct H3; subst; try easy).
       replace (@Mmult n (Init.Nat.add (S O) (S O)) (S O)  
                       (smash u v) 
                       (list2D_to_matrix [[c]; [-d]])) with (c .* u .+ (-d) .* v).
       rewrite H2; lma.
       apply mat_equiv_eq; auto with wf_db.
       apply WF_mult; auto with wf_db.
       apply WF_list2D_to_matrix; try easy.
       intros. repeat (destruct H3; subst; try easy).
       unfold mat_equiv; intros. 
       unfold Mmult, smash, list2D_to_matrix, Mplus, scale; simpl.
       destruct j; try lia.
       lca.
       unfold list2D_to_matrix in H'; simpl in H'.
       split.
       replace C0 with (@Zero 2%nat 1%nat 0%nat 0%nat) by easy. 
       rewrite <- H'; easy.
       replace d with (- (- d)) by lca.
       replace (-d) with C0. lca.
       replace C0 with (@Zero 2%nat 1%nat 1%nat 0%nat) by easy. 
       rewrite <- H'; easy.
       apply Cmod_ge_0.
Qed.



