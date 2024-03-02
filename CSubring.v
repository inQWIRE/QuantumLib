Require Import List.         
Require Import RowColOps.
Require Export Ring.
Require Export Complex.

Open Scope C_scope.
Open Scope group_scope.

(* not really sure what letter is best here for ring *)
Class CSubring F `{Ring F} :=
  { GtoC : F -> C
  ; G_inclusion_C : ring_inclusion_map F C GtoC
  ; Gconj : F -> F
  ; Gconj_Cconj : forall r, Cconj (GtoC r) = GtoC (Gconj r)
  }.


(** these lemmas follow directly from CSubring props, but it is nice to have these which can 
    be used faster *)

(* lemmas about GtoC *)

Lemma GtoC_inj : forall {F} `{CSubring F} (a b : F),
  GtoC a = GtoC b -> a = b.
Proof. intros. 
       assert (H' : ring_inclusion_map F C GtoC). 
       apply G_inclusion_C.
       inversion H'.
       apply H5; easy.
Qed.       

Lemma GtoC_0 : forall {F} `{CSubring F},
  GtoC 0 = 0. 
Proof. intros. 
       destruct G_inclusion_C.  
       apply (ring_homo_id _ _ _ H5).
Qed. 

Lemma GtoC_1 : forall {F} `{CSubring F},
  GtoC 1 = 1. 
Proof. intros. 
       destruct G_inclusion_C.  
       destruct H5.
       easy.
Qed. 

Lemma GtoC_plus : forall {F} `{CSubring F} (a b : F),
  GtoC (a + b) = GtoC a + GtoC b. 
Proof. intros. 
       assert (H' : ring_inclusion_map F C GtoC). 
       apply G_inclusion_C.
       inversion H'; inversion H5; subst.
       rewrite H7; easy.
Qed.  

Lemma GtoC_opp : forall {F} `{CSubring F} (a : F),
  GtoC (- a) = - GtoC a. 
Proof. intros. 
       assert (H' : ring_inclusion_map F C GtoC). 
       apply G_inclusion_C.
       inversion H'; inversion H5; subst.
       erewrite <- ring_homo_opp; easy.
Qed.  

Lemma GtoC_minus : forall {F} `{CSubring F} (a b : F),
  GtoC (a - b) = GtoC a - GtoC b. 
Proof. intros. 
       unfold Gminus.
       rewrite GtoC_plus, GtoC_opp. 
       easy.
Qed.  

Lemma GtoC_mult : forall {F} `{CSubring F} (a b : F),
  GtoC (a * b) = GtoC a * GtoC b. 
Proof. intros. 
       assert (H' : ring_inclusion_map F C GtoC). 
       apply G_inclusion_C.
       inversion H'; inversion H5; subst.
       rewrite H8; easy.
Qed.

Lemma Csubring_mult_comm : forall {F} `{CSubring F} (a b : F),
  a * b = b * a.
Proof. intros. 
       apply GtoC_inj.
       rewrite 2 GtoC_mult.
       lca.
Qed.

Global Program Instance Csubring_is_comm_ring : forall {F} `{CSubring F}, Comm_Ring F.
Next Obligation. apply Csubring_mult_comm. Qed.



(* Lemmas about Gconj *)

Lemma Gconj_0 : forall {F} `{CSubring F}, Gconj 0 = 0.                  
Proof. intros. 
       apply GtoC_inj.
       erewrite <- Gconj_Cconj, ring_homo_id.
       replace 0 with C0 by easy.
       apply Cconj_0.
       apply G_inclusion_C.
Qed.

Lemma Gconj_involutive : forall {F} `{CSubring F} (c : F), Gconj (Gconj c) = c. 
Proof. intros.
       apply GtoC_inj.
       erewrite <- 2 Gconj_Cconj, Cconj_involutive. 
       easy.
Qed.

Lemma Gconj_plus_distr : forall {F} `{CSubring F} (x y : F), Gconj (x + y) = Gconj x + Gconj y. 
Proof. intros. 
       apply GtoC_inj.
       rewrite GtoC_plus, <- 3 Gconj_Cconj, GtoC_plus.
       apply Cconj_plus_distr.
Qed.

Lemma Gconj_minus_distr : forall {F} `{CSubring F} (x y : F), Gconj (x - y) = Gconj x - Gconj y. 
Proof. intros. 
       apply GtoC_inj.
       rewrite GtoC_minus, <- 3 Gconj_Cconj, GtoC_minus.
       apply Cconj_minus_distr.
Qed.

Lemma Gconj_mult_distr : forall {F} `{CSubring F} (x y : F), Gconj (x * y) = Gconj x * Gconj y. 
Proof. intros. 
       apply GtoC_inj.
       rewrite GtoC_mult, <- 3 Gconj_Cconj, GtoC_mult.
       apply Cconj_mult_distr.
Qed.




(** Defining adjoint *)


Definition adjoint {F : Type} `{CSubring F} {m n} (A : GenMatrix F m n) : GenMatrix F n m := 
  fun x y => Gconj (A y x).


(* TODO: remove redundant definition in GenMatrix.v *)
Definition Cinner_product {F : Type} `{CSubring F} {n} (u v : Vector F n) : F := 
  GMmult (adjoint u) (v) O O.

Definition Couter_product {F : Type} `{CSubring F} {n} (u v : Vector F n) : Square F n := 
  GMmult u (adjoint v).

Notation "A †" := (adjoint A) (at level 0) : genmatrix_scope.
Notation "⟨ u , v ⟩" := (Cinner_product u v) (at level 0) : genmatrix_scope. 



Lemma WF_adjoint : forall {F : Type} `{CSubring F} {m n : nat} (A : GenMatrix F m n), 
      WF_GenMatrix A -> WF_GenMatrix A†. 
Proof. intros. 
       unfold WF_GenMatrix, adjoint; intros. 
       rewrite H4; try lia.
       apply GtoC_inj.
       rewrite <- Gconj_Cconj.
       erewrite ring_homo_id.
       lca.
       apply G_inclusion_C.
Qed.


Theorem adjoint_involutive : forall {F : Type} `{CSubring F} (m n : nat) (A : GenMatrix F m n), 
    A†† = A. 
Proof. intros.
       unfold adjoint. 
       prep_genmatrix_equality.
       rewrite Gconj_involutive.
       easy. 
Qed.

Lemma id_adjoint_eq : forall {F : Type} `{CSubring F} (n : nat), (I n)† = (I n).
Proof. intros.
       unfold adjoint, I.
       prep_genmatrix_equality.
       bdestruct (y =? x); bdestruct (x =? y); bdestruct (y <? n); bdestruct (x <? n);
         try lia; apply GtoC_inj; rewrite <- Gconj_Cconj; simpl; 
         try rewrite GtoC_0; try rewrite GtoC_1; lca.
Qed.

Lemma zero_adjoint_eq : forall {F : Type} `{CSubring F} m n, (@Zero F _ m n)† = @Zero F _ n m.
Proof. intros. 
       unfold adjoint, Zero. rewrite Gconj_0. reflexivity. 
Qed.

Lemma Mscale_adj : forall {F : Type} `{CSubring F} (m n : nat) (x : F) (A : GenMatrix F m n),
    (x .* A)† = Gconj x .* A†.
Proof.
  intros.
  unfold scale, adjoint.
  prep_genmatrix_equality.
  rewrite Gconj_mult_distr.          
  reflexivity.
Qed.

Lemma Mplus_adjoint : forall {F : Type} `{CSubring F} (m n : nat) (A B : GenMatrix F m n),
  (A .+ B)† = A† .+ B†.
Proof.  
  intros.
  unfold GMplus, adjoint.
  prep_genmatrix_equality.
  rewrite Gconj_plus_distr.
  reflexivity.
Qed.

Lemma Mmult_adjoint : forall {F : Type} `{CSubring F} {m n o : nat} 
                        (A : GenMatrix F m n) (B : GenMatrix F n o),
      (A × B)† = B† × A†.
Proof.
  intros.
  unfold GMmult, adjoint.
  prep_genmatrix_equality.
  erewrite (@big_sum_func_distr F F _ H0 _ H0). 
  apply big_sum_eq.  
  apply functional_extensionality. intros z.
  rewrite Gconj_mult_distr.
  rewrite Csubring_mult_comm.
  reflexivity.
  intros; apply Gconj_plus_distr. 
Qed.

Lemma kron_adjoint : forall {F : Type} `{CSubring F} {m n o p : nat} 
                       (A : GenMatrix F m n) (B : GenMatrix F o p),
  (A ⊗ B)† = A† ⊗ B†.
Proof. 
  intros. unfold adjoint, Gkron. 
  prep_genmatrix_equality.
  rewrite Gconj_mult_distr.
  reflexivity.
Qed.

Local Close Scope nat_scope.

(* some inner product lemmas *)
Lemma inner_product_scale_l : forall {F : Type} `{CSubring F} {n} (u v : Vector F n) (c : F),
  ⟨c .* u, v⟩ = Gconj c * ⟨u,v⟩.
Proof. intros.
       unfold Cinner_product, scale, adjoint, GMmult.
       rewrite big_sum_mult_l.  
       apply big_sum_eq_bounded; intros.
       rewrite Gconj_mult_distr.

       
       solve_comm_monoid.
       Set Printing All. 
       
       
Qed.       

Lemma inner_product_scale_r : forall {F : Type} `{CSubring F} {n} (u v : Vector F n) (c : F),
  ⟨u, c .* v⟩ = c * ⟨u,v⟩.
Proof. intros.
       unfold Cinner_product, scale, adjoint, GMmult.
       rewrite big_sum_mult_l. 
       apply big_sum_eq_bounded; intros.
       solve_comm_ring; auto.
Qed.       

Lemma inner_product_plus_l : forall {F : Type} `{CSubring F} {n} (u v w : Vector F n),
  ⟨u .+ v, w⟩ = ⟨u, w⟩ + ⟨v, w⟩.
Proof. intros.
       unfold Cinner_product, scale, adjoint, GMplus, GMmult.
       rewrite <- big_sum_plus. 
       apply big_sum_eq_bounded; intros.
       rewrite Gconj_plus_distr.
       solve_comm_ring; auto.
Qed.       

Lemma inner_product_plus_r : forall {F : Type} `{CSubring F} {n} (u v w : Vector F n),
  ⟨u, v .+ w⟩ = ⟨u, v⟩ + ⟨u, w⟩.
Proof. intros.
       unfold Cinner_product, scale, adjoint, GMplus, GMmult.
       rewrite <- big_sum_plus. 
       apply big_sum_eq_bounded; intros.  
       solve_comm_ring; auto.
Qed.    
 
Lemma inner_product_big_sum_l : forall {F : Type} `{CSubring F} {n} (u : Vector F n) 
                                       (f : nat -> Vector F n) (k : nat),
  ⟨big_sum f k, u⟩ = big_sum (fun i => ⟨f i, u⟩) k.
Proof. induction k.
       - unfold Cinner_product; simpl.
         rewrite zero_adjoint_eq, GMmult_0_l; try easy.
         apply Csubring_is_comm_ring.
       - simpl. 
         rewrite inner_product_plus_l, IHk.
         reflexivity.
Qed.       

Lemma inner_product_big_sum_r : forall {F : Type} `{CSubring F} {n} (u : Vector F n) 
                                       (f : nat -> Vector F n) (k : nat),
  ⟨u, big_sum f k⟩ = big_sum (fun i => ⟨u, f i⟩) k.
Proof. induction k.
       - unfold Cinner_product; simpl.
         rewrite GMmult_0_r; try easy.
         apply Csubring_is_comm_ring.
       - simpl. 
         rewrite inner_product_plus_r, IHk.
         reflexivity.
Qed.       

Lemma inner_product_conj_sym : forall {F : Type} `{CSubring F} {n} (u v : Vector F n),
  ⟨u, v⟩ = Gconj ⟨v, u⟩.
Proof. intros. 
       unfold Cinner_product, adjoint, GMmult.
       rewrite (@big_sum_func_distr F F _ H0 _ H0).
       apply big_sum_eq_bounded; intros.
       rewrite Gconj_mult_distr, Gconj_involutive.
       solve_comm_ring; auto.
       intros.
       rewrite Gconj_plus_distr; auto.
Qed.

Lemma inner_product_mafe_WF_l : forall {F : Type} `{CSubring F} {n} (u v : Vector F n),
  ⟨u, v⟩ = ⟨make_WF u, v⟩.
Proof. intros. 
       unfold Cinner_product, adjoint, GMmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.

Lemma inner_product_mafe_WF_r : forall {F : Type} `{CSubring F} {n} (u v : Vector F n),
  ⟨u, v⟩ = ⟨u, make_WF v⟩.
Proof. intros. 
       unfold Cinner_product, adjoint, GMmult, make_WF.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; simpl; easy.
Qed.



(** Norm and normalization *)


(* TODO: make another restriction so that square roots exist so vectors can be normalized *) 
Definition norm_sqr {F : Type} `{CSubring F} {n} (ψ : Vector F n) : F :=
  ⟨ψ,ψ⟩.

(* we can at least get the norm in R *)
Definition norm_R {F : Type} `{CSubring F} {n} (ψ : Vector F n) : R :=
  sqrt (fst (GtoC ⟨ψ,ψ⟩)).

(*
Definition normalize {n} (ψ : Vector n) :=
  / (norm ψ) .* ψ.

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
       rewrite Rinv_mult_distr; try easy. 
       rewrite <- Rmult_comm.
       rewrite <- Rmult_assoc.
       rewrite Rinv_r; try easy.
       autorewrite with R_db.
       reflexivity. 
       unfold Cinv.
       simpl. 
       autorewrite with R_db.
       rewrite Rinv_mult_distr; try easy. 
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
Qed. *)

(* "Quick" proof of |x| = 0 iff x = 0 *)
Lemma inner_product_zero_iff_zero : forall {F : Type} `{CSubring F} {n} (v : Vector F n),
  WF_GenMatrix v -> (⟨v,v⟩ = 0 <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         destruct (genmat_equiv_dec _ _ _ _ _ v Zero).
         apply genmat_equiv_eq; try easy.
         assert (H' : v <> Zero). 
         { unfold not; intros. 
           apply n0. rewrite H6.
           easy. }
         eapply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         unfold WF_GenMatrix in H4.
         bdestruct (x <? n)%nat.
         assert (H0' := Rle_0_sqr).  
         unfold Rsqr in H0'. 
         assert (H' : (0 < fst (GtoC (Cinner_product v v)))%R).
         { unfold Cinner_product.
           unfold GMmult. 
           rewrite (@big_sum_func_distr F C _ H0 _ C_is_group).
           apply big_sum_gt_0.
           unfold adjoint. 
           intros.
           rewrite GtoC_mult, <- Gconj_Cconj, <- Cmod_sqr.
           simpl. autorewrite with R_db.
           apply H0'. 
           exists x. split; try easy.
           unfold adjoint. 
           rewrite GtoC_mult, <- Gconj_Cconj, <- Cmod_sqr.
           simpl. autorewrite with R_db.
           assert (H' : (0 <= Cmod (GtoC (v x 0%nat)) * Cmod (GtoC (v x 0%nat)))%R). 
           { apply H0'. } 
           destruct H'; try easy. 
           assert (H' := Rsqr_0_uniq).
           unfold Rsqr in H'. 
           assert (H'' : forall a b : R, a = b -> b = a). { easy. }
           apply H'' in H8. 
           apply H' in H8.
           apply Cmod_eq_0 in H8.
           assert (GtoC_0' := GtoC_0).
           simpl in GtoC_0'.
           rewrite <- GtoC_0' in H8.
           apply GtoC_inj in H8.
           easy.
           intros. 
           apply GtoC_plus. }
         rewrite H5, GtoC_0 in H'. 
         simpl in H'. lra. 
         assert (H' : v x O = 0).
         { apply H4. left; easy. }
         easy.
         apply H2.
       - intros. 
         unfold Cinner_product.  
         rewrite H5. 
         rewrite GMmult_0_r. 
         easy.
         apply Csubring_is_comm_ring.
Qed.

(*
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
*)

Local Close Scope nat_scope.




(** Defining WF_Unitary *)


Definition WF_Unitary {F : Type} `{CSubring F} {n} (U : GenMatrix F n n) : Prop :=
  WF_GenMatrix U /\ U † × U = I n.




(*
 *
 *
 *)
