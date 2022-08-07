Require Import VectorStates.

(** This file contains predicates for describing the outcomes of measurement. *)

(** * Probability of outcome ϕ given input ψ *)
Definition probability_of_outcome {n} (ϕ ψ : Vector n) : R :=
  Cmod (inner_product ϕ ψ) ^2.

(** * Probability of measuring ϕ on the first m qubits given (m + n) qubit input ψ *)
Definition prob_partial_meas {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))) :=
  big_sum (fun y => probability_of_outcome (ϕ ⊗ basis_vector (2^n) y) ψ) (2^n).

Lemma probability_of_outcome_comm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = probability_of_outcome ψ ϕ.
Proof.
  intros d ψ ϕ. unfold probability_of_outcome.
  rewrite inner_product_conj_sym.
  rewrite Cmod_Cconj; easy.
Qed.

Lemma probability_of_outcome_is_norm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = ((norm (ϕ† × ψ)) ^ 2)%R.
Proof.
  intros d ψ ϕ.
  unfold probability_of_outcome, Cmod, norm.
  apply f_equal2; try reflexivity.
  apply f_equal.
  unfold Mmult, adjoint.
  simpl.
  autorewrite with R_db.
  reflexivity.
Qed.

Lemma rewrite_I_as_sum : forall m n,
  (m <= n)%nat -> 
  I m = big_sum (fun i => (basis_vector n i) × (basis_vector n i)†) m.
Proof.
  intros.
  induction m.
  simpl.
  unfold I.
  prep_matrix_equality.
  bdestruct_all; reflexivity.
  simpl.
  rewrite <- IHm by lia.
  unfold basis_vector.
  solve_matrix.
  bdestruct_all; simpl; try lca. 
  all: destruct m; simpl; try lca.
  all: bdestruct_all; lca.
Qed.

Lemma prob_partial_meas_alt : 
  forall {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))),
  @prob_partial_meas m n ϕ ψ = ((norm ((ϕ ⊗ I (2 ^ n))† × ψ)) ^ 2)%R.
Proof.
  intros.
  rewrite kron_adjoint, id_adjoint_eq.
  unfold prob_partial_meas.
  rewrite norm_squared.
  unfold inner_product, Mmult, adjoint.
  rewrite (@big_sum_func_distr C R _ C_is_group _ R_is_group), mult_1_l.
  apply big_sum_eq_bounded; intros. 
  unfold probability_of_outcome.
  assert (H' : forall c, ((Cmod c)^2)%R = fst (c^* * c)).
  { intros.
    rewrite <- Cmod_sqr.
    unfold RtoC.
    simpl; lra. }
  rewrite H'. 
  apply f_equal.
  assert (H'' : forall a b, a = b -> a^* * a = b^* * b). { intros; subst; easy. }
  apply H''.
  unfold inner_product, Mmult.
  apply big_sum_eq_bounded; intros. 
  apply f_equal_gen; auto.
  apply f_equal.
  unfold kron, adjoint.
  rewrite Cconj_mult_distr.
  rewrite Nat.div_0_l, Nat.mod_0_l, (Nat.div_small x (2^n)), (Nat.mod_small x); try nia.
  apply f_equal_gen; auto.
  unfold basis_vector, I.
  bdestruct_all; try lia; simpl; try lca.
  intros.
  destruct a; destruct b; easy. 
Qed.

Lemma partial_meas_tensor : 
  forall {m n} (ϕ : Vector (2^m)) (ψ1 : Vector (2^m)) (ψ2 : Vector (2^n)),
  Pure_State_Vector ψ2 ->
  @prob_partial_meas m n ϕ (ψ1 ⊗ ψ2) = probability_of_outcome ϕ ψ1.
Proof.
  intros ? ? ? ? ? [H H0].
  rewrite prob_partial_meas_alt.
  rewrite probability_of_outcome_is_norm.
  unfold norm, inner_product.
  apply f_equal2; try reflexivity.
  do 2 apply f_equal.
  distribute_adjoint.
  Msimpl.
  rewrite H0.
  Msimpl.
  reflexivity.
Qed.
