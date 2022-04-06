Require Import VectorStates.

(** This file contains predicates for describing the outcomes of measurement. *)

(** * Probability of outcome ϕ given input ψ *)
Definition probability_of_outcome {n} (ϕ ψ : Vector n) : R :=
  let c := (ϕ† × ψ) O O in
  (Cmod c) ^ 2.

(** * Probability of measuring ϕ on the first m qubits given (m + n) qubit input ψ *)
Definition prob_partial_meas {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))) :=
  big_sum (fun y => probability_of_outcome (ϕ ⊗ basis_vector (2^n) y) ψ) (2^n).

Lemma probability_of_outcome_comm : forall {d} (ϕ ψ : Vector d),
  probability_of_outcome ϕ ψ = probability_of_outcome ψ ϕ.
Proof.
  intros d ψ ϕ. unfold probability_of_outcome.
  replace (ϕ † × ψ) with (ϕ † × ψ ††) by (rewrite adjoint_involutive; easy).
  rewrite <- Mmult_adjoint.
  unfold adjoint.
  rewrite Cmod_Cconj.
  reflexivity.
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

(* 
Lemma Rsum_Msum : forall n (f : nat -> Square 1),
  big_sum (fun i : nat => fst (f i O O)) n = fst (big_sum f O O n).
Proof.
  intros.
  rewrite Msum_Csum.
  rewrite <- Rsum_Csum.
  induction n; simpl.
  reflexivity.
  rewrite IHn.
  reflexivity.
Qed.
*)

Lemma prob_partial_meas_alt : 
  forall {m n} (ϕ : Vector (2^m)) (ψ : Vector (2^(m + n))),
  @prob_partial_meas m n ϕ ψ = ((norm ((ϕ ⊗ I (2 ^ n))† × ψ)) ^ 2)%R.
Proof.
  intros.
  unfold prob_partial_meas.
  erewrite big_sum_eq.
  2: { intros.
       apply functional_extensionality; intros. 
       rewrite probability_of_outcome_is_norm.
       unfold norm.
       rewrite pow2_sqrt.
       restore_dims.
       distribute_adjoint.
       Msimpl.
       repeat rewrite Mmult_assoc.
       restore_dims.
       rewrite <- (Mmult_assoc (ϕ ⊗ _)).
       rewrite kron_mixed_product.
       unify_pows_two.
       rewrite <- Mmult_assoc.
       reflexivity. 
       apply inner_product_ge_0. }  
  rewrite rewrite_I_as_sum by lia.
  rewrite kron_Msum_distr_l.
  rewrite Msum_adjoint.
  erewrite big_sum_eq_bounded.
  2: { intros. distribute_adjoint. reflexivity. }
  rewrite Mmult_Msum_distr_r.
  unfold norm.
  rewrite pow2_sqrt.
  2: apply inner_product_ge_0.
  rewrite Msum_adjoint, Mmult_Msum_distr_l.
  erewrite big_sum_eq_bounded.
  2: { intros.
       Admitted. 

(*
       rewrite Mmult_Msum_distr_r. 
       erewrite big_sum_eq_bounded.
       2: { intros.
            distribute_adjoint.
            Msimpl.
            repeat rewrite Mmult_assoc.
            restore_dims.
            rewrite <- (Mmult_assoc (ϕ ⊗ _)).
            rewrite kron_mixed_product.
            repeat rewrite Mmult_assoc.
            rewrite <- (Mmult_assoc (_†)).
            reflexivity. } 
       reflexivity. }
  rewrite Msum_diagonal.
  2: { intros. rewrite basis_vector_product_neq by auto.
       do 2 Msimpl. reflexivity. }
  erewrite big_sum_eq_bounded.
  2: { intros. rewrite basis_vector_product_eq by assumption.
       Msimpl. unify_pows_two.
       repeat rewrite <- Mmult_assoc.
       reflexivity. }
  remember (fun i : nat => ψ† × (ϕ × ϕ† ⊗ (basis_vector (2 ^ n) i × (basis_vector (2 ^ n) i) †)) × ψ) as f.
  erewrite Rsum_eq.
  2: { intros.
       replace (ψ† × (ϕ × ϕ† ⊗ (basis_vector (2 ^ n) i × (basis_vector (2 ^ n) i) †)) × ψ) with (f i) by (subst; reflexivity).
       reflexivity. }
  apply Rsum_Msum.
Qed.

*)

Lemma partial_meas_tensor : 
  forall {m n} (ϕ : Vector (2^m)) (ψ1 : Vector (2^m)) (ψ2 : Vector (2^n)),
  Pure_State_Vector ψ2 ->
  @prob_partial_meas m n ϕ (ψ1 ⊗ ψ2) = probability_of_outcome ϕ ψ1.
Proof.
  intros ? ? ? ? ? [H H0].
  rewrite prob_partial_meas_alt.
  rewrite probability_of_outcome_is_norm.
  unfold norm.
  apply f_equal2; try reflexivity.
  do 2 apply f_equal.
  distribute_adjoint.
  Msimpl.
  rewrite H0.
  Msimpl.
  reflexivity.
Qed.
