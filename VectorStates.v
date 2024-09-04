Require Export Pad.
Require Export CauchySchwarz.
Require Import PermutationInstances.
Require Export Bits.

(* This file provides abstractions for describing quantum states as vectors.
   - f_to_vec describes classical states as boolean functions
   - basis_vector describes classical states as natural numbers
   - vsum describes superposition states
   - vkron describes states as the tensor product of qubit states

   It also provides automation (ket_db, f_to_vec_db) for simplifying
   matrix × vector expressions. *)


(************************************)
(* Unitary Properties on Basis Kets *)
(************************************)

Notation "∣ + ⟩" := (/√2 .* ∣ 0 ⟩ .+ /√2 .* ∣ 1 ⟩).
Notation "∣ - ⟩" := (/√2 .* ∣ 0 ⟩ .+ (-/√2) .* ∣ 1 ⟩).

(* Bra-Ket properties *)

Lemma bra0_equiv : ⟨0∣ = bra 0.
Proof. reflexivity. Qed.

Lemma bra1_equiv : ⟨1∣ = bra 1.
Proof. reflexivity. Qed.

Lemma ket0_equiv : ∣0⟩ = ket 0.
Proof. reflexivity. Qed.

Lemma ket1_equiv : ∣1⟩ = ket 1.
Proof. reflexivity. Qed.

Lemma plus_equiv : ∣+⟩ = ∣ + ⟩.
Proof. lma'. Qed.

Lemma minus_equiv : ∣-⟩ = ∣ - ⟩.
Proof. lma'. Qed.

Lemma bra0_eqb : ⟨0∣ = (fun i j => if (i =? 0) && (j =? 0) then C1 else C0).
Proof. lma'. intros i j []; Modulus.bdestructΩ'. Qed.

Lemma bra1_eqb : ⟨1∣ = (fun i j => if (i =? 0) && (j =? 1) then C1 else C0).
Proof. lma'. intros i j []; Modulus.bdestructΩ'. Qed.

Lemma ket0_eqb : ∣0⟩ = (fun i j => if (i =? 0) && (j =? 0) then C1 else C0).
Proof. lma'. intros i j []; Modulus.bdestructΩ'. Qed.

Lemma ket1_eqb : ∣1⟩ = (fun i j => if (i =? 1) && (j =? 0) then C1 else C0).
Proof. lma'. intros i j []; Modulus.bdestructΩ'. Qed.

Lemma bra0ket0 : bra 0 × ket 0 = I 1.
Proof. lma'. Qed.

Lemma bra0ket1 : bra 0 × ket 1 = Zero.
Proof. lma'. Qed.

Lemma bra1ket0 : bra 1 × ket 0 = Zero.
Proof. lma'. Qed.

Lemma bra1ket1 : bra 1 × ket 1 = I 1.
Proof. lma'. Qed.

Lemma bra0ket_eqb i : bra 0 × ket i =
  if i =? 0 then I 1 else Zero.
Proof.
  destruct i; simpl. 
  - apply bra0ket0.
  - apply bra0ket1.
Qed.

Lemma bra1ket_eqb i : bra 1 × ket i =
  if i =? 0 then Zero else I 1.
Proof.
  destruct i; simpl. 
  - apply bra1ket0.
  - apply bra1ket1.
Qed.

(* Hadamard properties *)
Lemma H0_spec : hadamard × ∣ 0 ⟩ = ∣ + ⟩.
Proof. lma'. Qed.

Lemma H1_spec : hadamard × ∣ 1 ⟩ = ∣ - ⟩.
Proof. lma'. Qed.

Lemma Hplus_spec : hadamard × ∣ + ⟩ = ∣ 0 ⟩.
Proof. solve_matrix_fast_with 
  (autounfold with U_db) (try lca; C_field; lca). Qed.

Lemma Hminus_spec : hadamard × ∣ - ⟩ = ∣ 1 ⟩.
Proof. solve_matrix_fast_with 
  (autounfold with U_db) (try lca; C_field; lca). Qed.

Local Open Scope nat_scope. 


(* TODO: make general *)                                            
Lemma H0_kron_n_spec : forall n,
  n ⨂ hadamard × n ⨂ ∣0⟩ = n ⨂ ∣+⟩.
Proof.
  intros n.
  rewrite kron_n_mult.
  rewrite ket0_equiv, plus_equiv.
  now rewrite H0_spec.
Qed.

Local Close Scope nat_scope. 

Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.
Local Coercion Nat.b2n : bool >-> nat.

(* X properties *)
Lemma X0_spec : σx × ∣ 0 ⟩ = ∣ 1 ⟩.
Proof. lma'. Qed.

Lemma X1_spec : σx × ∣ 1 ⟩ = ∣ 0 ⟩.
Proof. lma'. Qed.

Lemma X_specb (b : bool) : σx × ∣ b ⟩ = ∣ negb b ⟩.
Proof.
  destruct b.
  - apply X1_spec.
  - apply X0_spec.
Qed.

(* Y properties *)
Lemma Y0_spec : σy × ∣ 0 ⟩ = Ci .* ∣ 1 ⟩.
Proof. lma'. Qed.

Lemma Y1_spec : σy × ∣ 1 ⟩ = -Ci .* ∣ 0 ⟩.
Proof. lma'. Qed.

Lemma Y_specb (b : bool) : 
  σy × ∣ b ⟩ = (-1)^b * Ci .* ∣ negb b ⟩.
Proof.
  destruct b.
  - simpl. rewrite Y1_spec.
    f_equal; lca.
  - simpl. rewrite Y0_spec.
    f_equal; lca.
Qed.

(* Z properties *)
Lemma Z0_spec : σz × ∣ 0 ⟩ = ∣ 0 ⟩.
Proof. lma'. Qed.

Lemma Z1_spec : σz × ∣ 1 ⟩ = -1 .* ∣ 1 ⟩.
Proof. lma'. Qed.

Lemma Z_specb (b : bool) : 
  σz × ∣ b ⟩ = (-1)^b .* ∣ b ⟩.
Proof.
  destruct b.
  - simpl. rewrite Z1_spec.
    now Csimpl.
  - simpl. rewrite Z0_spec.
    now rewrite Mscale_1_l.
Qed.

Lemma Z_bspec (b : bool) : 
  bra b × σz = (-1)^b .* bra b.
Proof.
  destruct b.
  - simpl. lma'.
  - simpl. lma'.
Qed.

Lemma MmultZ1 : σz × ∣1⟩ = - C1 .* ∣1⟩.
Proof. rewrite ket1_equiv, Z1_spec. f_equal; lca. Qed.

Lemma MmultZ0 : σz × ∣0⟩ = ∣0⟩.
Proof. rewrite ket0_equiv, Z0_spec. reflexivity. Qed.

Lemma Mmult1Z : ⟨1∣ × σz = - C1 .* ⟨1∣.
Proof. lma'. Qed.

Lemma Mmult0Z : ⟨0∣ × σz = ⟨0∣.
Proof. lma'. Qed.

(* phase shift properties *)
Lemma phase0_spec : forall ϕ, phase_shift ϕ × ket 0 = ket 0.
Proof. intros. lma'. Qed.

Lemma phase1_spec : forall ϕ, phase_shift ϕ × ket 1 = Cexp ϕ .* ket 1.
Proof. intros. lma'. Qed.

Lemma phase_shift_on_ket : forall (θ : R) (b : bool),
  phase_shift θ × ∣ b ⟩ = (Cexp (b * θ)) .* ∣ b ⟩.
Proof.
  intros.
  destruct b; simpl;
    [rewrite Rmult_1_l | rewrite Rmult_0_l, Cexp_0]; 
    solve_matrix_fast.
Qed.

Lemma hadamard_on_ket : forall (b : bool),
  hadamard × ∣ b ⟩ = /√2 .* (∣ 0 ⟩ .+ (-1)^b .* ∣ 1 ⟩).
Proof.
  intros.
  destruct b; solve_matrix_fast.
Qed.

(* CNOT properties *)

Lemma CNOT00_spec : cnot × ∣ 0,0 ⟩ = ∣ 0,0 ⟩.
Proof. lma'. Qed.

Lemma CNOT01_spec : cnot × ∣ 0,1 ⟩ = ∣ 0,1 ⟩.
Proof. lma'. Qed.

Lemma CNOT10_spec : cnot × ∣ 1,0 ⟩ = ∣ 1,1 ⟩.
Proof. lma'. Qed.
                                        
Lemma CNOT11_spec : cnot × ∣ 1,1 ⟩ = ∣ 1,0 ⟩.
Proof. lma'. Qed.

Lemma CNOT_spec : forall (x y : nat), (x < 2)%nat -> (y < 2)%nat -> 
  cnot × ∣ x,y ⟩ = ∣ x, (x + y) mod 2 ⟩.
Proof.
  by_cell_no_intros.
  - apply CNOT00_spec.
  - apply CNOT01_spec.
  - apply CNOT10_spec.
  - apply CNOT11_spec.
Qed.



(* SWAP properties *)

Lemma SWAP_spec : forall x y, swap × ∣ x,y ⟩ = ∣ y,x ⟩.
Proof. intros. apply swap_spec; auto_wf. Qed.

(* Automation *)

(* General matrix rewrites *)
#[global] Hint Rewrite bra0_equiv bra1_equiv ket0_equiv ket1_equiv : ket_db.
#[global] Hint Rewrite bra0ket0 bra0ket1 bra1ket0 bra1ket1 : ket_db.
#[global] Hint Rewrite Mmult_plus_distr_l Mmult_plus_distr_r kron_plus_distr_l kron_plus_distr_r Mscale_plus_distr_r : ket_db.
#[global] Hint Rewrite Mscale_mult_dist_l Mscale_mult_dist_r Mscale_kron_dist_l Mscale_kron_dist_r : ket_db.
#[global] Hint Rewrite Mscale_assoc @Mmult_assoc : ket_db.
#[global] Hint Rewrite Mmult_1_l Mmult_1_r kron_1_l kron_1_r Mscale_0_l Mscale_0_r Mscale_1_l Mplus_0_l Mplus_0_r using (auto with wf_db) : ket_db.
#[global] Hint Rewrite kron_0_l kron_0_r Mmult_0_l Mmult_0_r : ket_db.
#[global] Hint Rewrite @kron_mixed_product : ket_db.

(* Quantum-specific identities *)
#[global] Hint Rewrite H0_spec H1_spec Hplus_spec Hminus_spec X0_spec X1_spec Y0_spec Y1_spec
     Z0_spec Z1_spec phase0_spec phase1_spec : ket_db.
#[global] Hint Rewrite CNOT00_spec CNOT01_spec CNOT10_spec CNOT11_spec SWAP_spec : ket_db.

Lemma ket2bra : forall n, (ket n) † = bra n. 
Proof. destruct n; reflexivity. Qed.
#[global] Hint Rewrite ket2bra : ket_db.

(* TODO: add transpose and adjoint lemmas to ket_db? *)
Lemma ket0_transpose_bra0 : (ket 0) ⊤ = bra 0.
Proof. lma'. Qed.

Lemma ket1_transpose_bra1 : (ket 1) ⊤ = bra 1.
Proof. lma'. Qed.

Lemma bra0_transpose_ket0 : (bra 0) ⊤ = ket 0.
Proof. lma'. Qed.

Lemma bra1_transpose_ket1 : (bra 1) ⊤ = ket 1.
Proof. lma'. Qed.

Lemma bra1_adjoint_ket1 : (bra 1) † = ket 1.
Proof. lma'. Qed.

Lemma ket1_adjoint_bra1 : (ket 1) † = bra 1.
Proof. lma'. Qed.

Lemma bra0_adjoint_ket0 : (bra 0) † = ket 0.
Proof. lma'. Qed.

Lemma ket0_adjoint_bra0 : (ket 0) † = bra 0.
Proof. lma'. Qed.

(* Examples using ket_db *)
Lemma XYZ0 : -Ci .* σx × σy × σz × ∣ 0 ⟩ = ∣ 0 ⟩.
Proof. autorewrite with ket_db C_db; easy. Qed.
                                           
Lemma XYZ1 : -Ci .* σx × σy × σz × ∣ 1 ⟩ = ∣ 1 ⟩.
Proof. 
  autorewrite with ket_db C_db.
  replace (Ci * -1 * Ci) with (RtoC 1) by lca. 
  apply Mscale_1_l.
Qed.


(*******************************)
(**      Classical States     **)
(*******************************)

Local Close Scope C_scope.
Local Close Scope R_scope.
Local Open Scope nat_scope. 

(* Convert a boolean function to a vector; examples: 
     f_to_vec 3 f --> I 1 ⊗ ∣ f 0 ⟩ ⊗ ∣ f 1 ⟩ ⊗ | f 2 ⟩ 
     f_to_vec 2 (shift f 2) -->  I 1 ⊗ ∣ f 2 ⟩ ⊗ ∣ f 3 ⟩ 
*)
Fixpoint f_to_vec (n : nat) (f : nat -> bool) : Vector (2^n) :=
  match n with 
  | 0 => I 1
  | S n' =>  (f_to_vec n' f) ⊗ ∣ f n' ⟩
  end.

Lemma f_to_vec_WF : forall (n : nat) (f : nat -> bool),
  WF_Matrix (f_to_vec n f).
Proof.
  intros.
  induction n; simpl; try auto with wf_db.
Qed.
#[export] Hint Resolve f_to_vec_WF : wf_db.

Lemma f_to_vec_eq : forall n f f',
  (forall i, i < n -> f i = f' i) ->
  f_to_vec n f = f_to_vec n f'.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  replace (f' n) with (f n) by auto.
  rewrite IHn by auto.
  reflexivity.
Qed.

(* Convert a natural number to a vector *)


(* TODO: this is very similar to e_i in VecSet.v. Could use just e_i? *)
Definition basis_vector (n k : nat) : Vector n :=
  fun i j => if (i =? k) && (j =? 0) then C1 else C0.

Lemma basis_vector_WF : forall n i, (i < n)%nat -> WF_Matrix (basis_vector n i).
Proof.
  unfold basis_vector, WF_Matrix.
  intros.
  bdestruct (n <=? x)%nat; bdestruct (1 <=? y)%nat; try lia.
  bdestructΩ (x =? i)%nat. reflexivity.
  bdestructΩ (x =? i)%nat. reflexivity.
  bdestructΩ (y =? 0)%nat. rewrite andb_false_r. reflexivity.
Qed.
#[export] Hint Resolve basis_vector_WF : wf_db.

Lemma basis_vector_product_eq : forall d n,
  n < d -> (basis_vector d n)† × basis_vector d n = I 1.
Proof.
  intros. 
  prep_matrix_equality.
  unfold basis_vector, adjoint, Mmult, I.
  bdestruct (x =? y); bdestruct (x <? 1); simpl.
  apply big_sum_unique.
  exists n.
  repeat split; auto.
  bdestruct_all; simpl; lca.
  intros i Hi. bdestructΩ (i =? n).
  intros. lca.
  all: apply (@big_sum_0 C C_is_monoid); intro i; bdestruct_all; simpl; lca.
Qed.

Lemma basis_vector_pure_state : forall n i,
  (i < n)%nat -> Pure_State_Vector (basis_vector n i).
Proof.
  intros. split. apply basis_vector_WF. easy.
  apply basis_vector_product_eq. easy.
Qed.

Lemma basis_vector_product_neq : forall d m n,
  (m < d)%nat -> (n < d)%nat -> (m <> n)%nat -> (basis_vector d m)† × basis_vector d n = Zero.
Proof.
  intros.
  prep_matrix_equality.
  unfold basis_vector, adjoint, Mmult, Zero.
  apply (@big_sum_0 C C_is_monoid). 
  intro i; bdestruct_all; lca.
Qed.

Lemma matrix_times_basis_eq : forall m n (A : Matrix m n) i j,
  WF_Matrix A ->
  (A × basis_vector n j) i 0 = A i j.
Proof.
  intros m n A i j WFA.
  unfold basis_vector.
  unfold Mmult.
  bdestruct (j <? n).
  2:{ rewrite big_sum_0. rewrite WFA; auto. 
      intros j'. bdestruct (j' =? j); subst; simpl; try lca.
      rewrite WFA by auto. lca. }
  erewrite big_sum_unique.
  reflexivity.
  exists j.
  repeat split; trivial.
  rewrite 2 Nat.eqb_refl; simpl; lca.
  intros j' Hj.
  bdestruct_all; auto. 
  all : intros; simpl; try lca.
  subst; easy.
Qed.

Lemma equal_on_basis_vectors_implies_equal : forall m n (A B : Matrix m n),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall k, k < n -> A × (basis_vector n k) = B × (basis_vector n k)) ->
  A = B.
Proof.
  intros m n A B WFA WFB H.
  prep_matrix_equality.
  bdestruct (y <? n). 2: rewrite WFA, WFB; auto.
  rewrite <- matrix_times_basis_eq; trivial.
  rewrite H; trivial.
  rewrite matrix_times_basis_eq; easy.
Qed.

Lemma divmod_decomp : forall x y z r,
    (r > 0)%nat ->
    (z < r)%nat ->
    (x = y * r + z <-> x / r = y /\ x mod r = z)%nat.
Proof.
  split; intros.
  - split. symmetry. apply Nat.div_unique with (r := z); try lia.
    symmetry. apply Nat.mod_unique with (q := y); try lia.
  - destruct H1.
    replace (y * r)%nat with (r * y)%nat by lia.
    rewrite <- H1, <- H2.
    apply Nat.div_mod.
    lia.
Qed.

Lemma split_basis_vector : forall m n x y,
  (x < 2 ^ m)%nat ->
  (y < 2 ^ n)%nat ->
  basis_vector (2 ^ (m + n)) (x * 2 ^ n + y)
    = basis_vector (2 ^ m) x ⊗ basis_vector (2 ^ n) y.
Proof.
  intros m n x y Hx Hy.
  apply mat_equiv_eq; 
  [apply basis_vector_WF; Modulus.show_moddy_lt|auto_wf|].
  unfold kron, basis_vector.
  intros i j Hi Hj.
  replace j with 0 by lia.
  Modulus.simpl_bools.
  rewrite Cmult_if_if_1_l.
  rewrite Modulus.eqb_comb_iff_div_mod_eqb by easy.
  now rewrite andb_comm.
Qed.

(* rewrite f_to_vec as basis_vector *)
Lemma basis_f_to_vec : forall n f,
  f_to_vec n f = basis_vector (2^n) (funbool_to_nat n f).
Proof.
  intros.
  induction n.
  - unfold funbool_to_nat; simpl.
    solve_matrix_fast.
  - pose proof (funbool_to_nat_bound (S n) f). 
    prep_matrix_equivalence.
    cbn -[Nat.pow Nat.mul].
    rewrite IHn.
    unfold funbool_to_nat; cbn -[Nat.pow Nat.mul].
    unfold basis_vector.
    intros i j Hi Hj.
    replace j with 0 by lia.
    unfold kron. 
    rewrite Nat.div_1_r, Nat.mod_1_r.
    Modulus.simpl_bools.
    rewrite Nat.add_comm, Nat.mul_comm.
    rewrite Modulus.eqb_comb_iff_div_mod_eqb 
      by (destruct (f n); simpl; lia).
    rewrite andb_comm, <- Cmult_if_if_1_l.
    f_equal.
    generalize (Nat.mod_upper_bound i 2 ltac:(lia)).
    generalize (f n) (i mod 2).
    now intros []; (intros [|[]]; [..|easy]).
Qed.

(* rewrite basis_vector as f_to_vec *)
Lemma basis_f_to_vec_alt : forall len n, (n < 2 ^ len)%nat -> 
  basis_vector (2 ^ len) n = f_to_vec len (nat_to_funbool len n).
Proof.
  intros.
  rewrite basis_f_to_vec.
  rewrite nat_to_funbool_inverse; auto.
Qed.

(* allows us to prove equivalence of unitary programs using 
   vector state reasoning *)
Lemma equal_on_basis_states_implies_equal : forall {n dim} (A B : Matrix n (2 ^ dim)),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall f, A × (f_to_vec dim f) = B × (f_to_vec dim f)) ->
  A = B.
Proof.
  intros n dim A B WFA WFB H.
  apply equal_on_basis_vectors_implies_equal; trivial.
  intros k Lk.
  rewrite basis_f_to_vec_alt; auto.
Qed.

Lemma equal_on_conj_basis_states_implies_equal {n m} 
  (A B : Matrix (2 ^ n) (2 ^ m)) : WF_Matrix A -> WF_Matrix B -> 
  (forall f g, (f_to_vec n g) ⊤ × (A × f_to_vec m f) = 
    (f_to_vec n g) ⊤ × (B × f_to_vec m f)) -> A = B.
Proof.
  intros HA HB HAB.
  apply equal_on_basis_states_implies_equal; [auto..|].
  intros f.
  apply transpose_matrices.
  apply equal_on_basis_states_implies_equal; [auto_wf..|].
  intros g.
  apply transpose_matrices.
  rewrite Mmult_transpose, transpose_involutive, HAB.
  rewrite Mmult_transpose, transpose_involutive.
  reflexivity.
Qed.

Lemma f_to_vec_update_oob : forall (n : nat) (f : nat -> bool) (i : nat) (b : bool),
  n <= i -> f_to_vec n (update f i b) = f_to_vec n f.
Proof.
  intros.
  induction n; simpl; try reflexivity.
  rewrite <- IHn by lia.
  unfold update.
  bdestructΩ (n =? i).  
  reflexivity.
Qed.

Lemma f_to_vec_shift_update_oob : forall (n : nat) (f : nat -> bool) (i j : nat) (b : bool),
  j + n <= i \/ i < j -> 
  f_to_vec n (shift (update f i b) j) = f_to_vec n (shift f j).
Proof.
  intros. destruct H.
  - induction n; simpl; try reflexivity.
    rewrite <- IHn by lia.
    unfold shift, update.
    bdestructΩ (n + j =? i).
    reflexivity.
  - induction n; simpl; try reflexivity.
    rewrite <- IHn by lia.
    unfold shift, update.
    bdestructΩ (n + j =? i).
    reflexivity.
Qed.

Lemma f_to_vec_split : forall (base n i : nat) (f : nat -> bool),
  i < n ->
  f_to_vec n f = (f_to_vec i f) ⊗ ∣ f i ⟩ ⊗ (f_to_vec (n - 1 - i) (shift f (i + 1))).
Proof.
  intros.
  induction n.
  - contradict H. lia.
  - bdestruct (i =? n).
    + subst.
      replace (S n - 1 - n)%nat with O by lia.
      simpl. Msimpl.
      reflexivity.
    + assert (i < n)%nat by lia.
      specialize (IHn H1).
      replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
      simpl.
      rewrite IHn.
      restore_dims; repeat rewrite kron_assoc by auto with wf_db. 
      unfold shift; simpl.
      replace (n - 1 - i + (i + 1))%nat with n by lia.
      reflexivity.
Qed.

Lemma f_to_vec_merge : forall f1 f2 m n, 
  f_to_vec m f1 ⊗ f_to_vec n f2 = 
    f_to_vec (m + n) (fun x => if x <? m then f1 x else f2 (x - m)%nat).
Proof.
  intros f1 f2 m n.
  induction n.
  - simpl. Msimpl. 
    replace (m + 0)%nat with m by lia.
    apply f_to_vec_eq; intros i Hi.
    bdestructΩ (i <? m).
    reflexivity.
  - replace (m + S n)%nat with (S (m + n)) by lia.
    simpl. 
    restore_dims.
    rewrite <- kron_assoc; auto with wf_db.
    rewrite IHn.
    bdestructΩ (m + n <? m).
    replace (m + n - m)%nat with n by lia.
    reflexivity.
Qed.

(* lemmas to describe the action of various gates on f_to_vec states *)

Lemma f_to_vec_σx : forall (n i : nat) (f : nat -> bool),
  i < n ->
  (pad_u n i σx) × (f_to_vec n f) = f_to_vec n (update f i (¬ (f i))).
Proof.
  intros.
  unfold pad_u, pad.
  rewrite (f_to_vec_split 0 n i f H).
  repad. 
  replace (i + 1 + x - 1 - i) with x by lia.
  Msimpl.
  rewrite (f_to_vec_split 0 (i + 1 + x) i) by lia.
  rewrite f_to_vec_update_oob by lia.
  rewrite f_to_vec_shift_update_oob by lia.
  rewrite update_index_eq. 
  replace (i + 1 + x - 1 - i) with x by lia.
  destruct (f i); simpl; autorewrite with ket_db; reflexivity.
Qed.

Lemma f_to_vec_σy : forall (n i : nat) (f : nat -> bool),
  i < n ->
  (pad_u n i σy) × (f_to_vec n f) = 
  (-1)%R^(f i) * Ci .* f_to_vec n (update f i (¬ f i)).
Proof.
  intros n i f Hi.
  unfold pad_u, pad.
  rewrite (f_to_vec_split 0 n i f Hi).
  repad. 
  replace (i + 1 + x - 1 - i) with x by lia.
  Msimpl.
  rewrite Y_specb.
  distribute_scale.
  rewrite (f_to_vec_split 0 (i + 1 + x) i) by lia.
  rewrite f_to_vec_update_oob by lia.
  rewrite f_to_vec_shift_update_oob by lia.
  rewrite update_index_eq. 
  replace (i + 1 + x - 1 - i) with x by lia.
  easy.
Qed.

Lemma f_to_vec_σz : forall (n i : nat) (f : nat -> bool),
  i < n ->
  (pad_u n i σz) × (f_to_vec n f) = 
  (-1)%R^(f i) .* f_to_vec n f.
Proof.
  intros n i f Hi.
  unfold pad_u, pad.
  rewrite (f_to_vec_split 0 n i f Hi).
  repad. 
  replace (i + 1 + x - 1 - i) with x by lia.
  Msimpl.
  rewrite Z_specb.
  distribute_scale.
  reflexivity.
Qed.

Lemma f_to_vec_cnot : forall (n i j : nat) (f : nat -> bool),
  i < n -> j < n -> i <> j ->
  (pad_ctrl n i j σx) × (f_to_vec n f) = f_to_vec n (update f j (f j ⊕ f i)).
Proof.
  intros.
  unfold pad_ctrl, pad.
  repad.
  - repeat rewrite (f_to_vec_split 0 (i + (1 + d + 1) + x) i) by lia.
    rewrite f_to_vec_update_oob by lia.
    rewrite update_index_neq by lia.
    repeat rewrite (f_to_vec_split (0 + i + 1) (i + (1 + d + 1) + x - 1 - i) d) by lia.
    repeat rewrite shift_plus.
    replace (i + (1 + d + 1) + x - 1 - i - 1 - d) with x by lia.
    repeat rewrite f_to_vec_shift_update_oob by lia.
    repeat rewrite shift_simplify. 
    replace (d + (i + 1)) with (i + 1 + d) by lia.
    rewrite update_index_eq.
    restore_dims.
    rewrite <- !kron_assoc by auto_wf.
    restore_dims.
    rewrite kron_mixed_product' by lia.
    rewrite Mmult_1_l by auto_wf.
    restore_dims.
    rewrite (kron_assoc (f_to_vec i f)) by auto_wf.
    restore_dims.
    rewrite !(kron_assoc (f_to_vec i f)) by auto_wf.
    restore_dims.
    f_equal.
    rewrite kron_mixed_product, Mmult_1_l by auto_wf.
    f_equal.
    simpl.
    restore_dims.
    distribute_plus.
    rewrite !kron_mixed_product.
    rewrite 2!Mmult_1_l by auto_wf.
    symmetry.
    rewrite <- (Mmult_1_l _ _ (∣ f i ⟩)) at 1 by auto_wf.
    rewrite <- Mplus10.
    distribute_plus.
    rewrite !(Mmult_assoc _ _ (∣ f i ⟩)).
    rewrite bra1_equiv, bra1ket_eqb.
    rewrite bra0_equiv, bra0ket_eqb.
    destruct (f i); simpl; rewrite Mmult_0_r, !kron_0_l.
    + rewrite xorb_true_r.
      now rewrite X_specb.
    + now rewrite xorb_false_r.
  - repeat rewrite (f_to_vec_split 0 (j + (1 + d + 1) + x0) j); try lia.
    rewrite f_to_vec_update_oob by lia.
    rewrite update_index_eq.
    repeat rewrite (f_to_vec_split (j + 1) (j + (1 + d + 1) + x0 - 1 - j) d); try lia.
    repeat rewrite shift_plus.
    repeat rewrite f_to_vec_shift_update_oob by lia.
    repeat rewrite shift_simplify. 
    replace (d + (j + 1)) with (j + 1 + d) by lia.
    rewrite update_index_neq by lia.
    replace (j + (1 + d + 1) + x0 - 1 - j - 1 - d) with x0 by lia.
    restore_dims.
    rewrite kron_assoc, !(kron_assoc (f_to_vec j f)) by auto_wf.
    restore_dims.
    rewrite kron_mixed_product' by lia.
    f_equal; [lia | apply Mmult_1_l; auto_wf|].
    rewrite <- 4!kron_assoc by auto_wf.
    restore_dims.
    rewrite kron_mixed_product.
    f_equal; [| apply Mmult_1_l; auto_wf].
    distribute_plus.
    rewrite !kron_mixed_product, Mmult_1_l by auto_wf.
    rewrite !Mmult_assoc.
    rewrite Mmult_1_l by auto_wf.
    rewrite bra1_equiv, bra1ket_eqb.
    rewrite bra0_equiv, bra0ket_eqb.
    destruct (f (j + 1 + d)); simpl; rewrite Mmult_0_r, !kron_0_r.
    + rewrite Mplus_0_r. 
      rewrite xorb_true_r.
      rewrite Mmult_1_r, ket1_equiv by auto_wf.
      now rewrite X_specb.
    + rewrite Mplus_0_l.
      rewrite Mmult_1_r, ket0_equiv by auto_wf.
      now rewrite xorb_false_r.
Qed.

Lemma f_to_vec_swap : forall (n i j : nat) (f : nat -> bool),
  i < n -> j < n -> i <> j ->
  (pad_swap n i j) × (f_to_vec n f) = f_to_vec n (fswap f i j).
Proof.
  intros n i j f ? ? ?.
  unfold pad_swap.
  repeat rewrite Mmult_assoc.
  rewrite 3 f_to_vec_cnot by auto.
  repeat rewrite update_index_eq.
  repeat rewrite update_index_neq by lia.
  repeat rewrite update_index_eq.
  replace ((f j ⊕ f i) ⊕ (f i ⊕ (f j ⊕ f i))) with (f i).
  replace (f i ⊕ (f j ⊕ f i)) with (f j).
  rewrite update_twice_neq by auto.
  rewrite update_twice_eq.
  reflexivity.
  all: destruct (f i); destruct (f j); reflexivity.
Qed.

Lemma f_to_vec_phase_shift : forall (n i : nat) (θ : R) (f : nat -> bool),
  (i < n)%nat ->
  (pad_u n i (phase_shift θ)) × (f_to_vec n f) =
    (Cexp ((f i) * θ)) .* f_to_vec n f.
Proof.
  intros.
  unfold pad_u, pad.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i)%nat with (n - (i + 1))%nat by lia.
  repad. 
  Msimpl.
  rewrite phase_shift_on_ket.
  rewrite Mscale_kron_dist_r.
  rewrite Mscale_kron_dist_l.
  reflexivity.
Qed.

Local Open Scope R_scope.

Lemma f_to_vec_hadamard : forall (n i : nat) (f : nat -> bool),
  (i < n)%nat ->
  (pad_u n i hadamard) × (f_to_vec n f) 
      = /√2 .* ((f_to_vec n (update f i false)) .+ 
                (Cexp ((f i) * PI)) .* f_to_vec n (update f i true)).
Proof.
  intros.
  unfold pad_u, pad.
  rewrite (f_to_vec_split 0 n i f H). 
  simpl; replace (n - 1 - i)%nat with (n - (i + 1))%nat by lia.
  repad. 
  Msimpl.
  rewrite hadamard_on_ket.
  rewrite Mscale_kron_dist_r, Mscale_kron_dist_l.
  rewrite kron_plus_distr_l, kron_plus_distr_r.
  rewrite Mscale_kron_dist_r, Mscale_kron_dist_l.
  rewrite 2 (f_to_vec_split 0 (i + 1 + x) i _) by lia.
  replace (i + 1 + x - 1 - i)%nat with x by lia.
  simpl.
  rewrite 2 update_index_eq.
  repeat rewrite f_to_vec_update_oob by lia.
  repeat rewrite f_to_vec_shift_update_oob by lia.
  do 3 (apply f_equal2; auto).
  destruct (f i); simpl; autorewrite with R_db Cexp_db; lca.
Qed.

Local Close Scope R_scope.

#[global] Hint Rewrite f_to_vec_cnot f_to_vec_σx f_to_vec_phase_shift using lia : f_to_vec_db.
#[global] Hint Rewrite (@update_index_eq bool) (@update_index_neq bool) (@update_twice_eq bool) (@update_same bool) using lia : f_to_vec_db.

Import Modulus.

Lemma kron_f_to_vec {n m p q} (A : Matrix (2^n) (2^m)) 
  (B : Matrix (2^p) (2^q)) f : 
  @mat_equiv _ 1 (A ⊗ B × f_to_vec (m + q) f)
  ((A × f_to_vec m f (* : Matrix _ 1 *)) ⊗ 
  (B × f_to_vec q (fun k => f (m + k)) (* : Matrix _ 1) *))).
Proof.
  rewrite <- kron_mixed_product.
  rewrite f_to_vec_merge.
  Morphisms.f_equiv.
  apply f_to_vec_eq.
  intros; bdestructΩ'; f_equal; lia.
Qed.

Lemma kron_f_to_vec_eq {n m p q : nat} (A : Matrix (2^n) (2^m))
  (B : Matrix (2^p) (2^q)) (f : nat -> bool) : WF_Matrix A -> WF_Matrix B -> 
  A ⊗ B × f_to_vec (m + q) f
  = A × f_to_vec m f ⊗ (B × f_to_vec q (fun k : nat => f (m + k))).
Proof.
  intros.
  prep_matrix_equivalence.
  apply kron_f_to_vec.
Qed.

Lemma f_to_vec_split' n m f : 
  mat_equiv (f_to_vec (n + m) f)
  (f_to_vec n f ⊗ f_to_vec m (fun k => f (n + k))).
Proof.
  intros i j Hi Hj.
  rewrite f_to_vec_merge.
  erewrite f_to_vec_eq; [reflexivity|].
  intros; simpl; bdestructΩ'; f_equal; lia.
Qed.

Lemma f_to_vec_split'_eq n m f : 
  (f_to_vec (n + m) f) =
  (f_to_vec n f ⊗ f_to_vec m (fun k => f (n + k))).
Proof.
  apply mat_equiv_eq; [..|apply f_to_vec_split']; auto with wf_db.
Qed.

Lemma f_to_vec_1_eq f : 
  f_to_vec 1 f = if f 0 then ∣1⟩ else ∣0⟩.
Proof.
  cbn.
  unfold ket.
  rewrite kron_1_l by (destruct (f 0); auto with wf_db).
  now destruct (f 0).
Qed.

Lemma f_to_vec_1_mult_r f (A : Matrix (2^1) (2^1)) : 
  A × f_to_vec 1 f = (fun x j => if j =? 0 then A x (Nat.b2n (f 0)) else 0%R).
Proof.
  cbn.
  rewrite kron_1_l by auto with wf_db.
  apply functional_extensionality; intros i.
  apply functional_extensionality; intros j.
  unfold Mmult.
  simpl.
  destruct (f 0);
  unfold ket;
  simpl;
  now destruct j; simpl; Csimpl.
Qed.

Lemma f_to_vec_1_mult_r_decomp f (A : Matrix (2^1) (2^1))  : 
  A × f_to_vec 1 f ≡
  A 0 (Nat.b2n (f 0)) .* ∣0⟩ .+ 
  A 1 (Nat.b2n (f 0)) .* ∣1⟩.
Proof.
  rewrite f_to_vec_1_mult_r.
  intros i j Hi Hj.
  replace j with 0 by lia.
  simpl.
  autounfold with U_db.
  do 2 (try destruct i); [..| simpl in *; lia]; 
  now Csimpl.
Qed.

Lemma f_to_vec_1_mult_r_decomp_eq f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  A × f_to_vec 1 f =
  A 0 (Nat.b2n (f 0)) .* ∣0⟩ .+ 
  A 1 (Nat.b2n (f 0)) .* ∣1⟩.
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  apply f_to_vec_1_mult_r_decomp.
Qed.

Lemma qubit0_f_to_vec : ∣0⟩ = f_to_vec 1 (fun x => false).
Proof. now rewrite f_to_vec_1_eq. Qed.

Lemma qubit1_f_to_vec : ∣1⟩ = f_to_vec 1 (fun x => x =? 0).
Proof. now rewrite f_to_vec_1_eq. Qed.

Lemma ket_f_to_vec b : ∣ Nat.b2n b ⟩ = f_to_vec 1 (fun x => b).
Proof.
  destruct b; [apply qubit1_f_to_vec | apply qubit0_f_to_vec].
Qed.

Lemma f_to_vec_1_mult_r_decomp_eq' f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  A × f_to_vec 1 f =
  A 0 (Nat.b2n (f 0)) .* f_to_vec 1 (fun x => false) .+ 
  A 1 (Nat.b2n (f 0)) .* f_to_vec 1 (fun x => x=?0).
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  rewrite f_to_vec_1_mult_r_decomp.
  rewrite 2!f_to_vec_1_eq.
  easy.
Qed.

Lemma f_to_vec_1_mult_l_decomp f (A : Matrix (2^1) (2^1))  : 
  (f_to_vec 1 f) ⊤ × A ≡
  A (Nat.b2n (f 0)) 0 .* (∣0⟩ ⊤) .+ 
  A (Nat.b2n (f 0)) 1 .* (∣1⟩ ⊤).
Proof.
  rewrite <- (transpose_involutive _ _ A).
  rewrite <- Mmult_transpose, <- Mscale_trans.
  intros i j Hi Hj.
  apply (f_to_vec_1_mult_r_decomp f (A ⊤)); easy.
Qed.

Lemma f_to_vec_1_mult_l_decomp_eq f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  (f_to_vec 1 f) ⊤ × A =
  A (Nat.b2n (f 0)) 0 .* (∣0⟩ ⊤) .+ 
  A (Nat.b2n (f 0)) 1 .* (∣1⟩ ⊤).
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  apply f_to_vec_1_mult_l_decomp.
Qed.

Lemma f_to_vec_1_mult_l_decomp_eq' f (A : Matrix (2^1) (2^1))  : 
  WF_Matrix A -> 
  (f_to_vec 1 f) ⊤ × A =
  A (Nat.b2n (f 0)) 0 .* ((f_to_vec 1 (fun x => false)) ⊤) .+ 
  A (Nat.b2n (f 0)) 1 .* ((f_to_vec 1 (fun x => x =? 0)) ⊤).
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  rewrite f_to_vec_1_mult_l_decomp_eq by easy.
  now rewrite qubit0_f_to_vec, qubit1_f_to_vec.
Qed.

Lemma basis_trans_basis {n} i j : 
  ((basis_vector n i) ⊤ × basis_vector n j) 0 0 =
  if (i =? j) && (i <? n) then C1 else 0%R.
Proof.
  unfold Mmult, basis_vector, Matrix.transpose.
  bdestructΩ'.
  - erewrite big_sum_eq_bounded.
    2: {
      intros k Hk.
      simpl_bools.
      rewrite Cmult_if_if_1_l.
      replace_bool_lia ((k =? j) && (k =? j)) (k =? j).
      reflexivity.
    }
    rewrite big_sum_if_eq_C.
    bdestructΩ'.
  - rewrite big_sum_0_bounded; [easy|].
    intros; bdestructΩ'; lca.
  - rewrite big_sum_0_bounded; [easy|].
    intros; bdestructΩ'; lca.
  - rewrite big_sum_0_bounded; [easy|].
    intros; bdestructΩ'; lca.
Qed.

Lemma f_to_vec_transpose_f_to_vec n f g :
  transpose (f_to_vec n f) × f_to_vec n g = 
  b2R (forallb (fun k => eqb (f k) (g k)) (seq 0 n)) .* I 1.
Proof.
  prep_matrix_equivalence.
  intros [] []; [|lia..]; intros _ _.
  rewrite 2!basis_f_to_vec.
  rewrite basis_trans_basis.
  pose proof (funbool_to_nat_bound n f).
  simplify_bools_lia_one_kernel.
  unfold scale.
  cbn.
  rewrite Cmult_1_r.
  unfold b2R.
  rewrite (if_dist _ _ _ RtoC).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite Nat.eqb_eq, forallb_seq0, <- funbool_to_nat_eq_iff.
  now setoid_rewrite eqb_true_iff.
Qed.

Lemma f_to_vec_transpose_f_to_vec' n f g :
  transpose (f_to_vec n f) × f_to_vec n g = 
  (if funbool_to_nat n f =? funbool_to_nat n g then  
    C1 else C0) .* I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec.
  f_equal.
  unfold b2R.
  rewrite (if_dist R C).
  apply f_equal_if; [|easy..].
  apply eq_iff_eq_true.
  rewrite forallb_seq0, Nat.eqb_eq.
  setoid_rewrite eqb_true_iff.
  apply funbool_to_nat_eq_iff.
Qed.

Lemma f_to_vec_transpose_self n f :
  transpose (f_to_vec n f) × f_to_vec n f = 
  I 1.
Proof.
  rewrite f_to_vec_transpose_f_to_vec', Nat.eqb_refl.
  now Msimpl_light.
Qed.

(*******************************)
(**   Indexed Vector Sum      **)
(*******************************)

(* Any vector ψ can be written as a weighted sum over basis vectors. *)
Lemma basis_vector_decomp : forall {d} (ψ : Vector d),
  WF_Matrix ψ ->
  ψ = big_sum (fun i => (ψ i O) .* basis_vector d i) d.
Proof.
  intros d ψ WF. 
  do 2 (apply functional_extensionality; intros). 
  rewrite Msum_Csum.
  bdestruct (x <? d).
  - unfold scale. destruct x0.
    + rewrite big_sum_unique with (k:=ψ x O). easy.
      exists x. split. easy.
      split. unfold basis_vector. rewrite Nat.eqb_refl. simpl. lca.
      intros. unfold basis_vector. 
      bdestruct_all; lca.
    + unfold WF_Matrix in WF. rewrite WF by lia.
      rewrite big_sum_0. easy. intro.
      unfold basis_vector. assert (S x0 <> 0)%nat by lia.
      bdestruct_all; simpl; lca.
  - unfold WF_Matrix in WF. rewrite WF by lia. 
    rewrite big_sum_0_bounded. easy. intros. unfold scale.
    unfold basis_vector. assert (x <> x1) by lia.
    bdestruct_all; simpl; lca.
Qed.

Lemma vsum_sum : forall d n (f : nat -> Vector d),
  big_sum f (2 * n) =
  big_sum (fun i => f (2 * i)%nat) n .+ big_sum (fun i => f (2 * i + 1)%nat) n.
Proof.
  intros d n f.
  induction n.
  rewrite Nat.mul_0_r. simpl. Msimpl. reflexivity.
  replace (2 * S n)%nat with (S (S (2 * n)))%nat  by lia.
  repeat rewrite <- big_sum_extend_r.
  rewrite IHn; clear.
  replace (2 * n + 1)%nat with (S (2 * n)) by lia.
  lma.
Qed.

Lemma vsum_split : forall {d} (n i : nat) (v : nat -> Vector d),
  (i < n)%nat ->
  big_sum v n = (big_sum v i) .+ v i .+ (big_sum (shift v (i + 1)) (n - 1 - i)).
Proof.
  intros.
  induction n.
  - contradict H. lia.
  - bdestruct (i =? n).
    + subst.
      replace (S n - 1 - n)%nat with O by lia.
      rewrite <- big_sum_extend_r. Msimpl.
      reflexivity.
    + assert (i < n)%nat by lia.
      specialize (IHn H1).
      replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
      repeat rewrite <- big_sum_extend_r.
      rewrite IHn.
      repeat rewrite Mplus_assoc. 
      unfold shift; simpl.
      replace (n - 1 - i + (i + 1))%nat with n by lia.
      lma. 
Qed.

(*******************************)
(** Indexed Kronecker Product **)
(*******************************)

(* This could also be defined over (f : nat -> Vector d) *)
(* TODO: switch order of arguments to match big_sum. may mess of SQIR stuff though... *)
Fixpoint vkron n (f : nat -> Vector 2) : Vector (2 ^ n) :=
  match n with
  | 0    => I 1
  | S n' => vkron n' f ⊗ f n'
  end.

Lemma WF_vkron : forall n (f : nat -> Vector 2), 
  (forall i, (i < n)%nat -> WF_Matrix (f i)) -> 
  WF_Matrix (vkron n f).
Proof.
  intros. 
  induction n; simpl; auto with wf_db.
Qed.
#[export] Hint Resolve WF_vkron: wf_db.

Lemma WF_shift : forall m n j k (f : nat -> Matrix m n),
  (forall i, WF_Matrix (f i)) ->
  WF_Matrix (shift f j k).
Proof. intros. apply H. Qed.
#[export] Hint Resolve WF_shift: wf_db.
  
Lemma vkron_extend_r : forall n f, 
  vkron n f ⊗ f n = vkron (S n) f.
Proof. reflexivity. Qed.

Lemma vkron_extend_l : forall n (f : nat -> Vector 2),
  (forall i, WF_Matrix (f i)) ->
  (f O) ⊗ vkron n (shift f 1) = vkron (S n) f.
Proof.
  intros n f WF.
  induction n; [simpl; now rewrite kron_1_l, kron_1_r|].
  remember (S n) as n'.
  simpl.
  rewrite <- IHn; clear IHn.  
  subst; simpl.
  restore_dims; rewrite <- kron_assoc; auto with wf_db.
  rewrite shift_simplify.
  replace (n + 1)%nat with (S n) by lia.
  reflexivity.
Qed.

Lemma kron_n_f_to_vec : forall n (A : Square 2) f,
  n ⨂ A × f_to_vec n f = vkron n (fun k => A × ∣ f k ⟩ ).
Proof.
  intros n A f.
  induction n; simpl; [now Msimpl_light|].
  restore_dims.
  rewrite kron_mixed_product.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Mscale_vkron_distr_r : forall n x (f : nat -> Vector 2),
  vkron n (fun i => x .* f i) = x ^ n .* vkron n f.
Proof.
  intros n x f.
  induction n; simpl; [now Msimpl_light|].
  rewrite IHn. 
  distribute_scale.
  rewrite Cmult_comm.
  reflexivity.
Qed.

Lemma vkron_split : forall n i (f : nat -> Vector 2),
  (forall j, WF_Matrix (f j)) ->
  i < n ->
  vkron n f = (vkron i f) ⊗ f i ⊗ (vkron (n - 1 - i) (shift f (i + 1))).
Proof.
  intros.
  induction n; [lia|].
  bdestruct (i =? n).
  - subst.
    replace (S n - 1 - n)%nat with O by lia.
    simpl. 
    now rewrite kron_1_r. 
  - assert (i < n)%nat by lia.
    (* specialize (IHn H2). *)
    replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
    simpl.
    rewrite IHn by lia.
    unfold shift.
    replace (n - 1 - i + (i + 1))%nat with n by lia.
    restore_dims; repeat rewrite kron_assoc; auto 100 with wf_db. 
Qed.

Lemma vkron_eq : forall n (f f' : nat -> Vector 2),
  (forall i, i < n -> f i = f' i) -> vkron n f = vkron n f'.
Proof.
  intros n f f' Heq.
  induction n; simpl.
  reflexivity.
  rewrite Heq by lia.
  rewrite IHn. reflexivity.
  intros. apply Heq. lia.
Qed.

(* Of the lemmas below, the important two are vkron_to_vsum1 and vsum_to_vkron2 
   (TODO: better names). Both lemmas provide a way to convert from an indexed
   Kronecker product to an index sum. vkron_to_vsum1 is used in the QPE proof
   and vsum_to_vkron2 is used in the QPE and Deutsch-Josza proofs. *)

Lemma basis_vector_prepend_0 : forall n k,
  n <> 0 -> k < n ->
  ∣0⟩ ⊗ basis_vector n k = basis_vector (2 * n) k.
Proof.
  intros.
  prep_matrix_equivalence.
  unfold basis_vector, kron.
  intros i j Hi Hj.
  rewrite ket0_eqb.
  rewrite Cmult_if_if_1_l.
  replace j with 0 by lia.
  simpl_bools.
  symmetry.
  rewrite (eqb_iff_div_mod_eqb n).
  rewrite (Nat.mod_small k n), (Nat.div_small k n) by easy.
  bdestructΩ'.
Qed.

Lemma basis_vector_prepend_1 : forall n k,
  n <> 0 -> k < n ->
  ∣1⟩ ⊗ basis_vector n k = basis_vector (2 * n) (k + n).
Proof.
  intros.
  intros.
  prep_matrix_equivalence.
  unfold basis_vector, kron.
  intros i j Hi Hj.
  rewrite ket1_eqb.
  rewrite Cmult_if_if_1_l.
  replace j with 0 by lia.
  simpl_bools.
  symmetry.
  rewrite (eqb_iff_div_mod_eqb n).
  replace ((k + n) / n) with 1 
    by (symmetry; rewrite Kronecker.div_eq_iff; lia).
  rewrite (mod_n_to_2n (k + n)) by lia.
  bdestructΩ'.
Qed.

Lemma basis_vector_append_0 : forall n k,
  n <> 0 -> k < n ->
  basis_vector n k ⊗ ∣0⟩ = basis_vector (2 * n) (2 * k).
Proof.
  intros.
  apply mat_equiv_eq; [auto using WF_Matrix_dim_change with wf_db zarith..|].
  unfold basis_vector, kron.
  intros i j Hi Hj.
  rewrite ket0_eqb.
  rewrite Cmult_if_if_1_l.
  replace j with 0 by lia.
  simpl_bools.
  symmetry.
  rewrite (eqb_iff_div_mod_eqb 2).
  rewrite Nat.mul_comm, Nat.Div0.mod_mul, Nat.div_mul by easy.
  now rewrite andb_comm.
Qed.

Lemma basis_vector_append_1 : forall n k,
  n <> 0 -> k < n ->
  basis_vector n k ⊗ ∣1⟩ = basis_vector (2 * n) (2 * k + 1).
Proof.
  intros.
  apply mat_equiv_eq; [auto using WF_Matrix_dim_change with wf_db zarith..|].
  unfold basis_vector, kron.
  intros i j Hi Hj.
  rewrite ket1_eqb.
  rewrite Cmult_if_if_1_l.
  replace j with 0 by lia.
  simpl_bools.
  symmetry.
  rewrite (eqb_iff_div_mod_eqb 2).
  rewrite Nat.mul_comm, mod_add_l, Nat.div_add_l by easy.
  rewrite Nat.add_0_r.
  now rewrite andb_comm.
Qed.

Lemma kron_n_0_is_0_vector : forall (n:nat), n ⨂ ∣0⟩ = basis_vector (2 ^ n) O.
Proof.
  intros.
  induction n; [solve_matrix_fast|].
  simpl.
  rewrite IHn.
  replace (1 ^ n)%nat with 1%nat by now rewrite Nat.pow_1_l.
  rewrite (basis_vector_append_0 (2 ^ n) 0) by show_nonzero.
  rewrite Nat.mul_0_r.
  reflexivity.
Qed.

Lemma vkron_to_vsum1 : forall n (c : R),
  n > 0 -> 
  vkron n (fun k => ∣0⟩ .+ Cexp (c * 2 ^ (n - k - 1)) .* ∣1⟩) = 
    big_sum (fun k => Cexp (c * INR k) .* basis_vector (2 ^ n) k) (2 ^ n).
Proof.
  intros n c Hn.
  destruct n; try lia.
  induction n.
  - simpl. 
    repeat rewrite <- big_sum_extend_r.
    Msimpl. 
    rewrite Rmult_0_r, Cexp_0, Mscale_1_l.
    replace (basis_vector 2 0) with ∣0⟩ by solve_matrix_fast.
    replace (basis_vector 2 1) with ∣1⟩ by solve_matrix_fast.
    reflexivity. 
  - remember (S n) as n'.
    rewrite <- vkron_extend_l; auto with wf_db.
    replace (shift (fun k => ∣0⟩ .+ Cexp (c * 2 ^ (S n' - k - 1)) .* ∣1⟩) 1)
      with (fun k => ∣0⟩ .+ Cexp (c * 2 ^ (n' - k - 1)) .* ∣1⟩).
    2: { unfold shift. 
        apply functional_extensionality; intro k.
        replace (S n' - (k + 1) - 1)%nat with (n' - k - 1)%nat by lia.
        reflexivity. }
    rewrite IHn by lia.
    replace (S n' - 0 - 1)%nat with n' by lia.
    remember (2 ^ n')%nat as N.
    assert (HN: (N > 0)%nat) by (subst; show_nonzero).
    replace (2 ^ n')%R with (INR N).
    2: { subst. rewrite pow_INR. f_equal; lra. }
    replace (2 ^ S n')%nat with (2 * N)%nat by (subst; unify_pows_two).
    clear - HN.
    rewrite kron_plus_distr_r.
    rewrite 2 kron_Msum_distr_l.
    replace (2 * N) with (N + N) by lia.
    rewrite big_sum_sum.
    replace (N + N) with (2 * N) by lia.
    apply f_equal_gen; try apply f_equal; apply big_sum_eq_bounded; intros.
    + distribute_scale. 
      rewrite basis_vector_prepend_0 by lia.
      reflexivity.
    + distribute_scale.
      rewrite <- Cexp_add, <- Rmult_plus_distr_l, <- plus_INR. 
      rewrite basis_vector_prepend_1 by lia.
      rewrite Nat.add_comm.
      reflexivity.
Qed.

Local Open Scope R_scope.
Local Open Scope C_scope.
Local Opaque Nat.mul.
Lemma vkron_to_vsum2 : forall n (f : nat -> bool),
  (n > 0)%nat -> 
  vkron n (fun k => ∣0⟩ .+ (-1) ^ f k .* ∣1⟩) = 
    big_sum 
      (fun k => (-1) ^ (product f (nat_to_funbool n k) n) .* basis_vector (2 ^ n) k) (2^n).
Proof.
  intros n f ?.
  destruct n; try lia.
  clear.
  induction n.
  - simpl.
    repeat rewrite Nat.mul_1_r.
    repeat rewrite <- big_sum_extend_r.
    Msimpl.
    unfold nat_to_funbool; simpl.
    rewrite 2 update_index_eq.
    replace (basis_vector 2 0) with ∣0⟩ by solve_matrix_fast.
    replace (basis_vector 2 1) with ∣1⟩ by solve_matrix_fast.
    destruct (f O); simpl; restore_dims; lma. 
  - remember (S n) as n'.
    simpl vkron.
    rewrite IHn; clear.
    replace (2 ^ S n')%nat with (2 * 2 ^ n')%nat by reflexivity. 
    rewrite vsum_sum.
    rewrite kron_Msum_distr_r.
    assert (H' := (@big_sum_plus _ _ _ (M_is_comm_group (2 * 2 ^ n')%nat 1%nat))).
    simpl in H'.
    rewrite <- H'.
    apply big_sum_eq_bounded.
    intros i Hi.
    distribute_plus.
    distribute_scale.
    rewrite (basis_vector_append_0 (2 ^ n')); auto; try lia.
    rewrite (basis_vector_append_1 (2 ^ n')); auto; try lia.
    apply f_equal2; apply f_equal2; try reflexivity.
    apply f_equal2; try reflexivity.
    simpl.
    destruct i.
    rewrite Nat.mul_0_r. 
    unfold nat_to_funbool, nat_to_binlist; simpl.
    replace (n' - 0)%nat with n' by lia.
    rewrite update_index_eq.
    rewrite andb_false_r, xorb_false_l.
    rewrite product_update_oob by lia.
    reflexivity.
    unfold nat_to_funbool, nat_to_binlist.
    rewrite nat_to_binlist'_even by lia.
    simpl.
    replace (n' - 0)%nat with n' by lia.
    rewrite update_index_eq.
    rewrite andb_false_r, xorb_false_l.
    rewrite product_update_oob by lia.
    reflexivity. 
    repeat rewrite RtoC_pow.
    rewrite <- RtoC_mult.
    rewrite <- pow_add.
    simpl.
    unfold nat_to_funbool, nat_to_binlist.
    rewrite nat_to_binlist'_odd by lia.
    simpl.
    replace (n' - 0)%nat with n' by lia.
    rewrite update_index_eq.
    rewrite andb_true_r.
    rewrite product_update_oob by lia.
    remember (product f (list_to_funbool n' (nat_to_binlist' i ++ repeat false (n' - length (nat_to_binlist' i)))) n') as p.
    destruct (f n'); destruct p; simpl; lca.
Qed.
Local Transparent Nat.mul.

Lemma H_spec : (* slightly different from hadamard_on_basis_state *)
  forall b : bool, hadamard × ∣ b ⟩ = / √ 2 .* (∣ 0 ⟩ .+ (-1)^b .* ∣ 1 ⟩).
Proof.
  apply hadamard_on_ket.
Qed.

Lemma H_kron_n_spec : forall n x, (n > 0)%nat ->
  n ⨂ hadamard × f_to_vec n x = 
    /√(2 ^ n) .* big_sum (fun k => (-1) ^ (product x (nat_to_funbool n k) n) .* basis_vector (2 ^ n) k) (2 ^ n).
Proof. 
  intros n x Hn. 
  rewrite kron_n_f_to_vec.
  erewrite (vkron_eq _ (fun k : nat => hadamard × ∣ x k ⟩)).
  2: { intros i Hi.
       rewrite H_spec.
       reflexivity. }
  rewrite Mscale_vkron_distr_r.
  apply f_equal2.  
  repeat rewrite <- RtoC_inv by nonzero.
  rewrite RtoC_pow.
  rewrite pow_inv by nonzero.
  rewrite <- sqrt_pow by lra. 
  reflexivity.
  apply vkron_to_vsum2.
  assumption.
Qed.

Lemma H0_kron_n_spec_alt : forall n, (n > 0)%nat ->
  n ⨂ hadamard × n ⨂ ∣0⟩ = 
    /√(2 ^ n) .* big_sum (fun k => basis_vector (2 ^ n) k) (2 ^ n).
Proof. 
  intros.
  replace (n ⨂ ∣0⟩) with (f_to_vec n (fun _ => false)).
  replace (1^n)%nat with (S O).
  rewrite H_kron_n_spec by assumption.
  apply f_equal2; try reflexivity.
  apply big_sum_eq_bounded.
  intros.
  rewrite product_0; simpl. lma.
  symmetry. apply Nat.pow_1_l. 
  clear.
  induction n; try reflexivity.
  simpl. rewrite IHn. reflexivity.
Qed.


(* Generalizing vkron to larger matrices *)
Fixpoint big_kron' (ns ms : nat -> nat)
  (As : forall i, Matrix (2 ^ ns i) (2 ^ ms i)) (n : nat) : 
  Matrix (2 ^ big_sum ns n) (2 ^ (big_sum ms n)) :=
  match n with 
  | O => I (2 ^ 0)
  | S n' => 
    big_kron' ns ms As n' ⊗ As n'
  end.

Lemma WF_big_kron' ns ms As n 
  (HAs : forall k, (k < n)%nat -> WF_Matrix (As k)) : 
  WF_Matrix (big_kron' ns ms As n).
Proof. induction n; cbn; auto_wf. Qed.

#[export] Hint Resolve WF_big_kron' : wf_db.

Lemma big_kron'_eq_bounded ns ms As Bs n 
  (HAB : forall k, (k < n)%nat -> As k = Bs k) : 
  big_kron' ns ms As n = big_kron' ns ms Bs n.
Proof.
  induction n; [easy|].
  cbn; f_equal; auto.
Qed.

Lemma big_kron'_Mmult ns ms os As Bs n
  (HAs : forall k, (k < n)%nat -> WF_Matrix (As k)) 
  (HBs : forall k, (k < n)%nat -> WF_Matrix (Bs k)) : 
  big_kron' ns ms As n × big_kron' ms os Bs n = 
  big_kron' ns os (fun i => As i × Bs i) n.
Proof.
  induction n; [apply Mmult_1_l; auto_wf|].
  cbn.
  restore_dims.
  rewrite kron_mixed_product.
  f_equal.
  apply IHn; auto.
Qed.

Lemma big_kron'_transpose ns ms As n : 
  (big_kron' ns ms As n) ⊤%M = 
  big_kron' ms ns (fun k => (As k) ⊤%M) n.
Proof.
  induction n; cbn.
  - apply id_transpose_eq.
  - change ((?A ⊗ ?B) ⊤%M) with 
      (transpose A ⊗ transpose B).
    f_equal.
    auto.
Qed.

Lemma big_kron'_transpose' ns ms As n n' m' : 
  @transpose n' m' (big_kron' ns ms As n) = 
  big_kron' ms ns (fun k => (As k) ⊤%M) n.
Proof. apply big_kron'_transpose. Qed.

Lemma big_kron'_adjoint ns ms As n : 
  (big_kron' ns ms As n) † = 
  big_kron' ms ns (fun k => (As k) †) n.
Proof.
  induction n; cbn.
  - apply id_adjoint_eq.
  - restore_dims. 
    rewrite kron_adjoint.
    f_equal.
    auto.
Qed.

Lemma big_kron'_id ns As n 
  (HAs : forall k, (k < n)%nat -> (As k) = I (2 ^ (ns k))) : 
  big_kron' ns ns As n = I (2 ^ (big_sum ns n)).
Proof.
  induction n; [easy|].
  simpl.
  rewrite IHn by auto.
  rewrite HAs by auto.
  rewrite id_kron.
  now unify_pows_two.
Qed.

Lemma big_kron'_unitary ns As n 
  (HAs : forall k, (k < n)%nat -> WF_Unitary (As k)) : 
  WF_Unitary (big_kron' ns ns As n).
Proof.
  pose proof (fun k Hk => proj1 (HAs k Hk)) as HAs'.
  split; [auto_wf|].
  rewrite big_kron'_adjoint.
  rewrite big_kron'_Mmult by (intros; auto_wf).
  apply big_kron'_id.
  intros k Hk.
  now apply HAs.
Qed.

Lemma f_to_vec_big_split n ns f : 
  f_to_vec (big_sum ns n) f = 
  big_kron' ns (fun _ => O) 
    (fun i => f_to_vec (ns i) (fun k => f (big_sum ns i + k)%nat)) n.
Proof.
  induction n; [easy|].
  cbn.
  rewrite <- IHn.
  rewrite f_to_vec_split'_eq.
  f_equal.
  now rewrite big_sum_0.
Qed.

Lemma big_kron'_f_to_vec ns ms As n f 
  (HAs : forall k, (k < n)%nat -> WF_Matrix (As k)): 
  big_kron' ns ms As n × f_to_vec (big_sum ms n) f =
  big_kron' ns (fun _ => O) 
  (fun i => As i × f_to_vec (ms i) (fun k => f (big_sum ms i + k)%nat)) n.
Proof.
  rewrite f_to_vec_big_split.
  restore_dims.
  rewrite big_kron'_Mmult by (intros; auto_wf).
  easy.
Qed.

Lemma big_kron'_split_add ns ms As n n' 
  (HAs : forall k, (k < n + n')%nat -> WF_Matrix (As k)) :
  big_kron' ns ms As (n + n') = 
  big_kron' ns ms As n ⊗
  big_kron' (fun k => ns (n + k)%nat) (fun k => ms (n + k)%nat)
    (fun k => As (n + k)%nat) n'.
Proof.
  induction n'.
  - simpl.
    now rewrite Nat.add_0_r, kron_1_r.
  - rewrite Nat.add_succ_r. simpl.
    rewrite IHn' by auto with zarith.
    restore_dims.
    apply kron_assoc; auto_wf.
Qed.

Lemma big_kron'_split_add' ns ms As n n' 
  (HAs : forall k, (k < n + n')%nat -> WF_Matrix (As k)) :
  big_kron' ns ms As (n + n') = 
  big_kron' ns ms As n ⊗
  big_kron' (fun k => ns (k + n)%nat) (fun k => ms (k + n)%nat)
    (fun k => As (k + n)%nat) n'.
Proof.
  rewrite big_kron'_split_add by auto.
  f_equal; 
  [f_equal; apply big_sum_eq_bounded; intros ? ?; f_equal; lia..|].
  induction n'; [easy|].
  simpl.
  rewrite IHn' by auto with zarith.
  rewrite (Nat.add_comm n n').
  f_equal; 
  f_equal; apply big_sum_eq_bounded; 
  intros ? ?; f_equal; lia.
Qed.

Lemma big_kron'_split n i (Hk : (i < n)%nat) ns ms As 
  (HAs : forall k, (k < n)%nat -> WF_Matrix (As k))  :
  big_kron' ns ms As n = 
  big_kron' ns ms As i ⊗ As i ⊗
  big_kron' (fun k => ns (k + 1 + i)%nat) (fun k => ms (k + 1 + i)%nat)
    (fun k => As (k + 1 + i)%nat) (n - 1 - i).
Proof. 
  fill_differences.
  replace (i + 1 + x - 1 - i)%nat with x by lia.
  rewrite 2!big_kron'_split_add' by auto with zarith.
  f_equal.
  1, 2: rewrite Nat.add_comm, <- Nat.pow_add_r; simpl; f_equal; lia.
  1, 2: f_equal; apply big_sum_eq_bounded; intros ? ?; f_equal; lia.
  - f_equal.
    cbn.
    apply kron_1_l, HAs; lia.
  - induction x; [easy|].
    simpl.
    rewrite IHx, (Nat.add_comm i 1), Nat.add_assoc by auto with zarith.
    f_equal.
    1, 2: f_equal; apply big_sum_eq_bounded; intros ? ?; f_equal; lia.
Qed.

Lemma big_kron'_0_0_eq_up_to_fswap
  As n x y (Hx : (x < n)%nat) (Hy : (y < n)%nat) 
  (HAs : forall k, (k < n)%nat -> WF_Matrix (As k))
  f (Hf : perm_bounded n f) :
  big_kron' (fun _ => O) (fun _ => O) (As ∘ f)%prg n = 
  big_kron' (fun _ => O) (fun _ => O) (As ∘ fswap f x y)%prg n.
Proof.
  bdestruct (x =? y);
  [apply big_kron'_eq_bounded; unfold fswap, compose; intros;
    bdestructΩ'|].
  assert (Hfs : perm_bounded n (fswap f x y))
    by (intros k Hk; unfold fswap; bdestructΩ'; auto).
  bdestruct (x <? y).
  - rewrite 2 (big_kron'_split n y) by (unfold compose; auto).
    rewrite 2 (big_kron'_split y x) by (unfold compose; auto with zarith).
    unfold compose.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_kron'_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite !kron_assoc by auto_wf.
    restore_dims.
    rewrite !kron_assoc by auto_wf.
    f_equal;
    [apply big_kron'_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    cbn. 
    rewrite big_sum_0 by easy.
    cbn. 
    rewrite kron_1_1_mid_comm by 
      first [apply WF_kron; [easy..| | auto_wf]; 
        apply WF_Matrix_dim_change;
        [now rewrite big_sum_0 by easy..|auto_wf] | auto_wf].
    symmetry.
    rewrite kron_1_1_mid_comm by 
      first [apply WF_kron; [easy..| | auto_wf]; 
        apply WF_Matrix_dim_change;
        [now rewrite big_sum_0 by easy..|auto_wf] | auto_wf].
    restore_dims.
    rewrite 2!kron_assoc by auto_wf.
    f_equal;
    [apply big_kron'_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    apply kron_1_1_mid_comm; auto.
  - rewrite 2 (big_kron'_split n x) by (unfold compose; auto).
    rewrite 2 (big_kron'_split x y) by (unfold compose; auto with zarith).
    unfold compose.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_kron'_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite !kron_assoc by auto_wf.
    restore_dims.
    rewrite !kron_assoc by auto_wf.
    f_equal;
    [apply big_kron'_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    cbn. 
    rewrite big_sum_0 by easy.
    cbn. 
    rewrite kron_1_1_mid_comm by 
      first [apply WF_kron; [easy..| | auto_wf]; 
        apply WF_Matrix_dim_change;
        [now rewrite big_sum_0 by easy..|auto_wf] | auto_wf].
    symmetry.
    rewrite kron_1_1_mid_comm by 
      first [apply WF_kron; [easy..| | auto_wf]; 
        apply WF_Matrix_dim_change;
        [now rewrite big_sum_0 by easy..|auto_wf] | auto_wf].
    restore_dims.
    rewrite 2!kron_assoc by auto_wf.
    f_equal;
    [apply big_kron'_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    apply kron_1_1_mid_comm; auto.
Qed.

Lemma big_kron'_0_0_reorder As n f (Hf : permutation n f) 
  (HAs : forall k, (k < n)%nat -> WF_Matrix (As k)) : 
  big_kron' (fun _ => O) (fun _ => O) As n = 
  big_kron' (fun _ => O) (fun _ => O) (As ∘ f)%prg n.
Proof.
  intros.
  generalize dependent f.
  induction n;
  [reflexivity|].
  intros f Hf. 
  pose proof Hf as [g Hg].
  destruct (Hg n) as [_ [H1' [_ H2']]]; try lia.
  symmetry.
  rewrite (big_kron'_0_0_eq_up_to_fswap _ _ (g n) n) 
    by auto with perm_bounded_db.
  simpl.
  unfold compose.
  rewrite fswap_simpl2.
  unfold compose.
  rewrite H2'.
  specialize (IHn ltac:(auto) (fswap f (g n) n)).
  rewrite IHn by
    (apply fswap_at_boundary_permutation; auto).
  reflexivity.
Qed.