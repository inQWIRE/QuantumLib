Require Export Pad.
Require Export CauchySchwarz.
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

Lemma bra0ket0 : bra 0 × ket 0 = I 1.
Proof. lma'. Qed.

Lemma bra0ket1 : bra 0 × ket 1 = Zero.
Proof. lma'. Qed.

Lemma bra1ket0 : bra 1 × ket 0 = Zero.
Proof. lma'. Qed.

Lemma bra1ket1 : bra 1 × ket 1 = I 1.
Proof. lma'. Qed.

(* Hadamard properties *)
Lemma H0_spec : hadamard × ∣ 0 ⟩ = ∣ + ⟩.
Proof. lma'. Qed.

Lemma H1_spec : hadamard × ∣ 1 ⟩ = ∣ - ⟩.
Proof. lma'. Qed.

Lemma Hplus_spec : hadamard × ∣ + ⟩ = ∣ 0 ⟩.
Proof. solve_matrix. Qed.

Lemma Hminus_spec : hadamard × ∣ - ⟩ = ∣ 1 ⟩.
Proof. solve_matrix.  Qed.

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

(* X properties *)
Lemma X0_spec : σx × ∣ 0 ⟩ = ∣ 1 ⟩.
Proof. lma'. Qed.

Lemma X1_spec : σx × ∣ 1 ⟩ = ∣ 0 ⟩.
Proof. lma'. Qed.

(* Y properties *)
Lemma Y0_spec : σy × ∣ 0 ⟩ = Ci .* ∣ 1 ⟩.
Proof. lma'. Qed.

Lemma Y1_spec : σy × ∣ 1 ⟩ = -Ci .* ∣ 0 ⟩.
Proof. lma'. Qed.

(* Z properties *)
Lemma Z0_spec : σz × ∣ 0 ⟩ = ∣ 0 ⟩.
Proof. lma'. Qed.

Lemma Z1_spec : σz × ∣ 1 ⟩ = -1 .* ∣ 1 ⟩.
Proof. lma'. Qed.

(* phase shift properties *)
Lemma phase0_spec : forall ϕ, phase_shift ϕ × ket 0 = ket 0.
Proof. intros. lma'. Qed.

Lemma phase1_spec : forall ϕ, phase_shift ϕ × ket 1 = Cexp ϕ .* ket 1.
Proof. intros. lma'. Qed.

Definition b2R (b : bool) : R := if b then 1%R else 0%R.
Local Coercion b2R : bool >-> R.
Local Coercion Nat.b2n : bool >-> nat.

Lemma phase_shift_on_ket : forall (θ : R) (b : bool),
  phase_shift θ × ∣ b ⟩ = (Cexp (b * θ)) .* ∣ b ⟩.
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db.
  reflexivity.
  rewrite Cexp_0; reflexivity.
Qed.

Lemma hadamard_on_ket : forall (b : bool),
  hadamard × ∣ b ⟩ = /√2 .* (∣ 0 ⟩ .+ (-1)^b .* ∣ 1 ⟩).
Proof.
  intros.
  destruct b; solve_matrix; autorewrite with R_db Cexp_db; lca.
Qed.

(* CNOT properties *)

Lemma CNOT_spec : forall (x y : nat), (x < 2)%nat -> (y < 2)%nat -> cnot × ∣ x,y ⟩ = ∣ x, (x + y) mod 2 ⟩.
Proof.
  intros; destruct x as [| [|x]], y as [| [|y]]; try lia; lma'.
Qed.

Lemma CNOT00_spec : cnot × ∣ 0,0 ⟩ = ∣ 0,0 ⟩.
Proof. lma'. Qed.

Lemma CNOT01_spec : cnot × ∣ 0,1 ⟩ = ∣ 0,1 ⟩.
Proof. lma'. Qed.

Lemma CNOT10_spec : cnot × ∣ 1,0 ⟩ = ∣ 1,1 ⟩.
Proof. lma'. Qed.
                                        
Lemma CNOT11_spec : cnot × ∣ 1,1 ⟩ = ∣ 1,0 ⟩.
Proof. lma'. Qed.

(* SWAP properties *)

Lemma SWAP_spec : forall x y, swap × ∣ x,y ⟩ = ∣ y,x ⟩.
Proof. intros. destruct x,y; lma'. Qed.

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
Proof. solve_matrix. Qed.

Lemma ket1_transpose_bra1 : (ket 1) ⊤ = bra 1.
Proof. solve_matrix. Qed.

Lemma bra0_transpose_ket0 : (bra 0) ⊤ = ket 0.
Proof. solve_matrix. Qed.

Lemma bra1_transpose_ket1 : (bra 1) ⊤ = ket 1.
Proof. solve_matrix. Qed.

Lemma bra1_adjoint_ket1 : (bra 1) † = ket 1.
Proof. solve_matrix. Qed.

Lemma ket1_adjoint_bra1 : (ket 1) † = bra 1.
Proof. solve_matrix. Qed.

Lemma bra0_adjoint_ket0 : (bra 0) † = ket 0.
Proof. solve_matrix. Qed.

Lemma ket0_adjoint_bra0 : (ket 0) † = bra 0.
Proof. solve_matrix. Qed.

(* Examples using ket_db *)
Lemma XYZ0 : -Ci .* σx × σy × σz × ∣ 0 ⟩ = ∣ 0 ⟩.
Proof. autorewrite with ket_db C_db; easy. Qed.
                                           
Lemma XYZ1 : -Ci .* σx × σy × σz × ∣ 1 ⟩ = ∣ 1 ⟩.
Proof. 
  autorewrite with ket_db C_db.
  replace (Ci * -1 * Ci) with (RtoC 1) by lca. 
  rewrite Mscale_1_l; reflexivity.
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
  unfold kron, basis_vector.
  solve_matrix.
  bdestruct (y0 =? 0).
  - repeat rewrite andb_true_r.
    assert (2^n > 0)%nat.
    { assert (0 < 2^n)%nat by (apply pow_positive; lia). lia.
    }
    specialize (divmod_decomp x0 x y (2^n)%nat H0 Hy) as G.
    bdestruct (x0 =? x * 2 ^ n + y).
    + apply G in H1. destruct H1.
      rewrite H1, H2. do 2 rewrite Nat.eqb_refl. lca.
    + bdestruct (x0 / 2 ^ n =? x); bdestruct (x0 mod 2 ^ n =? y); try lca.
      assert ((x0 / 2 ^ n)%nat = x /\ x0 mod 2 ^ n = y) by easy.
      apply G in H4.
      easy.
  - repeat rewrite andb_false_r.
    lca.
Qed.

(* rewrite f_to_vec as basis_vector *)
Lemma basis_f_to_vec : forall n f,
  f_to_vec n f = basis_vector (2^n) (funbool_to_nat n f).
Proof.
  intros.
  induction n.
  - unfold funbool_to_nat; simpl.
    unfold basis_vector.
    unfold I.
    prep_matrix_equality.
    bdestruct (x =? 0); bdestruct (x =? y); subst; simpl; trivial.
    bdestruct_all; easy.
    bdestructΩ (y <? 1); easy.
  - simpl.
    rewrite IHn.
    unfold funbool_to_nat; simpl.
    unfold basis_vector.
    prep_matrix_equality. unfold kron. 
    rewrite Nat.div_1_r.
    bdestruct (y =? 0).
    2: rewrite 2 andb_false_r; lca.
    rewrite 2 andb_true_r.
    rewrite Nat.mod_1_r, Nat.add_0_r.
    remember (binlist_to_nat (funbool_to_list n f)) as z.
    destruct (f n).
    + specialize (Nat.div_mod x 2) as DM.
      rewrite <- Nat.bit0_mod in *.
      destruct (Nat.testbit x 0); bdestruct (x / 2 =? z);
        simpl in *; bdestruct (x =? S (z + z)); try lia; try lca.
    + specialize (Nat.div_mod x 2) as DM.
      rewrite <- Nat.bit0_mod in *.
      destruct (Nat.testbit x 0); bdestruct (x / 2 =? z);
        simpl in *; bdestruct (x =? (z + z)); try lia; try lca.
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
Lemma equal_on_basis_states_implies_equal : forall {dim} (A B : Square (2 ^ dim)),
  WF_Matrix A -> 
  WF_Matrix B ->
  (forall f, A × (f_to_vec dim f) = B × (f_to_vec dim f)) ->
  A = B.
Proof.
  intros dim A B WFA WFB H.
  apply equal_on_basis_vectors_implies_equal; trivial.
  intros k Lk.
  rewrite basis_f_to_vec_alt; auto.
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
    distribute_plus.  
    restore_dims.
    repeat rewrite <- kron_assoc by auto with wf_db.
    destruct (f i); destruct (f (i + 1 + d)); simpl; Msimpl.
    all: autorewrite with ket_db; reflexivity.
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
    distribute_plus.  
    restore_dims.
    repeat rewrite <- kron_assoc by auto with wf_db.
    destruct (f j); destruct (f (j + 1 + d)); simpl; Msimpl.
    all: autorewrite with ket_db; reflexivity.
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
  all: destruct (f i); destruct (f j); auto.
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

Local Opaque Nat.mul.
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
Local Transparent Nat.mul.

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
  induction n.
  simpl. Msimpl. reflexivity.
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
  induction n; simpl. 
  Msimpl. reflexivity.
  restore_dims.
  rewrite kron_mixed_product.
  rewrite IHn.
  reflexivity.
Qed.

Lemma Mscale_vkron_distr_r : forall n x (f : nat -> Vector 2),
  vkron n (fun i => x .* f i) = x ^ n .* vkron n f.
Proof.
  intros n x f.
  induction n.
  simpl. Msimpl. reflexivity.
  simpl.
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
  induction n; try lia.
  bdestruct (i =? n).
  subst.
  replace (S n - 1 - n)%nat with O by lia.
  simpl. Msimpl.
  reflexivity.
  assert (i < n)%nat by lia.
  specialize (IHn H2).
  replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
  simpl.
  rewrite IHn.
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
  unfold basis_vector; solve_matrix. (* solve_matrix doesn't work? *)
  repeat rewrite andb_true_r.
  bdestruct (x / n =? 0).
  rewrite H1. apply Nat.div_small_iff in H1; auto.
  rewrite Nat.mod_small by auto.
  destruct (x =? k); lca.
  assert (H1' := H1).
  rewrite Nat.div_small_iff in H1'; auto.
  destruct (x / n)%nat; try lia.
  bdestructΩ (x =? k).
  destruct n0; lca.
  destruct (x / n)%nat; try lca.
  destruct n0; lca.
Qed.

Lemma basis_vector_prepend_1 : forall n k,
  n <> 0 -> k < n ->
  ∣1⟩ ⊗ basis_vector n k = basis_vector (2 * n) (k + n).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  all: repeat rewrite andb_true_r.
  specialize (Nat.div_mod x n H) as DM.
  destruct (x / n)%nat.
  rewrite Nat.mul_0_r, Nat.add_0_l in DM.
  assert (x < n)%nat.
  rewrite DM. apply Nat.mod_upper_bound; auto.
  bdestructΩ (x =? k + n)%nat.
  lca.
  destruct n0.
  bdestruct (x mod n =? k).
  bdestructΩ (x =? k + n); lca.
  bdestructΩ (x =? k + n); lca.
  assert (x >= 2 * n)%nat.
  assert (n * S (S n0) >= 2 * n)%nat.
  clear. induction n0; lia.
  lia.
  bdestructΩ (x =? k + n); lca.
  destruct (x /  n)%nat; try lca.
  destruct n0; lca.
Qed.

Local Opaque Nat.mul Nat.div Nat.modulo.
Lemma basis_vector_append_0 : forall n k,
  n <> 0 -> k < n ->
  basis_vector n k ⊗ ∣0⟩ = basis_vector (2 * n) (2 * k).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  rewrite Nat.div_1_r.
  bdestruct (y =? 0); subst.
  2: repeat rewrite andb_false_r; lca.
  bdestruct (x =? 2 * k); subst.
  rewrite Nat.mul_comm.
  rewrite Nat.div_mul by auto.
  rewrite Nat.eqb_refl.
  rewrite Nat.mod_mul, Nat.mod_0_l by auto. 
  lca.
  bdestruct (x / 2 =? k); simpl; try lca.
  destruct (x mod 2) eqn:m.
  contradict H1.
  rewrite <- H2.
  apply Nat.div_exact; auto.
  destruct n0; try lca.
  rewrite Nat.mod_0_l by auto.
  lca.
Qed.

Lemma basis_vector_append_1 : forall n k,
  n <> 0 -> k < n ->
  basis_vector n k ⊗ ∣1⟩ = basis_vector (2 * n) (2 * k + 1).
Proof.
  intros.
  unfold basis_vector; solve_matrix.
  rewrite Nat.div_1_r.
  bdestruct (y =? 0); subst.
  2: repeat rewrite andb_false_r; lca.
  bdestruct (x =? 2 * k + 1); subst. 
  rewrite Nat.mul_comm. 
  rewrite Nat.div_add_l by auto.
  replace (1 / 2) with 0 by auto.
  rewrite Nat.add_0_r.
  rewrite Nat.eqb_refl.
  rewrite Nat.add_comm, Nat.mod_add by auto. 
  replace (1 mod 2) with 1 by auto. 
  replace (0 mod 1) with 0 by auto.  
  lca. 
  bdestruct (x / 2 =? k); simpl; try lca.
  destruct (x mod 2) eqn:m.   
  replace (0 mod 1) with 0 by auto; lca.
  destruct n0; try lca.
  contradict H1.
  rewrite <- H2.
  remember 2 as two.
  rewrite <- m.
  subst.
  apply Nat.div_mod; auto.
Qed.
Local Transparent Nat.mul Nat.div Nat.modulo.

Lemma kron_n_0_is_0_vector : forall (n:nat), n ⨂ ∣0⟩ = basis_vector (2 ^ n) O.
Proof.
  intros.
  induction n.
  simpl.
  prep_matrix_equality.
  unfold basis_vector, I.
  bdestruct_all; reflexivity.
  simpl.
  rewrite IHn. replace (1 ^ n)%nat with 1%nat.
  rewrite (basis_vector_append_0 (2 ^ n) 0).
  rewrite Nat.mul_0_r.
  reflexivity.
  apply Nat.pow_nonzero. lia.
  apply pow_positive. lia.
  rewrite Nat.pow_1_l. reflexivity.
Qed.

Lemma vkron_to_vsum1 : forall n (c : R),
  n > 0 -> 
  vkron n (fun k => ∣0⟩ .+ Cexp (c * 2 ^ (n - k - 1)) .* ∣1⟩) = 
    big_sum (fun k => Cexp (c * INR k) .* basis_vector (2 ^ n) k) (2 ^ n).
Proof.
  intros n c Hn.
  destruct n; try lia.
  induction n.
  simpl. 
  repeat rewrite <- big_sum_extend_r.
  Msimpl. 
  rewrite Rmult_0_r, Cexp_0, Mscale_1_l.
  replace (basis_vector 2 0) with ∣0⟩ by solve_matrix.
  replace (basis_vector 2 1) with ∣1⟩ by solve_matrix.
  reflexivity. 
  remember (S n) as n'.
  rewrite <- vkron_extend_l; auto with wf_db.
  replace (shift (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (S n' - k - 1)) .* ∣1⟩) 1) with (fun k : nat => ∣0⟩ .+ Cexp (c * 2 ^ (n' - k - 1)) .* ∣1⟩).
  2: { unfold shift. 
       apply functional_extensionality; intro k.
       replace (S n' - (k + 1) - 1)%nat with (n' - k - 1)%nat by lia.
       reflexivity. }
  rewrite IHn by lia.
  replace (S n' - 0 - 1)%nat with n' by lia.
  remember (2 ^ n')%nat as N.
  assert (HN: (N > 0)%nat).
  subst. apply pow_positive. lia.
  replace (2 ^ n')%R with (INR N).
  2: { subst. rewrite pow_INR. simpl INR. replace (1+1)%R with 2%R by lra.
       reflexivity. }
  replace (2 ^ S n')%nat with (2 * N)%nat.
  2: { subst. unify_pows_two. }
  clear - HN.
  rewrite kron_plus_distr_r.
  rewrite 2 kron_Msum_distr_l.
  replace (2 * N) with (N + N) by lia.
  rewrite big_sum_sum.
  replace (N + N) with (2 * N) by lia.
  apply f_equal_gen; try apply f_equal; apply big_sum_eq_bounded; intros.
  distribute_scale. 
  rewrite basis_vector_prepend_0 by lia.
  reflexivity.
  distribute_scale.
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
    replace (basis_vector 2 0) with ∣0⟩ by solve_matrix.
    replace (basis_vector 2 1) with ∣1⟩ by solve_matrix.
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
  intro b.
  destruct b; simpl; autorewrite with ket_db.
  replace (/ √ 2 * (-1 * 1))%C with (- / √ 2)%C by lca.
  reflexivity. reflexivity.
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
