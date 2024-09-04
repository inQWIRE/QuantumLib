Require Import VectorStates.
Require Import Kronecker.
Require Export PermutationsBase.
Require Import PermutationAutomation.
Require Import PermutationInstances.
Require Import Modulus.
Require Import Pad.
Require Import Complex.
Import Setoid.

(** Implementation of permutations as matrices and facts about those matrices. **)

(** * Prerequisite lemmas **)

Lemma basis_vector_equiv_e_i : forall n k, 
  basis_vector n k ≡ e_i k.
Proof.
  intros n k i j Hi Hj.
  unfold basis_vector, e_i.
  bdestructΩ'.
Qed.

Lemma basis_vector_eq_e_i : forall n k, (k < n)%nat ->
  basis_vector n k = e_i k.
Proof.
  intros n k Hk.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  apply basis_vector_equiv_e_i.
Qed.

Lemma vector_equiv_basis_comb : forall n (y : Vector n),
  y ≡ big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  symmetry.
  rewrite Msum_Csum.
  apply big_sum_unique.
  exists i.
  repeat split; try easy.
  - unfold ".*", e_i; bdestructΩ'; now Csimpl.
  - intros l Hl Hnk.
    unfold ".*", e_i; bdestructΩ'; now Csimpl.
Qed.

Lemma vector_eq_basis_comb : forall n (y : Vector n),
  WF_Matrix y -> 
  y = big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y Hwfy.
  apply mat_equiv_eq; auto with wf_db.
  apply vector_equiv_basis_comb.
Qed.

Lemma Mmult_if_r {n m o} (A : Matrix n m) (B B' : Matrix m o) (b : bool) :
  A × (if b then B else B') = 
  if b then A × B else A × B'.
Proof.
  now destruct b.
Qed.

Lemma Mmult_if_l {n m o} (A A' : Matrix n m) (B : Matrix m o) (b : bool) :
  (if b then A else A') × B = 
  if b then A × B else A' × B.
Proof.
  now destruct b.
Qed.


Definition direct_sum' {n m o p : nat} (A : Matrix n m) (B : Matrix o p) :
  Matrix (n+o) (m+p) :=
  (fun i j => if (i <? n) && (j <? m) then A i j
  else if (¬ (i <? n) || (j <? m)) && (i <? n+o) && (j <? m+p) then B (i-n) (j-m)
  else C0)%nat.

#[export] Hint Unfold direct_sum' : U_db.

Notation "A .⊕' B" := (direct_sum' A B) 
  (at level 50, left associativity): matrix_scope.

Lemma direct_sum'_WF : forall {n m o p : nat} (A : Matrix n m) (B : Matrix o p),
  WF_Matrix (A .⊕' B).
Proof.
  intros n m o p A B i j [Hi | Hj];
  unfold direct_sum'; now bdestruct_all.
Qed.
#[export] Hint Resolve direct_sum'_WF : wf_db.

Lemma direct_sum'_assoc : forall {n m o p q r} 
  (A : Matrix n m) (B : Matrix o p) (C : Matrix q r), 
  A .⊕' B .⊕' C = A .⊕' (B .⊕' C).
Proof.
  intros n m o p q r A B C.
  apply mat_equiv_eq; auto using WF_Matrix_dim_change with wf_db.
  intros i j Hi Hj.
  unfold direct_sum'.
  rewrite !Nat.sub_add_distr.
  bdestructΩ'.
Qed.

Lemma direct_sum'_eq_direct_sum : forall {n m o p : nat}
  (A : Matrix n m) (B : Matrix o p), WF_Matrix A -> WF_Matrix B ->
  A .⊕' B = A .⊕ B.
Proof.
  intros n m o p A B HA HB.
  apply mat_equiv_eq; [|apply WF_direct_sum|]; auto with wf_db.
  intros i j Hi Hj.
  unfold direct_sum, direct_sum'.
  bdestruct_all; try lia + easy;
  rewrite HA by lia; easy.
Qed.

Lemma direct_sum'_simplify_mat_equiv {n m o p} : forall (A B : Matrix n m) 
  (C D : Matrix o p), A ≡ B -> C ≡ D -> direct_sum' A C ≡ direct_sum' B D.
Proof.
  intros A B C D HAB HCD i j Hi Hj.
  unfold direct_sum'.
  bdestruct (i <? n);
  bdestruct (j <? m); simpl; [rewrite HAB | | |]; try easy.
  bdestruct_all; try lia + easy; rewrite HCD by lia; easy.
Qed.

Lemma direct_sum'_Mmult {n m o p q r} (A : Matrix n m) (B : Matrix p q)
  (C : Matrix m o) (D : Matrix q r) : 
  (A .⊕' B) × (C .⊕' D) = (A × C) .⊕' (B × D).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold direct_sum'.
  bdestruct_all; simpl.
  - unfold Mmult.
    rewrite big_sum_sum.
    rewrite Cplus_comm.
    rewrite big_sum_0_bounded by
      (intros; now bdestruct_all; Csimpl).
    Csimpl.
    apply big_sum_eq_bounded.
    intros k Hk.
    now bdestruct_all; simpl; Csimpl.
  - unfold Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    now bdestruct_all; simpl; Csimpl.
  - unfold Mmult.
    rewrite big_sum_0_bounded; [easy|].
    intros k Hk.
    now bdestruct_all; simpl; Csimpl.
  - unfold Mmult.
    rewrite big_sum_sum.
    rewrite big_sum_0_bounded by
      (intros; now bdestruct_all; Csimpl).
    Csimpl.
    apply big_sum_eq_bounded.
    intros k Hk.
    bdestruct_all; simpl; Csimpl.
    do 2 f_equal; lia.
Qed.

Lemma direct_sum'_Mmult_mat_equiv {n m o p q r} 
  (A : Matrix n m) (B : Matrix p q)
  (C : Matrix m o) (D : Matrix q r) : 
  (A .⊕' B) × (C .⊕' D) ≡ (A × C) .⊕' (B × D).
Proof.
  now rewrite direct_sum'_Mmult.
Qed.

Lemma direct_sum_0_r {n m} (A : Matrix n m) o p :
  WF_Matrix A -> 
  @direct_sum' n m o p A Zero = A.
Proof.
  intros HA.
  prep_matrix_equality.
  unfold direct_sum', Zero.
  symmetry.
  bdestructΩ'_with ltac:
    (try lia; try rewrite HA by lia; try reflexivity).
Qed.

Lemma direct_sum_Mscale {n m p q} (A : Matrix n m) 
  (B : Matrix p q) (c : C) : 
  (c .* A) .⊕' (c .* B) = c .* (A .⊕' B).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  autounfold with U_db.
  bdestruct_all; simpl; now Csimpl.
Qed.

Lemma ei_direct_sum_split n m k : 
  @e_i (n + m) k = 
  (if k <? n then 
    @e_i n k .⊕' @Zero m 0
  else 
    @Zero n 0 .⊕' @e_i m (k - n)).
Proof.
  apply mat_equiv_eq; 
  [try bdestruct_one; auto using WF_Matrix_dim_change with wf_db..|].
  intros i j Hi Hj.
  replace j with O by lia.
  autounfold with U_db.
  simpl.
  simplify_bools_lia_one_kernel.
  bdestructΩ'_with ltac:(try lia; try reflexivity).
Qed.

Add Parametric Morphism {n m o p} : (@direct_sum' n m o p) 
  with signature (@mat_equiv n m) ==> (@mat_equiv o p) 
    ==> (@mat_equiv (n+o) (m+p)) as direct_sum'_mat_equiv_morph.
Proof. intros; apply direct_sum'_simplify_mat_equiv; easy. Qed.

Lemma ei_kron_split k n m :
  @e_i (n*m) k = 
  e_i (k / m) ⊗ e_i (k mod m).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia.
  unfold e_i, kron.
  do 2 simplify_bools_lia_one_kernel.
  do 2 simplify_bools_moddy_lia_one_kernel.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  now rewrite andb_comm, <- eqb_iff_div_mod_eqb.
Qed.

Lemma ei_kron_join k l n m :
  (l < m)%nat ->
  @e_i n k ⊗ e_i l =
  @e_i (n*m) (k*m + l).
Proof.
  intros Hl.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  replace j with O by lia.
  unfold e_i, kron.
  do 2 simplify_bools_lia_one_kernel.
  do 2 simplify_bools_moddy_lia_one_kernel.
  rewrite Cmult_if_if_1_l.
  apply f_equal_if; [|easy..].
  symmetry.
  rewrite (eqb_iff_div_mod_eqb m).
  rewrite mod_add_l, Nat.div_add_l by lia.
  rewrite (Nat.mod_small l m Hl), (Nat.div_small l m Hl).
  now rewrite Nat.add_0_r, andb_comm.
Qed.

Local Open Scope nat_scope.

Lemma matrix_times_basis_eq_lt {m n : nat} (A : Matrix m n) (i j : nat) :
  j < n -> (A × basis_vector n j) i 0 = A i j.
Proof.
  intros Hj.
  unfold Mmult.
  rewrite (big_sum_eq_bounded _ (fun k => if k =? j then A i j else 0%R)%C).
  2: {
    intros k Hk.
    unfold basis_vector.
    bdestructΩ'; lca.
  }
  rewrite big_sum_if_eq_C.
  bdestructΩ'.
Qed.

Lemma matrix_times_basis_mat_equiv {m n : nat} (A : Matrix m n) (j : nat) :
  j < n -> mat_equiv (A × basis_vector n j) 
  (get_col A j).
Proof.
  intros Hj i z Hi Hz.
  replace z with 0 by lia.
  rewrite matrix_times_basis_eq_lt by easy.
  unfold get_col.
  bdestructΩ'.
Qed.

Lemma matrix_conj_basis_eq_lt {m n : nat} (A : Matrix m n) (i j : nat) :
  i < m -> j < n -> ((basis_vector m i)⊤ × A × basis_vector n j) 0 0 = A i j.
Proof.
  intros Hi Hj.
  rewrite matrix_times_basis_mat_equiv by lia.
  unfold get_col.
  bdestructΩ'.
  unfold Mmult, Matrix.transpose.
  rewrite (big_sum_eq_bounded _ (fun k => if k =? i then A i j else 0%R)%C).
  2: {
    intros k Hk.
    unfold basis_vector.
    bdestructΩ'; lca.
  }
  rewrite big_sum_if_eq_C.
  bdestructΩ'.
Qed.

Lemma mat_equiv_of_all_basis_conj {m n : nat} (A B : Matrix m n) 
  (H : forall (i j : nat), i < m -> j < n -> 
  ((basis_vector m i) ⊤ × A × basis_vector n j) 0 0 =
  ((basis_vector m i) ⊤ × B × basis_vector n j) 0 0) :
  mat_equiv A B.
Proof.
  intros i j Hi Hj.
  specialize (H i j Hi Hj).
  now rewrite 2!matrix_conj_basis_eq_lt in H by easy.
Qed.

Local Open Scope nat_scope.

(** * Permutation matrices *)
Definition perm_mat n (p : nat -> nat) : Square n :=
  (fun x y => if (x =? p y) && (x <? n) && (y <? n) then C1 else C0).

Lemma perm_mat_WF : forall n p, WF_Matrix (perm_mat n p).
Proof.
  intros n p x y Hxy.
  unfold perm_mat. 
  bdestructΩ'.
Qed. 
#[export] Hint Resolve perm_mat_WF : wf_db.

Lemma perm_mat_defn n p : 
  perm_mat n p ≡
  fun x y => if x =? p y then C1 else C0.
Proof.
  intros i j Hi Hj.
  unfold perm_mat.
  bdestructΩ'.
Qed.

Add Parametric Morphism n : (perm_mat n) with signature
  perm_eq n ==> eq as perm_mat_perm_eq_to_eq_proper.
Proof.
  intros f g Hfg.
  apply mat_equiv_eq; auto with wf_db.
  rewrite !perm_mat_defn.
  intros i j Hi Hj.
  now rewrite Hfg by easy.
Qed.

Lemma perm_mat_id : forall n,
  perm_mat n (Datatypes.id) = (I n).
Proof. 
  intros n.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj. 
  unfold Datatypes.id, perm_mat, I.
  bdestructΩ'.
Qed.

Lemma perm_mat_idn n :
  perm_mat n idn = (I n).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj. 
  unfold perm_mat, I.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite perm_mat_idn : perm_cleanup_db.

Lemma perm_mat_unitary : forall n p, 
  permutation n p -> WF_Unitary (perm_mat n p).
Proof.
  intros n p [pinv Hp].
  split; [apply perm_mat_WF|].
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold Mmult, adjoint, perm_mat, I.
  do 2 simplify_bools_lia_one_kernel.
  bdestruct (i =? j).
  - subst.
    apply big_sum_unique.
    exists (p j).
    destruct (Hp j) as [? _]; auto.
    split; auto.
    split; intros; bdestructΩ'; lca.
  - apply (@big_sum_0 C C_is_monoid).
    intros z.
    bdestruct_all; simpl; try lca.
    subst.
    assert (pinv (p i) = pinv (p j)) by auto.
    pose proof (fun x Hx => proj1 (proj2 (proj2 (Hp x Hx)))) as Hrw.
    rewrite !Hrw in * by auto.
    congruence.
Qed.

Lemma perm_mat_Mmult n f g :
  perm_bounded n g ->
  perm_mat n f × perm_mat n g = perm_mat n (f ∘ g)%prg.
Proof.
  intros Hg.
  apply mat_equiv_eq; auto with wf_db.
  intros i j Hi Hj.
  unfold perm_mat, Mmult, compose.
  do 2 simplify_bools_lia_one_kernel.
  bdestruct (i =? f (g j)).
  - apply big_sum_unique.
    exists (g j).
    specialize (Hg j Hj).
    split; [now auto|].
    split; [bdestructΩ'; now Csimpl|].
    intros k Hk ?.
    bdestructΩ'; now Csimpl.
  - apply (@big_sum_0_bounded C).
    intros k Hk.
    bdestructΩ'; now Csimpl.
Qed.

Lemma perm_mat_I : forall n f,
  (forall x, x < n -> f x = x) ->
  perm_mat n f = I n.
Proof.
  intros n f Hinv.
  apply mat_equiv_eq; auto with wf_db.
  unfold perm_mat, I.
  intros i j Hi Hj.
  do 2 simplify_bools_lia_one_kernel.
  now rewrite Hinv by easy.
Qed.

Lemma perm_mat_col_swap : forall n f i j,
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = col_swap (perm_mat n f) i j.
Proof. 
  intros. 
  apply mat_equiv_eq; auto with wf_db.
  intros k l Hk Hl.
  unfold perm_mat, fswap, col_swap, I.
  bdestructΩ'.
Qed. 

Lemma perm_mat_col_swap_I : forall n f i j,
  (forall x, x < n -> f x = x) ->
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = col_swap (I n) i j.
Proof. 
  intros.
  rewrite perm_mat_col_swap by easy.
  now rewrite perm_mat_I by easy.
Qed.


Lemma perm_mat_row_swap : forall n f i j,
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = (row_swap (perm_mat n f)† i j)†.
Proof. 
  intros. 
  apply mat_equiv_eq; auto with wf_db.
  intros k l Hk Hl.
  unfold perm_mat, fswap, row_swap, I, adjoint.
  do 3 simplify_bools_lia_one_kernel.
  rewrite !(if_dist _ _ _ Cconj).
  Csimpl.
  bdestructΩ'.
Qed. 

Lemma perm_mat_e_i : forall n f i, 
  i < n ->
  (perm_mat n f) × e_i i = e_i (f i).
Proof. 
  intros n f i Hi. 
  apply mat_equiv_eq; auto with wf_db.
  unfold mat_equiv; intros k l Hk Hl.
  replace l with 0 in * by lia.
  unfold Mmult.
  apply big_sum_unique.
  exists i.
  split; auto.
  unfold e_i, perm_mat;
  split; [bdestructΩ'_with ltac:(try lia; try lca)|].
  intros. 
  bdestructΩ'_with ltac:(try lia; try lca). 
Qed.

(* with get_entry_with_e_i this became soo much easier *)
Lemma perm_mat_conjugate : forall {n} (A : Square n) f (i j : nat), 
  WF_Matrix A -> 
  i < n -> j < n ->
  perm_bounded n f ->
  ((perm_mat n f)† × A × ((perm_mat n f))) i j = A (f i) (f j). 
Proof. 
  intros. 
  rewrite get_entry_with_e_i, (get_entry_with_e_i A) 
    by auto with perm_bounded_db.
  rewrite <- 2 Mmult_assoc, <- Mmult_adjoint.
  rewrite perm_mat_e_i by auto with perm_bounded_db.
  rewrite 3 Mmult_assoc.
  rewrite perm_mat_e_i; auto.
Qed.

Lemma perm_mat_conjugate_nonsquare : 
  forall {m n} (A : Matrix m n) f g (i j : nat), 
  WF_Matrix A -> 
  i < m -> j < n ->
  perm_bounded m g -> perm_bounded n f ->
  ((perm_mat m g)† × A × ((perm_mat n f))) i j = A (g i) (f j). 
Proof. 
  intros. 
  rewrite get_entry_with_e_i, (get_entry_with_e_i A) by auto.
  rewrite <- 2 Mmult_assoc, <- Mmult_adjoint.
  rewrite perm_mat_e_i by auto.
  rewrite 3 Mmult_assoc.
  rewrite perm_mat_e_i; auto.
Qed.

Lemma perm_mat_permutes_basis_vectors_r : forall n f k, (k < n)%nat ->
  (perm_mat n f) × (basis_vector n k) = e_i (f k).
Proof.
  intros n f k Hk.
  rewrite basis_vector_eq_e_i by easy.
  apply perm_mat_e_i; easy.
Qed.

Lemma perm_mat_permutes_matrix_r : forall n m f (A : Matrix n m),
  permutation n f ->
  (perm_mat n f) × A ≡ (fun i j => A (perm_inv n f i) j).
Proof.
  intros n m f A Hperm.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite Mmult_assoc, <- 2(matrix_by_basis _ _ Hk).
  rewrite (vector_equiv_basis_comb _ (get_col _ _)).
  rewrite Mmult_Msum_distr_l.
  erewrite big_sum_eq_bounded.
  2: {
    intros l Hl.
    rewrite Mscale_mult_dist_r, perm_mat_e_i by easy.
    reflexivity.
  }
  intros i j Hi Hj; replace j with O by lia; clear j Hj.
  rewrite Msum_Csum.
  unfold get_col, scale, e_i.
  rewrite Nat.eqb_refl.
  apply big_sum_unique.
  exists (perm_inv n f i).
  repeat split; auto with perm_bounded_db.
  - rewrite (perm_inv_is_rinv_of_permutation n f Hperm i Hi), Nat.eqb_refl.
    bdestructΩ'; now Csimpl.
  - intros j Hj Hjne.
    bdestruct (i =? f j); [|bdestructΩ'; now Csimpl].
    exfalso; apply Hjne.
    apply (permutation_is_injective n f Hperm); auto with perm_bounded_db.
    rewrite (perm_inv_is_rinv_of_permutation n f Hperm i Hi); easy.
Qed.

Lemma perm_mat_equiv_of_perm_eq : forall n f g, 
  (perm_eq n f g) ->
  perm_mat n f ≡ perm_mat n g.
Proof.
  intros n f g Heq.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite 2!perm_mat_e_i, Heq by easy.
  easy.
Qed.

#[export] Hint Resolve perm_mat_equiv_of_perm_eq : perm_inv_db.

Lemma perm_mat_eq_of_perm_eq : forall n f g, 
  (perm_eq n f g) ->
  perm_mat n f = perm_mat n g.
Proof.
  intros.
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_mat_equiv_of_perm_eq.
Qed.

#[export] Hint Resolve perm_mat_eq_of_perm_eq : perm_inv_db.

Lemma perm_mat_equiv_of_perm_eq' : forall n m f g, n = m ->
  (perm_eq n f g) ->
  perm_mat n f ≡ perm_mat m g.
Proof.
  intros; subst n; apply perm_mat_equiv_of_perm_eq; easy.
Qed.

Lemma perm_mat_transpose {n f} (Hf : permutation n f) :
  (perm_mat n f) ⊤ ≡ perm_mat n (perm_inv n f).
Proof.
  intros i j Hi Hj.
  unfold "⊤".
  unfold perm_mat.
  simplify_bools_lia.
  rewrite <- (@perm_inv_eqb_iff n f) by cleanup_perm.
  now rewrite Nat.eqb_sym.
Qed.

Lemma perm_mat_transpose_eq {n f} (Hf : permutation n f) :
  (perm_mat n f) ⊤ = perm_mat n (perm_inv n f).
Proof. 
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_mat_transpose.
Qed.

Lemma matrix_by_basis_perm_eq {n m} (A : Matrix n m) (i : nat) (Hi : i < m) : 
  get_col A i ≡ A × e_i i.
Proof.
  intros k l Hk Hl.
  replace l with 0 by lia.
  unfold get_col.
  simplify_bools_lia_one_kernel.
  symmetry.
  unfold Mmult, e_i.
  simplify_bools_lia_one_kernel.
  apply big_sum_unique.
  exists i.
  split; auto.
  do 2 simplify_bools_lia_one_kernel.
  split; intros; 
  simplify_bools_lia;
  now Csimpl.
Qed.

Lemma perm_mat_permutes_matrix_l : forall n m f (A : Matrix n m),
  perm_bounded m f ->
  A × (perm_mat m f) ≡ (fun i j => A i (f j)).
Proof.
  intros n m f A Hf.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite Mmult_assoc, perm_mat_e_i, <- (matrix_by_basis _ _ Hk) by easy.
  rewrite <- matrix_by_basis_perm_eq by auto with perm_bounded_db.
  easy.
Qed.

Lemma perm_mat_permutes_matrix_l_eq : forall n m f (A : Matrix n m),
  WF_Matrix A ->
  perm_bounded m f ->
  A × (perm_mat m f) = make_WF (fun i j => A i (f j)).
Proof.
  intros n m f A HA Hf.
  apply mat_equiv_eq; auto with wf_db.
  rewrite make_WF_equiv.
  now apply perm_mat_permutes_matrix_l.
Qed.

Lemma perm_mat_permutes_matrix_r_eq : forall n m f (A : Matrix n m),
  WF_Matrix A ->
  permutation n f ->
  (perm_mat n f) × A = make_WF (fun i j => A (perm_inv n f i) j).
Proof.
  intros n m f A HA Hf.
  apply mat_equiv_eq; auto with wf_db.
  rewrite make_WF_equiv.
  now apply perm_mat_permutes_matrix_r.
Qed.

Lemma perm_mat_perm_eq_idn n f :
  perm_eq n f idn ->
  perm_mat n f = I n.
Proof.
  intros ->.
  apply perm_mat_idn.
Qed.

Lemma perm_mat_transpose_rinv {n f} (Hf : permutation n f) : 
  (perm_mat n f) × (perm_mat n f) ⊤ = I n.
Proof.
  rewrite perm_mat_transpose_eq by easy.
  rewrite perm_mat_Mmult by auto with perm_db.
  cleanup_perm.
Qed.

Lemma perm_mat_transpose_linv {n f} (Hf : permutation n f) : 
  (perm_mat n f) ⊤ × (perm_mat n f) = I n.
Proof.
  rewrite perm_mat_transpose_eq by easy.
  rewrite perm_mat_Mmult by auto with perm_db.
  cleanup_perm.
Qed.

Lemma perm_mat_of_stack_perms n0 n1 f g : 
  perm_bounded n0 f -> perm_bounded n1 g -> 
  perm_mat (n0 + n1) (stack_perms n0 n1 f g) = 
  direct_sum' (perm_mat n0 f) (perm_mat n1 g).
Proof.
  intros Hf Hg.
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite perm_mat_e_i by easy.
  rewrite 2!ei_direct_sum_split.
  rewrite Mmult_if_r.
  rewrite (direct_sum'_Mmult _ _ (e_i k) (Zero)).
  rewrite (direct_sum'_Mmult _ _ (@Zero n0 0) (e_i (k - n0))).
  rewrite 2!Mmult_0_r.
  bdestruct (k <? n0).
  - rewrite perm_mat_e_i, stack_perms_left by easy.
    pose proof (Hf k).
    now bdestructΩ (f k <? n0).
  - rewrite perm_mat_e_i, stack_perms_right by lia.
    pose proof (Hg (k - n0)).
    bdestructΩ (g (k - n0) + n0 <? n0).
    now rewrite Nat.add_sub.
Qed.

#[export] Hint Rewrite perm_mat_of_stack_perms
  using solve [auto with perm_bounded_db] : perm_cleanup_db.


Lemma perm_mat_of_tensor_perms n0 n1 f g : 
  perm_bounded n1 g ->
  perm_mat (n0 * n1) (tensor_perms n0 n1 f g) = 
  perm_mat n0 f ⊗ perm_mat n1 g.
Proof.
  intros Hg.
  apply mat_equiv_eq; auto with wf_db.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite perm_mat_e_i by easy.
  symmetry.
  rewrite ei_kron_split.
  restore_dims.
  rewrite kron_mixed_product.
  unfold tensor_perms.
  simplify_bools_lia_one_kernel.
  rewrite 2!perm_mat_e_i by show_moddy_lt.
  now rewrite ei_kron_join by cleanup_perm.
Qed.

Lemma perm_mat_inj_mat_equiv n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) : 
  perm_mat n f ≡ perm_mat n g ->
  perm_eq n f g.
Proof.
  intros Hequiv.
  intros i Hi.
  generalize (Hequiv (f i) i (Hf i Hi) Hi).
  unfold perm_mat.
  pose proof (Hf i Hi).
  pose proof C1_nonzero.
  bdestructΩ'.
Qed.

Lemma perm_mat_inj n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) : 
  perm_mat n f = perm_mat n g ->
  perm_eq n f g.
Proof.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  now apply perm_mat_inj_mat_equiv.
Qed.

Lemma perm_mat_determinant_sqr n f (Hf : permutation n f) : 
	(Determinant (perm_mat n f) ^ 2)%C = 1%R.
Proof.
  simpl.
  Csimpl.
  rewrite Determinant_transpose at 1.
  rewrite Determinant_multiplicative.
  rewrite perm_mat_transpose_linv by easy.
  now rewrite Det_I.
Qed.

Lemma perm_mat_perm_eq_of_proportional n f g : 
	(exists c, perm_mat n f = c .* perm_mat n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_eq n f g.
Proof.
	intros (c & Heq & Hc) Hf.
	rewrite <- mat_equiv_eq_iff in Heq by auto with wf_db.
	intros i Hi.
	pose proof (Hf i Hi) as Hfi.
	generalize (Heq (f i) i Hfi Hi).
	unfold perm_mat, scale.
	do 3 simplify_bools_lia_one_kernel.
	rewrite Cmult_if_1_r.
	pose proof C1_nonzero.
	bdestructΩ'.
Qed.

Lemma perm_mat_eq_of_proportional n f g : 
	(exists c, perm_mat n f = c .* perm_mat n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_mat n f = perm_mat n g.
Proof.
	intros H Hf.
	apply perm_mat_eq_of_perm_eq.
  now apply perm_mat_perm_eq_of_proportional.
Qed.

Lemma Mmult_perm_mat_l n m (A B : Matrix n m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation n f) : 
  perm_mat n f × A = B <-> A = perm_mat n (perm_inv n f) × B.
Proof.
  rewrite <- perm_mat_transpose_eq by auto.
  split; [intros <- | intros ->]; 
  now rewrite <- Mmult_assoc, 1?perm_mat_transpose_rinv, 
    1?perm_mat_transpose_linv, Mmult_1_l by auto.
Qed.

Lemma Mmult_perm_mat_l' n m (A B : Matrix n m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation n f) : 
  B = perm_mat n f × A <-> perm_mat n (perm_inv n f) × B = A.
Proof.
  split; intros H; symmetry;
  apply Mmult_perm_mat_l; auto.
Qed.

Lemma Mmult_perm_mat_r n m (A B : Matrix n m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation m f) : 
  A × perm_mat m f = B <-> A = B × perm_mat m (perm_inv m f).
Proof.
  rewrite <- perm_mat_transpose_eq by auto.
  split; [intros <- | intros ->]; 
  now rewrite Mmult_assoc, 1?perm_mat_transpose_rinv, 
    1?perm_mat_transpose_linv, Mmult_1_r by auto.
Qed.

Lemma Mmult_perm_mat_r' n m (A B : Matrix n m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation m f) : 
  B = A × perm_mat m f <-> B × perm_mat m (perm_inv m f) = A.
Proof.
  split; intros H; symmetry;
  apply Mmult_perm_mat_r; auto.
Qed.

(** Transform a (0,...,n-1) permutation into a 2^n by 2^n matrix. *)
Definition perm_to_matrix n p :=
  perm_mat (2 ^ n) (qubit_perm_to_nat_perm n p).

Lemma perm_to_matrix_WF : forall n p, WF_Matrix (perm_to_matrix n p).
Proof. intros. apply perm_mat_WF. Qed. 
#[export] Hint Resolve perm_to_matrix_WF : wf_db.

Add Parametric Morphism n : (perm_to_matrix n) with signature
  perm_eq n ==> eq as perm_to_matrix_perm_eq_to_eq_proper.
Proof.
  intros f g Hfg.
  unfold perm_to_matrix.
  now rewrite Hfg.
Qed.

Lemma perm_to_matrix_permutes_qubits : forall n p f, 
  perm_bounded n p ->
  perm_to_matrix n p × f_to_vec n f = f_to_vec n (fun x => f (p x)).
Proof.
  intros n p f Hp.
  rewrite 2 basis_f_to_vec.
  rewrite !basis_vector_eq_e_i by apply funbool_to_nat_bound.
  unfold perm_to_matrix.
  rewrite perm_mat_e_i by apply funbool_to_nat_bound.
  f_equal.
  rewrite qubit_perm_to_nat_perm_defn by apply funbool_to_nat_bound.
  apply funbool_to_nat_eq.
  intros i Hi.
  unfold compose.
  now rewrite funbool_to_nat_inverse by auto.
Qed.

Lemma perm_to_matrix_unitary : forall n p, 
  permutation n p ->
  WF_Unitary (perm_to_matrix n p).
Proof.
  intros.
  apply perm_mat_unitary.
  auto with perm_db.
Qed.


Lemma Private_perm_to_matrix_Mmult : forall n f g,
  permutation n f -> permutation n g ->
  perm_to_matrix n f × perm_to_matrix n g = perm_to_matrix n (g ∘ f)%prg.
Proof.
  intros n f g Hf Hg. 
  unfold perm_to_matrix.
  rewrite perm_mat_Mmult by auto with perm_bounded_db.
  now rewrite qubit_perm_to_nat_perm_compose by auto with perm_bounded_db.
Qed.

#[deprecated(note="Use perm_to_matrix_compose instead")]
Notation perm_to_matrix_Mmult := Private_perm_to_matrix_Mmult.

Lemma perm_to_matrix_I : forall n f,
  (forall x, x < n -> f x = x) ->
  perm_to_matrix n f = I (2 ^ n).
Proof.
  intros n f Hf. 
  unfold perm_to_matrix.
  apply perm_mat_I.
  intros x Hx.
  unfold qubit_perm_to_nat_perm, compose. 
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. rewrite Hf by assumption. reflexivity. }
  simplify_bools_lia_one_kernel.
  apply nat_to_funbool_inverse.
  assumption.
Qed.

Lemma perm_to_matrix_perm_eq n f g : 
  perm_eq n f g ->
  perm_to_matrix n f ≡ perm_to_matrix n g.
Proof.
  intros Hfg.
  apply perm_mat_equiv_of_perm_eq.
  now rewrite Hfg.
Qed.

#[export] Hint Resolve perm_to_matrix_perm_eq : perm_inv_db.

Lemma perm_to_matrix_eq_of_perm_eq n f g : 
  perm_eq n f g ->
  perm_to_matrix n f = perm_to_matrix n g.
Proof.
  intros Hfg.
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_to_matrix_perm_eq.
Qed.

#[export] Hint Resolve perm_to_matrix_eq_of_perm_eq : perm_inv_db.

Lemma perm_to_matrix_transpose {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ ≡ perm_to_matrix n (perm_inv n f).
Proof.
  unfold perm_to_matrix.
  rewrite perm_mat_transpose by auto with perm_db.
  cleanup_perm_inv.
Qed.

Lemma perm_to_matrix_transpose_eq {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ = perm_to_matrix n (perm_inv n f).
Proof. 
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_to_matrix_transpose.
Qed.

Lemma perm_to_matrix_transpose' {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ ≡ perm_to_matrix n (perm_inv' n f).
Proof.
  rewrite perm_to_matrix_transpose by easy.
  cleanup_perm.
Qed.

Lemma perm_to_matrix_transpose_eq' {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ = perm_to_matrix n (perm_inv' n f).
Proof.
  apply mat_equiv_eq; auto with wf_db.
  now apply perm_to_matrix_transpose'.
Qed.

Lemma perm_to_matrix_transpose_linv {n f} (Hf : permutation n f) :
  (perm_to_matrix n f) ⊤ × perm_to_matrix n f = I (2 ^ n).
Proof.
  apply perm_mat_transpose_linv; auto with perm_db.
Qed.

Lemma perm_to_matrix_transpose_rinv {n f} (Hf : permutation n f) :
  perm_to_matrix n f × (perm_to_matrix n f) ⊤ = I (2 ^ n).
Proof.
  apply perm_mat_transpose_rinv; auto with perm_db.
Qed.

Lemma Mmult_perm_to_matrix_l n m (A B : Matrix (2 ^ n) m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation n f) : 
  perm_to_matrix n f × A = B <-> A = perm_to_matrix n (perm_inv n f) × B.
Proof.
  rewrite <- perm_to_matrix_transpose_eq by auto.
  unfold perm_to_matrix.
  split; [intros <- | intros ->]; 
  now rewrite <- Mmult_assoc, 1?perm_mat_transpose_rinv, 
    1?perm_mat_transpose_linv, Mmult_1_l by auto with perm_db.
Qed.

Lemma Mmult_perm_to_matrix_l' n m (A B : Matrix (2 ^ n) m) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation n f) : 
  B = perm_to_matrix n f × A <-> perm_to_matrix n (perm_inv n f) × B = A.
Proof.
  split; intros H; symmetry; apply Mmult_perm_to_matrix_l;
  auto.
Qed.

Lemma Mmult_perm_to_matrix_r n m (A B : Matrix n (2 ^ m)) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation m f) : 
  A × perm_to_matrix m f = B <-> A = B × perm_to_matrix m (perm_inv m f).
Proof.
  rewrite <- perm_to_matrix_transpose_eq by auto.
  unfold perm_to_matrix.
  split; [intros <- | intros ->]; 
  now rewrite Mmult_assoc, 1?perm_mat_transpose_rinv, 
    1?perm_mat_transpose_linv, Mmult_1_r by auto with perm_db.
Qed.

Lemma Mmult_perm_to_matrix_r' n m (A B : Matrix n (2 ^ m)) 
  (HA : WF_Matrix A) (HB : WF_Matrix B) f (Hf : permutation m f) : 
  B = A × perm_to_matrix m f <-> B × perm_to_matrix m (perm_inv m f) = A.
Proof.
  split; intros H; symmetry; apply Mmult_perm_to_matrix_r;
  auto.
Qed.

Lemma perm_to_matrix_permutes_qubits_l n p f 
  (Hp : permutation n p) : 
  (f_to_vec n f) ⊤ × perm_to_matrix n p =
  (f_to_vec n (fun x => f (perm_inv n p x))) ⊤.
Proof.
  rewrite <- (transpose_involutive _ _ (perm_to_matrix _ _)).
  rewrite <- Mmult_transpose.
  rewrite perm_to_matrix_transpose_eq by easy.
  f_equal.
  apply perm_to_matrix_permutes_qubits.
  auto with perm_bounded_db.
Qed.

#[export] Hint Resolve perm_to_matrix_perm_eq
  perm_to_matrix_eq_of_perm_eq : perm_inv_db.

Lemma perm_to_matrix_of_stack_perms n0 n1 f g 
  (Hf : permutation n0 f) (Hg : permutation n1 g) : 
  perm_to_matrix (n0 + n1) (stack_perms n0 n1 f g) = 
  perm_to_matrix n0 f ⊗ perm_to_matrix n1 g.
Proof.
  unfold perm_to_matrix.
  rewrite <- perm_mat_of_tensor_perms by cleanup_perm.
  rewrite <- Nat.pow_add_r.
  cleanup_perm.
Qed.

#[export] Hint Rewrite perm_to_matrix_of_stack_perms : perm_cleanup_db.

Lemma perm_to_matrix_of_stack_perms' n0 n1 n01 f g 
  (Hf : permutation n0 f) (Hg : permutation n1 g) 
  (Hn01 : n0 + n1 = n01) :
  perm_to_matrix n01 (stack_perms n0 n1 f g) =
  perm_to_matrix n0 f ⊗ perm_to_matrix n1 g.
Proof.
  subst.
  now apply perm_to_matrix_of_stack_perms.
Qed.

Lemma perm_to_matrix_idn n : 
  perm_to_matrix n idn = I (2^n).
Proof.
  rewrite <- perm_mat_idn.
  apply perm_mat_eq_of_perm_eq.
  cleanup_perm_inv.
Qed.

Lemma perm_to_matrix_compose n f g : 
  perm_bounded n f -> perm_bounded n g -> 
  perm_to_matrix n (f ∘ g) =
  perm_to_matrix n g × perm_to_matrix n f.
Proof.
  intros Hf Hg.
  symmetry.
  unfold perm_to_matrix.
  rewrite <- qubit_perm_to_nat_perm_compose by easy.
  apply perm_mat_Mmult.
  auto with perm_bounded_db.
Qed.

#[export] Hint Rewrite perm_to_matrix_compose : perm_cleanup_db.

Lemma perm_to_matrix_inj_mat_equiv n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) :
  perm_to_matrix n f ≡ perm_to_matrix n g ->
  perm_eq n f g.
Proof.
  intros Hequiv.
  apply qubit_perm_to_nat_perm_inj; [easy|].
  apply perm_mat_inj_mat_equiv; [auto with perm_bounded_db..|].
  exact Hequiv.
Qed.

Lemma perm_to_matrix_inj n f g 
  (Hf : perm_bounded n f) (Hg : perm_bounded n g) :
  perm_to_matrix n f = perm_to_matrix n g ->
  perm_eq n f g.
Proof.
  rewrite <- mat_equiv_eq_iff by auto with wf_db.
  now apply perm_to_matrix_inj_mat_equiv.
Qed.


Lemma perm_to_matrix_perm_eq_of_proportional n f g : 
	(exists c, perm_to_matrix n f = 
    c .* perm_to_matrix n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_eq n f g.
Proof.
  intros H Hf.
  pose proof (perm_mat_perm_eq_of_proportional _ _ _ H).
  apply qubit_perm_to_nat_perm_inj; auto with perm_bounded_db.
Qed.

Lemma perm_to_matrix_eq_of_proportional n f g : 
	(exists c, perm_to_matrix n f = 
    c .* perm_to_matrix n g /\ c <> 0%R) ->
  perm_bounded n f ->
	perm_to_matrix n f = perm_to_matrix n g.
Proof.
	intros H Hf.
  apply perm_to_matrix_eq_of_perm_eq.
  now apply perm_to_matrix_perm_eq_of_proportional.
Qed.

Lemma kron_comm_pows2_eq_perm_to_matrix_big_swap n o :
  kron_comm (2^o) (2^n) = perm_to_matrix (n + o) (big_swap_perm o n).
Proof.
  symmetry.
  apply equal_on_basis_states_implies_equal; 
  [|rewrite WF_Matrix_dim_change_iff by show_pow2_le |];
  [auto with wf_db..|].
  intros f.
  rewrite perm_to_matrix_permutes_qubits by auto with perm_db.
  rewrite (f_to_vec_split'_eq _ _ f).
  restore_dims.
  rewrite kron_comm_commutes_vectors_l by auto with wf_db.
  rewrite Nat.add_comm, f_to_vec_split'_eq.
  f_equal; apply f_to_vec_eq; intros i Hi; f_equal;
  unfold big_swap_perm; bdestructΩ'.
Qed.

Lemma kron_comm_pows2_eq_perm_to_matrix_rotr n o :
  kron_comm (2^o) (2^n) = perm_to_matrix (n + o) (rotr (n + o) n).
Proof.
  rewrite kron_comm_pows2_eq_perm_to_matrix_big_swap.
  now rewrite big_swap_perm_eq_rotr, Nat.add_comm.
Qed.

Lemma kron_comm_eq_perm_mat_of_kron_comm_perm p q :
  kron_comm p q = perm_mat (p * q) (kron_comm_perm p q).
Proof.
  apply mat_equiv_eq; auto using WF_Matrix_dim_change with wf_db zarith.
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite (Nat.div_mod_eq k p) at 1. 
  rewrite (Nat.mul_comm p (k/p)), (Nat.mul_comm q p).
  rewrite <- (kron_e_i_e_i p q) at 1 by show_moddy_lt.
  restore_dims.
  rewrite kron_comm_commutes_vectors_l by auto with wf_db.
  rewrite perm_mat_e_i by show_moddy_lt.
  rewrite (kron_e_i_e_i q p) by show_moddy_lt.
  rewrite Nat.mul_comm.
  unfold kron_comm_perm.
  bdestructΩ'.
Qed.

Lemma perm_to_matrix_rotr_eq_kron_comm : forall n o,
  perm_to_matrix (n + o) (rotr (n + o) n) = kron_comm (2^o) (2^n).
Proof.
  intros n o.
  now rewrite <- kron_comm_pows2_eq_perm_to_matrix_rotr.
Qed.

#[export] Hint Rewrite perm_to_matrix_rotr_eq_kron_comm : perm_inv_db.

Lemma perm_to_matrix_rotr_eq_kron_comm_alt : forall n o,
  perm_to_matrix (n + o) (rotr (n + o) o) = kron_comm (2^n) (2^o).
Proof.
  intros n o.
  rewrite Nat.add_comm.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite perm_to_matrix_rotr_eq_kron_comm_alt : perm_inv_db.

Lemma perm_to_matrix_rotr_eq_kron_comm_mat_equiv : forall n o,
  perm_to_matrix (n + o) (rotr (n + o) n) ≡ kron_comm (2^o) (2^n).
Proof.
  intros n o.
  now rewrite perm_to_matrix_rotr_eq_kron_comm.
Qed.

#[export] Hint Resolve 
  perm_to_matrix_rotr_eq_kron_comm_mat_equiv : perm_inv_db.

Lemma perm_to_matrix_rotl_eq_kron_comm : forall n o,
  perm_to_matrix (n + o) (rotl (n + o) n) = kron_comm (2^n) (2^o).
Proof.
  intros n o.
  rewrite <- (perm_to_matrix_eq_of_perm_eq _ _ _ (rotr_inv (n + o) n)).
  rewrite <- perm_to_matrix_transpose_eq by auto with perm_db.
  rewrite perm_to_matrix_rotr_eq_kron_comm. 
  apply kron_comm_transpose.
Qed.

#[export] Hint Rewrite perm_to_matrix_rotl_eq_kron_comm : perm_inv_db.

Lemma perm_to_matrix_rotl_eq_kron_comm_mat_equiv : forall n o,
  perm_to_matrix (n + o) (rotl (n + o) n) ≡ kron_comm (2^n) (2^o).
Proof.
  intros.
  now rewrite perm_to_matrix_rotl_eq_kron_comm.
Qed.

#[export] Hint Resolve 
  perm_to_matrix_rotl_eq_kron_comm_mat_equiv : perm_inv_db.

Lemma perm_to_matrix_rotr_commutes_kron_mat_equiv {n m p q} 
  (A : Matrix (2^n) (2^m)) (B : Matrix (2^p) (2^q)) : 
  @Mmult (2^n*2^p) (2^m*2^q) (2^q*2^m)
  (A ⊗ B) (perm_to_matrix (q + m) (rotr (q + m) q)) ≡
  @Mmult (2^n*2^p) (2^p*2^n) (2^q*2^m)
  (perm_to_matrix (p + n) (rotr (p + n) p)) (B ⊗ A).
Proof.
  unify_pows_two.
  rewrite 2!perm_to_matrix_rotr_eq_kron_comm.
  restore_dims.
  pose proof (kron_comm_commutes_r_mat_equiv (2^n) (2^m)
    (2^p) (2^q) A B) as H.
  apply H.
Qed.

Lemma perm_to_matrix_rotr_commutes_kron {n m p q} 
  (A : Matrix (2^n) (2^m)) (B : Matrix (2^p) (2^q)) : 
  WF_Matrix A -> WF_Matrix B ->
  @Mmult (2^n*2^p) (2^m*2^q) (2^q*2^m)
  (A ⊗ B) (perm_to_matrix (q + m) (rotr (q + m) q)) =
  @Mmult (2^n*2^p) (2^p*2^n) (2^q*2^m)
  (perm_to_matrix (p + n) (rotr (p + n) p)) (B ⊗ A).
Proof.
  unify_pows_two.
  rewrite 2!perm_to_matrix_rotr_eq_kron_comm.
  restore_dims.
  pose proof (kron_comm_commutes_r (2^n) (2^m)
    (2^p) (2^q) A B) as H.
  rewrite !Nat.pow_add_r.
  apply H.
Qed.


Lemma perm_to_matrix_swap_block_perm_natural {padl padm padr a}
  (A : Matrix (2^a) (2^a)) :
  @mat_equiv (2^padl*2^a*2^padm*2^a*2^padr) (2^padl*2^a*2^padm*2^a*2^padr)
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _ 
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a))
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊗ I (2^padr))).
Proof.
  apply mat_equiv_of_all_basis_conj.
  intros i j Hi Hj.
  rewrite !Mmult_assoc. 
  rewrite <- !Nat.pow_add_r in *.
  rewrite !basis_f_to_vec_alt by easy.
  rewrite perm_to_matrix_permutes_qubits by cleanup_perm.
  rewrite <- (transpose_involutive _ _ 
    (perm_to_matrix _ (swap_block_perm _ _ _))).
  rewrite <- !Mmult_assoc, <- Mmult_transpose.
  rewrite (perm_to_matrix_transpose_eq
    (swap_block_perm_permutation padl padm padr a)).
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ _
    (swap_block_perm_inv padl padm padr a)).
  rewrite perm_to_matrix_permutes_qubits by cleanup_perm. 
  replace (padl+a+padm+a+padr) with (padl+a+(padm+a+padr)) in * by lia.
  rewrite 2!(f_to_vec_split'_eq (padl+a)), 2!(f_to_vec_split'_eq (padl)).
  rewrite !(fun x y => kron_transpose' _ _ x y).
  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite ?Nat.pow_add_r; simpl;lia).
  rewrite !Mmult_1_r by auto with wf_db.
  symmetry.
  
  replace (padl+a+(padm+a+padr)) with ((padl+a+padm)+a+padr) in * by lia.
  rewrite 2!(f_to_vec_split'_eq (padl+a+padm+a)), 2!(f_to_vec_split'_eq (_+_+_)).
  rewrite !(fun x y => kron_transpose' _ _ x y).
  rewrite !(fun x y z => kron_mixed_product' _ _ _ _ _ _ _ x y z) by
    (now rewrite ?Nat.pow_add_r; simpl;lia).
  rewrite !Mmult_1_r by auto with wf_db.
  unfold kron.
  rewrite !Nat.mod_1_r, Nat.Div0.div_0_l.
  rewrite !basis_f_to_vec.
  rewrite !basis_trans_basis.
  rewrite !matrix_conj_basis_eq_lt 
    by show_moddy_lt.
  rewrite !Cmult_if_1_l, !Cmult_if_if_1_r.
  apply f_equal_if.
  - do 4 simplify_bools_moddy_lia_one_kernel.
    apply eq_iff_eq_true.
    rewrite !andb_true_iff, !Nat.eqb_eq.
    rewrite <- !funbool_to_nat_eq_iff.
    split;intros [Hlow Hhigh];
    split.
    + intros k Hk.
      generalize (Hlow k ltac:(lia)).
      unfold swap_block_perm.
      now simplify_bools_lia.
    + intros k Hk.
      unfold swap_block_perm.
      simplify_bools_lia.
      bdestructΩ'.
      * generalize (Hlow (padl+a+k) ltac:(lia)).
        unfold swap_block_perm.
        now simplify_bools_lia.
      * generalize (Hlow (padl + a + k - (a + padm)) ltac:(lia)).
        unfold swap_block_perm.
        simplify_bools_lia.
        intros <-.
        f_equal; lia.
      * apply_with_obligations
          (Hhigh ((padl + a + k) - (padl + a + padm + a)) ltac:(lia));
        f_equal; [lia|].
        unfold swap_block_perm; bdestructΩ'.
    + intros k Hk.
      unfold swap_block_perm.
      simplify_bools_lia.
      bdestructΩ'.
      * generalize (Hlow (k) ltac:(lia)).
        unfold swap_block_perm.
        now simplify_bools_lia.
      * apply_with_obligations 
          (Hhigh ((a + padm) + k - (padl + a)) ltac:(lia));
        f_equal; [|lia].
        unfold swap_block_perm; bdestructΩ'.
      * apply_with_obligations 
          (Hhigh (k - (padl + a)) ltac:(lia));
        f_equal; [|lia].
        unfold swap_block_perm; bdestructΩ'.
    + intros k Hk.
      apply_with_obligations (Hhigh (padm + a + k) ltac:(lia));
      f_equal;
      unfold swap_block_perm;
      bdestructΩ'.
  - f_equal;
    apply Bits.funbool_to_nat_eq;
    intros;
    unfold swap_block_perm;
    bdestructΩ'; f_equal; lia.
  - easy.
Qed.

Lemma perm_to_matrix_swap_block_perm_natural_eq {padl padm padr a}
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @eq (Matrix (2^padl*2^a*2^padm*2^a*2^padr) (2^padl*2^a*2^padm*2^a*2^padr))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _ 
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a))
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊗ I (2^padr))).
Proof.
  apply mat_equiv_eq; 
  auto using WF_Matrix_dim_change with wf_db.
  apply perm_to_matrix_swap_block_perm_natural.
Qed.

Lemma perm_to_matrix_swap_block_perm_natural_eq_alt {padl padm padr a}
  (A : Matrix (2^a) (2^a)) (HA : WF_Matrix A) :
  @eq (Matrix (2^padl*2^a*2^padm*2^a*2^padr) (2^(padl+a+padm+a+padr)))
  (@Mmult _ (2^padl*2^a*2^padm*2^a*2^padr) _
    (I (2^padl) ⊗ A ⊗ I (2^padm * 2^a * 2^padr))
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a)))
  (@Mmult (2^padl*2^a*2^padm*2^a*2^padr) (2^padl*2^a*2^padm*2^a*2^padr) _ 
    (perm_to_matrix (padl + a + padm + a + padr)
      (swap_block_perm padl padm a))
    (I (2^padl * 2^a * 2^padm) ⊗ A ⊗ I (2^padr))).
Proof.
  generalize (@perm_to_matrix_swap_block_perm_natural_eq 
    padl padm padr a A HA).
  unify_pows_two.
  easy.
Qed.

Lemma perm_to_matrix_swap_block_perm_eq padl padm padr a :
  perm_to_matrix (padl + a + padm + a + padr) 
    (swap_block_perm padl padm a) =
  I (2^padl) ⊗
    (kron_comm (2^a) (2^padm * 2^a) ×
    (kron_comm (2^padm) (2^a) ⊗ I (2^a))) ⊗ 
  I (2^padr).
Proof.
  rewrite (swap_block_perm_decomp_eq padl padr padm a).
  rewrite <- !(Nat.add_assoc padl).
  rewrite 2!perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite perm_to_matrix_compose by auto with perm_db.
  rewrite perm_to_matrix_of_stack_perms by auto with perm_db.
  rewrite 3!perm_to_matrix_idn.
  rewrite kron_assoc by auto with wf_db.
  f_equal; [show_pow2_le..|].
  f_equal; [show_pow2_le..|].
  rewrite 2!perm_to_matrix_rotr_eq_kron_comm.
  unify_pows_two.
  rewrite (Nat.add_comm a padm).
  easy.
Qed.

#[export] Hint Rewrite perm_to_matrix_swap_block_perm_eq : perm_inv_db.

Lemma perm_to_matrix_pullthrough_middle_eq_idn padl padm padr padm' f
  (Hf : permutation (padl + padm + padr) f)
  (Hfid : perm_eq_id_mid padl padm f)
  (A : Matrix (2^padm') (2^padm)) (HA : WF_Matrix A) :
  @Mmult (2^padl*2^padm'*2^padr) (2^padl*2^padm*2^padr) (2^(padl+padm+padr))
  (I (2^padl) ⊗ A ⊗ I (2^padr)) (perm_to_matrix (padl + padm + padr) f) = 
  @Mmult (2^(padl+padm'+padr)) (2^padl*2^padm'*2^padr) (2^padl*2^padm*2^padr)
    (perm_to_matrix (padl + padm' + padr) 
      (expand_perm_id_mid padl padm' padr 
      (contract_perm_id_mid padl padm padr f)))
    (I (2^padl) ⊗ A ⊗ I (2^padr)).
Proof.
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ _
    (perm_eq_sym (expand_contract_perm_perm_eq_idn_inv Hf Hfid))).
  unfold expand_perm_id_mid.
  rewrite 4!perm_to_matrix_compose by
    (eapply perm_bounded_change_dims; auto with perm_db zarith 
    || apply compose_perm_bounded;
    eapply perm_bounded_change_dims; auto with perm_db zarith).
  (* replace (padl + padm + padr) with (padl + padr + padm) by lia. *)
  rewrite !perm_to_matrix_of_stack_perms' by auto with perm_db zarith.
  rewrite !perm_to_matrix_idn.
  rewrite !perm_to_matrix_rotr_eq_kron_comm_alt, 
    !perm_to_matrix_rotr_eq_kron_comm.
  unify_pows_two.
  rewrite <- !Mmult_assoc.
  rewrite !Nat.pow_add_r.
  rewrite kron_assoc, <- 2!Nat.mul_assoc by auto with wf_db.
  rewrite kron_mixed_product.
  restore_dims.
  rewrite (kron_comm_commutes_r _ _ _ _ A (I (2^padr))) by auto with wf_db.
  rewrite (Nat.mul_comm (2^padm) (2^padr)).
  rewrite <- kron_mixed_product.
  rewrite <- kron_assoc by auto with wf_db.
  rewrite !Mmult_assoc.
  f_equal.
  restore_dims.
  rewrite !Nat.pow_add_r.
  rewrite <- (Mmult_assoc (_ ⊗ _ ⊗ A)).
  rewrite kron_mixed_product.
  rewrite Mmult_1_r by auto.
  rewrite id_kron.
  restore_dims.
  rewrite Mmult_1_l, <- (Mmult_1_r _ _ (perm_to_matrix _ _)) by auto with wf_db.
  rewrite <- (Mmult_1_l _ _ A) by auto.
  rewrite <- kron_mixed_product.
  rewrite Mmult_1_r, Mmult_1_l by auto with wf_db.
  rewrite Mmult_assoc.
  f_equal.
  rewrite kron_mixed_product, kron_comm_commutes_l by auto with wf_db.
  rewrite <- kron_mixed_product.
  restore_dims.
  rewrite <- kron_assoc by auto with wf_db.
  rewrite Nat.pow_add_r, <- id_kron.
  now restore_dims.
Qed.

Lemma perm_to_matrix_swap_perm_S a n (Ha : S a < n) : 
  perm_to_matrix n (swap_perm a (S a) n) =
  I (2 ^ a) ⊗ swap ⊗ I (2 ^ (n - S (S a))).
Proof.
  rewrite (perm_to_matrix_eq_of_perm_eq _ _ 
  (stack_perms (a + 2) (n - S (S a))
    (stack_perms a 2 idn (swap_perm 0 1 2)) idn)).
  - rewrite 2!perm_to_matrix_of_stack_perms' by auto with perm_db zarith.
    rewrite 2!perm_to_matrix_idn.
    restore_dims.
    do 2 f_equal.
    apply mat_equiv_eq; auto with wf_db.
    by_cell; reflexivity.
  - cleanup_perm.
    rewrite 2!swap_perm_defn by lia.
    intros k Hk.
    rewrite stack_perms_idn_f.
    bdestructΩ'.
Qed.


Lemma enlarge_permutation_big_kron'_natural (ns ms : nat -> nat) 
  As (n : nat) (HAs : forall k, k < n -> WF_Matrix (As k)) 
  f (Hf : permutation n f) : 
  big_kron' ns ms As n × perm_to_matrix (big_sum ms n) 
    (enlarge_permutation n f ms) = 
  perm_to_matrix (big_sum ns n) 
    (enlarge_permutation n f ns) ×
    big_kron' (ns ∘ f) (ms ∘ f) 
    (fun i => As (f i)) n.
Proof.
  symmetry.
  assert (HAs' : forall k, k < n -> WF_Matrix (As (f k))) by 
    (intros k Hk; apply HAs; auto with perm_bounded_db).
  rewrite Mmult_perm_to_matrix_l; 
    [ | | auto_wf | auto with perm_db].
  2: {
    apply WF_Matrix_dim_change;
    [now rewrite <- Nsum_reorder by auto with perm_db..|].
    auto_wf.
  }
  apply equal_on_conj_basis_states_implies_equal.
  - apply WF_Matrix_dim_change;
    [now rewrite <- Nsum_reorder by auto with perm_db..|].
    auto_wf.
  - auto_wf.
  - intros g h.
    symmetry.
    rewrite !Mmult_assoc.
    rewrite perm_to_matrix_permutes_qubits by auto with perm_db.
    rewrite <- !Mmult_assoc.
    rewrite perm_to_matrix_permutes_qubits_l by auto with perm_db.
    rewrite 2!f_to_vec_big_split.
    rewrite (Nsum_reorder n ns f Hf). 
    rewrite (Nsum_reorder n ms f Hf). 
    rewrite 2!f_to_vec_big_split.
    rewrite 2!(big_kron'_transpose' _ (fun _ => 0) _ n _ 1).
    restore_dims_using shelve.
    rewrite big_kron'_Mmult by (intros; auto_wf).
    rewrite big_kron'_Mmult by (intros; auto_wf).
    rewrite big_kron'_Mmult by (unfold compose; intros; auto_wf).
    rewrite big_kron'_Mmult by (unfold compose; intros; auto_wf).
    rewrite (big_kron'_0_0_reorder _ n f (* (perm_inv' n f) *)
      ltac:(auto with perm_db)) by (intros; auto_wf).
    apply big_kron'_eq_bounded.
    intros k Hk.
    unfold compose at 1.
    f_equal; [f_equal|].
    + f_equal.
      apply f_to_vec_eq.
      intros i Hi.
      rewrite perm_inv_perm_inv.
      * rewrite enlarge_permutation_add_big_sum_l 
        by auto with perm_bounded_db.
        do 2 f_equal.
        rewrite perm_inv'_eq by auto_perm.
        rewrite perm_inv_is_linv_of_permutation by auto.
        easy.
      * rewrite <- Nsum_reorder by auto.
        auto_perm.
      * rewrite <- Nsum_reorder by auto.
        rewrite (big_sum_split n (f k)) by auto_perm.
        unfold compose in *.
        cbn; lia.
    + apply f_to_vec_eq.
      intros i Hi.
      unfold compose in Hi.
      rewrite enlarge_permutation_add_big_sum_l by auto_perm.
      do 2 f_equal.
      rewrite perm_inv'_eq by auto with perm_db.
      rewrite perm_inv_is_linv_of_permutation by auto.
      easy.
  Unshelve.
  1: now rewrite big_sum_0.
  all: now rewrite <- Nsum_reorder by auto.
Qed.