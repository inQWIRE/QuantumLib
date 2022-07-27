Require Import VectorStates.

(** Facts about permutations and matrices that implement them. *)

Local Open Scope nat_scope.

(** * Permutations on (0,...,n-1) *)
Definition permutation (n : nat) (f : nat -> nat) :=
  exists g, forall x, x < n -> (f x < n /\ g x < n /\ g (f x) = x /\ f (g x) = x).

Lemma permutation_is_injective : forall n f,
  permutation n f -> 
  forall x y, x < n -> y < n -> f x = f y -> x = y.
Proof.
  intros n f [g Hbij] x y Hx Hy H.
  destruct (Hbij x Hx) as [_ [_ [H0 _]]].
  destruct (Hbij y Hy) as [_ [_ [H1 _]]].
  rewrite <- H0. 
  rewrite <- H1.
  rewrite H.
  reflexivity.
Qed.

Lemma permutation_compose : forall n f g,
  permutation n f ->
  permutation n g ->
  permutation n (f ∘ g)%prg.
Proof.
  intros n f g [finv Hfbij] [ginv Hgbij].
  exists (ginv ∘ finv)%prg.
  unfold compose.
  intros x Hx.
  destruct (Hgbij x) as [? [_ [? _]]]; auto.
  destruct (Hfbij (g x)) as [? [_ [Hinv1 _]]]; auto.
  destruct (Hfbij x) as [_ [? [_ ?]]]; auto.
  destruct (Hgbij (finv x)) as [_ [? [_ Hinv2]]]; auto.
  repeat split; auto.
  rewrite Hinv1. 
  assumption.
  rewrite Hinv2. 
  assumption.
Qed.

Lemma fswap_at_boundary_permutation : forall n f x,
  permutation (S n) f ->
  (x < S n)%nat -> f x = n ->
  permutation n (fswap f x n).
Proof.
  intros n f x Hf Hx Hfx.
  assert (Hneq: forall x0, x0 < S n -> x0 <> x -> f x0 <> n).
  { intros x0 Hx0 Hneq contra.
    rewrite <- Hfx in contra.
    eapply permutation_is_injective in contra.
    contradiction.
    apply Hf.
    assumption.
    assumption. }  

  destruct Hf as [g Hg].
  exists (compose (fswap (fun x : nat => x) x n) g).
  intros x0 Hx0.
  unfold fswap, compose.
  bdestructΩ (x0 =? n).
  repeat split.
  - bdestruct (x0 =? x).
    subst x0.
    assert (f n <> n).
    apply Hneq; lia.
    destruct (Hg n) as [? _]; lia.
    assert (f x0 <> n).
    apply Hneq; lia.
    destruct (Hg x0) as [? _]; lia.
  - assert (g x0 <> x).
    intro contra. 
    rewrite <- contra in Hfx.
    destruct (Hg x0) as [_ [_ [_ ?]]]; lia.
    bdestruct_all.
    lia.
    destruct (Hg x0) as [_ [? _]]; lia.
  - bdestruct (x0 =? x).
    subst x0.
    destruct (Hg n) as [_ [_ [H1 _]]]; try lia.
    rewrite H1.
    bdestruct_all; trivial.
    destruct (Hg x0) as [_ [_ [H1 _]]]; try lia.
    rewrite H1.
    bdestruct_all; trivial.
  - assert (g x0 <> x).
    intro contra. 
    rewrite <- contra in Hfx.
    destruct (Hg x0) as [_ [_ [_ ?]]]; lia.
    bdestructΩ (g x0 =? x).
    bdestruct (g x0 =? n).
    bdestructΩ (x =? x).
    destruct (Hg x0) as [_ [_ [_ ?]]]; try lia.
    rewrite <- H2.
    assumption.
    bdestruct_all.
    destruct (Hg x0) as [_ [_ [_ ?]]]; lia.
Qed.
  
(** vsum terms can be arbitrarily reordered *)
Lemma vsum_reorder : forall {d} n (v : nat -> Vector d) f,
  permutation n f ->
  big_sum v n = big_sum (fun i => v (f i)) n.
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f [g Hg].
  destruct (Hg n) as [_ [H1 [_ H2]]]; try lia.
  rewrite (vsum_eq_up_to_fswap _ f _ (g n) n) by auto.
  repeat rewrite <- big_sum_extend_r.
  rewrite fswap_simpl2.
  rewrite H2.
  specialize (IHn (fswap f (g n) n)).
  rewrite <- IHn.
  reflexivity.
  apply fswap_at_boundary_permutation; auto.
  exists g. auto.
Qed.

(** * Permutation matrices *)

Definition perm_mat n (p : nat -> nat) : Square n :=
  (fun x y => if (x =? p y) && (x <? n) && (y <? n) then C1 else C0).

Lemma perm_mat_WF : forall n p, WF_Matrix (perm_mat n p).
Proof.
  intros n p.
  unfold WF_Matrix, perm_mat. 
  intros x y [H | H].
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
Qed. 
#[export] Hint Resolve perm_mat_WF : wf_db.

Lemma perm_mat_unitary : forall n p, 
  permutation n p -> WF_Unitary (perm_mat n p).
Proof.
  intros n p [pinv Hp].
  split.
  apply perm_mat_WF.
  unfold Mmult, adjoint, perm_mat, I.
  prep_matrix_equality.
  destruct ((x =? y) && (x <? n)) eqn:H.
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  subst.
  apply big_sum_unique.
  exists (p y).
  destruct (Hp y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros.  
  bdestruct_all; simpl; lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite andb_true_r in H.
  apply beq_nat_false in H.
  assert (pinv (p x) = pinv (p y)) by auto.
  destruct (Hp x) as [_ [_ [H5 _]]]; auto.
  destruct (Hp y) as [_ [_ [H6 _]]]; auto.
  contradict H.
  rewrite <- H5, <- H6.
  assumption.
Qed.

Lemma perm_mat_Mmult : forall n f g,
  permutation n g ->
  perm_mat n f × perm_mat n g = perm_mat n (f ∘ g)%prg.
Proof.
  intros n f g [ginv Hgbij].
  unfold perm_mat, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? f (g y)) && (x <? n) && (y <? n)) eqn:H.
  apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  apply Nat.ltb_lt in H3.
  subst.
  apply big_sum_unique.
  exists (g y).
  destruct (Hgbij y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros.
  bdestruct_all; simpl; lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite 2 andb_true_r in H.
  apply beq_nat_false in H.
  contradiction.
Qed.

Lemma perm_mat_I : forall n f,
  (forall x, x < n -> f x = x) ->
  perm_mat n f = I n.
Proof.
  intros n f Hinv.
  unfold perm_mat, I.
  prep_matrix_equality.
  bdestruct_all; simpl; try lca.
  rewrite Hinv in H1 by assumption.
  contradiction.
  rewrite Hinv in H1 by assumption.
  contradiction.
Qed.

(** Given a permutation p over n qubits, construct a permutation over 2^n indices. *)
Definition qubit_perm_to_nat_perm n (p : nat -> nat) :=
  fun x:nat => funbool_to_nat n ((nat_to_funbool n x) ∘ p)%prg.

Lemma qubit_perm_to_nat_perm_bij : forall n p,
  permutation n p -> permutation (2^n) (qubit_perm_to_nat_perm n p).
Proof.
  intros n p [pinv Hp].
  unfold qubit_perm_to_nat_perm.
  exists (fun x => funbool_to_nat n ((nat_to_funbool n x) ∘ pinv)%prg).
  intros x Hx.
  repeat split.
  apply funbool_to_nat_bound.
  apply funbool_to_nat_bound.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [_ H]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [_ [? _]]; auto. }
  rewrite nat_to_funbool_inverse; auto.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [H _]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [? _]; auto. }
  rewrite nat_to_funbool_inverse; auto.
Qed.  

(** Transform a (0,...,n-1) permutation into a 2^n by 2^n matrix. *)
Definition perm_to_matrix n p :=
  perm_mat (2 ^ n) (qubit_perm_to_nat_perm n p).
 
Lemma perm_to_matrix_permutes_qubits : forall n p f, 
  permutation n p ->
  perm_to_matrix n p × f_to_vec n f = f_to_vec n (fun x => f (p x)).
Proof.
  intros n p f [pinv Hp].
  rewrite 2 basis_f_to_vec.
  unfold perm_to_matrix, perm_mat, qubit_perm_to_nat_perm.
  unfold basis_vector, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? funbool_to_nat n (fun x0 : nat => f (p x0))) && (y =? 0)) eqn:H.
  apply andb_prop in H as [H1 H2].
  rewrite Nat.eqb_eq in H1.
  rewrite Nat.eqb_eq in H2.
  apply big_sum_unique.
  exists (funbool_to_nat n f).
  split.
  apply funbool_to_nat_bound.
  split.
  erewrite funbool_to_nat_eq.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  specialize (funbool_to_nat_bound n f) as ?.
  specialize (funbool_to_nat_bound n (fun x0 : nat => f (p x0))) as ?.
  bdestruct_all; lca.
  intros z Hz H3.
  bdestructΩ (z =? funbool_to_nat n f).
  lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  rewrite andb_true_r in H.
  apply beq_nat_false in H.
  subst z.
  erewrite funbool_to_nat_eq in H2.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  contradiction.
Qed.

Lemma perm_to_matrix_unitary : forall n p, 
  permutation n p ->
  WF_Unitary (perm_to_matrix n p).
Proof.
  intros.
  apply perm_mat_unitary.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma qubit_perm_to_nat_perm_compose : forall n f g,
  permutation n f ->
  (qubit_perm_to_nat_perm n f ∘ qubit_perm_to_nat_perm n g = 
    qubit_perm_to_nat_perm n (g ∘ f))%prg.
Proof.
  intros n f g [finv Hbij].
  unfold qubit_perm_to_nat_perm, compose.
  apply functional_extensionality.
  intro x.
  apply funbool_to_nat_eq.
  intros y Hy.
  rewrite funbool_to_nat_inverse.
  reflexivity.
  destruct (Hbij y) as [? _]; auto.
Qed.

Lemma perm_to_matrix_Mmult : forall n f g,
  permutation n f ->
  permutation n g ->
  perm_to_matrix n f × perm_to_matrix n g = perm_to_matrix n (g ∘ f)%prg.
Proof.
  intros. 
  unfold perm_to_matrix.
  rewrite perm_mat_Mmult.
  rewrite qubit_perm_to_nat_perm_compose by assumption.
  reflexivity.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma perm_to_matrix_I : forall n f,
  permutation n f ->
  (forall x, x < n -> f x = x) ->
  perm_to_matrix n f = I (2 ^ n).
Proof.
  intros n f g Hbij. 
  unfold perm_to_matrix.
  apply perm_mat_I.
  intros x Hx.
  unfold qubit_perm_to_nat_perm, compose. 
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. rewrite Hbij by assumption. reflexivity. }
  apply nat_to_funbool_inverse.
  assumption.
Qed.

Lemma perm_to_matrix_WF : forall n p, WF_Matrix (perm_to_matrix n p).
Proof. intros. apply perm_mat_WF. Qed. 
#[export] Hint Resolve perm_to_matrix_WF : wf_db.
