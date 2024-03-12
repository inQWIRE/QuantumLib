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

Lemma id_permutation : forall n,
  permutation n Datatypes.id.
Proof. intros.
       exists Datatypes.id.
       intros.
       unfold Datatypes.id.
       easy.
Qed.

Lemma fswap_permutation : forall n f x y,
  permutation n f ->
  (x < n)%nat -> 
  (y < n)%nat -> 
  permutation n (fswap f x y).
Proof. intros. 
       replace (fswap f x y) with (f ∘ (fswap (fun i => i) x y))%prg.
       apply permutation_compose; auto.
       exists (fswap (fun i => i) x y).
       intros. unfold fswap.
       bdestruct_all; subst; auto.
       apply functional_extensionality; intros.
       unfold compose, fswap.
       bdestruct_all; easy.
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


(** * showing every permutation is a sequence of fswaps *)


(* note the list acts on the left, for example, [s1,s2,...,sk] ⋅ f = s1 ⋅ ( ... ⋅ (sk ⋅ f)) *)
Fixpoint stack_fswaps (f : nat -> nat) (l : list (nat * nat)) :=
  match l with 
  | [] => f
  | p :: ps => (fswap (Datatypes.id) (fst p) (snd p) ∘ (stack_fswaps f ps))%prg 
  end.

Definition WF_fswap_stack n (l : list (nat * nat)) :=
  forall p, In p l -> (fst p < n /\ snd p < n). 

Lemma WF_fswap_stack_pop : forall n a l, 
  WF_fswap_stack n (a :: l) -> WF_fswap_stack n l.
Proof. intros.
       unfold WF_fswap_stack in *.
       intros.
       apply H.
       right; easy.
Qed.

Lemma WF_fswap_stack_cons : forall n a l, 
  fst a < n -> snd a < n -> WF_fswap_stack n l -> WF_fswap_stack n (a :: l).
Proof. intros.
       unfold WF_fswap_stack in *.
       intros.
       destruct H2; subst; auto.
Qed.

Lemma WF_fswap_miss : forall n l i,
  WF_fswap_stack n l ->
  n <= i -> 
  (stack_fswaps Datatypes.id l) i = i.
Proof. induction l. 
       intros; simpl; easy.
       intros; simpl.
       unfold compose.
       rewrite IHl; auto.
       unfold fswap, Datatypes.id; simpl.
       destruct (H a).
       left; auto.
       bdestruct_all; try lia.
       apply WF_fswap_stack_pop in H; auto.
Qed.

Lemma stack_fswaps_permutation : forall {n} (f : nat -> nat) (l : list (nat * nat)),
  WF_fswap_stack n l -> 
  permutation n f -> 
  permutation n (stack_fswaps f l).
Proof. induction l.
       - intros. easy.
       - intros. 
         simpl.
         apply permutation_compose.
         apply fswap_permutation.
         apply id_permutation.
         3 : apply IHl; auto.
         3 : apply WF_fswap_stack_pop in H; auto.
         all : apply H; left; easy.
Qed.

Lemma stack_fswaps_cons : forall (p : nat * nat) (l : list (nat * nat)),
  ((stack_fswaps Datatypes.id [p]) ∘ (stack_fswaps Datatypes.id l))%prg = 
  stack_fswaps Datatypes.id (p :: l).
Proof. intros. 
       simpl.
       rewrite compose_id_right.
       easy.
Qed.
 
(*
Theorem all_perms_are_fswap_stacks : forall {n} f,
  permutation n f -> 
  exists l, WF_fswap_stack n l /\ f = (stack_fswaps Datatypes.id l) /\ length l = n.
Proof. induction n. 
       - intros. 
         exists []; simpl.
*)     

Definition ordered_real_function n (f : nat -> R) :=
  forall i j, i < n -> j < n -> i <= j -> (f j <= f i)%R.

Lemma get_real_function_min : forall {n} (f : nat -> R),
  exists n0, (n0 < (S n))%nat /\ (forall i, (i < (S n))%nat -> (f n0 <= f i)%R).
Proof. induction n.
       - intros.
         exists O; intros.
         split; auto.
         intros. 
         destruct i; try lia.
         easy.
       - intros.  
         destruct (IHn f) as [n0 [H H0] ]. 
         destruct (Rlt_le_dec (f n0) (f (S n))). 
         + exists n0; intros. 
           split; try lia. 
           intros.
           bdestruct (i =? (S n))%nat; subst.
           lra.
           apply H0.
           bdestruct (n0 <? S n)%nat; bdestruct (i <? S n)%nat; try lia.
         + exists (S n).
           split.
           lia.
           intros.
           specialize (H0 i).
           unfold get_minor in H0.
           bdestruct (n0 <? S n)%nat; bdestruct (i <? S n)%nat; try lia.
           apply H0 in H3.
           lra.
           bdestruct (i =? S n)%nat; try lia; subst.
           easy.
Qed.

Lemma order_real_function : forall n (f : nat -> R), 
  exists l, WF_fswap_stack n l /\ 
         ordered_real_function n (f ∘ (stack_fswaps Datatypes.id l))%prg.
Proof. intros.
       generalize dependent f.
       induction n.
       - intros; exists [].
         split; auto.
         unfold WF_fswap_stack; intros.
         destruct H.
         simpl.
         unfold ordered_real_function; intros; lia.
       - intros. 
         destruct (@get_real_function_min n f) as [n0 [H H0]].
         destruct (IHn (f ∘ (stack_fswaps Datatypes.id [(n0, n)]))%prg) as [l [H1 H2]].
         exists ((n0, n) :: l).
         split. 
         apply WF_fswap_stack_cons; simpl; auto. 
         unfold WF_fswap_stack in *; intros. 
         apply H1 in H3.
         lia.
         rewrite compose_assoc, stack_fswaps_cons in H2.
         unfold ordered_real_function in *.
         intros.  
         bdestruct (j =? n); subst.
         simpl.
         rewrite <- compose_assoc.
         assert (H' : permutation (S n) 
                                  (fswap Datatypes.id n0 n ∘ stack_fswaps Datatypes.id l)%prg).
         { apply permutation_compose.
           apply fswap_permutation; auto.
           apply id_permutation.
           apply stack_fswaps_permutation.
           unfold WF_fswap_stack in *; intros. 
           apply H1 in H6.
           lia.
           apply id_permutation. }
         unfold compose in *.
         destruct H' as [g H6].  
         destruct (H6 i); auto.
         rewrite (WF_fswap_miss n); auto.
         replace (fswap Datatypes.id n0 n n) with n0.
         apply H0; easy. 
         unfold fswap, Datatypes.id.
         bdestruct_all; simpl; easy.
         bdestruct (j <? n); bdestruct (i <? n); try lia.
         apply H2; auto. 
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

Lemma perm_mat_id : forall n,
  perm_mat n (Datatypes.id) = (I n).
Proof. intros. 
       unfold Datatypes.id, I, perm_mat.
       prep_matrix_equality.
       bdestruct_all; easy.
Qed.

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
  apply Nat.eqb_neq in H.
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
  apply Nat.eqb_neq in H.
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

Lemma perm_mat_col_swap_I : forall n f i j,
  (forall x, x < n -> f x = x) ->
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = col_swap (I n) i j.
Proof. intros. 
       unfold perm_mat, fswap, col_swap, I.
       prep_matrix_equality.
       rewrite 2 H; auto.
       bdestruct_all; simpl; try lia; auto.
       rewrite H in H4; auto; lia.
       rewrite H in H4; auto; lia.
Qed.

Lemma perm_mat_col_swap : forall n f i j,
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = col_swap (perm_mat n f) i j.
Proof. intros. 
       unfold perm_mat, fswap, col_swap, I.
       prep_matrix_equality.
       bdestruct_all; simpl; try lia; auto.
Qed. 

Lemma perm_mat_row_swap : forall n f i j,
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = (row_swap (perm_mat n f)† i j)†.
Proof. intros. 
       unfold perm_mat, fswap, row_swap, I, adjoint.
       prep_matrix_equality.
       bdestruct_all; simpl; try lia; auto; lca.
Qed. 

Lemma perm_mat_e_i : forall n f i, 
  i < n ->
  permutation n f ->
  (perm_mat n f) × e_i i = e_i (f i).
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros.
       destruct j; try lia.
       unfold Mmult.
       apply big_sum_unique.
       exists i.
       split; auto.
       split. 
       unfold e_i, perm_mat. 
       bdestruct_all; simpl; lca.
       intros. 
       unfold e_i.
       bdestruct_all; simpl; lca.
Qed.

(* with get_entry_with_e_i this became soo much easier *)
Lemma perm_mat_conjugate : forall {n} (A : Square n) f (i j : nat), 
  WF_Matrix A -> 
  i < n -> j < n ->
  permutation n f ->
  ((perm_mat n f)† × A × ((perm_mat n f))) i j = A (f i) (f j). 
Proof. intros. 
       rewrite get_entry_with_e_i, (get_entry_with_e_i A); auto.
       rewrite <- 2 Mmult_assoc, <- Mmult_adjoint.
       rewrite perm_mat_e_i; auto.
       rewrite 3 Mmult_assoc.
       rewrite perm_mat_e_i; auto.
       all : destruct H2; apply H2; auto.
Qed.       

Lemma perm_mat_conjugate_nonsquare : forall {m n} (A : Matrix m n) f (i j : nat), 
  WF_Matrix A -> 
  i < m -> j < n ->
  permutation m f -> permutation n f ->
  ((perm_mat m f)† × A × ((perm_mat n f))) i j = A (f i) (f j). 
Proof. intros. 
       rewrite get_entry_with_e_i, (get_entry_with_e_i A); auto.
       rewrite <- 2 Mmult_assoc, <- Mmult_adjoint.
       rewrite perm_mat_e_i; auto.
       rewrite 3 Mmult_assoc.
       rewrite perm_mat_e_i; auto.
       all : destruct H2; destruct H3; try apply H2; try apply H3; auto.
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
  apply Nat.eqb_neq in H.
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
