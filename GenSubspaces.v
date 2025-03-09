Require Import Permutation.
Require Export Summation.
Require Export GenVecSet.

(* Problems of current Subspaces.v:
1. Use of deprecated definitions and lemmas such as col_append, row_append
2. Names use obsolete terms such as col_vec
*)

Declare Scope subspaces_scope.
Delimit Scope subspaces_scope with SS.
Open Scope subspaces_scope.


Module SubspacesOverField
  (FM : FieldModule).

  Include VecSetOverField FM.


#[export] Program Instance F_is_module_space : Module_Space F F :=
  { Vscale := Gmult }.
Next Obligation. field. Qed.
Next Obligation. field. Qed.
Next Obligation. field. Qed.


Lemma cons_conc : forall (X : Type) (x : X) (ls : list X),
    x :: ls = [x] ++ ls.
Proof. reflexivity. Qed.

Lemma nth_helper : forall {X : Type} (n : nat) (ls : list X) (x : X),
    (n < length ls)%nat -> skipn n ls = [nth n ls x] ++ skipn (S n) ls.
Proof. induction n as [| n']. 
       - destruct ls. easy. easy. 
       - intros. destruct ls. 
         assert (H' : forall (n : nat), (S n < 0)%nat -> False). { nia. }
         apply H' in H. easy.
         rewrite skipn_cons.
         assert (H'' : nth (S n') (x0 :: ls) x = nth n' ls x). { easy. }
         rewrite H''.
         rewrite (IHn' ls x). 
         easy. 
         simpl in H. 
         assert (H''' : forall (n m : nat), (S m < S n)%nat -> (m < n)%nat). { nia. } 
         apply H''' in H.
         easy.
Qed.

Lemma Fopp_opp : forall (a b : F), -a = b <-> a = -b. Proof. split; intros; [rewrite <- H | rewrite H]; ring. Qed. 

Lemma Fplus_opp_l : forall c : F, - c + c = 0. Proof. intros; ring. Qed.

Lemma Fplus_opp_r : forall c : F, c + - c = 0. Proof. intros; ring. Qed.

Lemma Fplus_inj_r : forall (c c1 c2 : F),
    c1 = c2 -> c1 + c = c2 + c.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Fplus_inj_l : forall (c c1 c2 : F),
    c1 = c2 -> c + c1 = c + c2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Fplus_inv_r : forall (c c1 c2 : F),
    c1 + c = c2 + c -> c1 = c2.
Proof. intros. apply Fplus_inj_r with (c:=-c) in H.
  rewrite <- ! Gplus_assoc in H.
  rewrite ! Fplus_opp_r in H.
  rewrite ! Gplus_0_r in H.
  assumption.
Qed.

Lemma Fplus_inv_l : forall (c c1 c2 : F),
    c + c1= c + c2 -> c1 = c2.
Proof. intros. apply Fplus_inj_l with (c:=-c) in H.
  rewrite ! Gplus_assoc in H.
  rewrite ! Fplus_opp_l in H.
  rewrite ! Gplus_0_l in H.
  assumption.
Qed.

Lemma Fplus_zero_iff_equals_minus : forall (c1 c2 : F),
    c1 + c2 = 0 <-> c1 = -c2.
Proof. split.
  - intro. apply Fplus_inj_r with (c := -c2) in H.
    rewrite <- ! Gplus_assoc in H.
    rewrite Fplus_opp_r in H.
    rewrite Gplus_0_l, Gplus_0_r in H.
    assumption.
  - intro. rewrite H. rewrite Fplus_opp_l. reflexivity.
Qed.

Lemma F_inj_l : forall (c x y : F), x = y -> (c * x = c * y)%G.
Proof. intros. rewrite H. easy. Qed.

Lemma F_inv_l : forall (c x y : F), c <> 0%G -> (c * x = c * y)%G -> x = y.
Proof. intros. apply F_inj_l with (c:=/c) in H0. rewrite ! Gmult_assoc in H0.
  rewrite Finv_l in H0. 2: apply F_field_theory. 
  all : try rewrite ! Gmult_1_l  in H0; assumption.
Qed.

Lemma F_inj_r : forall (c x y : F), x = y -> (x * c = y * c)%G.
Proof. intros. rewrite H. easy. Qed.

Lemma F_inv_r : forall (c x y : F), c <> 0%G -> (x * c = y * c)%G -> x = y.
Proof. intros. apply F_inj_r with (c:=/c) in H0. rewrite <- ! Gmult_assoc in H0.
  replace (c * / c)%G with (/ c * c)%G in H0 by (rewrite Gmult_comm; auto).
  rewrite Finv_l in H0. 2: apply F_field_theory.
  all: try rewrite ! Gmult_1_r in H0; assumption.
Qed.

Lemma Gneg1_neq_0 : (- 1%G) <> 0%G.
Proof. intro H.
  assert (forall a b : F, a = b -> - a = - b)%G. { intros. rewrite H0. auto. }
  apply H0 in H. rewrite Gopp_involutive in H.
  replace (- 0)%G with 0%G in H by ring.
  contradict H.
  apply G1_neq_0.
Qed.

Lemma Fopp_mult_distr_r : forall c1 c2 : F, - (c1 * c2) = c1 * - c2.
Proof. intros; ring. Qed.
Lemma Fopp_mult_distr_l : forall c1 c2 : F, - (c1 * c2) = - c1 * c2.
Proof. intros; ring. Qed.

Lemma Fplus_simplify : forall (a b c d : F),
    a = b -> c = d -> (a + c = b + d)%G.
Proof. intros. rewrite H, H0; easy. Qed.

Lemma Fmult_simplify : forall (a b c d : F),
    a = b -> c = d -> (a * c = b * d)%G.
Proof. intros. rewrite H, H0; easy. Qed.


Lemma Mmult_eq_l : forall {m n o : nat} (A A' : GenMatrix m n) (B : GenMatrix n o), A = A' -> A × B = A' × B.
Proof. intros. rewrite H. easy. Qed.

Lemma Mmult_eq_r : forall {m n o : nat} (A : GenMatrix m n) (B B' : GenMatrix n o), B = B' -> A × B = A × B'.
Proof. intros. rewrite H. easy. Qed.

Lemma Mscale_inj : forall {m n} (A B : GenMatrix m n) (c : F), A = B -> (c .* A = c .* B)%GM.
Proof. intros m n A B c H. rewrite H. easy. Qed. 

Lemma Mscale_cancel : forall {m n} (A B : GenMatrix m n) (c : F), c <> 0%G -> (c .* A = c .* B)%GM ->  A = B.
Proof. intros m n A B c H H0. apply Mscale_inj with (c:= /c) in H0.
  rewrite ! Mscale_assoc in H0. rewrite Finv_l in H0; try easy.
  rewrite ! Mscale_1_l in H0. easy.
  apply F_field_theory. auto.
Qed.

Lemma Mmult_double_side : forall {i j k : nat} {m1 m1' : GenMatrix i j} {m2 m2' : GenMatrix j k} ,
    m1 = m1' -> m2 = m2' -> m1 × m2 = m1' × m2'.
Proof. intros. rewrite H, H0. reflexivity. Qed.

Lemma Mplus_inj_l : forall {j k : nat} (m m1 m2 : GenMatrix j k),
    m1 = m2 -> m .+ m1 = m .+ m2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Mplus_inj_r : forall {j k : nat} (m m1 m2 : GenMatrix j k),
    m1 = m2 -> m1 .+ m = m2 .+ m.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma Mplus_double_side : forall {j k : nat} {m1 m1' m2 m2' : GenMatrix j k} ,
    m1 = m1' -> m2 = m2' -> m1 .+ m2 = m1' .+ m2'.
Proof. intros. rewrite H, H0. reflexivity. Qed.

Lemma Mplus_opp_r : forall {j k : nat} (m : GenMatrix j k),
    WF_GenMatrix m -> m .+ - 1%G .* m = Zero.
Proof. intros. lgma. Qed.

Lemma Mplus_opp_l : forall {j k : nat} (m : GenMatrix j k),
    WF_GenMatrix m -> - 1%G .* m .+ m = Zero.
Proof. intros. lgma. Qed.

Lemma Mplus_inv_r : forall {j k : nat} (m m1 m2 : GenMatrix j k),
    WF_GenMatrix m -> m1 .+ m = m2 .+ m -> m1 = m2.
Proof. intros. apply Mplus_inj_r with (m := - 1%G .* m) in H0.
  rewrite ! GMplus_assoc in H0.
  rewrite ! Mplus_opp_r in H0; auto.
  rewrite ! GMplus_0_r in H0.
  assumption.
Qed. 

Lemma Mplus_inv_l : forall {j k : nat} (m m1 m2 : GenMatrix j k),
    WF_GenMatrix m -> m .+ m1 = m .+ m2 -> m1 = m2.
Proof. intros. apply Mplus_inj_l with (m := - 1%G .* m) in H0.
  rewrite <- ! GMplus_assoc in H0.
  rewrite ! Mplus_opp_l in H0; auto.
  rewrite ! GMplus_0_l in H0.
  assumption.
Qed. 

Lemma Mplus_zero_iff_equals_minus : forall {j k : nat} (m1 m2 : GenMatrix j k),
    WF_GenMatrix m2 -> (m1 .+ m2 = Zero <-> m1 = - 1%G .* m2).
Proof. intros. split.
  - intro. apply Mplus_inj_r with (m := - 1%G .* m2) in H0.
    rewrite GMplus_assoc in H0.
    rewrite Mplus_opp_r in H0; auto.
    rewrite GMplus_0_l, GMplus_0_r in H0.
    assumption.
  - intro. rewrite H0. lgma.
Qed.



Lemma big_sum_permutation : forall (A : Type) (m : nat) (d : A) (l1 l2 : list A) (f : A -> F),
    Permutation l1 l2 -> (m >= length l1)%nat ->
    Σ (fun y : nat => f (nth y l1 d)) m = Σ (fun y : nat => f (nth y l2 d)) m.
Proof. intros.
  gen m.
  induction H.
  - simpl. easy.
  - intros. simpl in *.
    destruct m; try easy.
    rewrite <- ! big_sum_extend_l.
    rewrite IHPermutation.
    easy. lia.
  - intros. 
    destruct m; try easy.
    destruct m.
    simpl in *.
    lia.
    rewrite <- ! big_sum_extend_l.
    simpl.
    ring.
  - intros.
    rewrite IHPermutation1; try easy.
    rewrite IHPermutation2; try easy.
    rewrite Permutation_length with (l' := l') in H1; auto.
Qed.  


Lemma get_col_vec : forall {n} (v : GenVector n),
  WF_GenMatrix v -> get_col v 0 = v.
Proof. intros. 
       unfold get_col.
       prep_genmatrix_equality. 
       bdestruct (y =? 0). 
       - rewrite H0; easy.
       - unfold WF_GenMatrix in H.  
         rewrite H; try easy.
         right. 
         bdestruct (y <? 1); try lia.          
Qed.


Lemma linearly_independent_dimensions : forall {n m : nat} (A : GenMatrix n m),
    WF_GenMatrix A -> linearly_independent A -> (m <= n)%nat.
Proof. intros n m A H H0. 
  bdestruct (n <? m)%nat; auto.
  contradict H0.
  apply lindep_implies_not_linindep.
  apply gt_dim_lindep; auto.
Qed.

Definition list_vector_to_matrix {n} (l : list (GenVector n)) : GenMatrix n (length l) := (fun r c : nat => (nth c l (@Zero n 1)) r 0%nat).
Check list_vector_to_matrix.

Definition matrix_column_choose {n m} (indices_list : list nat) (M : GenMatrix n m) : GenMatrix n (length indices_list) := list_vector_to_matrix (map (fun i : nat => get_col M i) indices_list).

Definition vector_row_choose {n} (indices_list : list nat) (v : GenVector n) : GenVector (length indices_list) := (fun r c : nat => v (nth r indices_list n) c).


Lemma   WF_GenMatrix_matrix_column_choose_indices_list_I_n: forall (n : nat) (indices_list : list nat),
    WF_GenMatrix (matrix_column_choose indices_list (@I n)).
Proof. intros.
  unfold WF_GenMatrix.
  intros.
  unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  assert (Zero = get_col (@I n) n).
  { unfold get_col.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; try easy.
    unfold I.
    bdestruct_all; try easy. }
  rewrite H0.
  rewrite map_nth with (d := n).
  unfold get_col.
  bdestruct_all.
  destruct H0; unfold I; bdestruct_all; simpl; try easy.
  rewrite nth_overflow in H2; lia.
Qed.

Lemma WF_GenMatrix_matrix_column_choose_indices_list : forall {n m : nat} (indices_list : list nat) (M : GenMatrix n m), WF_GenMatrix M -> WF_GenMatrix (matrix_column_choose indices_list M).
Proof. intros.
  unfold WF_GenMatrix.
  intros.
  unfold matrix_column_choose.
  unfold list_vector_to_matrix.
  assert (Zero = get_col M m).
  { unfold get_col.
    do 2 (apply functional_extensionality; intros).
    bdestruct_all; try easy.
    unfold WF_GenMatrix in H0.
    assert ((x0 >= n)%nat \/ (m >= m)%nat). { right. lia. }
    specialize (H x0 m H2).
    rewrite H.
    trivial. }
  rewrite H1.
  rewrite map_nth with (d := m).
  unfold get_col.
  bdestruct_all.
  destruct H0.
  - unfold WF_GenMatrix in H.
    assert ((x >= n)%nat \/ ((nth y indices_list m) >= m)%nat). { left. assumption. }
    specialize (H x (nth y indices_list m) H3).
    assumption.
  - rewrite nth_overflow.
    2 : lia.
    unfold WF_GenMatrix in H0.
    assert ((x >= n)%nat \/ (m >= m)%nat). { right. lia. }
    specialize (H x m H3).
    assumption.
Qed.

Lemma  WF_GenMatrix_vector_row_choose_indices_list : forall {n : nat} (indices_list : list nat) (v : GenVector n), WF_GenMatrix v -> WF_GenMatrix (vector_row_choose indices_list v).
Proof. intros.
  unfold WF_GenMatrix.
  intros.
  unfold vector_row_choose.
  destruct H0.
  - rewrite nth_overflow.
    2 : lia.
    unfold WF_GenMatrix in H0.
    assert ((n >= n)%nat \/ (y >= 1)%nat). { left. lia. }
    specialize (H n y H1).
    apply H.
  - unfold WF_GenMatrix in H0.
    assert (((nth x indices_list n) >= n)%nat \/ (y >= 1)%nat). { right. assumption. }
    specialize (H (nth x indices_list n) y H1).
    apply H.
Qed.

#[export] Hint Resolve WF_GenMatrix_matrix_column_choose_indices_list_I_n WF_GenMatrix_matrix_column_choose_indices_list WF_GenMatrix_vector_row_choose_indices_list : wf_db.



(** subspace of the form { v | P v } **)
Definition subspace {n : nat} (P : GenVector n -> Prop) : Prop :=
  (forall (v : GenVector n), P v -> WF_GenMatrix v) /\
    P Zero /\
    (forall (v w : GenVector n), P v -> P w -> P (v .+ w)) /\
    (forall (v : GenVector n) (c : F), P v -> P (c .* v)).

Lemma WF_subspace : forall {n : nat} {P : GenVector n -> Prop} {v : GenVector n},
    subspace P -> P v -> WF_GenMatrix v.
Proof. intros n P v H0 H1. destruct H0 as [WFP [PZero [Psum Pscale]]].
  auto.
Qed.

#[export] Hint Resolve WF_subspace : wf_db.


Lemma matrix_column_choose_original : forall {n m : nat} (A : GenMatrix n m),
    WF_GenMatrix A -> matrix_column_choose (List.seq 0 m) A = A.
Proof. intros n m A H0. 
  unfold matrix_column_choose, list_vector_to_matrix.
  unfold WF_GenMatrix in H0.
  prep_genmatrix_equality.
  assert (@Zero n 1 = (get_col A m)).
  { unfold get_col.
    prep_genmatrix_equality.
    bdestruct_all; trivial.
    rewrite H0; trivial.
    lia. }
  bdestruct (x <? n)%nat.
  - bdestruct (y <? m)%nat.
    + rewrite H.
      rewrite map_nth with (d := m).
      rewrite seq_nth; trivial.
    + rewrite nth_overflow.
      * rewrite H0; trivial.
        lia.
      * rewrite map_length.
        rewrite seq_length.
        assumption.
  - bdestruct (y <? m)%nat.
    + rewrite H.
      rewrite map_nth with (d := m).
      rewrite seq_nth; trivial.
    + rewrite nth_overflow.
      * rewrite H0; trivial.
        lia.
      * rewrite map_length.
        rewrite seq_length.
        assumption.
Qed.

Lemma subspace_closed_under_linear_combinations : forall {n m : nat} {P : GenVector n -> Prop} (M : GenMatrix n m) (a : GenVector m), WF_GenMatrix a -> subspace P -> (forall (i : nat), (i < m)%nat -> P (get_col M i)) -> P (M × a).
Proof. intros n m P M a H0 H1 H2. 
  induction m.
  - unfold GMmult. simpl.
    unfold subspace in H1.
    destruct H1 as [WFP [PZero [Psum Pscale]]].
    assumption.
  - assert (M × a = (matrix_column_choose (List.seq 0 m) M) × (vector_row_choose (List.seq 0 m) a) .+ (a m 0%nat) .* (get_col M m)).
      { unfold GMmult.
        unfold scale.
        unfold matrix_column_choose, list_vector_to_matrix.
        unfold vector_row_choose.
        unfold get_col.
        unfold GMplus.
        simpl.
        do 2 (apply functional_extensionality; intros).
        unfold WF_GenMatrix in *.
        bdestruct (x0 <? 1)%nat.
        - bdestruct_all.
          subst.
          f_equal.
          2 : apply Gmult_comm.
          rewrite seq_length.
          apply big_sum_eq_bounded.
          intros.
          rewrite seq_nth.
          2 : assumption.
          simpl.
          f_equal.
          rewrite nth_indep with (d' := (fun i0 x1 y : nat => if (y =? 0)%nat then M x1 i0 else 0) (S m)).
          2 : rewrite map_length;
          rewrite seq_length;
          assumption.
          rewrite map_nth with (d := S m).
          bdestruct_all.
          rewrite seq_nth; trivial.
        - remember H0 as H0'. clear HeqH0'.
          remember H0 as H0''. clear HeqH0''.
          assert ((m >= S m)%nat \/ (x0 >= 1)%nat). { right. assumption. }
          specialize (H0 m x0 H3).
          rewrite H0. rewrite Gmult_0_r, Gplus_0_r.
          bdestruct_all.
          rewrite Gmult_0_r, Gplus_0_r.
          f_equal.
          2 : symmetry; apply seq_length.
          apply functional_extensionality; intros.
          assert ((x1 >= S m)%nat \/ (x0 >= 1)%nat). { right. assumption. }
          specialize (H0' x1 x0 H5).
          rewrite H0'.
          rewrite Gmult_0_r.
          assert ((nth x1 (List.seq 0 m) (S m) >= S m)%nat \/ (x0 >= 1)%nat). { right. assumption. }
          specialize (H0'' (nth x1 (List.seq 0 m) (S m)) x0 H6).
          rewrite H0''.
          rewrite Gmult_0_r.
          reflexivity. }
      rewrite H.
      remember H1 as H1'.
      clear HeqH1'.
      unfold subspace in H1.
      destruct H1 as [WFP [PZero [Psum Pscale]]].
      apply Psum.
    + rewrite ! seq_length.
      apply IHm. 
      * pose (WF_GenMatrix_vector_row_choose_indices_list (List.seq 0 m) a).
        rewrite ! seq_length in w; auto.
      * intros i0 H1.
        assert (get_col (matrix_column_choose (List.seq 0 m) M) i0 = get_col M i0).
           { unfold matrix_column_choose, list_vector_to_matrix.
             unfold get_col.
             do 2 (apply functional_extensionality; intros).
             bdestruct_all; trivial.
             subst.
             rewrite nth_indep with (d' := (fun i1 x0 y : nat => if (y =? 0)%nat then M x0 i1 else 0) (S m)).
             2 : rewrite map_length;
             rewrite seq_length;
             assumption.
             rewrite map_nth with (d := S m).
             bdestruct_all.
             rewrite seq_nth; trivial. }
           setoid_rewrite H3.
           auto.
    + apply Pscale.
      auto.
Qed.


Definition span {n m : nat} (M : GenMatrix n m) (u : GenVector n) : Prop := (exists (a : GenVector m), WF_GenMatrix a /\ u = M × a).

Lemma span_is_subspace : forall (n m : nat) (M : GenMatrix n m),
    WF_GenMatrix M -> subspace (span M).
Proof. intros n m M H0. 
  repeat constructor.
  - intros v H1.
    unfold span in H1.
    destruct H1 as [a [WFa vMa]].
    rewrite vMa.
    auto with wf_db.
  - exists Zero.
    split; auto with wf_db.
    rewrite GMmult_0_r.
    reflexivity.
  - intros v w H1 H2.
    unfold span in *.
    destruct H1 as [a [WFa vMa]].
    destruct H2 as [b [WFb wMb]].
    exists (a .+ b).
    split; auto with wf_db.
    subst.
    rewrite GMmult_plus_distr_l.
    reflexivity.
  - intros v c H1. 
    unfold span in *.
    destruct H1 as [a [WFa vMa]].
    exists (c .* a).
    split; auto with wf_db.
    subst.
    rewrite Mscale_mult_dist_r; auto.
Qed.


(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)
Lemma equal_span_col_append : forall {n m : nat} (M : GenMatrix n m) (v u : GenVector n),
    span M u -> span (col_append M v) u.
Proof. intros n m M v u H0.
  unfold span in *.
  destruct H0 as [a [H0 H1]].
  exists (fun (r c : nat) => if r <? m then a r c else 0%G).
  split.
  - unfold WF_GenMatrix.
    intros x y H2. 
    unfold WF_GenMatrix in H0.
    rewrite H0.
    bdestruct_all; reflexivity.
    lia.
  - rewrite H1.
    unfold col_append, col_wedge.
    unfold GMmult.
    prep_genmatrix_equality.
    simpl.
    bdestruct_all.
    rewrite Gmult_0_r, Gplus_0_r.
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all.
    reflexivity.
Qed.

(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)
Lemma equal_span_col_append_inv : forall {n m : nat} (M : GenMatrix n m) (v : GenVector n), span M v -> (forall (u : GenVector n), span (col_append M v) u -> span M u).
Proof. intros n m M v H u H0.
  unfold span in *.
  do 2 destruct H.
  do 2 destruct H0.
  rewrite H1 in H2.
  rewrite H2.
  unfold GMmult in H2.
  (** Σ_{i = 0}^{i = m-1} M_i x0_i + x0_m * Σ_{i = 0}^{i = m-1} M_i x_i 
           = Σ_{i = 0}^{i = m-1} M_i (x0_i + x0_m * x_i) **)
  (** (fun (r c : nat) => (big_sum (fun (i : nat) => M r i  * ((x0 i c) + (x0 m c) * (x i c))) m)). **)
  exists (fun (r c : nat) => if (r <? m) then ((x0 r c) + (x0 m c) * (x r 0%nat)) else 0%G).
  split.
  - unfold WF_GenMatrix.
    intros x1 y H3.
    destruct H3; bdestruct_all; trivial.
    remember H0 as H0'. clear HeqH0'.
    unfold WF_GenMatrix in H0, H0'.
    assert ((x1 >= S m)%nat \/ (y >= 1)%nat). { right. lia. }
    specialize (H0 x1 y H5).
    rewrite H0.
    assert ((m >= S m)%nat \/ (y >= 1)%nat). { right. lia. }
    specialize (H0' m y H6).
    rewrite H0'.
    ring.
  - unfold col_append, col_wedge.
    unfold GMmult.
    do 2 (apply functional_extensionality; intros).
    simpl.
    bdestruct_all.
    assert ( Σ (fun y : nat => M x1 y * (if y <? m then x0 y x2 + x0 m x2 * x y 0%nat else 0)) m
             =  Σ (fun y : nat => M x1 y * (x0 y x2 + x0 m x2 * x y 0%nat)) m).
    { apply big_sum_eq_bounded.
      intros x3 H5.
      bdestruct_all.
      reflexivity. }
    rewrite H5.
    replace (fun y : nat => M x1 y * (x0 y x2 + x0 m x2 * x y 0%nat))
      with (fun y : nat => M x1 y * x0 y x2 + (M x1 y * x y 0%nat)* x0 m x2)
      by (apply functional_extensionality; intros; ring).
    assert (Σ (fun y : nat => M x1 y * x0 y x2 + M x1 y * x y 0%nat * x0 m x2) m
            = Σ (fun y : nat => M x1 y * x0 y x2) m + Σ (fun y : nat => M x1 y * x y 0%nat) m  * x0 m x2).
    { setoid_rewrite big_sum_plus.
      simpl.
      f_equal.
      rewrite @big_sum_mult_r with (R := F) (H := R0) (H0 := R1) (H1 := R2) (H2 := R3).
      simpl.
      reflexivity. }
    rewrite H6.
    f_equal.
    apply big_sum_eq_bounded.
    intros.
    bdestruct_all.
    reflexivity.
Qed.

(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)
Lemma equal_span_reduce_col_inv : forall {n m : nat} (M : GenMatrix n (S m)) (i : nat),
    (i < S m)%nat -> (forall (u : GenVector n), span (reduce_col M i) u -> span M u).
Proof. intros n m M i H u H0.
  unfold span in *.
  destruct H0 as [a [H0 H0']].
  exists (fun r c => if (r <? i)%nat then (a r c) else if (r =? i)%nat then 0%G else (a (r-1)%nat c)).
  split.
  - unfold WF_GenMatrix in *.
    intros.
    rewrite ! H0;
      bdestruct_all; trivial;
      lia.
  - rewrite H0'.
    unfold reduce_col.
    prep_genmatrix_equality.
    unfold GMmult.
    replace m with (i + (m - i))%nat at 1 by lia.
    rewrite @big_sum_sum with (H := R0) (m := i) (n := (m - i)%nat).
    replace (S m) with (i + ((S m) - i))%nat at 1 by lia.
    rewrite @big_sum_sum with (H := R0) (m := i) (n := ((S m) - i)%nat).
    f_equal.
    + apply big_sum_eq_bounded.
      intros.
      bdestruct_all.
      reflexivity.
    + replace ((S m) - i)%nat with (S (m - i))%nat by lia.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      rewrite Gmult_0_r, Gplus_0_l.
      apply big_sum_eq_bounded.
      intros.
      bdestruct_all.
      replace (1 + (i + x0))%nat with (i + S x0)%nat by lia.
      replace (i + S x0 - 1)%nat with (i + x0)%nat by lia.
      reflexivity.
Qed.
    
  
(* Lemma 19 Suppose V is a vector space, u1,u2,...,un are vectors in V, and v ∈ sp{u1,u2,...,un}. Then
sp{u1,u2,...,un,v} = sp{u1,u2,...,un}. *)

Lemma equal_span_reduce_col : forall {n m : nat} (M : GenMatrix n (S m)) (i : nat),
    (i < S m)%nat -> span (reduce_col M i) (get_col M i) ->
    (forall (u : GenVector n), span M u -> span (reduce_col M i) u).
Proof. intros n m M i H H0 u H1.
  unfold span in *.
  destruct H0 as [a [H0 H0']].
  destruct H1 as [b [H1 H1']].
  (* get_col i M = reduce_col M i × a
     =>  M_i = (Σ_{k=0}^{k=i-1} M_k a_k) + (Σ_{k=i+1}^{k=m} M_k a_{k-1})
     
        u = M × b = Σ_{k=0}^{k=m} M_k b_k
        = (Σ_{k=0}^{k=i-1} M_k b_k) + M_i b_i + (Σ_{k=i+1}^{k=m} M_k b_k)
        = (Σ_{k=0}^{k=i-1} M_k b_k) 
        + ((Σ_{k=0}^{k=i-1} M_k a_k) + (Σ_{k=i+1}^{k=m} M_k a_{k-1})) b_i 
        + (Σ_{k=i+1}^{k=m} M_k b_k)
        = (Σ_{k=0}^{k=i-1} M_k (b_i a_k + b_k)) + (Σ_{k=i+1}^{k=m} M_k (b_i a_{k-1} + b_k))
        
        u = reduce_col M i × c = (Σ_{k=0}^{k=i-1} M_k c_k) + (Σ_{k=i+1}^{k=m} M_k c_{k-1})
        c = ((b i 0%nat) .* a) .+ (reduce_row i b) *)
  exists (((b i 0%nat) .* a) .+ (reduce_row b i)).
  split.
  - auto with wf_db.
  - rewrite H1'.
    rewrite GMmult_plus_distr_l.
    rewrite Mscale_mult_dist_r; auto.
    rewrite <- H0'.
    unfold get_col, reduce_row, reduce_col.
    unfold GMmult, scale, GMplus.
    prep_genmatrix_equality.
    bdestruct_all.
    + subst.
      replace (S m) with (i + (S (m - i)))%nat by lia.
      rewrite @big_sum_sum with (H := R0) (m := i) (n := (S (m - i))%nat).
      rewrite <- big_sum_extend_l.
      simpl.
      setoid_rewrite Gplus_comm at 1.
      rewrite <- ! Gplus_assoc.
      f_equal.
      * replace (i + 0)%nat with i by lia.
        ring.
      * rewrite Gplus_comm at 1.
        replace m with (i + (m - i))%nat at 2 by lia.
        rewrite @big_sum_sum with (H := R0) (m := i) (n := (m - i)%nat).
        simpl.
        f_equal.
        -- apply big_sum_eq_bounded.
           intros.
           bdestruct_all.
           ring.
        -- apply big_sum_eq_bounded.
           intros.
           bdestruct_all.
           replace (i + S x0)%nat with (S (i + x0)) by lia.
           reflexivity.
    + assert ((fun y0 : nat => M x y0 * b y0 y)
              =
                (fun _ : nat => 0%G)).
      { apply functional_extensionality; intros.
        unfold WF_GenMatrix in H1.
        rewrite H1; try ring; lia. }
      rewrite H3.
      simpl.
      rewrite Gmult_0_r, Gplus_0_l, Gplus_0_r.
      apply big_sum_eq_bounded.
      intros.
      unfold WF_GenMatrix in H1.
      rewrite ! H1.
      bdestruct_all; ring.
      all : lia.
Qed.      

  

Lemma last_in_list : forall {A : Type} (d : A) (l : list A),
    l <> [] -> In (last l d) l.
Proof. intros A d l H0.
  apply app_removelast_last with (d := d) in H0.
  rewrite <- nth_middle with (a := (last l d)) (d := d) (l := removelast l) (l' := []).
  rewrite <- H0.
  apply nth_In.
  rewrite H0.
  rewrite removelast_last.
  rewrite app_length.
  simpl.
  lia.
Qed.

Definition col_insert_front {n m : nat} (M : GenMatrix n m) (v : GenVector n) : GenMatrix n (S m) :=
  fun r c => if (c =? 0)%nat then v r 0%nat else M r (c - 1)%nat.

Lemma WF_GenMatrix_col_insert_front : forall {n m : nat} (M : GenMatrix n m) (v : GenVector n),
    WF_GenMatrix M -> WF_GenMatrix v -> WF_GenMatrix (col_insert_front M v).
Proof. intros n m M v H0 H1.
  unfold col_insert_front.
  unfold WF_GenMatrix in *.
  intros.
  bdestruct_all.
  - rewrite H1; trivial.
    lia.
  - rewrite H0; trivial.
    lia.
Qed.

#[export] Hint Resolve WF_GenMatrix_col_insert_front : wf_db.
 

(* # ~12 *)
    (** Theorem 24 Let V be a vector space over a field F, and let u1,u2,...,un be vectors in V , where n ≥ 2. Then {u1, u2, . . . , un} is linearly dependent if and only if at least one of u1, u2, . . . , un can be written as a linear combination of the remaining n − 1 vectors. **)

(* proves the "only if" part of theorem 24

Lemma lin_dep_gen_elem : forall {m n} (T : GenMatrix n (S m)),
  WF_GenMatrix T -> linearly_dependent T -> 
  (exists i, i < (S m) /\ 
             (exists v : GenVector m, WF_GenMatrix v /\ 
                 @GMmult n m 1 (reduce_col T i) v = (-C1) .* (get_col i T))). 
 *)

Lemma span_linearly_dependent_col_insert_front : forall {m n} (M : GenMatrix n m) (v : GenVector n),
    WF_GenMatrix M -> span M v -> linearly_dependent (col_insert_front M v).
Proof. intros m n M v H0 H1.
  unfold linearly_dependent.
  unfold span in H1.
  destruct H1 as [a [H1 H2]].
  exists (fun r c => if (r =? 0)%nat
             then if (c =? 0)%nat
                  then (- 1%G)
                  else 0%G
             else a (r - 1)%nat c).
  split.
  - unfold WF_GenMatrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H1.
    rewrite H1; trivial; lia.
  - split.
    + intro H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      unfold Zero in H3. simpl in H3.
      contradict H3.
      apply Gneg1_neq_0.
    + unfold col_insert_front.
      unfold GMmult.
      prep_genmatrix_equality.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      * subst.
        simpl.
        unfold GMmult.
        assert (@Zero n 1 x 0%nat
                = Σ (fun y : nat => M x y * a y 0%nat) m * - 1%G + Σ (fun y : nat => M x y * a y 0%nat) m).
        { unfold Zero. ring. }
        rewrite H2.
        apply Fplus_inj_l.
        apply big_sum_eq_bounded.
        intros.
        replace (x0 - 0)%nat with x0 by lia.
        reflexivity.
      * rewrite Gmult_0_r, Gplus_0_l.
        unfold Zero.
        simpl.
        rewrite big_sum_0_bounded; trivial.
        intros.
        unfold WF_GenMatrix in H1.
        rewrite H1; try ring; lia.
Qed.

Lemma span_linearly_dependent_col_append : forall {m n} (M : GenMatrix n m) (v : GenVector n),
    WF_GenMatrix M -> span M v -> linearly_dependent (col_append M v).
Proof. intros m n M v H0 H1.
  unfold linearly_dependent.
  unfold span in H1.
  destruct H1 as [a [H1 H2]].
  exists (fun r c => if (r =? m)%nat
             then if (c =? 0)%nat
                  then (- 1%G)
                  else 0%G
             else a r c).
  split.
  - unfold WF_GenMatrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H1.
    rewrite H1; trivial; lia.
  - split.
    + intro H3.
      apply f_equal_inv with (x := m) in H3.
      apply f_equal_inv with (x := 0%nat) in H3.
      simpl in H3.
      replace (m =? m)%nat with true in H3 by (rewrite Nat.eqb_refl; reflexivity).
      unfold Zero in H3.
      contradict H3.
      apply Gneg1_neq_0.
    + unfold col_append, col_wedge.
      unfold GMmult.
      prep_genmatrix_equality.
      rewrite <- big_sum_extend_r.
      bdestruct_all.
      * subst.
        simpl.
        unfold GMmult.
        assert (H2 : @Zero n 1 x 0%nat
                = Σ (fun y : nat => M x y * a y 0%nat) m + Σ (fun y : nat => M x y * a y 0%nat) m * - 1%G ).
        { unfold Zero. ring. }
        rewrite H2.
        apply Fplus_inj_r.
        apply big_sum_eq_bounded.
        intros.
        bdestruct_all.
        reflexivity.
      * rewrite Gmult_0_r, Gplus_0_r.
        unfold Zero.
        rewrite big_sum_0_bounded; trivial.
        intros.
        bdestruct_all.
        unfold WF_GenMatrix in H1.
        rewrite H1; try ring; lia.
Qed.

        

Lemma linearly_dependent_linear_combination : forall {n m : nat} (M : GenMatrix n m), (m > 1)%nat -> WF_GenMatrix M -> linearly_dependent M -> (exists (i : nat) (a : GenVector (m-1)), (i < m)%nat /\ WF_GenMatrix a /\ get_col M i = (matrix_column_choose ((List.seq 0 i) ++ (List.seq (i+1) (m - i - 1)%nat)) M) × a).
Proof. intros n m M H0 H1 H2.
  unfold linearly_dependent in H2.
  destruct H2 as [u [H2 [H3 H4]]].
  apply nonzero_vec_nonzero_elem in H3; trivial.
  destruct H3 as [i H3].
  exists i.
  bdestruct (i <? m).
  - exists (fun r c : nat => if r <? i then (- (/ (u i 0%nat)) * (u r c))%G else (- (/ (u i 0%nat)) * (u (r+1)%nat c))%G).
    split.
    + assumption.
    + split.
      * unfold WF_GenMatrix in *.
        intros x y H6.
        destruct H6; bdestruct_all.
        -- assert (H8 : (x+1 >= m)%nat \/ (y >= 1)%nat). { left. lia. }
           specialize (H2 (x+1)%nat y H8).
           rewrite H2.
           ring.
        -- assert (H8 : (x >= m)%nat \/ (y >= 1)%nat). { right. lia. }
           specialize (H2 x y H8).
           rewrite H2.
           ring.
        -- assert (H8 : (x+1 >= m)%nat \/ (y >= 1)%nat). { right. lia. }
           specialize (H2 (x+1)%nat y H8).
           rewrite H2.
           ring.
      * unfold GMmult in *.
        unfold matrix_column_choose, list_vector_to_matrix.
        unfold get_col.
        do 2 (apply functional_extensionality; intros).
        apply f_equal_inv with (x := x) in H4.
        apply f_equal_inv with (x := x0) in H4.
        unfold Zero in H4.
        bdestruct_all.
        -- assert (H7 : @Zero n 1%nat = (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0) m).
           { do 2 (apply functional_extensionality; intros).
             unfold Zero.
             bdestruct_all; trivial.
             unfold WF_GenMatrix in H1.
             assert (H8 : (x1 >= n)%nat \/ (m >= m)%nat). { right. lia. }
             specialize (H1 x1 m H8).
             rewrite H1.
             reflexivity. }
           rewrite H7.
           assert (H8 : (fun y : nat =>
                      nth y
                        (map (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0)
                           (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                        (fun x1 y0 : nat => if (y0 =? 0)%nat then M x1 m else 0) x 0%nat *
                        (if y <? i then - / u i 0%nat * u y x0 else - / u i 0%nat * u (y + 1)%nat x0))
                   =
                     (fun y : nat =>
                        (- / u i 0%nat)%G * ((M x (nth y (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m)) *
                                             (if y <? i then u y x0 else u (y + 1)%nat x0)))).
           { apply functional_extensionality; intros.
             rewrite map_nth with (d := m).
             bdestruct_all; ring. }
           setoid_rewrite H8.
           setoid_rewrite <- @big_sum_scale_l with (H7 := F_is_module_space).
           simpl.
           apply Gmult_cancel_l with (a := (- u i 0%nat)%G); auto.
           ++ intro H9.
              rewrite Fopp_opp in H9.
              replace (- 0%G) with 0%G in H9 by ring.
              contradiction.
           ++ rewrite Gmult_assoc.
              replace (- u i 0%nat * - / u i 0%nat)%G with 1%G.
              ** rewrite Gmult_1_l .
                 rewrite Gmult_comm.
                 rewrite <- Fopp_mult_distr_r.
                 apply Fplus_inv_r with (c := (M x i * u i 0%nat)%G).
                 replace (- (M x i * u i 0%nat) + M x i * u i 0%nat)%G with 0%G by ring.
                 rewrite <- H4 at 1.
                 assert (H9 : Σ
                           (fun x1 : nat =>
                              M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m) *
                                (if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0))
                           (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) +
                           M x i * u i 0%nat
                         =
                           Σ
                             (fun x1 : nat =>
                                M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                  (if (x1 =? m-1)%nat then u i 0%nat else
                                     (if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0)))
                             (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]))).
                 { rewrite app_assoc.
                   setoid_rewrite app_length at 2.
                   simpl.
                   Search ((?x + 1)%nat = Datatypes.S ?x).
                   setoid_rewrite Nat.add_1_r at 6.
                   rewrite <- @big_sum_extend_r with (H := R0).
                   simpl.
                   assert (H9 : (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) = (m-1)%nat).
                   { rewrite app_length.
                     rewrite ! seq_length.
                     lia. }
                   rewrite ! H9.
                   bdestruct_all.
                   rewrite <- H9 at 3.
                   rewrite nth_middle with (a := i) (l' := []).
                   f_equal.
                   apply big_sum_eq_bounded.
                   intros x1 H12.
                   bdestruct_all.
                   - setoid_rewrite app_nth1 at 2.
                     + reflexivity.
                     + rewrite app_length.
                       rewrite ! seq_length.
                       lia.
                   - setoid_rewrite app_nth1 at 2.
                     + reflexivity.
                     + rewrite app_length.
                       rewrite ! seq_length.
                       lia. }
                 rewrite H9.
                 rewrite ! app_length.
                 rewrite ! seq_length.
                 simpl.
                 replace (i + (m - i - 1 + 1))%nat with m by lia.
                 assert (H10 : Σ (fun y : nat => M x y * u y x0) m
                         =
                           Σ (fun y : nat => M x (nth y (List.seq 0 m) m) *
                                          u (nth y (List.seq 0 m) m) x0) m).
                 { apply big_sum_eq_bounded.
                   intros x1 H10. 
                   rewrite seq_nth. simpl.
                   ring.
                   assumption. }
                 rewrite H10.
                 assert (H11 : (fun x1 : nat =>
                            M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                              (if (x1 =? m - 1)%nat
                               then u i 0%nat
                               else if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0))
                         =
                           (fun x1 : nat =>
                              M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                u (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) x0)).
                 { apply functional_extensionality; intros.
                   subst.
                   f_equal.
                   bdestruct_all.
                   - rewrite <- nth_firstn with (n := i); try lia.
                     rewrite firstn_app.
                     rewrite seq_length.
                     replace (i - i)%nat with 0%nat by lia.
                     simpl.
                     rewrite app_nil_r.
                     replace i with (length (List.seq 0 i)) at 1
                       by (rewrite seq_length; reflexivity).
                     rewrite firstn_all.
                     rewrite seq_nth; try lia.
                     simpl. ring.
                   - subst.
                     rewrite app_assoc.
                     replace (m - 1)%nat with (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                       by (rewrite app_length; rewrite ! seq_length; lia).
                     rewrite nth_middle.
                     reflexivity.
                   - bdestruct (x1 <? (m-1)%nat).
                     + rewrite <- nth_firstn with (n := (m-1)%nat); try assumption.
                       rewrite <- firstn_removelast.
                       * rewrite app_assoc.
                         rewrite removelast_last.
                         rewrite nth_firstn; try assumption.
                         rewrite app_nth2.
                         -- rewrite seq_length.
                            rewrite seq_nth; try lia.
                            replace (i + 1 + (x1 - i))%nat with (x1 + 1)%nat by lia.
                            reflexivity.
                         -- rewrite seq_length; assumption.
                       * rewrite ! app_length; rewrite ! seq_length; simpl; lia.
                     + remember H2 as H2'. clear HeqH2'.
                       unfold WF_GenMatrix in H2, H2'.
                       rewrite nth_overflow.
                       * assert (H13 : (x1 + 1 >= m)%nat \/ (0 >= 1)%nat). { left; lia. }
                         assert (H14 : (m >= m)%nat \/ (0 >= 1)%nat). { left; lia. }
                         specialize (H2 (x1+1)%nat 0%nat H13).
                         specialize (H2' m 0%nat H14).
                         rewrite H2, H2'.
                         reflexivity.
                       * rewrite ! app_length; rewrite ! seq_length; simpl; lia. }
                 rewrite H11.
                 apply big_sum_permutation with (f := fun z => M x z * u z x0).
                 2: rewrite seq_length; lia.
                 replace (List.seq 0 m) with (List.seq 0 i ++ List.seq i (m - i))
                   by (rewrite <- seq_app; f_equal; lia).
                 apply Permutation_app.
                 1: apply Permutation_refl.
                 replace (m - i)%nat with ((m - i - 1) + 1)%nat at 1 by lia.
                 rewrite Nat.add_1_r at 1.
                 simpl.
                 rewrite cons_conc.
                 rewrite <- Nat.add_1_r.
                 apply Permutation_app_comm.
              ** rewrite <- Fopp_mult_distr_l, <- Fopp_mult_distr_r.
                 rewrite Gopp_involutive.
                 rewrite Ginv_r; trivial.
        -- unfold WF_GenMatrix in H2.
           assert (H7 : (fun y : nat =>
                      nth y
                        (map (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0)
                           (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) (@Zero n 1%nat) x 0%nat *
                        (if y <? i then - / u i 0%nat * u y x0 else - / u i 0%nat * u (y + 1)%nat x0)) =
                     (fun _ : nat => 0%G)).
           { apply functional_extensionality; intros.
             assert (H7 : @Zero n 1%nat = (fun i0 x2 y0 : nat => if (y0 =? 0)%nat then M x2 i0 else 0) m).
             { do 2 (apply functional_extensionality; intros).
               replace (Zero x2 x3) with 0%G by reflexivity.
               bdestruct_all; trivial.
               unfold WF_GenMatrix in H1.
               assert (H8 : (x2 >= n)%nat \/ (m >= m)%nat). { right. lia. }
               specialize (H1 x2 m H8).
               rewrite H1.
               reflexivity. }
             rewrite H7.
             rewrite map_nth with (d := m).
             bdestruct_all.
             - assert (H10 : (x1 >= m)%nat \/ (x0 >= 1)%nat). { right. lia. }
               specialize (H2 x1 x0 H10).
               rewrite H2.
               ring.
             - assert (H10 : (x1+1 >= m)%nat \/ (x0 >= 1)%nat). { right. lia. }
               specialize (H2 (x1+1)%nat x0 H10).
               rewrite H2.
               ring. }
           setoid_rewrite H7.
           rewrite big_sum_0; trivial. 
  - assert (H6 : (i >= m)%nat \/ (0 >= 1)%nat). { left. lia. }
    unfold WF_GenMatrix in H2.
    specialize (H2 i 0%nat H6).
    contradiction.
Qed.

(*** Admitted. : Not Used.
     Use lin_dep_gen_elem *)
(** lin_dep_gen_elem :
forall {m n : nat} (T : GenMatrix n (s m)),
WF_GenMatrix T ->
linearly_dependent T ->
exists i : nat,
  (i < s m)%nat /\
  (exists v : GenVector m, WF_GenMatrix v /\ reduce_col T i × v = - C1 .* get_col i T) *)
(* 
Lemma linearly_dependent_linear_combination' : forall {n m : nat} (M : GenMatrix n m), (m > 1)%nat -> WF_GenMatrix M -> (linearly_dependent M <-> (exists (i : nat) (a : GenVector (m-1)), (i < m)%nat /\ WF_GenMatrix a /\ get_col i M = (matrix_column_choose ((List.seq 0 i) ++ (List.seq (i+1) (m-i-1))) M) × a)).
Proof. intros n m M H0 H1.
  split.
  - intros H2.
    unfold linearly_dependent in H2.
    destruct H2 as [u [H2 [H3 H4]]].
    apply nonzero_vec_nonzero_elem in H3; trivial.
    destruct H3 as [i H3].
    exists i.
    bdestruct (i <? m).
    + exists (fun r c : nat => if r <? i then (- (/ (u i 0%nat)) * (u r c))%C else (- (/ (u i 0%nat)) * (u (r+1)%nat c))%C).
      split.
      * assumption.
      * split.
        -- unfold WF_GenMatrix in *.
           intros.
           destruct H6; bdestruct_all.
           ++ assert ((x+1 >= m)%nat \/ (y >= 1)%nat). { left. lia. }
              specialize (H2 (x+1)%nat y H8).
              rewrite H2.
              lca.
           ++ assert ((x >= m)%nat \/ (y >= 1)%nat). { right. lia. }
              specialize (H2 x y H8).
              rewrite H2.
              lca.
           ++ assert ((x+1 >= m)%nat \/ (y >= 1)%nat). { right. lia. }
              specialize (H2 (x+1)%nat y H8).
              rewrite H2.
              lca.
        -- unfold GMmult in *.
           unfold matrix_column_choose, list_vector_to_matrix.
           unfold get_col.
           do 2 (apply functional_extensionality; intros).
           apply f_equal_inv with (x := x) in H4.
           apply f_equal_inv with (x := x0) in H4.
           replace (Zero x x0) with C0 in H4 by reflexivity.
           bdestruct_all.
           ++ assert (@Zero n 1%nat = (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0) m).
              { do 2 (apply functional_extensionality; intros).
                replace (Zero x1 x2) with C0 by reflexivity.
                bdestruct_all; trivial.
                unfold WF_GenMatrix in H1.
                assert ((x1 >= n)%nat \/ (m >= m)%nat). { right. lia. }
                specialize (H1 x1 m H8).
                rewrite H1.
                reflexivity. }
              rewrite H7.
              assert ((fun y : nat =>
                         nth y
                           (map (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0)
                              (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                           (fun x1 y0 : nat => if (y0 =? 0)%nat then M x1 m else 0) x 0%nat *
                           (if y <? i then - / u i 0%nat * u y x0 else - / u i 0%nat * u (y + 1)%nat x0))
                      =
                        (fun y : nat =>
                           (- / u i 0%nat)%C * ((M x (nth y (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m)) *
                             (if y <? i then u y x0 else u (y + 1)%nat x0)))).
              { apply functional_extensionality; intros.
                rewrite map_nth with (d := m).
                bdestruct_all; lca. }
              setoid_rewrite H8.
              rewrite <- @big_sum_scale_l with (H7 := C_is_module_space).
              simpl.
              apply Cmult_cancel_l with (a := (- u i 0%nat)%C).
              ** intro.
                 rewrite Copp_opp in H9.
                 replace (- C0)%C with C0%C in H9 by lca.
                 contradiction.
              ** rewrite Cmult_assoc.
                 replace (- u i 0%nat * - / u i 0%nat)%C with C1.
                 --- rewrite Cmult_1_l.
                     rewrite Cmult_comm.
                     rewrite <- Copp_mult_distr_r.
                     apply Cplus_inv_r with (c := (M x i * u i 0%nat)%C).
                     replace (- (M x i * u i 0%nat) + M x i * u i 0%nat)%C with C0 by lca.
                     rewrite <- H4 at 1.
                     Search big_sum.

                     assert (Σ
                               (fun x1 : nat =>
                                  M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m) *
                                    (if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0))
                               (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) +
                              M x i * u i 0%nat
                             =
                               Σ
                                 (fun x1 : nat =>
                                    M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                      (if (x1 =? m-1)%nat then u i 0%nat else
                                         (if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0)))
                                 (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]))).
                     { rewrite app_assoc.
                       setoid_rewrite app_length at 2.
                       simpl.
                       Search ((?x + 1)%nat = Datatypes.S ?x).
                       setoid_rewrite Nat.add_1_r at 6.
                       rewrite <- @big_sum_extend_r with (H := C_is_monoid).
                       simpl.
                       assert ((length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) = (m-1)%nat).
                       { rewrite app_length.
                         rewrite ! seq_length.
                         lia. }
                       rewrite ! H9.
                       bdestruct_all.
                       rewrite <- H9 at 3.
                       rewrite nth_middle with (a := i) (l' := []).
                       f_equal.
                       apply big_sum_eq_bounded.
                       intros x1 H12.
                       bdestruct_all.
                       - setoid_rewrite app_nth1 at 2.
                         + reflexivity.
                         + rewrite app_length.
                           rewrite ! seq_length.
                           lia.
                       - setoid_rewrite app_nth1 at 2.
                         + reflexivity.
                         + rewrite app_length.
                           rewrite ! seq_length.
                           lia. }
                     rewrite H9.
                     rewrite ! app_length.
                     rewrite ! seq_length.
                     simpl.
                     replace (i + (m - i - 1 + 1))%nat with m by lia.
                     assert (Σ (fun y : nat => M x y * u y x0) m
                             =
                               Σ (fun y : nat => M x (nth y (List.seq 0 m) m) *
                                              u (nth y (List.seq 0 m) m) x0) m).
                     { apply big_sum_eq_bounded.
                       intros x1 H10. 
                       rewrite seq_nth.
                       lca.
                       assumption. }
                     rewrite H10.
                     assert ((fun x1 : nat =>
                                 M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                   (if (x1 =? m - 1)%nat
                                    then u i 0%nat
                                    else if x1 <? i then u x1 x0 else u (x1 + 1)%nat x0))
                              =
                                (fun x1 : nat =>
                                   M x (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) *
                                     u (nth x1 (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]) m) x0)).
                     { apply functional_extensionality; intros.
                       subst.
                       f_equal.
                       bdestruct_all.
                       - rewrite <- nth_firstn with (n := i); try lia.
                         rewrite firstn_app.
                         rewrite seq_length.
                         replace (i - i)%nat with 0%nat by lia.
                         simpl.
                         rewrite app_nil_r.
                         replace i with (length (List.seq 0 i)) at 1
                           by (rewrite seq_length; reflexivity).
                         rewrite firstn_all.
                         rewrite seq_nth; try lia.
                         lca.
                       - subst.
                         rewrite app_assoc.
                         replace (m - 1)%nat with (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                           by (rewrite app_length; rewrite ! seq_length; lia).
                         rewrite nth_middle.
                         reflexivity.
                       - bdestruct (x1 <? (m-1)%nat).
                         + rewrite <- nth_firstn with (n := (m-1)%nat); try assumption.
                           rewrite <- firstn_removelast.
                           * rewrite app_assoc.
                             rewrite removelast_last.
                             rewrite nth_firstn; try assumption.
                             rewrite app_nth2.
                             -- rewrite seq_length.
                                rewrite seq_nth; try lia.
                                replace (i + 1 + (x1 - i))%nat with (x1 + 1)%nat by lia.
                                reflexivity.
                             -- rewrite seq_length; assumption.
                           * rewrite ! app_length; rewrite ! seq_length; simpl; lia.
                         + remember H2 as H2'. clear HeqH2'.
                           unfold WF_GenMatrix in H2, H2'.
                           rewrite nth_overflow.
                           * assert ((x1 + 1 >= m)%nat \/ (0 >= 1)%nat). { left; lia. }
                             assert ((m >= m)%nat \/ (0 >= 1)%nat). { left; lia. }
                             specialize (H2 (x1+1)%nat 0%nat H13).
                             specialize (H2' m 0%nat H14).
                             rewrite H2, H2'.
                             reflexivity.
                           * rewrite ! app_length; rewrite ! seq_length; simpl; lia. }
                     rewrite H11.
                     apply big_sum_permutation with (f := fun z => M x z * u z x0).
                     2: rewrite seq_length; lia.
                     replace (List.seq 0 m) with (List.seq 0 i ++ List.seq i (m - i))
                       by (rewrite <- seq_app; f_equal; lia).
                     apply Permutation_app.
                     1: apply Permutation_refl.
                     replace (m - i)%nat with ((m - i - 1) + 1)%nat at 1 by lia.
                     rewrite Nat.add_1_r at 1.
                     simpl.
                     rewrite cons_conc.
                     rewrite <- Nat.add_1_r.
                     apply Permutation_app_comm.
                     (** unused old code


                       apply big_sum_permutation_function'. (*** Admitted *)
                     assert (List.seq 0 m = List.seq 0 i ++ [i] ++ List.seq (i + 1) (m - i - 1)).
                     { replace m with (i + (m-i))%nat at 1 by lia.
                       rewrite seq_app.
                       simpl.
                       replace (m - i)%nat with (1 + (m - i - 1))%nat at 1 by lia.
                       rewrite seq_app.
                       simpl.
                       reflexivity. }
                     assert (List.seq 0 m = List.seq 0 i ++ List.seq i (m - i - 1) ++ [m - 1])%nat.
                     { replace m with (i + (m-i))%nat at 1 by lia.
                       rewrite seq_app.
                       simpl.
                       replace (m - i)%nat with ((m - i - 1) + 1)%nat at 1 by lia.
                       rewrite seq_app.
                       simpl.
                       replace (i + (m - i - 1))%nat with (m - 1)%nat by lia.
                       reflexivity. }
                     exists (List.seq 0 i ++ List.seq (i + 1) (m - i - 1) ++ [i]).
                     split.
                     +++ rewrite H11.
                         apply Permutation_app.
                         *** apply Permutation_refl.
                         *** apply Permutation_app_comm.
                     +++ setoid_rewrite H12 at 3.
                         rewrite ! map_app.
                         f_equal.
                         *** rewrite map_ext_in_iff.
                             intros a H13.
                             f_equal.
                             ---- f_equal.
                                  rewrite in_seq in H13.
                                  rewrite seq_nth; try lia.
                                  rewrite <- nth_firstn with (n := i); try lia.
                                  rewrite firstn_app.
                                  rewrite seq_length.
                                  replace (i - i)%nat with 0%nat by lia.
                                  simpl.
                                  rewrite app_nil_r.
                                  replace i with (length (List.seq 0 i)) at 1
                                    by (rewrite seq_length; reflexivity).
                                  rewrite firstn_all.
                                  rewrite seq_nth; lia.
                             ---- rewrite in_seq in H13.
                                  bdestruct_all; try lia.
                                  f_equal.
                                  rewrite seq_nth; try lia.
                         *** f_equal.
                             ---- rewrite map_ext_nth.
                                  assert (length (List.seq (i + 1) (m - i - 1)) = length (List.seq i (m - i - 1))).
                                  { rewrite ! seq_length.
                                    reflexivity. }
                                  split; try assumption.
                                  intros n0 H14.
                                  rewrite seq_length in H14.
                                  f_equal.
                                  ++++ f_equal.
                                       rewrite ! seq_nth; try lia.
                                       **** rewrite <- nth_firstn with (n := (i + n0 + 1)%nat).
                                         ----- rewrite <- Nat.add_assoc with (n := i) (m := n0) (p := 1%nat).
                                         replace i with (length (List.seq 0 i)) at 3
                                           by (rewrite seq_length; reflexivity).
                                         rewrite firstn_app_2.
                                         rewrite app_nth2 with (n := (i + n0)%nat);
                                           try (rewrite seq_length; lia).
                                         rewrite seq_length.
                                         replace (i + n0 - i)%nat with n0 by lia.
                                         rewrite nth_firstn; try lia.
                                         rewrite <- nth_firstn with (n := (m - i - 1)%nat); try lia.
                                         rewrite firstn_app.
                                         rewrite seq_length.
                                         replace (m - i - 1 - (m - i - 1))%nat with 0%nat by lia.
                                         simpl.
                                         rewrite app_nil_r.
                                         rewrite nth_firstn; try assumption.
                                         rewrite seq_nth; try assumption.
                                         reflexivity.
                                         ----- lia.
                                       **** rewrite seq_nth; lia.
                                  ++++ bdestruct_all;
                                         rewrite seq_nth in H15;
                                         rewrite seq_nth in H16;
                                         try lia.
                                       f_equal.
                                       rewrite ! seq_nth; try lia.
                                       rewrite seq_nth; lia.
                             ---- simpl.
                                  f_equal.
                                  bdestruct_all.
                                  f_equal.
                                  +++++ f_equal.
                                  rewrite seq_nth; try lia.
                                  assert (length (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) + 0 = m - 1)%nat.
                                  { rewrite app_length.
                                    rewrite ! seq_length.
                                    lia. }
                                  rewrite <- H15.
                                  rewrite app_assoc.
                                  rewrite app_nth2_plus.
                                  reflexivity.
                                  +++++ f_equal; try assumption.
                                  rewrite seq_nth; lia. *)
                 --- rewrite <- Copp_mult_distr_l, <- Copp_mult_distr_r.
                     rewrite Copp_involutive.
                     rewrite Cinv_r; trivial.
           ++ unfold WF_GenMatrix in H2.
              assert ((fun y : nat =>
                         nth y
                           (map (fun i0 x1 y0 : nat => if (y0 =? 0)%nat then M x1 i0 else 0)
                              (List.seq 0 i ++ List.seq (i + 1) (m - i - 1))) (@Zero n 1%nat) x 0%nat *
                           (if y <? i then - / u i 0%nat * u y x0 else - / u i 0%nat * u (y + 1)%nat x0)) =
                        (fun _ : nat => C0)).
              { apply functional_extensionality; intros.
                assert (@Zero n 1%nat = (fun i0 x2 y0 : nat => if (y0 =? 0)%nat then M x2 i0 else 0) m).
                { do 2 (apply functional_extensionality; intros).
                  replace (Zero x2 x3) with C0 by reflexivity.
                  bdestruct_all; trivial.
                  unfold WF_GenMatrix in H1.
                  assert ((x2 >= n)%nat \/ (m >= m)%nat). { right. lia. }
                  specialize (H1 x2 m H8).
                  rewrite H1.
                  reflexivity. }
                rewrite H7.
                rewrite map_nth with (d := m).
                bdestruct_all.
                - assert ((x1 >= m)%nat \/ (x0 >= 1)%nat). { right. lia. }
                  specialize (H2 x1 x0 H10).
                  rewrite H2.
                  lca.
                - assert ((x1+1 >= m)%nat \/ (x0 >= 1)%nat). { right. lia. }
                  specialize (H2 (x1+1)%nat x0 H10).
                  rewrite H2.
                  lca. }
              setoid_rewrite H7.
              rewrite big_sum_0; trivial. 
    + assert ((i >= m)%nat \/ (0 >= 1)%nat). { left. lia. }
      unfold WF_GenMatrix in H2.
      specialize (H2 i 0%nat H6).
      contradiction.
  - intros H2.
    destruct H2 as [i [u [H2 [H3 H4]]]].
    unfold linearly_dependent.
    exists (fun r c : nat => if r <? i then u r c else (if (r =? i)%nat then (if (c =? 0)%nat then (- C1)%C else C0) else u (r-1)%nat c)).
    split.
    + unfold WF_GenMatrix.
      intros x y H5.
      unfold WF_GenMatrix in H3.
      destruct H5; bdestruct_all; trivial.
      * assert ((x-1 >= m - 1)%nat \/ (y >= 1)%nat). { left. lia. }
        specialize (H3 (x-1)%nat y H8).
        assumption.
      * assert ((x >= m - 1)%nat \/ (y >= 1)%nat). { right. lia. }
        specialize (H3 x y H7).
        assumption.
      * assert ((x-1 >= m - 1)%nat \/ (y >= 1)%nat). {right. lia. }
        specialize (H3 (x-1)%nat y H8).
        assumption.
    + split.
      * intro.
        apply f_equal_inv with (x := i) in H5.
        apply f_equal_inv with (x := 0%nat) in H5.
        contradict H5.
        bdestruct_all.
        replace (Zero i 0%nat) with C0 by reflexivity.
        nonzero.
      * unfold GMmult in *.
        do 2 (apply functional_extensionality; intros).
        unfold matrix_column_choose, list_vector_to_matrix in H4.
        unfold get_col in H4.
        apply f_equal_inv with (x := x) in H4.
        apply f_equal_inv with (x := x0) in H4.
        replace (@Zero n 1%nat x x0) with C0 by lca.
        assert (@Zero n 1%nat = (fun i x y0 : nat => if (y0 =? 0)%nat then M x i else 0) m).
        { do 2 (apply functional_extensionality; intros).
          replace (@Zero n 1%nat x1 x2) with C0 by lca.
          bdestruct_all; trivial.
          unfold WF_GenMatrix in H1.
          assert ((x1 >= n)%nat \/ (m >= m)%nat). { right. lia. }
          specialize (H1 x1 m H6).
          rewrite H1.
          reflexivity. }
        rewrite H5 in H4.
        assert ((fun y : nat =>
                   nth y
                     (map (fun i x y0 : nat => if (y0 =? 0)%nat then M x i else 0)
                        (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)))
                     (fun x y0 : nat => if (y0 =? 0)%nat then M x m else 0) x 0%nat * 
                     u y x0)
                =
                  (fun y : nat =>
                    M x (nth y (List.seq 0 i ++ List.seq (i + 1) (m - i - 1)) m) * u y x0)).
        { apply functional_extensionality; intros.
          rewrite map_nth with (d := m).
          bdestruct_all.
          reflexivity. }
        setoid_rewrite H6 in H4.
        clear H5 H6.
        bdestruct_all; try lca.
        -- subst.
           
           

           
           admit.


        (**   

           
           Lemma vsum_reorder : forall {d} n (v : nat -> GenVector d) f,
  permutation n f ->
  big_sum v n = big_sum (fun i => v (f i)) n.



           (*** Admitted *)
          Lemma big_sum_split :
           big_sum f m = big_sum f i + f i + (big_sum f m - big_sum f (i + 1))
                                               f = fun y => ...
            i+1 <= y < m
                        
           **)
           
        -- assert ((fun y : nat =>
                      M x y *
                        (if y <? i then u y x0 else if (y =? i)%nat then 0 else u (y - 1)%nat x0))
                   = (fun _ : nat => C0)).
           { apply functional_extensionality; intros.
             bdestruct_all; try lca.
             - unfold WF_GenMatrix in H3.
               assert ((x1 >= m - 1)%nat \/ (x0 >= 1)%nat). { right. lia. }
               specialize (H3 x1 x0 H7).
               rewrite H3.
               lca.
             - unfold WF_GenMatrix in H3.
               assert ((x1-1 >= m - 1)%nat \/ (x0 >= 1)%nat). { right. lia. }
               specialize (H3 (x1-1)%nat x0 H8).
               rewrite H3.
               lca. }
           rewrite H6.
           apply @big_sum_0 with (H := C_is_monoid).
           trivial.
Admitted.
*)

(* # ~11 *)
(** Theorem 26 Let V be a vector space over a field F, and let u1,u2,...,un be vectors in V . Then {u1, u2, . . . , un} is linearly independent if and only if each vector in sp{u1,u2,...,un} can be written uniquely as a linear combination of u1,u2,...,un. **)

Lemma linearly_independent_iff_unique_linear_combination_of_span : forall {n m : nat} (M : GenMatrix n m), linearly_independent M <-> (forall v : GenVector n, span M v -> (exists a : GenVector m, WF_GenMatrix a /\ v = M × a /\ (forall b : GenVector m, WF_GenMatrix b -> v = M × b -> b = a))).
Proof. intros n m M.
  split.
  - intros H0 v H1.
    unfold span in *.
    destruct H1 as [x [H1 H2]].
    exists x.
    split; trivial.
    split; trivial.
    intros b H3 H4.
    apply Mscale_inj with (c := (- 1%G)) in H2.
    apply (Mplus_double_side H4) in H2.
    replace (v .+ - 1%G .* v) with (@Zero n 1) in H2 by (unfold Zero; lgma).
    unfold linearly_independent in *.
    symmetry in H2.
    rewrite <- Mscale_mult_dist_r in H2.
    rewrite <- GMmult_plus_distr_l in H2.
    specialize (H0 (b .+ - 1%G .* x)).
    apply H0 in H2; auto with wf_db.
    apply Mplus_inj_r with (m := x) in H2.
    rewrite GMplus_assoc in H2.
    replace (- 1%G .* x .+ x) with (@Zero m 1) in H2 by (unfold Zero; lgma).
    rewrite GMplus_0_l, GMplus_0_r in H2.
    assumption.
  - intros H0.
    unfold linearly_independent.
    intros a H1 H2.
    assert (H3 : span M Zero).
    { unfold span.
      exists Zero.
      split; auto with wf_db.
      rewrite GMmult_0_r.
      reflexivity. }
    specialize (H0 Zero H3).
    destruct H0 as [x [H0 [H4 H5]]].
    destruct H4.
    symmetry in H2.
    remember H5 as H5'. clear HeqH5'.
    specialize (H5' Zero).
    assert (H6 : WF_GenMatrix (@Zero m 1%nat)). { auto with wf_db. }
    assert (H7 : @Zero n 1%nat = M × (@Zero m 1%nat)). { rewrite GMmult_0_r. reflexivity. }
    specialize (H5' H6 H7).
    specialize (H5 a H1 H2).
    subst.
    reflexivity.
Qed.

(** Definition 27 Let V be a vector space over a field F, and let u1,u2,...,un be vectors in V. We say that {u1,u2,...,un} is a basis for V if and only if {u1,u2,...,un} spans V and is linearly independent. **)

Definition basis {n m : nat} (P : GenVector n -> Prop) (M : GenMatrix n m) : Prop := subspace P /\ (forall i : nat, (i < m)%nat -> P (get_col M i)) /\ (forall v : GenVector n, P v -> span M v) /\ linearly_independent M.

(** Theorem 28 Let V be a vector space over a field F, and suppose u1,u2,...,un are vectors in V. Then {u1,u2,...,un} is a basis for V if and only if each v ∈ V can be written uniquely as a linear combination of u1, u2, . . . , un. **)

Lemma basis_iff_unique_linear_combination : forall {n m : nat} (P : GenVector n -> Prop) (M : GenMatrix n m), basis P M <-> subspace P /\ (forall i : nat, (i < m)%nat -> P (get_col M i)) /\ (forall v : GenVector n, P v -> (exists a : GenVector m, WF_GenMatrix a /\ v = M × a /\ (forall b : GenVector m, WF_GenMatrix b -> v = M × b -> b = a))).
Proof. intros n m P M.
  split.
  - intros H. 
    unfold basis in H.
    destruct H.
    destruct H0.
    destruct H1.
    do 2 (split; trivial).
    intros v H3.
    specialize (H1 v H3).
    rewrite linearly_independent_iff_unique_linear_combination_of_span in H2.
    specialize (H2 v H1).
    assumption.
  - intros H.
    destruct H.
    destruct H0.
    unfold basis.
    do 2 (split; trivial).
    split.
    + intros v H2.
      unfold span.
      specialize (H1 v H2).
      destruct H1.
      exists x.
      destruct H1.
      destruct H3.
      split; trivial.
    + rewrite linearly_independent_iff_unique_linear_combination_of_span.
      intros v H2.
      unfold span in H2.
      destruct H2.
      destruct H2.
      assert (P (M × x)).
      { apply subspace_closed_under_linear_combinations; trivial. }
      rewrite <- H3 in H4.
      specialize (H1 v H4).
      assumption.
Qed.

(** another way to say the first n columns **)
Definition submatrix_column {n m} (k : nat) (M : GenMatrix n m) : GenMatrix n k :=
  (fun r c : nat => if (c <? k)%nat then M r c else 0%G).

Lemma subsubmatrix_column_outer : forall {n m} (i j : nat) (M : GenMatrix n m),
    (i >= j)%nat -> submatrix_column i (submatrix_column j M) = (submatrix_column j M).
Proof. intros.
  unfold submatrix_column.
  apply functional_extensionality; intros r.
  apply functional_extensionality; intros c.
  bdestruct_all; trivial.
Qed.

Lemma subsubmatrix_column_inner : forall {n m} (i j : nat) (M : GenMatrix n m),
    (i < j)%nat -> submatrix_column i (submatrix_column j M) = (submatrix_column i M).
Proof. intros.
  unfold submatrix_column.
  apply functional_extensionality; intros r.
  apply functional_extensionality; intros c.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_matrix_column_choose : forall {n m} (k : nat) (M : GenMatrix n m), WF_GenMatrix M -> submatrix_column k M = matrix_column_choose (List.seq 0 k) M.
Proof. intros.
  unfold submatrix_column.
  unfold matrix_column_choose, list_vector_to_matrix.
  apply functional_extensionality; intros r.
  apply functional_extensionality; intros c.
  assert (Zero = (fun i0 : nat => get_col M i0) m).
  { unfold get_col.
    apply functional_extensionality; intros x.
    apply functional_extensionality; intros y.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H0.
    assert ((x >= n)%nat \/ (m >= m)%nat). { right. lia. }
    specialize (H x m H1).
    rewrite H.
    trivial. }
  rewrite H0.
  rewrite map_nth with (d := m).
  unfold get_col.
  bdestruct_all.
  - rewrite seq_nth; auto.
  - rewrite nth_overflow.
    + unfold WF_GenMatrix in H.
      rewrite H; auto.
    + rewrite seq_length; trivial.
Qed.

Lemma WF_GenMatrix_submatrix_column : forall {n m} (k : nat) (M : GenMatrix n m),
    WF_GenMatrix M -> WF_GenMatrix (submatrix_column k M).
Proof. intros.
  unfold WF_GenMatrix in *.
  unfold submatrix_column.
  intros.
  bdestruct_all; trivial.
  rewrite H; trivial.
  destruct H0; lia.
Qed.

#[export] Hint Resolve WF_GenMatrix_submatrix_column : wf_db.




 (** Lemma 33 Let V be a vector space over a field F, and let v1,v2,...,vn be nonzero vectors in V . If {v1, v2, . . . , vn} is linearly dependent, then there exists an integer k, with 2 ≤ k ≤ n, such that vk is a linear combination of v1,v2,...,vk−1. **)

(* Proof Let k be the smallest positive integer such that {v1, v2, . . . , vk} is linearly dependent. By assumption k ≤ n, and k ≥ 2 because the singleton set {v1} is linearly dependent only if v1 is the zero vector, which is not the case. By Theorem 24, one of the vectors v1,v2,...,vk is a linear combination of the others. If it is vk, then the proof is complete, so suppose vt, 1 ≤ t < k, is a linear combination of v1, ..., vt−1, vt+1, ..., vk:

vt = α1 v1 + ... + αt−1 vt−1 + αt+1 vt+1 + ... + αk vk. (2.12)

We must have αk ̸= 0, since otherwise {v1, v2, . . . , vk−1} would be linearly dependent by Theorem 26, contradicting that {v1, v2, . . . , vl} is linearly inde- pendent for l < k. But, with αk ̸= 0, we can solve (2.12) for vk:

vk = −α−1α1v1−...−α−1αt−1vt−1+α−1vt−α−1αt+1vt+1−...−α−1αk−1vk−1.
Therefore vk is a linear combination of v1,v2,...,vk−1. *)


Lemma linearly_dependent_bounded_linear_combination : forall {n m : nat} (M : GenMatrix n m), WF_GenMatrix M -> (forall i : nat, (i < m)%nat -> get_col M i <> Zero) -> linearly_dependent M -> (exists k : nat, (0 < k < m)%nat /\ (exists a : GenVector k, WF_GenMatrix a /\ get_col M k = (submatrix_column k M) × a)).
Proof. intros n m M H H0 H1.
  induction m.
  - exists 0%nat.
    intros.
    Search Zero.
    unfold linearly_dependent in H1.
    destruct H1 as [a [H1 [H2 H3]]].
    contradict H2.
    unfold WF_GenMatrix in H1.
    prep_genmatrix_equality.
    apply H1.
    lia.
  - remember (submatrix_column m M) as M'.
    destruct (Classical_Prop.classic (linearly_dependent M')).
    + destruct (IHm M') as [k H'].
      * subst.
        apply WF_GenMatrix_submatrix_column.
        assumption.
      * intros.
        rewrite HeqM'.
        intro.
        apply (H0 i).
        -- lia.
        -- unfold get_col.
           unfold get_col in H4.
           rewrite <- H4.
           unfold submatrix_column.
           bdestruct_all.
           reflexivity.
      * assumption.
      * exists k.
        intros.
        destruct H'.
        split; try lia.
        assert (submatrix_column k M' = submatrix_column k M).
        { rewrite HeqM'.
          rewrite subsubmatrix_column_inner; trivial.
          lia. }
        assert (get_col M' k = get_col M k).
        { rewrite HeqM'.
          unfold get_col.
          unfold submatrix_column.
          bdestruct_all.
          reflexivity. }
        rewrite <- H6.
        rewrite <- H5.
        assumption.
    + assert (linearly_independent M').
      { unfold linearly_independent.
        unfold linearly_dependent in H2.
        intros.
        apply Classical_Pred_Type.not_ex_all_not with (U := GenVector m) (n := a) in H2.
        apply Classical_Prop.not_and_or in H2.
        destruct H2; try contradiction.
        apply Classical_Prop.not_and_or in H2.
        destruct H2; try contradiction.
        unfold "<>" in H2.
        rewrite Decidable.not_not_iff in H2; trivial.
        unfold Decidable.decidable.
        apply (Classical_Prop.classic (a = Zero)). }
      subst.
      exists m.
      bdestruct (m =? 0)%nat.
      * subst.
        remember H1 as H1'. clear HeqH1'.
        apply lindep_implies_not_linindep in H1'.
        assert (M <> Zero).
        { intro.
          assert (0 < 1)%nat. { lia. }
          specialize (H0 0%nat H5).
          contradict H0.
          rewrite H4.
          unfold get_col.
          prep_genmatrix_equality.
          bdestruct_all; trivial. }
        pose (lin_indep_vec M H H4).
        contradiction.
      * split; try lia.
        unfold linearly_dependent in H1.
        destruct H1 as [a [H5 [H6 H7]]].
        assert (a m 0%nat <> 0%G).
        { intro.
          assert (WF_GenMatrix (reduce_row a m)).
          { unfold WF_GenMatrix.
            unfold WF_GenMatrix in H5.
            intros.
            unfold reduce_row.
            bdestruct_all.
            - apply H5. right. lia.
            - apply H5. left. lia. }
          assert (reduce_row a m <> Zero).
          { unfold reduce_row.
            intro.
            destruct (nonzero_vec_nonzero_elem a H5 H6) as [x H10].
            apply f_equal_inv with (x := x) in H9.
            apply f_equal_inv with (x := 0%nat) in H9.
            replace (Zero x 0%nat) with 0%G in H9 by trivial.
            bdestruct (x <? m)%nat.
            - contradiction.
            - bdestruct (x =? m)%nat.
              + subst. contradiction.
              + contradict H10.
                unfold WF_GenMatrix in H5.
                apply H5.
                left.
                lia. }
          assert ((submatrix_column m M) × (reduce_row a m) = Zero).
          { unfold reduce_row, submatrix_column.
            unfold GMmult.
            prep_genmatrix_equality.
            replace (@Zero n 1%nat x y) with 0%G by trivial.
            assert ((fun y0 : nat =>
                       (if y0 <? m then M x y0 else 0) *
                         (if y0 <? m then a y0 y else a (1 + y0)%nat y))
                    =
                      (fun y0 : nat =>
                         (if y0 <? m then M x y0 * a y0 y else 0))).
            { apply functional_extensionality; intros.
              bdestruct_all; ring. }
            rewrite H10.
            assert (Σ (fun y0 : nat => if y0 <? m then M x y0 * a y0 y else 0) m
                    =
                      Σ (fun y0 : nat => M x y0 * a y0 y) m).
            { apply big_sum_eq_bounded.
              intros.
              bdestruct_all.
              reflexivity. }
            rewrite H11.
            unfold GMmult in H7.
            apply f_equal_inv with (x := x) in H7.
            apply f_equal_inv with (x := y) in H7.
            replace (@Zero n 1%nat x y) with 0%G in H7 by (unfold Zero; ring).
            rewrite <- H7.
            simpl.
            bdestruct (y =? 0)%nat.
            - subst.
              rewrite H1.
              rewrite Gmult_0_r.
              rewrite Gplus_0_r.
              reflexivity.
            - unfold WF_GenMatrix in H5.
              rewrite H5.
              + rewrite Gmult_0_r.
                rewrite Gplus_0_r.
                reflexivity.
              + right. lia. }
          unfold linearly_independent in H3.
          specialize (H3 (reduce_row a m) H8 H10).
          contradiction. }
        exists ((- (/ (a m 0%nat)))%G .* (reduce_row a m)).
        split; auto with wf_db. 
        rewrite Mscale_mult_dist_r.
        apply Mscale_div with (c := (- (a m 0%nat))%G).
        -- intro.
           rewrite Fopp_opp in H8.
           replace (- 0%G) with 0%G in H8 by ring.
           contradiction.
        -- rewrite Mscale_assoc.
           replace (- a m 0%nat * - / a m 0%nat)%G with (a m 0%nat * / a m 0%nat)%G by ring.
           rewrite Ginv_r; trivial.
           rewrite Mscale_1_l.
           apply Mplus_inv_r with (m := a m 0%nat .* get_col M m); auto with wf_db.
           replace (- a m 0%nat .* get_col M m .+ a m 0%nat .* get_col M m) with (@Zero n 1)
             by lgma.
           rewrite <- H7.
           unfold submatrix_column, reduce_row, get_col.
           unfold GMmult, scale, GMplus.
           prep_genmatrix_equality.
           simpl.
           assert ((fun y0 : nat =>
                      (if y0 <? m then M x y0 else 0) * (if y0 <? m then a y0 y else a (S y0) y))
                   =
                     (fun y0 : nat =>
                        (if y0 <? m then M x y0 *a y0 y else 0%G))).
           { apply functional_extensionality; intros.
             bdestruct_all; ring. }
           rewrite H8.
           bdestruct_all.
           ++ subst.
              f_equal; try ring.
              apply big_sum_eq_bounded.
              intros.
              bdestruct_all.
              reflexivity.
           ++ unfold WF_GenMatrix in H5.
              rewrite H5 at 1.
              ** f_equal; try ring.
                 apply big_sum_eq_bounded.
                 intros.
                 bdestruct_all.
                 reflexivity.
              ** right. lia.
Qed.

Lemma linearly_dependent_submatrix_column : forall {n m : nat} (k : nat) (M : GenMatrix n m),
    (k < m)%nat -> linearly_dependent (submatrix_column k M) -> linearly_dependent M.
Proof. intros n m k M H H0.
  unfold submatrix_column in H0.
  unfold linearly_dependent in *.
  destruct H0 as [a [H0 [H1 H2]]].
  exists (fun r c => if (r <? k) then a r c else 0%G).
  split.
  - unfold WF_GenMatrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H1.
    rewrite H0; trivial.
    lia.
  - split.
    + pose (nonzero_vec_nonzero_elem a H0 H1) as H3.
      destruct H3 as [x H3].
      intro.
      apply f_equal_inv with (x := x) in H4.
      apply f_equal_inv with (x := 0%nat) in H4.
      bdestruct (x <? k)%nat.
      * contradiction.
      * unfold WF_GenMatrix in H1.
        rewrite H0 in H3.
        -- contradiction.
        -- lia.
    + rewrite <- H2.
      unfold GMmult.
      prep_genmatrix_equality.
      replace m with (k + (m - k))%nat by lia.
      rewrite @big_sum_sum with (H := R0) (m := k) (n := (m - k)%nat).
      simpl.
      rewrite <- Gplus_0_r with (g := Σ (fun y0 : nat => (if y0 <? k then M x y0 else 0) * a y0 y) k).
      f_equal.
      * apply big_sum_eq_bounded.
        intros.
        bdestruct_all.
        reflexivity.
      * rewrite big_sum_0_bounded; trivial.
        intros.
        bdestruct_all.
        ring.
Qed.

Lemma some_zero_vector_linearly_dependent : forall {n m : nat} (M : GenMatrix n m),
    ~ (forall i : nat, (i < m)%nat -> get_col M i <> Zero) -> linearly_dependent M.
Proof. intros n m M H.
  apply Classical_Pred_Type.not_all_ex_not in H.
  destruct H as [k H ].
  apply Classical_Prop.imply_to_and in H.
  destruct H.
  unfold "~", "<>" in H0.
  rewrite Decidable.not_not_iff in H0.
  2 : { unfold Decidable.decidable.
        apply (Classical_Prop.classic (get_col M k = Zero)). }
  unfold linearly_dependent.
  exists (e_i k).
  split; auto with wf_db.
  split.
  - intro.
    unfold e_i in H1.
    apply f_equal_inv with (x := k) in H1.
    apply f_equal_inv with (x := 0%nat) in H1.
    assert ((k =? k)%nat && (k <? m) && (0 =? 0)%nat = true).
    { bdestruct_all. trivial. }
    rewrite H2 in H1.
    replace (Zero k 0%nat) with 0%G in H1; trivial.
    inversion H1.
    contradict H1.
    apply G1_neq_0.
  - rewrite <- H0.
    rewrite matrix_by_basis; trivial.
Qed.

Lemma submatrix_column_overflow : forall {n m : nat} (k : nat) (M : GenMatrix n m),
    WF_GenMatrix M -> (k >= m)%nat -> submatrix_column k M = M.
Proof. intros n m k M H0 H1.
  unfold submatrix_column.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
  unfold WF_GenMatrix in H0.
  rewrite H0; trivial; lia.
Qed.

Lemma get_col_submatrix_column : forall {n m : nat} (i k : nat) (M : GenMatrix n m),
    (i < k)%nat -> get_col (submatrix_column k M) i = get_col M i.
Proof. intros n m i0 k M H0.
  unfold submatrix_column.
  unfold get_col.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma get_col_col_insert_front_front : forall {n m : nat} (i : nat) (M : GenMatrix n m) (v : GenVector n),
    WF_GenMatrix v -> (i = 0%nat) -> get_col (col_insert_front M v) i = v.
Proof. intros n m i0 M v H0 H1.
  unfold get_col, col_insert_front.
  prep_genmatrix_equality.
  bdestruct_all.
  - subst.
    reflexivity.
  - unfold WF_GenMatrix in H0.
    rewrite H0; trivial.
    lia.
Qed.

Lemma get_col_col_insert_front_back : forall {n m : nat} (i : nat) (M : GenMatrix n m) (v : GenVector n),
    (i <> 0%nat) -> get_col (col_insert_front M v) i = get_col M (i - 1)%nat.
Proof. intros n m i0 M v H0.
  unfold get_col, col_insert_front.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.


Lemma get_col_col_append_front : forall {n m : nat} (i : nat) (M : GenMatrix n m) (v : GenVector n),
    (i < m) -> get_col (col_append M v) i = get_col M i.
Proof. intros n m i0 M v H0.
  unfold get_col, col_append, col_wedge.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma get_col_col_append_back : forall {n m : nat} (i : nat) (M : GenMatrix n m) (v : GenVector n),
    WF_GenMatrix v -> (i = m) -> get_col (col_append M v) i = v.
Proof. intros n m i0 M v H0 H1.
  unfold get_col, col_append, col_wedge.
  prep_genmatrix_equality.
  bdestruct_all.
  - subst.
    reflexivity.
  - unfold WF_GenMatrix in H0.
    rewrite H0; trivial.
    lia.
Qed.

Lemma submatrix_column_col_append : forall {n m : nat} (k : nat) (M : GenMatrix n m) (v : GenVector n),
    (k <= m)%nat -> submatrix_column k (col_append M v) = submatrix_column k M.
Proof. intros n m k M v H0.
  unfold submatrix_column.
  unfold col_append, col_wedge.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_1_get_col : forall {n m : nat} (M : GenMatrix n m),
    submatrix_column 1%nat M = get_col M 0%nat.
Proof. intros n m M.
  unfold submatrix_column, get_col.
  prep_genmatrix_equality.
  bdestruct_all; auto.
Qed.

Lemma span_submatrix_column_span_reduce_col :
  forall {n m : nat} (k i : nat) (M : GenMatrix n (S m)) (v : GenVector n),
    (k <= m)%nat -> (i >= k)%nat -> span (submatrix_column k M) v -> span (reduce_col M i) v.
Proof. intros n m k i0 M v H0 H1 H2.
  unfold span in *.
  destruct H2 as [a [H2 H3]].
  exists (fun r c => if (r <? k)%nat then a r c else 0%G).
  split.
  - unfold WF_GenMatrix.
    intros.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H2.
    rewrite H2; trivial.
    lia.
  - rewrite H3.
    unfold submatrix_column, reduce_col.
    unfold GMmult.
    prep_genmatrix_equality.
    replace m with (k + (m - k))%nat by lia.
    rewrite @big_sum_sum with (H := R0).
    rewrite <- Gplus_0_r with (g := Σ (fun y0 : nat => (if y0 <? k then M x y0 else 0) * a y0 y) k).
    simpl.
    f_equal.
    + apply big_sum_eq_bounded.
      intros.
      bdestruct_all.
      reflexivity.
    + rewrite big_sum_0_bounded; trivial.
      intros.
      bdestruct_all; ring.
Qed. 
    

Lemma span_col_insert_front :
  forall {n m : nat} (P : GenVector n -> Prop) (M : GenMatrix n m) (v : GenVector n),
    basis P M -> span M v ->
    (forall u : GenVector n, span M u <-> span (col_insert_front M v) u).
Proof. intros n m P M v H0 H1 u.
  split.
  - intros H2.
    unfold span in *.
    unfold basis in *.
    destruct H0 as [H0 [H0' [H0'' H0''']]].
    destruct H1 as [a [H1 H1']].
    destruct H2 as [b [H2 H2']].
    exists (fun r c => if (r =? 0)%nat then 0%G else b (r - 1)%nat c).
    split.
    + unfold WF_GenMatrix.
      intros x y H3.
      bdestruct_all; trivial.
      unfold WF_GenMatrix in H2.
      rewrite H2; trivial.
      lia.
    + rewrite H2'.
      unfold col_insert_front, GMmult.
      prep_genmatrix_equality.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      rewrite Gmult_0_r, Gplus_0_l.
      apply big_sum_eq_bounded.
      intros x0 H4.
      bdestruct_all.
      replace (S x0 - 1)%nat with x0 by lia.
      reflexivity.
  - intros H2. 
    unfold span in *.
    unfold basis in *.
    destruct H0 as [H0 [H0' [H0'' H0''']]].
    destruct H1 as [a [H1 H1']].
    destruct H2 as [b [H2 H2']].
    exists (fun r c => (b 0%nat c) * (a r 0%nat) + (b (r + 1)%nat c)).
    split.
    + unfold WF_GenMatrix in *.
      intros x y H3.
      destruct H3.
      * rewrite H1; try lia.
        setoid_rewrite H2 at 2; try lia.
        ring.
      * setoid_rewrite H2; try lia.
        ring.
    + rewrite H2'.
      unfold col_insert_front, GMmult.
      prep_genmatrix_equality.
      rewrite <- big_sum_extend_l.
      bdestruct_all.
      rewrite H1'.
      unfold GMmult.
      simpl.
      rewrite @big_sum_mult_r with (H2 := R3).
      rewrite <- @big_sum_plus with (H0 := R1).
      2 : apply R2.
      apply big_sum_eq_bounded.
      intros x0 H4.
      simpl.
      replace (x0 - 0)%nat with x0 by lia.
      replace (x0 + 1)%nat with (S x0) by lia.
      ring.
Qed.


 Lemma span_col_append :
  forall {n m : nat} (P : GenVector n -> Prop) (M : GenMatrix n m) (v : GenVector n),
    basis P M -> span M v ->
    (forall u : GenVector n, span M u <-> span (col_append M v) u).
 Proof. intros n m P M v H0 H1 u.
   split.
   - intros H2.
     unfold span in *.
     unfold basis in *.
     destruct H0 as [H0 [H0' [H0'' H0''']]].
     destruct H1 as [a [H1 H1']].
     destruct H2 as [b [H2 H2']].
     exists (fun r c => if (r <? m)%nat then b r c else 0%G).
     split.
     + unfold WF_GenMatrix.
       intros x y H3.
       bdestruct_all; trivial.
       unfold WF_GenMatrix in H2.
       rewrite H2; trivial.
       lia.
     + rewrite H2'.
       unfold col_append, col_wedge, GMmult.
       prep_genmatrix_equality.
       simpl.
       bdestruct_all.
       rewrite Gmult_0_r, Gplus_0_r.
       apply big_sum_eq_bounded.
       intros x0 H5.
       bdestruct_all.
       reflexivity.
   - intros H2.
     unfold span in *.
     unfold basis in *.
     destruct H0 as [H0 [H0' [H0'' H0''']]].
     destruct H1 as [a [H1 H1']].
     destruct H2 as [b [H2 H2']].
     exists (fun r c => if (r <? m) then (b m c) * (a r 0%nat) + (b r c) else 0%G).
     split.
     + unfold WF_GenMatrix.
       intros x y H3.
       bdestruct_all; trivial.
       unfold WF_GenMatrix in *.
       rewrite ! H2; try lia.
       ring.
     + rewrite H2'.
       unfold col_append, col_wedge, GMmult.
       prep_genmatrix_equality.
       simpl.
       bdestruct_all.
       rewrite H1'.
       unfold GMmult.
       rewrite @big_sum_mult_r with (H2 := R3).
       rewrite <- @big_sum_plus with (H0 := R1).
       2 : apply R2.
       apply big_sum_eq_bounded.
       intros x0 H4.
       bdestruct_all.
       ring.
 Qed.

 Lemma get_col_reduce_col_back : forall {n m : nat} (i col : nat) (A : GenMatrix n (S m)),
     (i >= col)%nat -> get_col (reduce_col A col) i = get_col A (1 + i)%nat.
 Proof. intros n m i0 col A H0.
   unfold get_col, reduce_col.
   prep_genmatrix_equality.
   bdestruct_all; reflexivity.
 Qed.

 Lemma get_col_overflow : forall {n m : nat} (k : nat) (A : GenMatrix n m),
    (k >= m)%nat -> WF_GenMatrix A -> get_col A k = Zero.
Proof. intros n m k A H0 H1.
  prep_genmatrix_equality.
  unfold get_col.
  bdestruct_all; trivial.
  unfold WF_GenMatrix in H1.
  rewrite H1; trivial; lia.
Qed.



Lemma submatrix_column_zero : forall {n m : nat} (A : GenMatrix n m),
    submatrix_column 0 A = @Zero n 0.
Proof. intros n m A.
  unfold submatrix_column.
  prep_genmatrix_equality.
  bdestruct_all.
  reflexivity.
Qed.

Lemma get_col_smash_left : forall {n m o : nat} (i : nat) (A : GenMatrix n m) (B : GenMatrix n o),
    (i < m)%nat -> get_col (smash A B) i = get_col A i.
Proof. intros n m o i0 A B H0.
  unfold smash, get_col.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma get_col_smash_right : forall {n m o : nat} (i : nat) (A : GenMatrix n m) (B : GenMatrix n o),
    (i >= m)%nat -> get_col (smash A B) i = get_col B (i - m).
Proof. intros n m o i0 A B H0.
  unfold smash, get_col.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma get_col_matrix_column_choose : forall {n m : nat} (i d : nat) (indices_list : list nat) (A : GenMatrix n m),
    (i < length indices_list)%nat -> WF_GenMatrix A ->
    get_col (matrix_column_choose indices_list A) i = get_col A (nth i indices_list d).
Proof. intros n m i0 d indices_list A H H1. 
  unfold get_col, matrix_column_choose, list_vector_to_matrix.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
  assert (@Zero n 1 = get_col A m).
  { unfold get_col.
    prep_genmatrix_equality.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H1.
    rewrite H1; trivial.
    lia. }
  rewrite H2.
  rewrite map_nth with (d := m).
  unfold get_col.
  bdestruct_all.
  rewrite nth_indep with (d := d) (d' := m); trivial.
Qed.

Lemma submatrix_column_smash_left : forall {n m o : nat} (k : nat) (A : GenMatrix n m) (B : GenMatrix n o),
    (k <= m)%nat -> submatrix_column k (smash A B) = submatrix_column k A.
Proof. intros n m o k A B H0.
  unfold smash, submatrix_column.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_smash_right : forall {n m o : nat} (k : nat) (A : GenMatrix n m) (B : GenMatrix n o),
    (k > m)%nat -> submatrix_column k (smash A B) = smash A (submatrix_column (k - m) B).
Proof. intros n m o k A B H0.
  unfold smash, submatrix_column.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma submatrix_column_original : forall {n m : nat} (k : nat) (A : GenMatrix n m),
    WF_GenMatrix A -> (k >= m)%nat -> submatrix_column k A = A.
Proof. intros n m k A H0 H1.
  unfold submatrix_column.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
  unfold WF_GenMatrix in H0.
  rewrite H0; trivial; lia.
Qed.

Lemma get_col_submatrix_column_linearly_dependent : forall {n m : nat} (k : nat) (a : GenVector k) (A : GenMatrix n m),
    (k < m)%nat -> get_col A k = (submatrix_column k A) × a -> linearly_dependent A.
Proof. intros n m k a A H H0.
  unfold linearly_dependent.
  exists (fun r c => if (r <? k)%nat then (if (c =? 0)%nat then a r c else 0%G)
             else if (r =? k)%nat then (if (c =? 0)%nat then (- 1%G) else 0%G)
                  else 0%G).
  repeat split.
  - unfold WF_GenMatrix.
    intros x y H1.
    bdestruct_all; trivial.
  - intro.
    apply f_equal_inv with (x := k) in H1.
    apply f_equal_inv with (x := 0%nat) in H1.
    simpl in H1.
    rewrite Nat.ltb_irrefl in H1.
    rewrite Nat.eqb_refl in H1.
    unfold Zero in H1.
    contradict H1.
    apply Gneg1_neq_0.
  - unfold GMmult.
    prep_genmatrix_equality.
    replace (@Zero n 1 x y) with 0%G by easy.
    replace m with (k + (1 + (m - k - 1)))%nat by lia.
    rewrite big_sum_sum with (m := k).
    rewrite big_sum_sum with (m := 1%nat).
    simpl.
    rewrite Gplus_0_l.
    bdestruct_all.
    + assert (forall x y z : F, x + z = y -> x + (y * (- 1%G) + z) = 0).
      { intros x0 y0 z H4.
        rewrite <- H4.
        ring. }
      apply H4.
      replace (k + 0)%nat with k by lia.
      unfold get_col in H0.
      apply f_equal_inv with (x := x) in H0.
      apply f_equal_inv with (x := 0%nat) in H0.
      simpl in H0.
      rewrite H0.
      unfold submatrix_column, GMmult.
      rewrite <- Gplus_0_r.
      f_equal.
      * apply big_sum_eq_bounded.
        intros x0 H5.
        bdestruct_all.
        subst.
        reflexivity.
      * rewrite big_sum_0_bounded; trivial.
        intros x0 H5.
        bdestruct_all.
        ring.
    + rewrite Gmult_0_r, Gplus_0_l.
      rewrite <- Gplus_0_r.
      f_equal.
      * rewrite big_sum_0_bounded; trivial.
        intros x0 H4.
        bdestruct_all.
        ring.
      * rewrite big_sum_0_bounded; trivial.
        intros x0 H4.
        bdestruct_all.
        ring.
Qed.
    
Lemma reduce_col_smash_left : forall {n m o : nat} (k : nat) (A : GenMatrix n (S m)) (B : GenMatrix n o),
    (k <= m)%nat -> reduce_col (smash A B) k = smash (reduce_col A k) B.
Proof. intros n m o k A B H0.
  unfold smash, reduce_col.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Lemma reduce_col_smash_right : forall {n m o : nat} (k : nat) (A : GenMatrix n m) (B : GenMatrix n (S o)),
    (k >= m)%nat -> reduce_col (smash A B) k = smash A (reduce_col B (k - m)).
Proof. intros n m o k A B H0.
  unfold smash, reduce_col.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
  replace (1 + (y - m))%nat with (1 + y - m)%nat by lia.
  reflexivity.
Qed.

Lemma reduce_col_submatrix_column_last : forall {n m : nat} (j : nat) (A : GenMatrix n m),
    reduce_col (submatrix_column (S j) A) j = submatrix_column j A.
Proof. intros n m j A.
  unfold submatrix_column, reduce_col.
  prep_genmatrix_equality.
  bdestruct_all; trivial.
Qed.

Definition delete_nth {A : Type} (l : list A) (n : nat) := firstn n l ++ skipn (n + 1) l.
Compute (delete_nth [0; 1; 2; 3]%nat 0). (* = [1; 2; 3]%nat *)
Compute (delete_nth [0; 1; 2; 3]%nat 1). (* = [0; 2; 3]%nat *)

Lemma reduce_col_matrix_column_choose_delete : forall {n m : nat} (k : nat) (indices_list : list nat) (A : GenMatrix n m),
    WF_GenMatrix A -> (length indices_list > k)%nat->
    reduce_col (matrix_column_choose indices_list A) k = matrix_column_choose (delete_nth indices_list k) A.
Proof. intros n m k indices_list A H H0. 
  unfold reduce_col, delete_nth, matrix_column_choose, list_vector_to_matrix.
  prep_genmatrix_equality.
  assert (@Zero n 1 = get_col A m).
  { unfold get_col.
    prep_genmatrix_equality.
    bdestruct_all; trivial.
    unfold WF_GenMatrix in H.
    rewrite H; trivial; lia. }
  bdestruct_all.
  - rewrite <- firstn_skipn with (n := k) (l := indices_list) at 1.
    rewrite ! H1.
    rewrite ! map_nth with (d := m).
    unfold get_col.
    bdestruct_all.
    f_equal.
    rewrite ! app_nth1; trivial; rewrite firstn_length; lia.
  - rewrite H1.
    rewrite ! map_nth with (d := m).
    unfold get_col.
    bdestruct_all.
    f_equal.
    rewrite app_nth2.
    + rewrite firstn_length.
      replace (Init.Nat.min k (length indices_list)) with k by lia.
      rewrite <- firstn_skipn with (n := (k + 1)%nat) at 1.
      rewrite app_nth2.
      * rewrite firstn_length.
        replace (Init.Nat.min (k + 1) (length indices_list)) with (k + 1)%nat by lia.
        f_equal.
        lia.
      * rewrite firstn_length.
        lia.
    + rewrite firstn_length.
      lia.
Qed.

Lemma length_delete_nth : forall {A : Type} (l : list A) (k : nat),
    (k < length l)%nat -> length (delete_nth l k) = ((length l) - 1)%nat.
Proof. intros A l k H0. 
  unfold delete_nth.
  rewrite app_length.
  rewrite firstn_length.
  rewrite skipn_length.
  lia.
Qed.

Lemma incl_firstn_next : forall {A : Type} (l : list A) (k : nat),
    incl (firstn k l) (firstn (S k) l).
Proof. unfold incl.
  intros A l k a H.
  gen l.
  induction k.
  - intros.
    simpl in H.
    contradiction.
  - intros.
    destruct l.
    + inversion H.
    + simpl in H.
      destruct H.
      * simpl.
        auto.
      * right.
        auto.
Qed.

Lemma incl_skipn_previous : forall {A : Type} (l : list A) (k : nat),
    incl (skipn (S k) l) (skipn k l).
Proof. unfold incl.
  intros A l k a H0.
    gen l.
  induction k.
  - intros.
    simpl.
    destruct l.
    + inversion H0.
    + simpl in H0.
      simpl.
      auto.
  - intros. 
    destruct l.
    + inversion H0.
    + simpl.
      apply IHk.
      simpl in H0.
      apply H0.
Qed.

Lemma incl_delete_nth_original : forall {A : Type} (l : list A) (k : nat),
    incl (delete_nth l k) l.
Proof. intros A l k.
  unfold incl, delete_nth.
  intros a H0.
  rewrite in_app_iff in H0.
  destruct H0 as [H0 | H0].
  - induction l.
    + rewrite firstn_nil in H0.
      assumption.
    + destruct k.
      * simpl in *.
        contradiction.
      * rewrite firstn_cons in H0.
        simpl in H0.
        simpl.
        destruct H0.
        -- left; assumption.
        -- right.
           apply IHl.
           apply incl_firstn_next; trivial.
  - induction k.
    + replace l with (skipn 0%nat l) by easy.
      apply incl_skipn_previous.
      assumption.
    + apply IHk.
      apply incl_skipn_previous.
      assumption.
Qed.

Lemma incl_delete_nth : forall {A : Type} (l l' : list A) (k : nat),
    incl l l' -> incl (delete_nth l k) l'.
Proof. intros A l l' k H0.
  apply (incl_tran (incl_delete_nth_original l k)) in H0.
  assumption.
Qed.

Lemma matrix_column_choose_empty : forall {n m : nat} (A : GenMatrix n m),
    matrix_column_choose [] A = Zero.
Proof. intros n m A.
  unfold matrix_column_choose, list_vector_to_matrix.
  prep_genmatrix_equality.
  simpl.
  destruct y; auto.
Qed.


 (** separate lemma of invariant for Theorem 34 *)
Lemma invariant_span : forall {n m o : nat} (P : GenVector n -> Prop) (M : GenMatrix n m) (A : GenMatrix n o),
    WF_GenMatrix M -> WF_GenMatrix A -> basis P M ->
    (forall i : nat, (i < o)%nat -> P (get_col A i)) -> (o > m)%nat ->
    (forall i : nat, (i < m)%nat -> get_col M i <> Zero) ->
    (forall i : nat, (i < o)%nat -> get_col A i <> Zero) ->
    forall j , (j <= m)%nat ->
          (linearly_dependent (submatrix_column j A) \/
             (exists indices_list : list nat,
                 length indices_list = (m - j)%nat /\
                   incl indices_list (List.seq 0 m) /\
                   (forall v : GenVector n,
                       span M v <->
                         (span
                            (smash
                               (submatrix_column j A)
                               (matrix_column_choose indices_list M))
                            v)))).
Proof. intros n m o P M A H0 H1 H2 H3 H4 nonzero_col_M nonzero_col_A  j H5.
  induction j.
  - right.
    exists (List.seq 0 m).
    split.
    + rewrite seq_length. lia.
    + split.
      * unfold incl.
        intros a H6.
        assumption.
      * intros v.
        -- assert (H7 : submatrix_column 0 A = @Zero n 0).
           { apply submatrix_column_zero. }
           rewrite H7.
           assert (H8 : matrix_column_choose (List.seq 0 m) M = M).
           { apply matrix_column_choose_original.
             assumption. }
           rewrite H8.
           assert (H9 : smash (@Zero n 0) M = M).
           { prep_genmatrix_equality.
             unfold smash.
             bdestruct_all.
             replace (y - 0)%nat with y by lia.
             reflexivity. }
           rewrite seq_length.
           rewrite H9.
           split; auto.
  - assert (H6 : (j <= m)%nat). { lia. }
    specialize (IHj H6).
    destruct IHj as [H7 | H7].
    + left.
      assert (H8 : submatrix_column j A = submatrix_column j (submatrix_column (S j) A)).
      { rewrite subsubmatrix_column_inner; auto. }
      rewrite H8 in H7.
      apply linearly_dependent_submatrix_column in H7; auto.
    + destruct H7 as [indices_list [length_indices_list [incl_indices_list eq_span]]].
      assert (H7 : WF_GenMatrix (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M))).
      { auto with wf_db. }
      assert (H8 : forall i : nat, (i < S m)%nat ->
                       get_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M))  i <> @Zero n (S m)).
      { intros i0 H8.
        bdestruct (i0 <? S j).
        - rewrite get_col_smash_left; try lia.
          rewrite get_col_submatrix_column; try lia.
          apply nonzero_col_A; lia.
        - rewrite get_col_smash_right; try lia.
          rewrite get_col_matrix_column_choose with (d := 0%nat); trivial; try lia.
          apply nonzero_col_M.
          assert (H10 : In (nth (i0 - S j) indices_list 0%nat) indices_list). { apply nth_In; lia. }
          apply incl_indices_list in H10.
          rewrite in_seq in H10.
          lia. }
      assert (H9 : linearly_dependent
                (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M))).
      { unfold linearly_dependent.
        assert (H9 : span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) (get_col A j)).
        { rewrite <- eq_span.
          unfold basis in H2.
          destruct H2 as [subspaceP [MinP [MspansP lin_indep_m]]].
          apply MspansP.
          apply H3.
          lia. }
        unfold span in H9.
        destruct H9 as [a [WFa H9]].
        exists (fun r c => if (r <? j)%nat then a r c else
                     if (r =? j)%nat then
                       if (c =? 0)%nat then (- 1%G) else 0%G
                     else a (r - 1)%nat c).
        repeat split.
        - unfold WF_GenMatrix.
          intros x y H10.
          unfold WF_GenMatrix in WFa.
          bdestruct_all; trivial.
          + rewrite WFa; trivial; lia.
          + rewrite WFa; trivial; lia.
        - intro H10.
          apply f_equal_inv with (x := j) in H10.
          apply f_equal_inv with (x := 0%nat) in H10.
          simpl in H10.
          rewrite Nat.ltb_irrefl in H10.
          rewrite Nat.eqb_refl in H10.
          unfold Zero in H10.
          contradict H10.
          apply Gneg1_neq_0.
        - unfold smash, submatrix_column, matrix_column_choose, list_vector_to_matrix, GMmult.
          prep_genmatrix_equality.
          replace (@ Zero n 1 x y) with 0%G by easy.
          rewrite length_indices_list.
          replace (S j + (m - j))%nat with ((j) + ((1) + (m - j)))%nat by lia.

          rewrite big_sum_sum with (m := j) (n := (1 + (m - j))%nat).
          rewrite big_sum_sum with (m := 1%nat) (n := (m - j)%nat).
          assert (H10 : forall x y z : F, x + (y + z) = (x + z) + y). { intros. ring. }
          rewrite H10.
          simpl.
          rewrite Gplus_0_l.
          bdestruct_all; trivial.
          + subst.
            clear H10. clear H11. clear H13.  clear H.
            assert (H10 : forall x y z : F, x + y = z -> (x + y) + z * (- 1%G) = 0%G).
            { intros.
              rewrite H.
              ring. }
            apply H10.
            replace (j + 0)%nat with j by lia.
            apply f_equal_inv with (x := x) in H9.
            apply f_equal_inv with (x := 0%nat) in H9.
            unfold get_col in H9.
            simpl in H9.
            rewrite H9.
            unfold smash, submatrix_column, matrix_column_choose, list_vector_to_matrix, GMmult.
            rewrite length_indices_list.
            rewrite big_sum_sum with (m := j) (n := (m - j)%nat).
            simpl.
            f_equal.
            * apply big_sum_eq_bounded.
              intros x0 H11.
              bdestruct_all.
              reflexivity.
            * apply big_sum_eq_bounded.
              intros x0 H11.
              bdestruct_all.
              replace (j + S x0 - S j)%nat with x0 by lia.
              replace (j + x0 - j)%nat with x0 by lia.
              replace (j + S x0 - 1)%nat with (j + x0)%nat by lia.
              reflexivity.
          + unfold WF_GenMatrix in WFa.
            rewrite Gmult_0_r, Gplus_0_r.
            rewrite <- Gplus_0_r.
            f_equal.
            * rewrite big_sum_0_bounded; trivial.
              intros x0 H15.
              bdestruct_all.
              rewrite WFa; trivial.
              -- ring.
              -- lia.
            * rewrite big_sum_0_bounded; trivial.
              intros x0 H15.
              bdestruct_all.
              rewrite WFa; trivial.
              -- ring.
              -- lia. }
      
      assert (H10 : (S m = S j + length indices_list)%nat).
      { rewrite length_indices_list. rewrite <- Nat.add_1_r. lia. }
      rewrite H10 in H8.
      pose (linearly_dependent_bounded_linear_combination
              (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M))
              H7 H8 H9) as H11.
      destruct H11 as [k [H11 [a [WFa H12]]]].
(* split k into two cases: 
1. when k corresponds to (submatrix_column (s j) A)
2. when k corresponds to (matrix_column_choose indices_list M)
bdestruct (k <? s j). *)
      bdestruct (k <? S j).
      * (* For case 1: k < s j *)
        (* We can get "get_col k (submatrix_column (s j) A)
           = (submatrix_column k (submatrix_column (s j) A)) × a" *)
        rewrite get_col_smash_left in H12; try lia.
        rewrite submatrix_column_smash_left in H12; try lia.
        (* Prove that  (submatrix_column (s j) A) is linearly_dependent by proving a separate lemma "get_col k A = (submatrix_column k A) × a -> linearly_dependent A" then substitute A with (submatrix_column (s j) A) to get "linearly_dependent (submatrix_column (s j) A)" *)
        apply get_col_submatrix_column_linearly_dependent with (k := k) (a := a) (A := (submatrix_column (S j) A)) in H12; auto.
      * (* For case 2: k >= s j *)
        (* We prove the assertion "span (submatrix_column k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M))) (get_col k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        assert (H14 : span (submatrix_column k (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M))) (get_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) k)).
        { unfold span.
          exists a.
          auto. }
        (* Then, by using "span_submatrix_column_span_reduce_col" we prove the assertion "span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) (get_col k (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        apply span_submatrix_column_span_reduce_col with (i := k) in H14; auto.
        2: { rewrite length_indices_list.
             assert (k <= j + (m - j))%nat; trivial; lia. }
        (* Then, by using "equal_span_reduce_col" and "equal_span_reduce_col_inv" we can prove the assertion "∀ u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u <-> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) u" *)
        assert (H15 : forall u, span (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) u <-> span (reduce_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) k) u).
        { intros u.
          split.
          - intros H15.
            apply equal_span_reduce_col; trivial.
            rewrite length_indices_list.
            assert (k < S (j + (m - j)))%nat; trivial; lia.
          - intros H15.
            apply equal_span_reduce_col_inv with (i := k); trivial.
            rewrite length_indices_list.
            assert (k < S (j + (m - j)))%nat; trivial; lia. }
        (* We can directly prove the assertion "∀ u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u -> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u" *)
        assert (H16 : forall u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u -> span (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) u).
        { intros u H16.
          unfold span.
          unfold span in H16.
          rewrite length_indices_list in *.
          replace (j + (m - j))%nat with m in H16 by lia.
          replace (S j + (m - j))%nat with (S m) by lia.
          destruct H16 as [b [WFb H16]].
          exists (fun r c => if (r <? j)%nat then b r c else if (r =? j)%nat then 0%G else b (r - 1)%nat c).
          split.
          - unfold WF_GenMatrix.
            intros x y H17.
            bdestruct_all; trivial.
            assert (y >= 1)%nat; auto; try lia.
            destruct H17; auto.
            assert (x - 1 >= m)%nat; auto; lia.
          - rewrite H16.
            unfold smash, GMmult, submatrix_column.
            prep_genmatrix_equality.
            replace m with (j + (m - j))%nat at 1 by lia.
            rewrite big_sum_sum with (m := j) (n := (m - j)%nat) at 1.
            replace (S m) with (j + ((S m) - j))%nat at 1 by lia.
            rewrite big_sum_sum with (m := j) (n := ((S m) - j)%nat) at 1.
            f_equal.
            + apply big_sum_eq_bounded.
              intros x0 H17.
              bdestruct_all; trivial.
            + replace (S m - j)%nat with (1 + (m - j))%nat at 1 by lia.
              rewrite big_sum_sum with (m := 1%nat) (n := (m - j)%nat) at 1.
              simpl.
              rewrite ! Gplus_0_l.
              rewrite <- Gplus_0_l at 1.
              f_equal.
              * bdestruct_all.
                ring.
              * apply big_sum_eq_bounded.
                intros x0 H17.
                bdestruct_all.
                replace (j + x0 - j)%nat with x0 by lia.
                replace (j + S x0 - S j)%nat with x0 by lia.
                replace (j + S x0 - 1)%nat with (j + x0)%nat by lia.
                reflexivity. }
        (* Using "forall i : nat, (i < o)%nat -> P (get_col i A)" and "basis P M" and "∀ v, span M v <-> span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) v" and by proving the assertion "get_col j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) = get_col j A" we can prove the assertion "span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) (get_col j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        assert (H17 : span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) (get_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) j)).
        { rewrite get_col_smash_left; try lia.
          rewrite get_col_submatrix_column; try lia.
          rewrite <- eq_span.
          unfold basis in H2.
          destruct H2 as [subspaceP [MinP [MspansP lin_indep_M]]].
          apply MspansP.
          apply H3.
          lia. }
        (* By proving a separate general lemma "k <= size of A -> reduce_col (smash A B) k = smash (reduce_col A k) B" and by proving a separate lemma "reduce_col (submatrix_column (s j) A) j = submatrix_column j A", we can prove the assertion "smash (submatrix_column j A) (matrix_column_choose indices_list M) = reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j" *)
        assert (H18 : smash (submatrix_column j A) (matrix_column_choose indices_list M) = reduce_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) j).
        { rewrite reduce_col_smash_left, reduce_col_submatrix_column_last; trivial. }
        (* By combining the above assertions, we can get the assertion "span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j) (get_col j (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)))" *)
        rewrite H18 in H17.
        (* By using the lemma "equal_span_reduce_col", we can get the assertion "∀ u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u -> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) j) u" *)
        assert (H19 : forall u, span (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) u -> span (reduce_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) j) u).
        { intros u H19.
          apply equal_span_reduce_col; trivial.
          rewrite length_indices_list.
          assert (j < 1 + (j + (m - j)))%nat; trivial; lia. }
        (* By combining the above assertions, we can get the assertion "∀ u, span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u -> span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u" *)
        rewrite <- H18 in H19.
        (* Thus, we get the assertion "∀ u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u" *)
        assert (H20 : forall u, span (smash (submatrix_column j A) (matrix_column_choose indices_list M)) u <-> span (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) u).
        { intros u.
          split; auto. }
        (* We can now obtain the assertion "∀ u, span M u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) u" *)
        assert (H21 : forall u, span M u <-> span (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) u).
        { intros u.
          split.
          - intros H21.
            rewrite <- H20, <- eq_span; trivial.
          - intros H21.
            rewrite eq_span, H20; trivial. }
        (* By using the above assertions, we can obtain the assertion "∀ u, span M u <-> span (reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k) u" *)
        assert (H22 : forall u, span M u <-> span (reduce_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) k) u).
        { intros u.
          split.
          - intros H22.
            rewrite <- H15, <- H21; trivial.
          - intros H22.
            rewrite H21, H15; trivial. }
        (* We need to show that "reduce_col (smash (submatrix_column (s j) A) (matrix_column_choose indices_list M)) k = smash (submatrix_column (s j) A) (reduce_col (matrix_column_choose indices_list M) (k - # around (s j)))". We can do this by proving a separate general lemma "k > size of A -> reduce_col (smash A B) k = smash A (reduce_col B (k - size of A))" *)
        assert (H23 : reduce_col (smash (submatrix_column (S j) A) (matrix_column_choose indices_list M)) k = @smash n (S j) (m - j - 1)%nat (submatrix_column (S j) A) (reduce_col (matrix_column_choose indices_list M) (k - (S j)))).
        { rewrite ! length_indices_list.
          replace (Init.Nat.sub m j) with (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O))) by lia.
          replace ((fix add (n0 m0 : nat) {struct n0} : nat :=
           match n0 return nat with
           | O => m0
           | Datatypes.S p => Datatypes.S (add p m0)
           end) j (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O))))
            with
            (Init.Nat.add (Datatypes.S j) (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))
            by (rewrite Nat.add_succ_comm; trivial).
          rewrite reduce_col_smash_right; easy. }
        (* We show that "reduce_col (matrix_column_choose indices_list M) (k - # around (s j)) = matrix_column_choose indices_list0 M". We can do this by proving a separate general lemma "reduce_col (matrix_column_choose indices_list M) k = matrix_column_choose (delete the kth element of indices_list) M". We delete the kth element in "indices_list" to create indices_list0. Define : firstn n l ++ skipn (n + 1) l  <- ??? try to compute on a concrete sequence *)
        setoid_rewrite reduce_col_matrix_column_choose_delete with (k := (k - S j)%nat) in H23; trivial; try lia.
        (* Using the above, we obtain the assertion "∀ u, span M u <-> span (smash (submatrix_column (s j) A) (matrix_column_choose indices_list0 M)) u" *)
        rewrite H23 in H22.
        (* Additionally, we need to show "length indices_list0 = (m - s j)%nat" and "incl indices_list0 (List.seq 0 m)". You might need to prove separate additional lemmas about lists to prove these. *)
        right.
        exists (delete_nth indices_list (k - S j)%nat).
        split.
        -- rewrite length_delete_nth, length_indices_list; lia.
        -- split.
           ++ apply incl_delete_nth; trivial.
           ++ intros v.
              split.
              ** intros H24.
                 rewrite length_delete_nth; try lia.
                 assert (H25 : (Init.Nat.add (Datatypes.S j)
                            (Init.Nat.sub (@length nat indices_list) (Datatypes.S O)))
                         =
                           ((fix add (n m : nat) {struct n} : nat :=
                               match n return nat with
                               | O => m
                               | Datatypes.S p => Datatypes.S (add p m)
                               end) j (@length nat indices_list))).
                 { rewrite length_indices_list, Nat.add_succ_comm.
                   replace (Init.Nat.add j (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))) with m by lia.
                   replace ((fix add (n0 m0 : nat) {struct n0} : nat :=
                               match n0 return nat with
                               | O => m0
                               | Datatypes.S p => Datatypes.S (add p m0)
                               end) j (Init.Nat.sub m j))
                     with
                     (Init.Nat.add j (Init.Nat.sub m j))
                     by trivial.
                   lia. }
                 rewrite H25.
                 rewrite <- H22.
                 assumption.
              ** intros H24.
                 rewrite H22.
                 rewrite length_delete_nth, length_indices_list in H24; try lia.
                 rewrite length_indices_list.
                 assert (H25 : (Init.Nat.add (Datatypes.S j)
                                  (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))
                               =
                                 ((fix add (n m : nat) {struct n} : nat :=
                                     match n return nat with
                                     | O => m
                                     | Datatypes.S p => Datatypes.S (add p m)
                                     end) j (Init.Nat.sub m j))).
                 { rewrite Nat.add_succ_comm.
                   replace (Init.Nat.add j (Datatypes.S (Init.Nat.sub (Init.Nat.sub m j) (Datatypes.S O)))) with m by lia.
                   replace ((fix add (n0 m0 : nat) {struct n0} : nat :=
                               match n0 return nat with
                               | O => m0
                               | Datatypes.S p => Datatypes.S (add p m0)
                               end) j (Init.Nat.sub m j))
                     with
                     (Init.Nat.add j (Init.Nat.sub m j))
                     by trivial.
                   lia. }
                 rewrite H25 in H24.
                 assumption.
Qed.

Lemma invariant_span_final_step : forall {n m o : nat} (P : GenVector n -> Prop) (M : GenMatrix n m) (A : GenMatrix n o),
    WF_GenMatrix M -> WF_GenMatrix A -> basis P M ->
    (forall i : nat, (i < o)%nat -> P (get_col A i)) -> (o > m)%nat ->
    (forall v : GenVector n, span M v <-> span (submatrix_column m A) v) -> linearly_dependent A.
Proof. intros n m o P M A H0 H1 H2 H3 H4 H5.
  (** Show that the m+1 th column (get_col m A) of A is a linear combination of (submatrix_column m A): (span (submatrix_column m A) (get_col m A)) **)
  unfold basis in H2.
  destruct H2 as [subspaceP [MinP [MspansP lin_indep_M]]].
  specialize (H3 m H4).
  specialize (MspansP (get_col A m) H3).
  rewrite H5 in MspansP.
  unfold span in MspansP.
  destruct MspansP as [a [WFa H6]].
  (** Use the lemma "get_col_submatrix_column_linearly_dependent" to show (linearly_dependent A) **)
  apply (get_col_submatrix_column_linearly_dependent m a A H4 H6).
Qed.


(** Theorem 34 Let V be a finite-dimensional vector space over a field F, and let {u1,u2,...,um} be a basis for V. If v1,v2,...,vn are any n vectors in V, with n > m, then {v1, v2, . . . , vn} is linearly dependent. **)
Lemma dimension_overflow : forall {n m o : nat} (P : GenVector n -> Prop) (M : GenMatrix n m) (A : GenMatrix n o),
    WF_GenMatrix M -> WF_GenMatrix A ->
    basis P M -> (forall i : nat, (i < o)%nat -> P (get_col A i)) -> (o > m)%nat -> linearly_dependent A.
Proof. intros n m o P M A WFM WFA basisM AinP overflow.
  destruct (Classical_Prop.classic (forall i : nat, (i < m)%nat -> get_col M i <> Zero)) as [M_nonzero_cols | M_some_zero_cols].
  2 : { apply some_zero_vector_linearly_dependent in M_some_zero_cols.
        unfold basis in basisM.
        destruct basisM as [subspaceP [MinP [MspansP lin_indep_M]]].
        apply lindep_implies_not_linindep in M_some_zero_cols.
        contradiction. }  
  destruct (Classical_Prop.classic (forall i : nat, (i < o)%nat -> get_col A i <> Zero)) as [A_nonzero_cols | A_some_zero_cols].
  2 : { apply some_zero_vector_linearly_dependent in A_some_zero_cols.
        assumption. }
  remember basisM as basisM'. clear HeqbasisM'.
  unfold basis in basisM'.
  destruct basisM' as [subspaceP [MinP [MspansP lin_indep_M]]].
  assert (m_leq_m : (m <= m)%nat); auto.
  destruct (invariant_span P M A WFM WFA basisM AinP overflow M_nonzero_cols A_nonzero_cols m m_leq_m) as [lin_dep_A_m | [indices_list [length_indices_list [incl_indices_list_seq eq_span]]]].
  - apply linearly_dependent_submatrix_column in lin_dep_A_m; assumption.
  - replace (m - m)%nat with 0%nat in length_indices_list by lia.
    rewrite length_zero_iff_nil in length_indices_list.
    rewrite length_indices_list in eq_span.
    rewrite matrix_column_choose_empty in eq_span.
    rewrite smash_zero in eq_span; auto with wf_db.
    simpl in eq_span.
    rewrite Nat.add_0_r in eq_span.
    apply (invariant_span_final_step P M A WFM WFA basisM AinP overflow eq_span).
Qed.


(* Corollary 35 Let V be a vector space over a field F, and let {u1,u2,...,un}
and {v1,v2,...,vm} be two bases for V. Then m=n.
Proof Since {u1,u2,...,un} is a basis for V and {v1,v2,...,vm} is linearly independent, Theorem 34 implies that m ≤ n. But the same reasoning implies that n ≤ m, and so m = n must hold. *)
Lemma basis_equal_number : forall {n m o : nat} {P : GenVector n -> Prop} {A : GenMatrix n m} {B : GenMatrix n o},
    WF_GenMatrix A -> WF_GenMatrix B -> basis P A -> basis P B -> m = o.
Proof. intros n m o P A B WFA WFB basisA basisB.
  remember basisA as basisA'. clear HeqbasisA'.
  remember basisB as basisB'. clear HeqbasisB'.
  unfold basis in basisA', basisB'.
  destruct basisA' as [subspaceP [AinP [AspansP lin_indep_A]]].
  destruct basisB' as [subspaceP' [BinP [BspansP lin_indep_B]]].
  bdestruct (o <=? m)%nat.
  - bdestruct (m <=? o)%nat.
    + lia.
    + pose (dimension_overflow P B A WFB WFA basisB AinP H0) as lin_dep_B.
      apply lindep_implies_not_linindep in lin_dep_B.
      contradiction.
  - pose (dimension_overflow P A B WFA WFB basisA BinP H) as lin_dep_B.
    apply lindep_implies_not_linindep in lin_dep_B.
    contradiction.
Qed.

(* Definition 36 Let V be a finite-dimensional vector space. If V is the trivial vector space, then we say that the dimension of V is zero; otherwise, the dimension of V is the number of vectors in a basis for V . *)

Definition dimension {n : nat} (P : GenVector n -> Prop) (d : nat) := exists (A : GenMatrix n d), WF_GenMatrix A /\ basis P A.


Lemma subspace_dimension : forall {n : nat} {P Q : GenVector n -> Prop} {d1 d2 : nat},
    subspace Q -> subspace P -> (forall v, Q v -> P v) -> dimension Q d1  -> dimension P d2 ->
    (d1 <= d2)%nat.
Proof. intros n P Q d1 d2 H0 H1 H2 H3 H4.
  bdestruct (d1 <=? d2)%nat; auto.
  unfold dimension in *.
  destruct H3 as [A1 [WFA1 bA1]].
  destruct H4 as [A2 [WFA2 bA2]].
  unfold basis in bA1.
    destruct bA1 as [sQ [A1inQ [A1spQ indA1]]].
  assert (forall i, (i < d1)%nat -> P (get_col A1 i)).
  { intros i0 H3.
    apply H2.
    apply A1inQ; auto. }
  pose (dimension_overflow P A2 A1 WFA2 WFA1 bA2 H3 H) as H6.
  apply lindep_implies_not_linindep in H6.
  contradiction.
Qed.

Lemma unique_dimension : forall {n d1 d2 : nat} {P : GenVector n -> Prop},
    dimension P d1 -> dimension P d2 -> d1 = d2.
Proof. intros n d1 d2 P H0 H1.
  unfold dimension in *.
  destruct H0 as [A [WFA basisA]].
  destruct H1 as [B [WFB basisB]].
  apply (basis_equal_number WFA WFB basisA basisB).
Qed.

Lemma list_vector_to_matrix_nil : forall n : nat, @list_vector_to_matrix n nil = Zero.
Proof. intros n.
  unfold list_vector_to_matrix.
  prep_genmatrix_equality.
  destruct y; auto.
Qed.


Lemma map_const_repeat : forall {A B : Type} {a : A} {l : list B},
    map (fun x => a) l = repeat a (length l).
Proof. intros A B a l.
  induction l; auto.
  simpl. rewrite IHl.
  reflexivity.
Qed.

Lemma zero_all_zero : forall {n : nat} {a : GenVector n},
    WF_GenMatrix a -> ((forall i, (i < n)%nat -> a i 0%nat = 0%G) <-> a = Zero).
Proof. intros n a H.
  split; intros.
  - prep_genmatrix_equality.
    bdestruct (y <? 1)%nat.
    + replace y with 0%nat by lia.
      bdestruct (x <? n)%nat.
      * rewrite H0; auto.
      * rewrite H; auto; lia.
    + rewrite H; auto; lia.
  - rewrite H0; auto.
Qed.

Lemma repeat_nth : forall {A : Type} {a : A} {l : list A},
    l = repeat a (length l) <-> (forall i, nth i l a = a).
Proof. intros A a l.
  split; intros.
  - rewrite H, nth_repeat; reflexivity.
  - apply nth_ext with (d := a) (d' := a).
    + rewrite repeat_length; auto.
    + intros n H0.
      rewrite H.
      rewrite nth_repeat.
      reflexivity.
Qed.

Lemma permutation_repeat_nth : forall {A : Type} {a : A} {l : list A},
    Permutation l (repeat a (length l)) <-> (forall i, nth i l a = a).
Proof. intros A a l.
  split; intros.
  - rewrite Permutation_nth in H.
    destruct H as [H [f [H0 [H1 H2]]]].
    remember H1 as H3. clear HeqH3.
    rewrite FinFun.bInjective_bSurjective in H3; auto.
    destruct (FinFun.bSurjective_bBijective H0 H3) as [g [H4 H5]].
    bdestruct (i <? length l)%nat.
    + destruct (H5 i H6) as [H7 H8].
      unfold FinFun.bFun in H4.
      specialize (H4 i H6).
      specialize (H2 (g i) H4).
      rewrite H8 in H2.
      rewrite <- H2.
      rewrite nth_repeat.
      reflexivity.
    + rewrite nth_overflow; auto; lia.
  - rewrite <- repeat_nth in H.
    rewrite <- H.
    apply Permutation_refl.
Qed.

Lemma permutation_list_vector_to_matrix_times_vector : forall {n : nat} {l1 l2 : list (GenVector n)},
    Permutation l1 l2 ->
    forall a : GenVector (length l1), WF_GenMatrix a ->
            exists b : GenVector (length l2), WF_GenMatrix b /\
                    (list_vector_to_matrix l1) × a = (list_vector_to_matrix l2) × b /\
                    Permutation (map (fun i => a i 0%nat) (List.seq 0 (length l1))) (map (fun i => b i 0%nat) (List.seq 0 (length l2))).
Proof. intros n l1 l2 H a H0.
  induction H.
  - exists Zero.
    repeat (split; auto with wf_db).
  - assert (@WF_GenMatrix (length l) 1%nat (fun r c => a (r + 1)%nat c)).
    { unfold WF_GenMatrix.
      intros x0 y H1.
      apply Permutation_length in H.
      simpl in *.
      rewrite H0; auto; destruct H1; lia. }
    destruct (IHPermutation (fun r c => a (r + 1)%nat c) H1) as [b [WFb [eqn perm]]].
    exists (fun r c => if (r =? 0)%nat then a 0%nat c else b (r - 1)%nat c).
    repeat (split; auto with wf_db).
    + unfold WF_GenMatrix.
      intros x0 y H2. 
      apply Permutation_length in H.
      simpl in *.
      bdestruct_all.
      * subst.
        rewrite H0; auto; lia.
      * rewrite WFb; auto; lia.
    + unfold list_vector_to_matrix, GMmult.
      prep_genmatrix_equality.
      replace (length (x :: l)) with (S (length l)) by easy.
      replace (length (x :: l')) with (S (length l')) by easy.
      rewrite ! big_sum_shift.
      f_equal.
      apply Permutation_length in H.
      rewrite H in *.
      unfold list_vector_to_matrix, GMmult in eqn.
      apply f_equal_inv with (x := x0) in eqn.
      apply f_equal_inv with (x := y) in eqn.

      assert ((fun x1 : nat => nth (S x1) (x :: l) Zero x0 0%nat * a (S x1) y)
              = (fun x1 : nat => nth x1 l Zero x0 0%nat * a (x1 + 1)%nat y))
        by (apply functional_extensionality; intros; rewrite Nat.add_1_r; auto).
      rewrite H2, eqn.
      apply big_sum_eq_bounded.
      intros x1 H4.
      simpl.
      replace (x1 - 0)%nat with x1 by lia.
      reflexivity.
    + simpl.
      apply Permutation_cons; auto.
      assert ((map (fun i0 : nat => a i0 0%nat) (List.seq 1 (length l)))
              = (map (fun i : nat => a (i + 1)%nat 0%nat) (List.seq 0 (length l)))).
      { apply nth_ext with (d := 0%G) (d' := 0%G).
        - rewrite ! map_length, ! seq_length; reflexivity.
        - intros n0 H2.
          rewrite nth_indep with (d' := a 0%nat 0%nat); auto.
          rewrite map_nth with (f := (fun i0 : nat => a i0 0%nat)) (d := 0%nat).
          rewrite nth_indep with (d' := a (0 + 1)%nat 0%nat); auto.
          rewrite map_nth with (f := (fun i0 : nat => a (i0 + 1)%nat 0%nat)) (d := 0%nat).
          f_equal.
          rewrite ! seq_nth.
          lia.
          all : try rewrite map_length, seq_length;
          rewrite map_length, seq_length in H2;
            auto. }
      rewrite H2.
      assert ((map
                 (fun i0 : nat => if (i0 =? 0)%nat then a 0%nat 0%nat else b (i0 - 1)%nat 0%nat)
                 (List.seq 1 (length l')))
              = (map (fun i : nat => b i 0%nat) (List.seq 0 (length l')))).
      { apply nth_ext with (d := 0%G) (d' := 0%G).
        - rewrite ! map_length, ! seq_length; reflexivity.
        - intros n0 H3.
          rewrite map_length, seq_length in H3.
          rewrite nth_indep with (d' := (fun i0 : nat => if (i0 =? 0)%nat 
                                                   then a 0%nat 0%nat else b (i0 - 1)%nat 0%nat) 0%nat);
            auto.
          rewrite map_nth with (f := (fun i0 : nat => if (i0 =? 0)%nat
                                                then a 0%nat 0%nat else b (i0 - 1)%nat 0%nat)) (d := 0%nat).
          rewrite nth_indep with (d' := (fun i0 : nat => b i0 0%nat) 0%nat); auto.
          rewrite map_nth with (f := (fun i0 : nat => b i0 0%nat)) (d := 0%nat).
          bdestruct_all.
          + rewrite seq_nth in H4; auto; lia.
          + do 2 f_equal.
            rewrite ! seq_nth; auto; lia.
          + rewrite map_length, seq_length; easy.
          + rewrite map_length, seq_length; easy. }
      rewrite H3.
      auto.
  - exists (fun r c => if (r =? 0)%nat then a 1%nat c else
                 if (r =? 1)%nat then a 0%nat c else a r c).
    repeat (split; intros; auto).
    + unfold WF_GenMatrix.
      intros x0 y0 H.
      bdestruct_all; subst; simpl in *; auto; rewrite H0; auto; lia.
    + unfold list_vector_to_matrix, GMmult.
      prep_genmatrix_equality.
      replace (length (y :: x :: l)) with (S (S (length l))) by easy.
      replace (length (x :: y :: l)) with (S (S (length l))) by easy.
      rewrite ! big_sum_shift.
      simpl.
      rewrite ! Gplus_assoc.
      setoid_rewrite Gplus_comm at 2.
      auto.
    + simpl.
      assert (map
                (fun i0 : nat =>
                   if (i0 =? 0)%nat
                   then a 1%nat 0%nat
                   else if (i0 =? 1)%nat then a 0%nat 0%nat else a i0 0%nat)
                (List.seq 2 (length l))
              = map (fun i0 : nat => a i0 0%nat) (List.seq 2 (length l))).
      { apply nth_ext with (d := 0%G) (d' := 0%G).
        - rewrite ! map_length; reflexivity.
        - intros n0 H.
          rewrite ! map_length, seq_length in H.
          rewrite nth_indep with (d' := (fun i0 : nat =>
                                                 if (i0 =? 0)%nat
                                                 then a 1%nat 0%nat
                                                 else if (i0 =? 1)%nat then a 0%nat 0%nat else a i0 0%nat) 0%nat).
          rewrite map_nth with (f := (fun i0 : nat =>
                                       if (i0 =? 0)%nat
                                       then a 1%nat 0%nat
                                       else if (i0 =? 1)%nat then a 0%nat 0%nat else a i0 0%nat)).
          rewrite nth_indep with (d' := (fun i0 : nat => a i0 0%nat) 0%nat).
          rewrite map_nth with (f := (fun i0 : nat => a i0 0%nat)).
          bdestruct_all; auto.
          + rewrite seq_nth in H1; auto; lia.
          + rewrite seq_nth in H2; auto; lia.
          + rewrite map_length, seq_length; auto.
          + rewrite map_length, seq_length; auto. }
      rewrite H.
      apply perm_swap.
  - destruct (IHPermutation1 a H0) as [b [H2 [H3 H4]]].
    destruct (IHPermutation2 b H2) as [c [H5 [H6 H7]]].
    exists c.
    repeat (split; auto).
    + rewrite H3, H6; auto.
    + apply (perm_trans H4 H7).
Qed.

Lemma permutation_preserves_linearly_indep : forall {n : nat} {l1 l2 : list (GenVector n)},
    Permutation l1 l2 -> linearly_independent (list_vector_to_matrix l1) ->
    linearly_independent (list_vector_to_matrix l2).
Proof. intros n l1 l2 H0 H1.
  unfold linearly_independent in *.
  intros a H2 H3.
  apply Permutation_sym in H0.
  destruct (permutation_list_vector_to_matrix_times_vector H0 a H2) as [b [H4 [H5 H6]]].
  rewrite H3 in H5.
  symmetry in H5.
  specialize (H1 b H4 H5).
  rewrite H1 in H6.
  unfold Zero in H6.
  rewrite map_const_repeat in H6.
  rewrite seq_length in H6.
  rewrite <- (Permutation_length H0) in H6.
  assert (H7 : forall i, nth i (map (fun i : nat => a i 0%nat) (List.seq 0 (length l2))) 0%G = 0%G)
    by (rewrite <- permutation_repeat_nth, map_length, seq_length; auto).
  assert (H8 : forall i, (i < length l2)%nat -> a i 0%nat = 0%G).
  { intros i0 H8.
    assert (H9 : a (length l2) 0%nat = 0%G) by (rewrite H2; auto).
    setoid_rewrite <- H9 in H7 at 1.
    setoid_rewrite map_nth with (d := length l2) in H7.
    specialize (H7 i0).
    rewrite seq_nth in H7; auto. }
  rewrite zero_all_zero in H8; auto.
Qed.


Lemma permutation_preserves_linearly_indep_iff : forall {n : nat} {l1 l2 : list (GenVector n)},
    Permutation l1 l2 -> 
    (linearly_independent (list_vector_to_matrix l1) <->
    linearly_independent (list_vector_to_matrix l2)).
Proof. intros. split; intros.
  apply @permutation_preserves_linearly_indep with (l1 := l1); auto.
  apply @permutation_preserves_linearly_indep with (l1 := l2); auto. apply Permutation_sym in H; auto.
Qed.

Lemma permutation_preserves_span : forall {n : nat} {l1 l2 : list (GenVector n)},
  Permutation l1 l2 ->
  (forall v : GenVector n, span (list_vector_to_matrix l1) v -> span (list_vector_to_matrix l2) v).
Proof. intros.
  unfold span in *.
  destruct H0 as [a [WFa H1]].
  destruct (permutation_list_vector_to_matrix_times_vector H a WFa) as [b [WFb [H2 Perm]]].
  exists b.
  split; auto.
  rewrite <- H2; apply H1.
Qed.

Lemma permutation_preserves_span_iff : forall {n : nat} {l1 l2 : list (GenVector n)},
  Permutation l1 l2 ->
  (forall v : GenVector n, span (list_vector_to_matrix l1) v <-> span (list_vector_to_matrix l2) v).
Proof. intros. split; intros.
  apply @permutation_preserves_span with (l1 := l1); auto.
  apply @permutation_preserves_span with (l1 := l2); auto. apply Permutation_sym in H; auto.
Qed.

Lemma permutation_preserves_subspace_containment : forall {n : nat} {l1 l2 : list (GenVector n)} {P : GenVector n -> Prop},
        subspace P -> Permutation l1 l2 ->
        (forall i : nat, (i < (length l1))%nat -> P (get_col (list_vector_to_matrix l1) i)) ->
        (forall i : nat, (i < (length l2))%nat -> P (get_col (list_vector_to_matrix l2) i)).
Proof. intros n l1 l2 P H0 H1 H2 i0 H3.
  unfold get_col, list_vector_to_matrix in *.
  remember H1 as H4. clear HeqH4.
  rewrite Permutation_nth in H4.
  destruct H4 as [H4 [f [H5 [H6 H7]]]].
  remember H6 as H8. clear HeqH8.
  rewrite (FinFun.bInjective_bSurjective H5) in H8.
  destruct (FinFun.bSurjective_bBijective H5 H8) as [g [H9 H10]].
  rewrite H4 in *.
  rewrite H7; auto.
Qed.

Lemma permutation_preserves_subspace_containment_iff : forall {n : nat} {l1 l2 : list (GenVector n)} {P : GenVector n -> Prop},
        subspace P -> Permutation l1 l2 ->
        ((forall i : nat, (i < (length l1))%nat -> P (get_col (list_vector_to_matrix l1) i)) <->
        (forall i : nat, (i < (length l2))%nat -> P (get_col (list_vector_to_matrix l2) i))).
Proof. intros. split; intros.
  apply @permutation_preserves_subspace_containment with (l1 := l1); auto.
  apply @permutation_preserves_subspace_containment with (l1 := l2); auto. apply Permutation_sym in H0; auto.
Qed.

Lemma permutation_preserves_map_get_col_matrix : forall {n m : nat} {indices_list1 indices_list2 : list nat} (M : GenMatrix n m),
    Permutation indices_list1 indices_list2 ->
    Permutation (map (fun i : nat => get_col M i) indices_list1) (map (fun i : nat => get_col M i) indices_list2).
Proof. intros n m indices_list1 indices_list2 M H0.
  remember H0 as H0'. clear HeqH0'.
  rewrite Permutation_nth in H0.
  destruct H0 as [eq_len [f [bFunf [bInjf eq_nth]]]].
  rewrite Permutation_nth.
  split; try rewrite ! map_length, eq_len; auto. 
  exists f.
  repeat split; try rewrite map_length; auto.
  intros x H0.
  setoid_rewrite map_nth with (f := (fun i0 : nat => get_col M i0)).
  f_equal.
  apply eq_nth; auto.
  Unshelve.
  auto.
Qed.  

Lemma permutation_preserves_basis : forall {n m : nat} {indices_list1 indices_list2 : list nat} {P : GenVector n -> Prop} {M : GenMatrix n m},
    WF_GenMatrix M -> subspace P -> Permutation indices_list1 indices_list2 ->
    (basis P (matrix_column_choose indices_list1 M) <-> basis P (matrix_column_choose indices_list2 M)).
Proof. intros n m indices_list1 indices_list2 P M H0 H1 H2.
  pose (permutation_preserves_map_get_col_matrix M H2).
  unfold basis, matrix_column_choose. 
  split; intros H3; destruct H3 as [H4 [H5 [H6 H7]]]; repeat (split; intros; auto).
  - pose (permutation_preserves_subspace_containment H4 p).
    rewrite ! map_length in p0.
    specialize (p0 H5).
    apply p0; auto.
  -  pose (permutation_preserves_span p).
     rewrite ! map_length in s.
     specialize (s v).
     apply s; auto.
  - pose (permutation_preserves_linearly_indep p).
    rewrite ! map_length in l.
    specialize (l H7); auto.
  - apply Permutation_sym in p.
    pose (permutation_preserves_subspace_containment H4 p).
    rewrite ! map_length in p0.
    specialize (p0 H5).
    apply p0; auto.
  - apply Permutation_sym in p.
    pose (permutation_preserves_span p).
    rewrite ! map_length in s.
    specialize (s v).
    apply s; auto.
  - apply Permutation_sym in p.
    pose (permutation_preserves_linearly_indep p).
    rewrite ! map_length in l.
    specialize (l H7); auto.
Qed.

(* Theorem 41 Let V be a nontrivial vector space over a field F, and suppose {u1,u2,...,um} spans V. Then a subset of {u1,u2,...,um} is a basis for V. *)
Lemma subset_basis : forall {n m : nat} {P : GenVector n -> Prop} {M : GenMatrix n m},
    WF_GenMatrix M -> (m > 0)%nat -> subspace P -> (forall i, (i < m)%nat -> P (get_col M i)) -> (forall v, P v -> span M v) ->
    (exists v, v <> Zero /\ P v) -> 
    (exists indices_list, incl indices_list (List.seq 0 m) /\ NoDup indices_list /\
                       basis P (matrix_column_choose indices_list M)).
Proof. intros n m P M H H0 H1 H2 H3 H4.
  destruct (Classical_Prop.classic (linearly_dependent M)).
  - induction m.
    + inversion H0.
    + destruct m.
      * assert (M <> Zero).
        { destruct (Classical_Prop.classic (M = Zero)).
          - destruct H4 as [v [H4 H4']].
            specialize (H3 v H4').
            unfold span in H3.
            destruct H3 as [a [H3 H3']].
            rewrite H3' in H4.
            rewrite H6 in H4.
             rewrite GMmult_0_l in H4.
             contradiction.
          - assumption. }
        pose (lin_indep_vec M H H6) as H7.
        apply lindep_implies_not_linindep in H5.
        contradiction.
      * destruct (lin_dep_gen_elem M H H5) as [i [H6 [v [H7 H8]]]].
        assert (span (reduce_col M i) (get_col M i)).
        { unfold span.
          exists ((- 1%G) .* v).
          split; auto with wf_db.
          rewrite Mscale_mult_dist_r.
          rewrite H8.
          rewrite Mscale_assoc.
          lgma. }
        pose (equal_span_reduce_col M i H6 H9) as H10.
        assert (WF_GenMatrix (reduce_col M i)); auto with wf_db.
        assert (S m > 0)%nat; try lia.
        assert (forall i0 : nat, (i0 < S m)%nat -> P (get_col (reduce_col M i) i0)).
        { intros i0 H13.
          bdestruct (i0 <? i).
          - rewrite get_col_reduce_col; auto.
          - rewrite get_col_reduce_col_back; auto; apply H2; lia. }
        assert (forall v : GenVector n, P v -> span (reduce_col M i) v).
        { intros v0 H14.
          apply H10; auto. }
        destruct (Classical_Prop.classic (linearly_dependent (reduce_col M i))).
        -- specialize (IHm (reduce_col M i) H11 H12 H13 H14 H15).
           destruct IHm as [indices_list [incl_indices_list basis_P]].
           exists (map (fun n => if (n <? i) then n else S n) indices_list).
           split.
           ++ unfold incl.
              intros a H16.
              rewrite in_map_iff in H16.
              destruct H16 as [x [H16 H17]].
              bdestruct (x <? i).
              ** simpl in H16.
                 rewrite <- H16.
                 rewrite in_seq.
                 lia.
              ** simpl in H16.
                 rewrite <- H16.
                 unfold incl in incl_indices_list.
                 specialize (incl_indices_list x H17).
                 rewrite in_seq in incl_indices_list.
                 rewrite in_seq.
                 lia.
           ++ split.
              ** apply NoDup_map_inv
                   with (f := fun n0 : nat => if (n0 <? i)%nat then n0 else (Nat.pred n0)).
                 rewrite map_map.
                 assert ((fun x : nat =>
                            if (if x <? i then x else S x) <? i
                            then if x <? i then x else S x
                            else Nat.pred (if x <? i then x else S x))
                         = (fun x : nat => x)).
                 { apply functional_extensionality.
                   intros x.
                   bdestruct_all; auto. }
                 rewrite H16.
                 rewrite map_id.
                 destruct basis_P; auto.
              ** unfold basis.
                 assert ((matrix_column_choose (map (fun n0 : nat => if n0 <? i then n0 else S n0) indices_list) M) = (matrix_column_choose indices_list (reduce_col M i))).
                 { unfold matrix_column_choose, list_vector_to_matrix.
                   prep_genmatrix_equality.
                   rewrite map_map.
                   unfold reduce_col.
                   assert (Zero = ((fun x0 : nat => get_col M (if x0 <? i then x0 else S x0)) (S m))).
                   { prep_genmatrix_equality.
                     unfold get_col.
                     bdestruct_all; auto.
                     rewrite H; auto; lia. }
                   rewrite H16 at 1.
                   rewrite map_nth with (d := S m).
                   assert (Zero = (fun i0 : nat => @get_col n (S m) (fun x0 y0 : nat => if y0 <? i then M x0 y0 else M x0 (1 + y0)%nat) i0) (S m)).
                   { prep_genmatrix_equality.
                     unfold get_col.
                     bdestruct_all; auto.
                     rewrite H; auto; lia. }
                   rewrite H17.
                   rewrite map_nth with (d := S m).
                   bdestruct_all.
                   - unfold get_col.
                     bdestruct_all.
                     reflexivity.
                   - unfold get_col.
                     bdestruct_all.
                     reflexivity. }
                 rewrite ! H16.
                 destruct basis_P as [subspaceP [in_P [spans_P lin_ind]]].
                 rewrite ! map_length.
                 repeat (split; auto).
        -- apply not_lindep_implies_linindep in H15.
           exists (delete_nth (List.seq 0 (S (S m))) i).
           split.
           ++ unfold incl.
              intros a H16.
              unfold delete_nth in H16.
              rewrite in_app_iff in H16.
              destruct H16.
              ** apply firstn_subset in H16; auto.
              ** apply skipn_subset in H16; auto.
           ++ split.
              ** unfold delete_nth.
                 apply NoDup_remove_1 with (a := i).
                 assert (i :: skipn (i + 1) (List.seq 0 (S (S m))) = skipn i (List.seq 0 (S (S m)))).
                 { setoid_rewrite nth_helper with (x := 0%nat) at 2.
                   replace (S i) with (i + 1)%nat by lia.
                   rewrite seq_nth.
                   all : try rewrite seq_length; auto. }
                 rewrite H16.
                 rewrite firstn_skipn.
                 apply seq_NoDup.
              ** unfold basis.
                 rewrite <- ! reduce_col_matrix_column_choose_delete; auto.
                 2: rewrite seq_length; assumption.
                 rewrite ! matrix_column_choose_original; auto.
                 rewrite ! length_delete_nth.
                 2: rewrite seq_length; assumption.
                 rewrite ! seq_length.
                 replace ((S (S m)) - 1)%nat with (S m) by lia.
                 repeat (split; auto).
  - apply not_lindep_implies_linindep in H5.
    exists (List.seq 0 m).
    split.
    + apply incl_refl.
    + split.
      * apply seq_NoDup.
      * unfold basis.
        rewrite matrix_column_choose_original; auto.
        rewrite ! seq_length.
        repeat (split; try assumption).
Qed.


(* Exercise 2.5.4 Let V be a vector space over a field F and let {u1,...,uk} be a linearly independent subset of V . Prove that if v ̸∈ sp{u1, . . . , uk}, then {u1,...,uk,v} is also linearly independent. *)

Lemma extend1_lin_indep : forall {n m : nat} {P : GenVector n -> Prop} {A : GenMatrix n m} {v : GenVector n},
    subspace P -> WF_GenMatrix A -> WF_GenMatrix v -> linearly_independent A ->
    (forall i, (i < m)%nat -> P (get_col A i)) ->
    ~ span A v -> linearly_independent (col_append A v).
Proof. intros n m P A v H0 H1 H2 H3 H4 H5.
  unfold span in H5.
  unfold linearly_independent in H3.
  unfold linearly_independent.
  intros a H6 H7.
  destruct (Classical_Prop.classic (a = Zero)) as [H8 | H8]; auto.
  assert (H9 : a m 0%nat <> 0%G).
  { intro H9.
    assert (H10 : col_append A v × a = A × (reduce_row a m)).
    { unfold col_append, col_wedge, reduce_row, GMmult.
      prep_genmatrix_equality.
      simpl.
      bdestruct_all.
      bdestruct (y =? 0)%nat;
        [rewrite H11; rewrite H9 | rewrite H6; try lia];
        dumb_lRa; auto;
        apply big_sum_eq_bounded;
        intros x0 H12;
        bdestruct_all;
        reflexivity. }
    rewrite H10 in H7.
    assert (H11 : WF_GenMatrix (reduce_row a m)); auto with wf_db.
    specialize (H3 (reduce_row a m) H11 H7).
    assert (H12 : a = Zero).
    { prep_genmatrix_equality.
      bdestruct (y =? 0)%nat.
      - subst.
        bdestruct (x <? m)%nat.
        + unfold reduce_row in H3.
          apply f_equal_inv with (x := x) in H3.
          apply f_equal_inv with (x := 0%nat) in H3.
          rewrite <- Nat.ltb_lt in H.
          rewrite H in H3.
          assumption.
        + bdestruct (x =? m)%nat.
          * subst.
            assumption.
          * rewrite H6; auto; lia.
      - rewrite H6; auto; lia. }
    contradiction. }
  assert (v = A × (((- 1%G) * /(a m 0%nat)) .* (reduce_row a m))).
  { assert (H10 : col_append A v × a = A × (reduce_row a m) .+ (a m 0%nat) .* v).
    { unfold col_append, col_wedge, reduce_row, scale, GMmult, GMplus.
      prep_genmatrix_equality.
      simpl.
      bdestruct_all.
      bdestruct (y =? 0)%nat.
      - subst.
        f_equal.
        + apply big_sum_eq_bounded.
          intros x0 H11.
          bdestruct_all.
          reflexivity.
        + rewrite Gmult_comm.
          reflexivity.
      - setoid_rewrite H6 at 2; try lia.
        setoid_rewrite H2 at 3; try lia.
        dumb_lRa; auto.
        apply big_sum_eq_bounded.
        intros x0 H12.
        bdestruct_all.
        reflexivity. }
    rewrite H10 in H7.
    rewrite GMplus_comm in H7.
    apply Mplus_inj_r with (m := (- 1%G) .* (A × reduce_row a m)) in H7.
    rewrite GMplus_assoc in H7.
    assert (H11 : forall {n m} (A : GenMatrix n m), WF_GenMatrix A -> A .+ - 1%G .* A = Zero).
    { intros n0 m0 A0 H11. lgma. }
    rewrite H11 in H7; auto with wf_db.
    rewrite GMplus_0_r, GMplus_0_l in H7.
    apply Mscale_cancel with (c := a m 0%nat); auto.
    rewrite H7.
    rewrite Mscale_mult_dist_r.
    rewrite Mscale_assoc.
    f_equal.
    setoid_rewrite Gmult_comm at 2.
    rewrite Gmult_assoc.
    rewrite Ginv_r; auto.
    ring. }
  assert (WF_GenMatrix (- 1%G * / a m 0%nat .* reduce_row a m)); auto with wf_db.
  pose (Classical_Pred_Type.not_ex_all_not (GenVector m) (fun a : GenVector m => WF_GenMatrix a /\ v = A × a) H5 (- 1%G * / a m 0%nat .* reduce_row a m)) as H12.
  simpl in H12.
  apply Classical_Prop.not_and_or in H12.
  destruct H12; contradiction.
Qed.


Definition trichotomy (A B C : Prop) := (A /\ ~ B /\ ~ C) \/ (~ A /\ B /\ ~ C) \/ (~ A /\ ~ B /\ C).


(* Theorem 43 Let V be a finite-dimensional vector space over a field F, and suppose {u1, u2, . . . , uk} ⊂ V is linearly independent. If {u1, u2, . . . , uk} does not span V , then there exist vectors uk+1 , . . . , un such that
{u1,u2,...,uk,uk+1,...,un}
is a basis for V. *)

Definition temp_before {n k : nat} (P : GenVector n -> Prop) (A : GenMatrix n k) (m : nat) :=
  (exists (B : GenMatrix n (m - k)), (WF_GenMatrix B) /\ (forall i, (i < (m - k))%nat -> P (get_col B i)) /\
                               (linearly_independent (smash A B)) /\
                               ~ (forall v, P v -> span (smash A B) v)).

Definition temp_middle {n k : nat} (P : GenVector n -> Prop) (A : GenMatrix n k) (m : nat) :=
  (exists (B : GenMatrix n (m - k)), (WF_GenMatrix B) /\ (forall i, (i < (m - k))%nat -> P (get_col B i)) /\
                               (linearly_independent (smash A B)) /\
                               (forall v, P v -> span (smash A B) v)).

Definition temp_after {n k : nat} (P : GenVector n -> Prop) (A : GenMatrix n k) (m : nat) :=
  (forall (B : GenMatrix n (m - k)), (WF_GenMatrix B) -> (forall i, (i < (m - k))%nat -> P (get_col B i)) ->
                             linearly_dependent (smash A B)).

Lemma temp_begin : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
    ((temp_before P A (k + 1)%nat) \/ (temp_middle P A (k + 1)%nat)).
Proof. intros n k P A H0 H1 H2 H3 H4. 
  apply Classical_Pred_Type.not_all_ex_not in H4.
  destruct H4 as [v H4].
  apply Classical_Prop.imply_to_and in H4.
  destruct H4 as [H4 H5].
  assert (H6 : WF_GenMatrix v) by (apply (WF_subspace H1 H4); auto).
  pose (extend1_lin_indep H1 H0 H6 H3 H2 H5).
  unfold col_append in l.
  rewrite smash_wedge in l; auto.
  destruct (Classical_Prop.classic (forall w, P w -> span (smash A v) w)).
  - right.
    unfold temp_middle.
    exists v.
    replace (k + 1 - k)%nat with 1%nat by lia.
    replace (S k) with (k + 1)%nat by lia.
    repeat (split; auto).
    + intros i0 H8.
      replace i0 with 0%nat by lia.
      rewrite get_col_vec; auto.
    + replace (k + 1)%nat with (S k) by lia; auto.
  - left.
    unfold temp_before.
    exists v.
    replace (k + 1 - k)%nat with 1%nat by lia.
    replace (S k) with (k + 1)%nat by lia.
    repeat (split; auto).
    + intros i0 H8.
      replace i0 with 0%nat by lia.
      rewrite get_col_vec; auto.
    + replace (k + 1)%nat with (S k) by lia; auto.
Qed.

Lemma temp_end : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (temp_after P A (n + 1)%nat).
Proof. intros n k P A H0 H1 H2 H3.
  unfold temp_after.
  intros B H4 H5.
  apply gt_dim_lindep; auto with wf_db; lia.
Qed.

Lemma temp_before_step : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (temp_before P A m) ->
          ((temp_before P A (S m)) \/ (temp_middle P A (S m)))). 
Proof. intros n k P A H0 H1 H2 H3 m H4 H5.
  unfold temp_before in H5.
  destruct H5 as [B [WFB [BinP [linindAB notspanP]]]].
  apply Classical_Pred_Type.not_all_ex_not in notspanP.
  destruct notspanP as [v notspanP].
  apply Classical_Prop.imply_to_and in notspanP.
  destruct notspanP as [vinP vnotinspan].
  assert (H5 : WF_GenMatrix (smash A B)); auto with wf_db.
  assert (H6 : forall i : nat, (i < m)%nat -> P (get_col (smash A B) i)).
  { intros i0 H6.
    bdestruct (i0 <? k)%nat.
    - rewrite get_col_smash_left; try apply H2; lia.
    - rewrite get_col_smash_right; try apply BinP; lia. }
  replace m with (k + (m - k))%nat in H6 by lia.
  assert (WFv : WF_GenMatrix v) by (apply (WF_subspace H1 vinP); auto).
  pose (extend1_lin_indep H1 H5 WFv linindAB H6 vnotinspan) as l.
  unfold col_append in l.
  rewrite smash_wedge in l; auto with wf_db.
  rewrite smash_assoc in l.
  assert (H7 : forall i : nat, (i < (m - k) + 1)%nat -> P (get_col (smash B v) i)).
  { intros i0 H7.
    bdestruct (i0 <? m - k)%nat.
    - rewrite get_col_smash_left; try apply BinP; lia.
    - rewrite get_col_smash_right; replace (i0 - (m - k))%nat with 0%nat by lia;
        try rewrite get_col_vec; try apply vinP; auto with wf_db; lia. }
  destruct (Classical_Prop.classic (forall w, P w -> span (smash A (smash B v)) w)).
  - right.
    unfold temp_middle.
    exists (smash B v).
    replace (S m - k)%nat with ((m - k) + 1)%nat by lia.
    repeat (split; auto with wf_db).
    replace (k + (m - k + 1))%nat with (S (k + (m - k)))%nat by lia. 
    apply l.
  - left.
    unfold temp_before.
    exists (smash B v).
    replace (S m - k)%nat with ((m - k) + 1)%nat by lia.
    repeat (split; auto with wf_db).
    replace (k + (m - k + 1))%nat with (S (k + (m - k)))%nat by lia. 
    apply l.
Qed.

Lemma temp_middle_step : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (temp_middle P A m) ->
          (temp_after P A (S m))).
Proof. intros n k P A H0 H1 H2 H3 m H4 H5.
  unfold temp_middle in H5.
  destruct H5 as [B [WFB [BinP [linindAB ABspansP]]]].
  assert (basis P (smash A B)).
  repeat (split; auto).
  - intros i0 H5.
    bdestruct (i0 <? k)%nat.
    + rewrite get_col_smash_left; try apply H2; lia.
    + rewrite get_col_smash_right; try apply BinP; lia.
  - unfold temp_after.
    intros B0 H6 H7.
    apply (dimension_overflow P (smash A B) (smash A B0)); auto with wf_db; try lia.
    intros i0 H8.
    bdestruct (i0 <? k).
    + rewrite get_col_smash_left; auto.
    + rewrite get_col_smash_right; auto; apply H7; lia.
Qed.

Lemma append_mul : forall {n m} (A : GenMatrix n m) (v : GenVector n) (a : GenVector m),
  (col_append A v) × (row_append a (@Zero 1 1)) = A × a.
Proof. intros. 
       prep_genmatrix_equality. 
       unfold GMmult.
       simpl. 
       assert (H' : (col_append A v x m * row_append a Zero m y = 0%G)). 
       { unfold col_append, col_wedge, row_append, row_wedge.
         bdestruct_all; try lia; unfold Zero; ring. }
       rewrite H'. 
       rewrite Gplus_0_r. 
       apply big_sum_eq_bounded.
       intros. 
       unfold col_append, col_wedge, row_append, row_wedge. 
       bdestruct_all; try lia; unfold Zero; try easy.
Qed.

Lemma lin_dep_col_append_n : forall {n m} (A : GenMatrix n m) (v : GenVector n),
  linearly_dependent A -> linearly_dependent (col_append A v).
Proof. intros. 
       unfold linearly_dependent in *. 
       destruct H as [a [H [H1 H2]]].
       exists (row_append a (@Zero 1 1)). 
       unfold row_append.
       split; auto with wf_db. 
       split. unfold not; intros; apply H1.
       prep_genmatrix_equality. 
       assert (H' : row_append a Zero x y = 0%G). 
       { unfold row_append. rewrite H0. easy. }
       unfold row_append, row_wedge in H'.
       bdestruct (x =? m). 
       rewrite H; try easy; lia. 
       bdestruct (x <? m).
       rewrite H'; easy.
       rewrite H; auto; lia.
       unfold col_append.
       rewrite wedge_mul;
       easy.
Qed.

Lemma temp_after_step : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (temp_after P A m) ->
          (temp_after P A (S m))).
Proof. intros n k P A H0 H1 H2 H3 m H4 H5.
  unfold temp_after.
  intros B H6 H7.
  assert (H8: (smash A B)
          = (col_append (submatrix_column m (smash A B)) (get_col B (m - k)%nat))).
  { prep_genmatrix_equality.
    assert (H8: WF_GenMatrix (smash A B)); auto with wf_db.
    assert (H9: WF_GenMatrix (col_append (submatrix_column m (smash A B)) (get_col B (m - k)%nat))); (unfold col_append; auto with wf_db).
    bdestruct (x <? n)%nat.
    - bdestruct (y <? S m)%nat.
      + unfold smash, submatrix_column, col_append, col_wedge, get_col.
        bdestruct_all; auto.
      + rewrite H8; try lia.
        unfold col_append in H9.
        rewrite H9; try lia.
        reflexivity.
    - rewrite H8; try lia.
      unfold col_append in H9.
      rewrite H9; try lia.
      reflexivity. }
  rewrite H8.
  replace (k + (S m - k))%nat with (S m) by lia.
  apply lin_dep_col_append_n.
  unfold temp_after in H5.
  setoid_rewrite submatrix_column_smash_right; auto.
  assert (H9: WF_GenMatrix (submatrix_column (m - k)%nat B)); auto with wf_db.
  assert (H10: forall i : nat, (i < m - k)%nat -> P (get_col (submatrix_column (m - k)%nat B) i)).
  { intros i0 H10.
    rewrite get_col_submatrix_column; auto.
    apply H7; lia. }
  replace (k + (m - k))%nat with m in H5 by lia.
  apply (H5 (submatrix_column (m - k) B) H9 H10).
Qed.

Lemma temp_no_middle_all_before : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
     (forall m, (k < m)%nat -> ~ (temp_middle P A m)) ->
    (forall m, (k < m)%nat -> (temp_before P A m)).
Proof. intros n k P A H H0 H1 H2 H3 H4 m H5.
  induction m.
  - inversion H5.
  - bdestruct (m =? k)%nat.
    + subst.
      replace (S k) with (k + 1)%nat in * by lia.
      assert (temp_before P A (k + 1)%nat \/ temp_middle P A (k + 1)%nat)
        by (apply temp_begin; auto).
      destruct H6; auto.
      contradict H6; auto.
    + assert (k < m)%nat by lia.
      apply IHm in H7.
      apply temp_before_step in H7; auto; try lia.
      destruct H7; auto.
      contradict H7; auto.
Qed.

Lemma temp_all_after_from_end : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (n < m)%nat -> temp_after P A m).
Proof. intros n k P A H0 H1 H2 H3 m H4.
  induction m.
  - inversion H4.
  - bdestruct (m =? n)%nat.
    + subst.
      replace (S n) with (n + 1)%nat in * by lia.
      apply temp_end; auto.
    + assert (n < m)%nat by lia.
      apply temp_after_step; auto.
      pose (linearly_independent_dimensions A H0 H3).
      lia.
Qed.

Lemma temp_trichotomy_subpart1 : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (k < m)%nat ->
          (~ temp_after P A m <-> temp_before P A m \/ temp_middle P A m)).
Proof. intros n k P A H0 H1 H2 H3 m H4. 
  split.
  - intros H5.
    unfold temp_after in H5.
    apply Classical_Pred_Type.not_all_ex_not in H5.
    destruct H5 as [M H5].
    apply Classical_Prop.imply_to_and in H5.
    destruct H5 as [WFM H5].
    apply Classical_Prop.imply_to_and in H5.
    destruct H5 as [MinP linindep].
    apply not_lindep_implies_linindep in linindep.
    unfold temp_before, temp_middle.
    destruct (Classical_Prop.classic (forall v : GenVector n, P v -> span (smash A M) v));
      [right | left]; exists M; auto.
  - intros H5.
    unfold temp_after.
    destruct H5 as [before | middle].
    + unfold temp_before in before.
      destruct before as [M [WFM [MinP [linindep notspanP]]]].
      intro H5.
      specialize (H5 M WFM MinP).
      apply lindep_implies_not_linindep in H5.
      contradiction.
    + unfold temp_middle in middle.
      destruct middle as [M [WFM [MinP [lindep spanP]]]].
      intro H5.
      specialize (H5 M WFM MinP).
      apply lindep_implies_not_linindep in H5.
      contradiction.
Qed.

Lemma temp_trichotomy_subpart2 : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (k < m)%nat -> (~ temp_before P A m \/ ~ temp_middle P A m)).
Proof. intros n k P A H H0 H1 H2 m H3.
  apply Classical_Prop.not_and_or.
  intro.
  destruct H4.
  apply temp_before_step in H4; auto.
  rewrite <- temp_trichotomy_subpart1 in H4; auto.
  apply temp_middle_step in H5; auto.
Qed.

Lemma temp_trichotomy : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    (forall m, (k < m)%nat ->
          (trichotomy (temp_before P A m) (temp_middle P A m) (temp_after P A m))).
Proof. intros n k P A H0 H1 H2 H3 m H4.
  assert (H5: ~ temp_after P A m <-> temp_before P A m \/ temp_middle P A m) by
    (apply temp_trichotomy_subpart1; auto; lia).
  unfold trichotomy.
  destruct (Classical_Prop.classic (temp_after P A m)) as [H6 | H6].
  - do 2 right.
    assert (H7: ~ temp_before P A m /\ ~ temp_middle P A m).
    { apply Classical_Prop.not_or_and.
      intro H7.
      rewrite <- H5 in H7; auto. }
    destruct H7.
    repeat split; auto.
  - remember H6 as H6'. clear HeqH6'.
    rewrite H5 in H6.
    assert (H7: ~ temp_before P A m \/ ~ temp_middle P A m)
      by (apply temp_trichotomy_subpart2; auto).
    destruct H6; destruct H7; try contradiction;
      try (left; repeat split; assumption);
      try (right; left; repeat split; assumption).
Qed.

Lemma temp_exists_middle : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
    (exists m, (k < m <= n)%nat /\ (temp_middle P A m)).
Proof. intros n k P A H0 H1 H2 H3 H4.
  pose (linearly_independent_dimensions A H0 H3).
  destruct (Classical_Prop.classic (forall m : nat, (k < m)%nat -> ~ temp_middle P A m)) 
    as [H5 | H5].
  - assert (H6: temp_before P A (n + 1)%nat)
      by (apply temp_no_middle_all_before; auto; lia).
    assert (H7: temp_after P A (n + 1)%nat)
      by (apply temp_end; auto).
    assert (H8: (k < n + 1)%nat) by lia.
    destruct (temp_trichotomy H0 H1 H2 H3 (n + 1)%nat H8)
      as [[Hb [nHm nHa]] | [[nHb [Hm nHa]] | [nHb [nHm Ha]]]];
      contradiction.
  - apply Classical_Pred_Type.not_all_ex_not in H5.
    destruct H5 as [m H5].
    apply Classical_Prop.imply_to_and in H5.
    destruct H5 as [H5 H6].
    apply Classical_Prop.NNPP in H6.
    bdestruct (m <=? n)%nat.
    +  exists m.
       split; auto.
    + assert (temp_after P A m) by (apply temp_all_after_from_end; auto).
      destruct (temp_trichotomy H0 H1 H2 H3 m H5)
        as [[Hb [nHm nHa]] | [[nHb [Hm nHa]] | [nHb [nHm Ha]]]];
        contradiction.
Qed.

Lemma basis_extension : forall {n k : nat} {P : GenVector n -> Prop} {A : GenMatrix n k},
    WF_GenMatrix A -> subspace P ->
    (forall i, (i < k)%nat -> P (get_col A i)) -> linearly_independent A ->
    ~ (forall v, P v -> span A v) ->
    (exists d, (k < d <= n)%nat /\
            (exists (B : GenMatrix n (d - k)), WF_GenMatrix B /\
                (forall i, (i < (d - k))%nat -> P (get_col B i)) /\ basis P (smash A B))).
Proof. intros n k P A H0 H1 H2 H3 H4.
  destruct (temp_exists_middle H0 H1 H2 H3 H4)
    as [m [mbound [B [WFB [BinP [linindepAB ABspansP]]]]]].
  exists m; repeat (split; auto);
    exists B; repeat (split; auto).
  replace (k + (m - k))%nat with m by lia.
  intros i0 H5. 
  bdestruct (i0 <? k)%nat.
  - setoid_rewrite get_col_smash_left; auto.
  - setoid_rewrite get_col_smash_right; auto.
    apply BinP; lia.
Qed.

Lemma exists_dimension : forall {n : nat} {P : GenVector n -> Prop},
    subspace P -> (exists d, dimension P d /\ (d <= n)%nat).
Proof. intros n P H.
  destruct (Classical_Prop.classic (forall v : GenVector n, P v -> v = Zero)).
  - exists 0%nat.
    split; try lia.
    unfold dimension.
    exists Zero.
    split; auto with wf_db.
    unfold basis.
    repeat (split; auto).
    + intros i0 H1.
      inversion H1.
    + intros v H1.
      unfold span.
      specialize (H0 v H1).
      subst.
      exists Zero.
      split; auto with wf_db.
    + unfold linearly_independent.
      intros a H1 H2.
      unfold WF_GenMatrix in H1.
      prep_genmatrix_equality.
      rewrite H1; auto; lia.
  - apply Classical_Pred_Type.not_all_ex_not in H0.
    destruct H0 as [v H0].
    apply Classical_Prop.imply_to_and in H0.
    destruct H0.
    assert (WF_GenMatrix v).
    { unfold subspace in H.
      destruct H.
      apply H; auto. }
    assert (forall i : nat, (i < 1)%nat -> P (get_col v i)).
    { intros i0 H3.
      replace i0 with 0%nat by lia.
      setoid_rewrite get_col_vec; auto. }
    assert (linearly_independent v)
      by (apply lin_indep_vec; auto).
    destruct (Classical_Prop.classic (forall w : GenVector n, P w -> span v w)).
    + pose (linearly_independent_dimensions v H2 H4).
      exists 1%nat; split; try lia.
      unfold dimension.
      exists v; split; auto with wf_db.
      unfold basis.
      repeat (split; auto).
    + destruct (basis_extension H2 H H3 H4 H5)
        as [d [dbound [B [WFB [BinP basisAB]]]]].
      exists (1 + (d - 1))%nat; split; try lia.
      unfold dimension.
      exists (smash v B); split;
        auto with wf_db.
Qed.

(* Theorem 45 Let V be an n-dimensional vector space over a field F, and let u1,u2,...,un be vectors in V .
1. If {u1,u2,...,un} spans V , then {u1,u2,...,un} is linearly independent and hence is a basis for V .
2. If {u1,u2,...,un} is linearly independent, then {u1,u2,...,un} spans V and hence is a basis for V. *)
Lemma equal_dimension_span_lin_indep : forall {n d : nat} {P : GenVector n -> Prop} {A : GenMatrix n d},
    WF_GenMatrix A -> subspace P -> dimension P d ->
    (forall i, (i < d)%nat -> P (get_col A i)) ->
    (forall v, P v -> span A v) -> linearly_independent A.
Proof. intros n d P A H H0 H1 H2 H3.
  bdestruct (d <=? 0)%nat.
  - unfold linearly_independent.
    intros a H5 H6.
    prep_genmatrix_equality.
    rewrite H5; auto; try lia.
  - remember H1 as H1'. clear HeqH1'.
    unfold dimension in H1.
    destruct H1 as [B [WFB basisB]].
    unfold basis in basisB.
    destruct basisB as [subspaceP [BinP [BspansP linindepB]]].
    assert (nonzerovec : @e_i d 0%nat <> Zero).
      { intro.
        unfold e_i in H1.
        apply f_equal_inv with (x := 0%nat) in H1.
        apply f_equal_inv with (x := 0%nat) in H1.
        simpl in H1.
        rewrite andb_true_r in H1.
        assert ((0 <? d)%nat = true) by (rewrite Nat.ltb_lt; auto).
        rewrite H5 in H1.
        simpl in H1.
        unfold Zero in *.
        contradict H1.
        apply G1_neq_0. }
      assert (WF_GenMatrix (@e_i d 0%nat)) by auto with wf_db.
      assert (forall m, (@Zero m d) × (@e_i d 0%nat) = Zero) by (intros; rewrite GMmult_0_l; auto).
    assert (n <> 0%nat).
    { intro.
      subst.
      assert (B = Zero).
      { prep_genmatrix_equality.
        rewrite WFB; auto.
        left. lia. }
      subst.
      unfold linearly_independent in linindepB.
      contradict nonzerovec.
      apply linindepB; auto. }
    assert (~ forall i : nat, (i < d)%nat -> get_col B i = Zero).
    { intro.
      assert (B = Zero).
      { prep_genmatrix_equality.
        bdestruct (x <? n)%nat; [idtac | rewrite WFB; auto].
        bdestruct (y <? d)%nat; [idtac | rewrite WFB; auto].
        assert (B x y = get_col B y x 0%nat) by (bdestruct_all; auto).
        rewrite H10.
        rewrite H7; auto. }
      subst.
      unfold linearly_independent in linindepB.
      contradict nonzerovec.
      apply linindepB; auto. }
    assert (exists v : GenVector n, v <> Zero /\ P v).
    { apply Classical_Pred_Type.not_all_ex_not in H7.
      destruct H7 as [i H7].
      apply Classical_Prop.imply_to_and in H7.
      destruct H7.
      exists (get_col B i).
      split; auto. }
    destruct (subset_basis H H4 H0 H2 H3 H8)
      as [indices_list [incl_list [NoDuplist basisP]]].
    assert (length (List.seq 0 d) <= length indices_list)%nat.
    { assert (dimension P (length indices_list)).
      { unfold dimension.
        exists (matrix_column_choose indices_list A).
        split; auto with wf_db. }
      pose (unique_dimension H9 H1').
      rewrite seq_length, e; auto. }
    pose (NoDup_Permutation_bis NoDuplist H9 incl_list) as p.
    rewrite (permutation_preserves_basis H subspaceP p) in basisP.
    unfold basis in basisP.
    destruct basisP as [subspaceP' [AinP [AspansP linindepA]]].
    rewrite matrix_column_choose_original in *; auto.
    rewrite ! seq_length in *; auto.
Qed.

Lemma equal_dimension_span_basis : forall {n d : nat} {P : GenVector n -> Prop} {A : GenMatrix n d},
    WF_GenMatrix A -> subspace P -> dimension P d ->
    (forall i, (i < d)%nat -> P (get_col A i)) ->
    (forall v, P v -> span A v) -> basis P A.
Proof. intros n d P A H0 H1 H2 H3 H4.
  assert (linearly_independent A)
    by (apply @equal_dimension_span_lin_indep with (P := P); auto).
  unfold basis.
  repeat (split; auto).
Qed.

Lemma equal_dimension_lin_indep_span : forall {n d : nat} {P : GenVector n -> Prop} {A : GenMatrix n d},
    WF_GenMatrix A -> subspace P -> dimension P d ->
    (forall i, (i < d)%nat -> P (get_col A i)) ->
    linearly_independent A -> (forall v, P v -> span A v).
Proof. intros n d P A H H0 H1 H2 H3 v H4.
  bdestruct (d <=? 0)%nat.
  - unfold span.
    exists Zero; split; auto with wf_db.
    rewrite GMmult_0_r.
    destruct H1 as [M [WFM basisM]].
    assert (d = 0)%nat by lia.
    subst.
    assert (M = Zero).
    { prep_genmatrix_equality.
      rewrite WFM; auto; lia. }
    subst.
    unfold basis in basisM.
    destruct basisM as [subspaceP' [ZeroinP [ZerospansP linindepZero]]].
    specialize (ZerospansP v H4).
    unfold span in ZerospansP.
    destruct ZerospansP as [a [WFa vZero]].
    rewrite GMmult_0_l in vZero.
    assumption.
  - destruct (Classical_Prop.classic (forall w, P w -> span A w)); auto.
    apply Classical_Pred_Type.not_all_ex_not in H6.
    destruct H6 as [w H6].
    apply Classical_Prop.imply_to_and in H6.
    destruct H6.
    remember H0 as H0'. clear HeqH0'.
    destruct H0' as [WFP [PZero [Psum Pscale]]].
    assert (WF_GenMatrix w) by (apply WFP; auto).
    pose (extend1_lin_indep H0 H H8 H3 H2 H7).
    destruct H1 as [B [WFB basisB]].
    assert (WF_GenMatrix (col_append A w)) by (unfold col_append; auto with wf_db).
    assert (forall i : nat, (i < S d)%nat -> P (get_col (col_append A w) i)).
    { intros i0 H9.
      bdestruct (i0 =? d)%nat.
      - subst.
        rewrite get_col_col_append_back; auto.
      - rewrite get_col_col_append_front; auto.
        apply H2; lia. lia. }
    assert (S d > d)%nat by lia.
    pose (dimension_overflow P B (col_append A w) WFB H1 basisB H9 H10) as l0.
    apply lindep_implies_not_linindep in l0; contradiction.
Qed.

Lemma equal_dimension_lin_indep_basis : forall {n d : nat} {P : GenVector n -> Prop} {A : GenMatrix n d},
    WF_GenMatrix A -> subspace P -> dimension P d ->
    WF_GenMatrix A -> (forall i, (i < d)%nat -> P (get_col A i)) ->
    linearly_independent A -> basis P A.
Proof. intros n d P A H0 H1 H2 H3 H4 H5.
  assert (forall v, P v -> span A v)
    by (apply @equal_dimension_lin_indep_span with (P := P); auto).
  unfold basis.
  repeat (split; auto).
Qed.

Lemma span_get_col : forall {n m : nat} (M : GenMatrix n m) (i : nat),
    WF_GenMatrix M -> (i < m)%nat -> span M (get_col M i).
Proof. intros n m M i0 H0 H1.
  unfold span.
  exists (e_i i0).
  split; auto with wf_db; rewrite matrix_by_basis; auto with wf_db.
Qed.

Lemma swap_equivalent_subspace_in_basis : 
  forall {n m : nat} {P1 P2 : GenVector n -> Prop} {M : GenMatrix n m},
    (forall v : GenVector n, P1 v <-> P2 v) -> (basis P1 M <-> basis P2 M).
Proof. intros n m P1 P2 M H0.
  unfold basis; split; intros H1; destruct H1 as [H1 [H2 [H3 H4]]];
    destruct H1 as [H5 [H6 [H7 H8]]];
    repeat (split; intros; auto with wf_db).
  - apply H5; rewrite H0; easy.
  - rewrite <- H0; easy.
  - rewrite <- H0; apply H7; rewrite H0; auto.
  - rewrite <- H0; apply H8; rewrite H0; auto.
  - rewrite <- H0; apply H2; auto.
  - apply H3; rewrite H0; auto.
  - apply H5; rewrite <- H0; easy.
  - rewrite H0; easy.
  - rewrite H0; apply H7; rewrite <- H0; auto.
  - rewrite H0; apply H8; rewrite <- H0; auto.
  - rewrite H0; apply H2; auto.
  - apply H3; rewrite <- H0; auto.
Qed.

Lemma swap_equivalent_subspace_in_dimension : 
  forall {n d : nat} {P1 P2 : GenVector n -> Prop},
    (forall v : GenVector n, P1 v <-> P2 v) -> (dimension P1 d <-> dimension P2 d).
Proof. intros. unfold dimension. split; intros.
  - destruct H0 as [B [H0 H1]].
    exists B. split; auto.
    rewrite <- @swap_equivalent_subspace_in_basis with (P1 := P1); auto.
  - destruct H0 as [B [H0 H1]].
    exists B. split; auto.
    rewrite @swap_equivalent_subspace_in_basis with (P2 := P2); auto.
Qed.

Lemma span_WF_GenMatrix : forall {n m : nat} {M : GenMatrix n m} {v : GenVector n},
    WF_GenMatrix M -> span M v -> WF_GenMatrix v.
Proof. intros n m M v H0 H1.
  unfold span in H1.
  destruct H1 as [a [H1 H2]].
  rewrite H2.
  auto with wf_db.
Qed.

Lemma equal_matrix_iff_equal_cols : forall {n m : nat} {M1 M2 : GenMatrix n m},
    WF_GenMatrix M1 -> WF_GenMatrix M2 ->
    M1 = M2 <-> (forall i : nat, i < m -> get_col M1 i = get_col M2 i).
Proof. intros n m M1 M2 WF1 WF2. split; intros H.
  - rewrite H; auto.
  - prep_genmatrix_equality.
    unfold get_col in H.
    bdestruct (x <? n).
    + bdestruct (y <? m).
      * specialize (H y H1).
        apply f_equal_inv with (x := x) in H.
        apply f_equal_inv with (x := 0%nat) in H.
        simpl in H.
        auto.
      * rewrite WF1, WF2; auto; lia.
    + rewrite WF1, WF2; auto; lia.
Qed.

Lemma equal_matrix_iff_equal_vector_mult : forall {n m : nat} {M1 M2 : GenMatrix n m},
    WF_GenMatrix M1 -> WF_GenMatrix M2 ->
    M1 = M2 <-> (forall v : GenVector m, WF_GenMatrix v -> M1 × v = M2 × v).
Proof. intros n m M1 M2 WF1 WF2. split; intros H.
  - rewrite H; auto.
  - rewrite equal_matrix_iff_equal_cols; auto.
    intros i H0. 
    rewrite ! matrix_by_basis; auto.
    apply H.
    auto with wf_db.
Qed.

Lemma span_in_subspace : forall {n m : nat} {M : GenMatrix n m} {P : GenVector n -> Prop},
    subspace P ->
    (forall i : nat, (i < m)%nat -> P (get_col M i)) ->
    (forall v : GenVector n, span M v -> P v).
Proof. intros n m M P H0 H1 v H2.
  unfold span in H2.
  destruct H2 as [a [H2 H3]].
  rewrite H3.
  apply subspace_closed_under_linear_combinations;
    auto with wf_db.
Qed.

Lemma subspace_is_basis_span : forall {n m : nat} {P : GenVector n -> Prop} {M : GenMatrix n m},
    basis P M -> (forall v : GenVector n, P v <-> span M v).
Proof. intros n m P M H0 v.
  destruct H0 as [H0 [H1 [H2 H3]]];
    split; intros.
  - apply H2; easy.
  - apply (span_in_subspace H0 H1); easy.
Qed.

Lemma equal_basis_equivalent_subspace : 
  forall {n m : nat} {P1 P2 : GenVector n -> Prop} {M : GenMatrix n m},
    basis P1 M -> basis P2 M -> (forall v : GenVector n, P1 v <-> P2 v).
Proof. intros n m P1 P2 M H H0 v.
  split; intros H1.
  - unfold basis in H.
    destruct H as [subspaceP1 [MinP1 [MspanP1 lin_indep_M]]].
    specialize (MspanP1 v H1).
    rewrite (subspace_is_basis_span H0); auto.
  - unfold basis in H0.
    destruct H0 as [subspaceP2 [MinP2 [MspanP2 lin_indep_M']]].
    specialize (MspanP2 v H1).
    rewrite (subspace_is_basis_span H); auto.
Qed.

Lemma equal_dimension_subspace_basis : 
  forall {n m d : nat} {P1 P2 : GenVector n -> Prop} {M : GenMatrix n m},
    subspace P1 -> subspace P2 -> (forall v : GenVector n, P1 v -> P2 v) -> 
    dimension P1 d -> dimension P2 d -> 
    WF_GenMatrix M -> basis P1 M -> basis P2 M.
Proof. intros n m d P1 P2 M H H0 H1 H2 H3 H4 H5. 
  apply equal_dimension_lin_indep_basis; auto.
  - unfold dimension in H2.
    destruct H2 as [A1 [WFA1 basisA1]].
    pose (basis_equal_number H4 WFA1 H5 basisA1) as e.
    remember e as e'. clear e Heqe'.
    subst. auto.
  - intros i H6. 
    unfold basis in H5.
    destruct H5 as [H5 [H7 [H8 H9]]].
    auto.
  - unfold basis in H5.
    destruct H5 as [H5 [H7 [H8 H9]]].
    auto.
Qed.

Lemma equal_dimension_subspace_basis_iff : 
  forall {n m d : nat} {P1 P2 : GenVector n -> Prop} {M : GenMatrix n m},
    subspace P1 -> subspace P2 -> (forall v : GenVector n, P1 v -> P2 v) -> 
    dimension P1 d -> dimension P2 d -> 
    WF_GenMatrix M -> (basis P1 M <-> basis P2 M).
Proof. intros n m d P1 P2 M H H0 H1 H2 H3 H4.
  split; intros H5.
  - apply (equal_dimension_subspace_basis H H0 H1 H2 H3 H4 H5).
  - remember H2 as H2'. clear HeqH2'.
    unfold dimension in H2'.
    destruct H2' as [A1 [WFA1 basisA1]].
    pose (equal_dimension_subspace_basis H H0 H1 H2 H3 WFA1 basisA1) as b.
    remember b as b'. clear b Heqb'.
    pose (equal_basis_equivalent_subspace basisA1 b') as l.
    rewrite (swap_equivalent_subspace_in_basis l). auto.
Qed.

Lemma span_dimension : forall {n m d : nat} {M : GenMatrix n m},
    WF_GenMatrix M -> dimension (span M) d -> d <= m.
Proof. intros n m d M WFM H.
  unfold dimension in H.
  destruct H as [B [WFB basisB]].
  remember basisB as basisB'. clear HeqbasisB'.
  unfold basis in basisB.
  destruct  basisB  as [subspace_span [Binspan [spanMinspanB lin_indep_B]]].
  bdestruct (m =? 0)%nat.
  - subst.
    assert (M = Zero).
    { unfold Zero. prep_genmatrix_equality. rewrite WFM; auto; lia. }
    subst.
    unfold span in Binspan.
    assert (B = Zero).
    { rewrite equal_matrix_iff_equal_cols; auto with wf_db.
      intros i H.
      specialize (Binspan i H).
      destruct Binspan as [a [WFa getcolB]].
      rewrite GMmult_0_l in getcolB; auto.
      rewrite getcolB.
      unfold get_col, Zero.
      prep_genmatrix_equality.
      bdestruct_all; auto. }
    bdestruct (d =? 0)%nat; try lia.
    unfold linearly_independent in lin_indep_B.
    assert (@WF_GenMatrix d 1%nat 
              (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then 1%G else 0%G)).
    { unfold WF_GenMatrix. intros x y H1. bdestruct_all; simpl; auto. }
    assert (@GMmult n d 1%nat B (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then 1%G else 0%G) = Zero). { rewrite H, GMmult_0_l; auto. }
    specialize (lin_indep_B (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then 1%G else 0%G)
               H1 H2).
    apply f_equal_inv with (x := 0%nat) in lin_indep_B.
    apply f_equal_inv with (x := 0%nat) in lin_indep_B.
    unfold Zero in lin_indep_B.
    simpl in lin_indep_B.
    contradict lin_indep_B.
    apply G1_neq_0.
  - bdestruct (d =? 0)%nat; try lia.
    destruct (@subset_basis n m (span M) M) 
      as [indices_list [incl_indices [NoDup_indices basis_subset]]]; auto; try lia.
    + intros i H1. apply span_get_col; auto.
    + exists (get_col B 0%nat). split.
      * intro H1.
        unfold linearly_independent in lin_indep_B.
        assert (@WF_GenMatrix d 1%nat 
                  (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then 1%G else 0%G)).
        { unfold WF_GenMatrix. intros x y H2. bdestruct_all; simpl; auto. }
        assert (@GMmult n d 1%nat B (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then 1%G else 0%G) = Zero).
        { unfold GMmult, Zero. prep_genmatrix_equality. unfold get_col, Zero in H1.
          apply f_equal_inv with (x := x) in H1.
          apply f_equal_inv with (x := 0%nat) in H1.
          simpl in H1. 
          apply big_sum_unique.
          exists 0%nat. split; try lia.
          split; intros; bdestruct_all; try rewrite ! H1; simpl; auto; ring. }
        specialize (lin_indep_B (fun r c : nat => if (r =? 0)%nat && (c =? 0)%nat then 1%G else 0%G)
                      H2 H3).
        apply f_equal_inv with (x := 0%nat) in lin_indep_B.
        apply f_equal_inv with (x := 0%nat) in lin_indep_B.
        unfold Zero in lin_indep_B.
        simpl in lin_indep_B.
        contradict lin_indep_B.
        apply G1_neq_0.
      * apply Binspan; lia.
    + assert (WF_GenMatrix (matrix_column_choose indices_list M)).
      { apply WF_GenMatrix_matrix_column_choose_indices_list; auto. }
      pose (basis_equal_number WFB H1 basisB' basis_subset) as e.
      rewrite e.
      pose (NoDup_incl_length NoDup_indices incl_indices) as l.
      rewrite seq_length in l. auto.
Qed.

Lemma zerospace_is_subspace : forall {n : nat}, subspace (fun v : GenVector n => v = Zero).
Proof. repeat split; intros; subst; auto with wf_db; lgma. Qed.

Lemma totalspace_is_subspace : forall (n : nat), subspace (fun v : GenVector n => WF_GenMatrix v).
Proof. intros n. repeat split; intros; auto with wf_db. Qed. 

Lemma basis_I_totalspace : forall (n : nat), basis (fun v : GenVector n => WF_GenMatrix v) (I n).
Proof. intros n. unfold basis. repeat split; intros; auto with wf_db.
  - unfold span. exists v. split; auto. rewrite GMmult_1_l; auto.
  - unfold linearly_independent.
    intros a H H0. rewrite GMmult_1_l in H0; auto.
Qed.

Lemma  dimension_totalspace : forall (n : nat), dimension (fun v : GenVector n => WF_GenMatrix v) n.
Proof. intros n. unfold dimension. exists (I n). split; auto with wf_db. apply basis_I_totalspace. Qed.

Definition kernel {n m : nat} (M : GenMatrix n m) (u : GenVector m) : Prop := WF_GenMatrix u /\ M × u = Zero.

Inductive nullity {n m : nat} (M : GenMatrix n m) (k : nat) : Prop :=
| Null : dimension (kernel M) k -> nullity M k.

Lemma kernel_is_subspace : forall {n m : nat} (M : GenMatrix n m), subspace (kernel M).
Proof. intros n m M.
  unfold subspace, kernel. 
  repeat split; intros.
  1,3,5: destruct H; try destruct H0; auto with wf_db.
  - rewrite GMmult_0_r; auto.
  - destruct H, H0.
    rewrite GMmult_plus_distr_l; rewrite H1, H2; 
      unfold Zero, GMplus; prep_genmatrix_equality; simpl; ring.
  - destruct H. rewrite Mscale_mult_dist_r; auto. rewrite H0.
    unfold Zero, scale. prep_genmatrix_equality. ring.
Qed.

Lemma span_in_kernel : forall {n m o : nat} {M : GenMatrix n m} {K : GenMatrix m o},
    (forall i : nat, (i < o)%nat -> kernel M (get_col K i)) ->
    (forall v : GenVector n, span K v -> kernel M v).
Proof. intros n m o M K H v H0. 
  unfold span in H0.
  destruct H0 as [a [H0 H1]].
  rewrite H1.
  apply subspace_closed_under_linear_combinations;
    auto with wf_db.
  apply kernel_is_subspace.
Qed.

Inductive col_rank {n m : nat} (M : GenMatrix n m) (r : nat) : Prop :=
| ColRank : dimension (span M) r -> col_rank M r.

Inductive row_rank {n m : nat} (M : GenMatrix n m) (r : nat) : Prop := 
| RowRank : dimension (span (M ⊤)) r -> row_rank M r.

Definition rank {n m : nat} (M : GenMatrix n m) (r : nat) := col_rank (M : GenMatrix n m) (r : nat).

Lemma col_rank_transposed_is_row_rank : forall {n m : nat} {M : GenMatrix n m} {r : nat},
    col_rank (M ⊤) r <-> row_rank M r.
Proof. intros n m M r. split; intros H.
  - inversion H. constructor. auto.
  - inversion H. constructor. auto.
Qed.

Lemma row_rank_transposed_is_col_rank : forall {n m : nat} {M : GenMatrix n m} {r : nat},
    row_rank (M ⊤) r <-> col_rank M r.
Proof. intros n m M r. split; intros H.
  - inversion H. constructor. rewrite transpose_involutive in *. auto.
  - inversion H. constructor. rewrite transpose_involutive in *. auto.
Qed.


(*****************************************************************)
(** * Preparing to prove the Rank-Nullity Theorem * **)
(*****************************************************************)

Lemma get_col_mult_nonsquare : forall {n m o : nat} (i : nat) (A : GenMatrix n m) (B : GenMatrix m o),
    get_col (A × B) i = A × (get_col B i).
Proof. intros. unfold get_col, GMmult.
       prep_genmatrix_equality.
       bdestruct (y =? 0).
       - reflexivity.
       - symmetry. apply (@big_sum_0 F R0). intros.
         apply Gmult_0_r.
Qed.

Lemma lin_indep_smash_left : forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
  linearly_independent (smash A1 A2) -> linearly_independent A1. 
Proof. induction n2 as [| n2'].
       - intros.  
         unfold linearly_independent in *. 
         intros. assert (H' : (n1 + 0)%nat = n1). lia. 
         rewrite H' in *.
         apply H; try easy.
         rewrite <- H1.
         unfold smash, GMmult. 
         prep_genmatrix_equality. 
         apply big_sum_eq_bounded.
         intros. 
         bdestruct_all; try lia; easy.
       - intros.  
         assert (H1 := @lin_indep_col_reduce m (n1 + n2') (smash A1 A2) (n1 + n2')). 
         rewrite <- plus_n_Sm in H.
         apply H1 in H; auto.
         rewrite smash_reduce in H.
         apply (IHn2' n1 A1 (reduce_col A2 n2')).
         easy.
Qed.

Definition matrix_to_list_vector {n m : nat} (M : GenMatrix n m) :=
  map (fun i : nat => get_col M i) (List.seq 0 m).

Lemma matrix_to_list_vector_to_matrix : forall {n m : nat} {M : GenMatrix n m},
    WF_GenMatrix M -> list_vector_to_matrix (matrix_to_list_vector M) = M.
Proof. intros n m M H.
  unfold list_vector_to_matrix, matrix_to_list_vector.
  prep_genmatrix_equality.
  assert (@Zero n 1%nat = get_col M m).
  { prep_genmatrix_equality.
    unfold get_col.
    bdestruct_all; auto.
    rewrite H; auto; lia. }
  rewrite H0.
  rewrite map_nth with (d := m).
  unfold get_col.
  bdestruct_all.
  bdestruct (y <? m)%nat.
  - rewrite seq_nth; auto.
  - rewrite nth_overflow; try rewrite seq_length; auto.
    rewrite ! H; auto.
Qed.

Lemma list_vector_to_matrix_to_list_vector : forall {n : nat} {list_vector : list (GenVector n)},
    (Forall WF_GenMatrix list_vector) ->
    matrix_to_list_vector (list_vector_to_matrix list_vector) = list_vector.
Proof. intros n list_vector AllWFM.
  apply (nth_ext (matrix_to_list_vector (list_vector_to_matrix list_vector)) list_vector (@Zero n 1%nat) (@Zero n 1%nat)); unfold matrix_to_list_vector, list_vector_to_matrix;
    rewrite map_length, seq_length; auto.
  intros n0 H0.
  assert (@Zero n 1%nat = @get_col n (length list_vector) (fun r c : nat => nth c list_vector (@Zero n 1%nat) r 0%nat) (length list_vector)).
  { prep_genmatrix_equality.
    unfold get_col.
    bdestruct_all; auto.
    rewrite nth_overflow; auto. }
  rewrite H at 1.
  rewrite map_nth with (d := length list_vector).
  unfold get_col.
  prep_genmatrix_equality.
  bdestruct_all.
  - rewrite seq_nth; auto.
  - rewrite Forall_nth in AllWFM.
    specialize (AllWFM n0 (@Zero n 1%nat) H0).
    rewrite AllWFM; auto; lia.
Qed.

Lemma matrix_to_list_vector_smash : forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
    (matrix_to_list_vector (smash A1 A2)) = 
      (matrix_to_list_vector A1) ++ (matrix_to_list_vector A2).
Proof. intros m n2 n1 A1 A2.
  unfold matrix_to_list_vector, get_col, smash.
  rewrite seq_app.
  rewrite map_app.
  f_equal.
  - apply map_ext_in.
    intros a H. rewrite in_seq in H.
    prep_genmatrix_equality.
    bdestruct_all; auto.
  - destruct n2; auto. 
    apply nth_ext with (d := (fun i x y : nat =>
                               if y =? 0 then if i <? n1 then A1 x i else A2 x (i - n1)%nat else 0) 0%nat) 
                       (d' := (fun i x y : nat => if y =? 0 then A2 x i else 0) 0%nat).
    + rewrite ! map_length. rewrite ! seq_length. auto.
    + intros n H. rewrite ! map_length in H. rewrite ! seq_length in H.
      rewrite ! map_nth with (d := 0%nat).
      prep_genmatrix_equality.
      bdestruct_all; auto.
      rewrite seq_nth in H0; auto. lia.
      rewrite seq_nth in H0; auto. f_equal. rewrite ! seq_nth; auto. lia.
Qed.

Lemma smash_swap_preserves_lin_indep : 
  forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    linearly_independent (smash A1 A2) -> linearly_independent (smash A2 A1).
Proof. intros m n2 n1 A1 A2 H H0 H1.
  assert (Permutation (matrix_to_list_vector (smash A1 A2)) (matrix_to_list_vector (smash A2 A1))).
  { rewrite ! matrix_to_list_vector_smash. 
    apply Permutation_app_comm. }
  rewrite <- matrix_to_list_vector_to_matrix; auto with wf_db.
  pose (permutation_preserves_linearly_indep H2) as l.
  assert ((@length (GenVector m) (@matrix_to_list_vector m (n2 + n1) (smash A2 A1))) =
            n2 + n1). { unfold matrix_to_list_vector. rewrite map_length, seq_length. auto. }
  rewrite H3 in l.
  apply l. 
  rewrite matrix_to_list_vector_to_matrix; auto with wf_db.
  assert ((@length (GenVector m) (@matrix_to_list_vector m (n1 + n2) (smash A1 A2))) =
            n1 + n2). { unfold matrix_to_list_vector. rewrite map_length, seq_length. auto. }
  rewrite H4.
  auto.
Qed.

Lemma smash_swap_preserves_lin_indep_iff : 
  forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    linearly_independent (smash A1 A2) <-> linearly_independent (smash A2 A1).
Proof. intros. split; intros;
  apply smash_swap_preserves_lin_indep; auto.
Qed.

Lemma smash_swap_preserves_span : 
  forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    (forall v : GenVector m, span (smash A1 A2) v -> span (smash A2 A1) v).
Proof. intros.
  assert (Permutation (matrix_to_list_vector (smash A1 A2)) (matrix_to_list_vector (smash A2 A1))).
  { rewrite ! matrix_to_list_vector_smash. 
    apply Permutation_app_comm. }
  rewrite <- matrix_to_list_vector_to_matrix; auto with wf_db.
  assert (length (matrix_to_list_vector (smash A2 A1)) = (n2 + n1)%nat).
  { unfold matrix_to_list_vector.
    rewrite map_length.
    rewrite seq_length. auto. }
  pose (@permutation_preserves_span m 
  (matrix_to_list_vector (smash A1 A2))
  (matrix_to_list_vector (smash A2 A1)) H2) as e.
  rewrite ! H3 in e.
  apply e.
  rewrite matrix_to_list_vector_to_matrix; auto with wf_db.
  assert (length (matrix_to_list_vector (smash A1 A2)) = (n1 + n2)%nat).
  { unfold matrix_to_list_vector.
    rewrite map_length.
    rewrite seq_length. auto. } 
  rewrite H4.
  apply H1; auto.
Qed.

Lemma smash_swap_preserves_span_iff : 
  forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    (forall v : GenVector m, span (smash A1 A2) v <-> span (smash A2 A1) v).
Proof. intros. split; intros;
  apply smash_swap_preserves_span; auto.
Qed.

Lemma smash_swap_preserves_subspace_containment : forall {m n1 n2 : nat} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2) {P : GenVector m -> Prop},
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    subspace P -> 
    (forall i : nat, (i < n1 + n2)%nat -> P (get_col (smash A1 A2) i)) ->
    (forall i : nat, (i < n2 + n1)%nat -> P (get_col (smash A2 A1) i)).
Proof. intros.
  bdestruct (i <? n2)%nat.
  - rewrite get_col_smash_left; try lia.
    specialize (H2 (n1 + i)%nat).
    rewrite get_col_smash_right in H2; try lia.
    replace (n1 + i - n1)%nat with i in H2 by lia.
    apply H2; lia.
  - rewrite get_col_smash_right; try lia.
    specialize (H2 (i - n2)%nat).
    rewrite get_col_smash_left in H2; try lia.
    apply H2; lia.
Qed.

Lemma smash_swap_preserves_subspace_containment_iff : forall {m n1 n2 : nat} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2) {P : GenVector m -> Prop},
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    subspace P -> 
    ((forall i : nat, (i < n1 + n2)%nat -> P (get_col (smash A1 A2) i)) <->
    (forall i : nat, (i < n2 + n1)%nat -> P (get_col (smash A2 A1) i))).
Proof. intros. split; intros;
  apply smash_swap_preserves_subspace_containment; auto.
Qed.

Lemma smash_swap_preserves_basis : forall {m n1 n2 : nat} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2) {P : GenVector m -> Prop},
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    subspace P -> 
    basis P (smash A1 A2) -> 
    basis P (smash A2 A1).
Proof. intros.
  unfold basis in *.
  destruct H2 as [H2 [H3 [H4 H5]]].
  split; auto.
  split. rewrite smash_swap_preserves_subspace_containment_iff; auto.
  split. setoid_rewrite smash_swap_preserves_span_iff; auto.
  rewrite smash_swap_preserves_lin_indep_iff; auto.
Qed.

Lemma lin_indep_smash_right : forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
    WF_GenMatrix A1 -> WF_GenMatrix A2 ->
    linearly_independent (smash A1 A2) -> linearly_independent A2. 
Proof. intros m n2 n1 A1 A2 H H0 H1.
  apply smash_swap_preserves_lin_indep in H1; auto.
  apply (lin_indep_smash_left A2 A1 H1).
Qed.

Lemma Mmult_smash_distr : forall {n m o2 o1} (M : GenMatrix n m) (A : GenMatrix m o1) (B : GenMatrix m o2), 
    M × (smash A B) = smash (M × A) (M × B).
Proof. intros n m o2 o1 M A B.
  unfold GMmult, smash.
  prep_genmatrix_equality.
  bdestruct_all; auto.
Qed.

Lemma rank_nullity_theorem : forall {n m : nat} {M : GenMatrix n m} {r k : nat},
    WF_GenMatrix M -> rank M r -> nullity M k -> (m = r + k)%nat.
Proof. intros n m M r k WFM H H0.
  inversion H. inversion H0.
  bdestruct (k =? m)%nat.
  - subst.
    unfold dimension in H2.
    destruct H2 as [K [WFK basis_kernelM_K]].
    assert (basis (fun v : GenVector m => WF_GenMatrix v) K).
    { apply @equal_dimension_subspace_basis with (P1 := kernel M) (d := m); auto.
      - unfold basis in basis_kernelM_K.
        destruct basis_kernelM_K
          as [subspace_kernelM [K_in_kernelM [kernelM_in_spanK lin_indep_K]]].
        auto.
      - apply totalspace_is_subspace.
      - intros v H2. unfold kernel in H2. destruct H2. auto.
      - unfold dimension. exists K. split; auto.
      - apply dimension_totalspace. }
    assert (forall v : GenVector m, WF_GenMatrix v -> M × v = Zero).
    { intros v H3. unfold basis in *.
      destruct basis_kernelM_K
        as [subspace_kernelM [K_in_kernelM [kernelM_in_spanK lin_indep_K]]].
      destruct H2
        as [subspace_totalspace [K_in_totalspace [totalspace_in_spanK lin_indep_K']]].
      specialize (totalspace_in_spanK v H3).
      pose (span_in_kernel K_in_kernelM v totalspace_in_spanK) as l.
      unfold kernel in l.
      destruct l; auto. }
    unfold dimension in H1.
    destruct H1 as [A [WFA basis_spanM_A]].
    assert (basis (span M) (@Zero n 0)).
    { unfold basis. split. 
      - apply span_is_subspace; auto.
      - split. 
        + intros i H1. unfold span. exists Zero. split; auto with wf_db.
          unfold get_col, GMmult, Zero. prep_genmatrix_equality. bdestruct_all. 
        + split. 
          * intros v H1. unfold span. exists Zero. split; auto with wf_db.
            rewrite GMmult_0_l; auto. unfold span in H1.
            destruct H1 as [a [WFa vZero]].
            specialize (H3 a WFa). rewrite H3 in vZero. auto.
          * unfold linearly_independent. intros a H1 H4.
            prep_genmatrix_equality. rewrite H1; auto; lia. }
    assert (WF_GenMatrix (@Zero n 0)) by auto with wf_db.
    pose (basis_equal_number WFA H4 basis_spanM_A H1) as e.
    rewrite e. auto.
  - destruct (exists_dimension (kernel_is_subspace M)) as [d [dim_d d_bound]].
    pose (unique_dimension dim_d H2) as e. remember e as e'. clear e Heqe'. subst.
    assert (k_bound : (k < m)%nat) by lia. clear H3 d_bound.
    unfold dimension in H2.
    destruct H2 as [K [WFK basis_kernelM_K]].
    destruct (@basis_extension m k (fun v : GenVector m => WF_GenMatrix v) K)
      as [d [d_bound [B [WFB [B_in_subspace basisPsmashKB]]]]]; auto.
    + unfold subspace.
      repeat (split; auto).
      * intros. auto with wf_db.
      * intros. auto with wf_db.
    + intros. auto with wf_db.
    + unfold basis in basis_kernelM_K.
      destruct basis_kernelM_K
        as [subspace_kernelM [K_in_kernelM [kernelM_in_spanK lin_indep_K]]].
      auto.
    + intro. assert (basis (fun v : GenVector m => WF_GenMatrix v) K).
      { unfold basis. split.
        - apply totalspace_is_subspace.
        - split. 
          + intros i H3. auto with wf_db.
          + split; auto. destruct basis_kernelM_K
              as [subspace_kernelM [K_in_kernelM [kernelM_in_spanK lin_indep_K]]].
            auto. }
      destruct (dimension_totalspace m) as [A [WFA basisA]].
      pose (basis_equal_number WFK WFA H3 basisA).
      lia.
    + assert (d = m).
      { destruct (dimension_totalspace m) as [A [WFA basisA]].
        assert (WF_GenMatrix (smash K B)) by auto with wf_db.
        pose (basis_equal_number H2 WFA basisPsmashKB basisA) as e.
        replace (k + (d - k))%nat with d in e by lia. auto. }
      subst.
      assert (basis (span M) (M × B)).
      { unfold basis. split; try apply span_is_subspace; auto. split.
        - intros i H2. unfold span. exists (get_col B i). split; auto with wf_db.
          rewrite get_col_mult_nonsquare; auto.
        - split. 
          + intros v H2. unfold span in *.
            destruct H2 as [a [WFa vMa]].
            unfold basis in basisPsmashKB.
            destruct basisPsmashKB
              as [subspace_totalspace [WFKB [KB_spans_totalspace lin_indep_smash]]].
        specialize (KB_spans_totalspace a WFa).
        unfold span in KB_spans_totalspace.
        destruct KB_spans_totalspace as [a' [WFa' aKBa']].
        exists (fun r c : nat => if (c =? 0)%nat then 
                         if (r <? m - k)%nat then a' (k + r)%nat 0%nat else 0%G
                       else 0%G).
        split.
            * unfold WF_GenMatrix.
              intros x y H2. 
              bdestruct_all; auto.
            * rewrite aKBa' in vMa.
              rewrite <- GMmult_assoc in vMa.
              rewrite Mmult_smash_distr in vMa.
              assert (M × K = Zero).
              { unfold basis in basis_kernelM_K.
                destruct basis_kernelM_K
                  as [subspace_kernelM [K_in_kernelM [kernelM_in_spanK lin_indep_K]]].
                rewrite equal_matrix_iff_equal_vector_mult; auto with wf_db.
                intros v0 H2.
                rewrite GMmult_assoc.
                pose (span_in_kernel K_in_kernelM) as l0.
                assert (span K (K × v0)).
                { unfold span. exists v0. split; auto. }
                specialize (l0 (K × v0) H3).
                unfold kernel in l0.
                destruct l0.
                rewrite GMmult_0_l; auto. }
              rewrite vMa.
              rewrite H2.
              unfold smash, GMmult, Zero.
              prep_genmatrix_equality.
              rewrite big_sum_sum.
              assert (Σ
                        (fun y0 : nat =>
                           (if y0 <? k then 0 else Σ (fun y1 : nat => M x y1 * B y1 (y0 - k)%nat) m) *
                             a' y0 y) k = 0%G).
              { rewrite big_sum_0_bounded; auto.
                intros x0 H3. bdestruct_all. ring. }
              rewrite H3.
              rewrite Gplus_0_l.
              apply big_sum_eq_bounded.
              intros x0 H4. bdestruct_all.
              -- subst. replace (k + x0 - k)%nat with x0 by lia. auto.
              -- replace (k + x0 - k)%nat with x0 by lia. f_equal.
                 rewrite WFa'; auto; lia.
          + unfold linearly_independent.
            intros a H2 H3.
            rewrite GMmult_assoc in H3.
            unfold basis in basis_kernelM_K.
            destruct basis_kernelM_K
              as [subspace_kernelM [K_in_kernelM [kernelM_in_spanK lin_indep_K]]].
            assert (kernel M (B × a)).
            { unfold kernel. split; auto with wf_db. }
            apply kernelM_in_spanK in H4.
            unfold span in H4.
            destruct H4 as [b [WFb BaKb]].

            assert (@GMmult m (k + (m - k))%nat 1%nat (smash K B) (fun r c : nat => 
                                 if (r <? k)%nat then - (b r c) else a (r - k)%nat c) = Zero).
            { unfold GMmult, smash, Zero.
              prep_genmatrix_equality.
              rewrite big_sum_sum.
              unfold GMmult in BaKb.
              apply f_equal_inv with (x := x) in BaKb.
              apply f_equal_inv with (x := y) in BaKb.
              assert (Σ
                        (fun x0 : nat =>
                           (if k + x0 <? k then K x (k + x0)%nat else B x (k + x0 - k)%nat) *
                             (if k + x0 <? k then - b (k + x0)%nat y else a (k + x0 - k)%nat y)) 
                        (m - k) =
                        Σ (fun y0 : nat => B x y0 * a y0 y) (m - k)).
              { apply big_sum_eq_bounded.
                intros x0 H4.
                bdestruct_all. repeat f_equal; lia. }
              rewrite H4.
              rewrite BaKb.
              assert (Σ
                        (fun y0 : nat =>
                           (if y0 <? k then K x y0 else B x (y0 - k)%nat) *
                             (if y0 <? k then - b y0 y else a (y0 - k)%nat y)) k =
                        Σ (fun y0 : nat => K x y0 * (- b y0 y)) k).
              { apply big_sum_eq_bounded.
                intros x0 H5.
                bdestruct_all. repeat f_equal; lia. }
              rewrite H5.
              rewrite <- big_sum_plus.
              rewrite big_sum_0_bounded; auto.
              intros x0 H6. ring. }
            unfold basis in basisPsmashKB.
            destruct basisPsmashKB
              as [subspace_totalspace [WFKB [KB_spans_totalspace lin_indep_smash]]].
            unfold linearly_independent in lin_indep_smash.
            assert (@WF_GenMatrix m 1%nat (fun r c : nat => if r <? k then - b r c else a (r - k)%nat c)).
            { unfold WF_GenMatrix. intros x y H6. bdestruct_all; auto. 
              rewrite WFb; auto; try lia; ring. rewrite H2; auto; lia. }
            replace (k + (m - k))%nat with m in lin_indep_smash by lia.
            specialize (lin_indep_smash (fun r c : nat => if r <? k then - b r c else a (r - k)%nat c) H5).
            replace (k + (m - k))%nat with m in H4 by lia.
            apply lin_indep_smash in H4.
            prep_genmatrix_equality.
            bdestruct (x <? m - k)%nat.
            * unfold Zero in *.
              apply f_equal_inv with (x := (k + x)%nat) in H4.
              apply f_equal_inv with (x := y) in H4.
              replace ((k + x) - k)%nat with x in H4 by lia.
              bdestruct (k + x <? k); auto; try lia.
            * rewrite H2; auto; lia. }
      unfold dimension in H1.
      destruct H1 as [A [WFA basisA]].
      assert (WF_GenMatrix (M × B)) by auto with wf_db.
      pose (basis_equal_number WFA H1 basisA H2) as e.
      rewrite e. lia.
Qed.

Lemma collect_columns_in_span : 
  forall {n m o : nat} {M : GenMatrix n m} {A : GenMatrix n o},
    WF_GenMatrix M -> WF_GenMatrix A ->
  (forall i : nat, i < m -> span A (get_col M i)) ->
  (exists B : GenMatrix o m, WF_GenMatrix B /\ M = A × B).
Proof. intros n m o M A WFM WFA H. 
  induction m.
  - exists Zero. split; auto with wf_db.
    rewrite GMmult_0_r; auto.
    prep_genmatrix_equality.
    rewrite WFM; auto; lia.
  - assert (forall i : nat, i < m -> span A (get_col (reduce_col M m) i)).
    { intros i H0. rewrite get_col_reduce_col; auto. }
    assert (WF_GenMatrix (reduce_col M m)).
    { apply WF_reduce_col; auto. }
    specialize (IHm (reduce_col M m) H1 H0).
    destruct IHm as [B [WFB reducedMAB]].
    assert (m < S m) by lia.
    specialize (H m H2).
    unfold span in H.
    destruct H as [a [WFa getcolMAa]].
    exists (col_wedge B a m).
    split; auto with wf_db.
    rewrite reduce_wedge_split_n with (T := M) at 1; auto with wf_db.
    rewrite ! smash_wedge; auto with wf_db.
    setoid_rewrite Mmult_smash_distr.
    f_equal; auto.
Qed.

Lemma row_rank_leq_col_rank : forall {n m : nat} {M : GenMatrix n m} {rr rc : nat},
    WF_GenMatrix M -> row_rank M rr -> col_rank M rc -> (rr <= rc)%nat.
Proof. intros n m M rr rc H H0 H1.
  inversion H0. inversion H1.
  destruct H3 as [Ac [WFAc basisAc]].
  unfold basis in basisAc.
  destruct basisAc 
    as [subsapce_spanM [Ac_in_spanM [Ac_spans_M lin_indep_Ac]]].
  assert (forall i : nat, i < m -> span Ac (get_col M i)).
  { intros i H3. apply Ac_spans_M. apply span_get_col; auto. }
  destruct (collect_columns_in_span H WFAc H3) as [B [WFB MAB]].
  assert (M⊤ = B⊤ × Ac⊤).
  { rewrite MAB. rewrite GMmult_transpose; auto. }
  assert (forall v : GenVector n, span M⊤ v -> span B⊤ v).
  { intros v H5.
    unfold span in H5.
    destruct H5 as [a' [WFa' vMta']].
    rewrite H4 in vMta'. rewrite GMmult_assoc in vMta'.
    unfold span.
    exists ((Ac) ⊤ × a'). split; auto with wf_db. }
  assert (subspace (span M⊤)) by (apply span_is_subspace; auto with wf_db).
  assert (subspace (span B⊤)) by (apply span_is_subspace; auto with wf_db).
  destruct (exists_dimension H7) as [d [dimd dbound]].
  assert (WF_GenMatrix (B⊤)) by auto with wf_db.
  pose (span_dimension H8 dimd).
  pose (subspace_dimension H6 H7 H5 H2 dimd).
  lia.
Qed.

Lemma row_rank_eq_col_rank : forall {n m : nat} {M : GenMatrix n m} {rr rc : nat},
    WF_GenMatrix M -> row_rank M rr -> col_rank M rc -> (rr = rc)%nat.
Proof. intros n m M rr rc H H0 H1.
  pose (row_rank_leq_col_rank H H0 H1).
  assert (WF_GenMatrix (M⊤)) by auto with wf_db.
  assert (row_rank (M⊤) rc).
  { rewrite row_rank_transposed_is_col_rank. auto. }
  assert (col_rank (M⊤) rr).
  { rewrite col_rank_transposed_is_row_rank. auto. }
  pose (row_rank_leq_col_rank H2 H3 H4).
  lia.
Qed.

Lemma row_rank_iff_col_rank : forall {n m r : nat} {M : GenMatrix n m},
    WF_GenMatrix M -> (row_rank M r <-> col_rank M r).
Proof. intros n m r M WFM. split; intros H. 
  - assert (dimension (span M) r).
    { destruct (@exists_dimension n (span M)) as [d [dimd dbound]]; 
        try apply span_is_subspace; auto with wf_db.
      assert (col_rank M d). { constructor. auto. }
      pose (row_rank_eq_col_rank WFM H H0) as e.
      rewrite e. auto. }
    constructor. auto.
  - assert (dimension (span M⊤) r).
    { destruct (@exists_dimension m (span M⊤)) as [d [dimd dbound]]; 
        try apply span_is_subspace; auto with wf_db.
      assert (row_rank M d). { constructor. auto. }
      pose (row_rank_eq_col_rank WFM H0 H) as e.
      rewrite <- e. auto. }
    constructor. auto.
Qed.

Lemma lin_indep_rows_implies_exists_sol : 
  forall {n m : nat} (A : GenMatrix n m) (b : GenVector n),
    WF_GenMatrix A -> WF_GenMatrix b -> 
    linearly_independent (A⊤) -> 
    (exists v : GenVector m, WF_GenMatrix v /\ A × v = b).
Proof. intros n m A b WFA WFb H.
  assert (row_rank A n).
  { constructor.
    unfold dimension.
    exists A⊤. split; auto with wf_db.
    unfold basis.
    split; try apply span_is_subspace; auto with wf_db.
    split. intros i H0. apply span_get_col; auto with wf_db. 
    split; auto. }
  rewrite row_rank_iff_col_rank in H0; auto.
  inversion H0. remember H1 as dimspanAn. clear HeqdimspanAn.
  unfold dimension in H1.
  destruct H1 as [B [WFB basisB]]. remember basisB as basisB'. clear HeqbasisB'.
  unfold basis in basisB.
  destruct basisB as [subspace_spanA [BinspanA [spanAinspanB lin_indep_B]]].
  assert (forall v : GenVector n, span A v <-> span B v).
  { intros v. split; intros H1. apply spanAinspanB; auto.
    assert (subspace (span A)) by (apply span_is_subspace; auto with wf_db).
    pose (span_in_subspace H2 BinspanA) as e.
    apply e. auto. }
  assert (basis (fun v : GenVector n => WF_GenMatrix v) B).
  { apply @equal_dimension_subspace_basis with (P1 := span B) (d := n); auto.
    - apply span_is_subspace; auto.
    - apply totalspace_is_subspace.
    - intro. apply span_WF_GenMatrix. auto.
    - unfold dimension.
      setoid_rewrite <- (swap_equivalent_subspace_in_basis H1).
      apply dimspanAn.
    - apply dimension_totalspace.
    - setoid_rewrite (swap_equivalent_subspace_in_basis H1) in basisB'. auto. }
  unfold basis in H2.
  destruct H2 as [subspace_totalspace [WFgetcolB [spanB lin_indep_B']]].
  specialize (spanB b WFb).
  rewrite <- H1 in spanB.
  unfold span in spanB.
  destruct spanB as [v [WFv bAv]].
  exists v. split; auto.
Qed.

Lemma invertible_right_mult_span_preserve :
  forall {n : nat} (A M : GenSquare n),
  WF_GenMatrix A -> invertible A -> 
    (forall v : GenVector n, 
      span M v <-> span (M × A) v).
Proof. intros.
  split; intros.
  - unfold span in *.
    destruct H1 as [a [WFa va]].
    assert (M × a = M × ((I n) × a)).
    { rewrite GMmult_1_l; auto. }
    unfold invertible in H.
    destruct H0 as [B [WFB invAB]].
    destruct invAB.
    rewrite <- H0 in H1.
    rewrite ! GMmult_assoc in H1.
    rewrite <- va in H1.
    exists (B × a). 
    split; auto with wf_db.
    rewrite ! GMmult_assoc.
    auto.
  - unfold span in *.
    destruct H1 as [a [WFa va]].
    unfold invertible in H.
    destruct H0 as [B [WFB invAB]].
    destruct invAB.
    exists (A × a).
    split; auto with wf_db.
    rewrite <- GMmult_assoc.
    auto.
Qed.

Lemma invertible_left_mult_basis :
  forall {n d : nat} (A M : GenSquare n) (B : GenMatrix n d),
  WF_GenMatrix A -> WF_GenMatrix M -> 
  WF_GenMatrix B -> invertible A -> 
    (basis (span M) B <-> 
      basis (span (A × M)) (A × B)).
Proof. intros. 
  unfold basis. split; intros.
  - destruct H3 as [[H3 [H4 [H5 H6]]] [H7 [H8 H9]]].
    split; [idtac | split; [idtac | split]].
    + apply span_is_subspace.
      auto with wf_db.
    + unfold span. intros.
      unfold span in H7.
      destruct (H7 i H10) as [a [H11 H12]].
      exists a.
      split; auto with wf_db.
      rewrite <- get_col_mult.
      rewrite GMmult_assoc.
      rewrite <- H12.
      auto.
    + unfold span. intros.
      destruct H10 as [a [H10 H11]].
      assert (span M (M × a)).
      { unfold span. exists a. 
        split; auto with wf_db. }
      specialize (H8 (M × a) H12).
      unfold span in H8.
      destruct H8 as [b [H8 H13]].
      rewrite GMmult_assoc in H11.
      rewrite H13 in H11.
      rewrite <- GMmult_assoc in H11.
      exists b.
      split; auto with wf_db.
    + unfold invertible in H2.
      destruct H2 as [A' [H2 H10]].
      destruct H10 as [H10 H11].
      unfold linearly_independent. intros.
      unfold linearly_independent in H9.
      assert (A' × (A × B × a) = Zero).
      { rewrite H13. rewrite GMmult_0_r. auto. }
      rewrite <- ! GMmult_assoc in H14.
      rewrite H11 in H14.
      rewrite GMmult_1_l in H14; auto.
  - destruct H3 as [[H3 [H4 [H5 H6]]] [H7 [H8 H9]]].
    unfold invertible in H2.
    destruct H2 as [A' [H2 H10]].
    destruct H10 as [H10 H11].
    split; [idtac | split; [idtac | split]].
    + apply span_is_subspace.
      auto with wf_db.
    + intros. unfold span in H7.
      destruct (H7 i H12) as [a [H13 H14]].
      rewrite <- get_col_mult in H14.
      assert (A' × (A × get_col B i) =
              A' × (A × M × a)).
      { rewrite H14. auto. }
      rewrite <- ! GMmult_assoc in H15.
      rewrite ! H11 in H15.
      rewrite ! GMmult_1_l in H15; auto with wf_db.
      rewrite H15.
      unfold span. exists a. split; auto.
    + unfold span. intros.
      destruct H12 as [a [H12 H13]].
      assert (span (A × M) (A × v)).
      { rewrite H13, <- GMmult_assoc.
        unfold span. exists a. split; auto. }
      specialize (H8 (A × v) H14).
      unfold span in H8.
      destruct H8 as [b [H8 H15]].
      assert (A' × (A × v) = A' × (A × B × b)).
      { rewrite H15. auto. }
      rewrite <- ! GMmult_assoc in H16.
      rewrite H11 in H16.
      rewrite ! GMmult_1_l in H16; auto with wf_db.
      exists b. split; auto. 
      rewrite H13. auto with wf_db.
    + unfold linearly_independent. intros.
      unfold linearly_independent in H9.
      assert (A × (B × a) = Zero).
      { rewrite H13. rewrite GMmult_0_r. auto. }
      rewrite <- GMmult_assoc in H14.
      auto.
Qed.

Lemma invertible_left_mult_dim_preserve :
  forall {n : nat} (d : nat) (A M : GenSquare n),
    WF_GenMatrix A -> WF_GenMatrix M -> 
    invertible A -> 
      (dimension (span M) d <-> 
        dimension (span (A × M)) d).
Proof. intros. unfold dimension. 
  split; intros H2;
  destruct H2 as [B [H2 H3]].
  - exists (A × B).
    split; auto with wf_db.
    rewrite <- invertible_left_mult_basis; auto.
  - remember H1 as H1'. clear HeqH1'.
    unfold invertible in H1.
    destruct H1 as [A' [H1 H4]].
    destruct H4 as [H4 H5].
    assert (B = I n × B).
    { rewrite GMmult_1_l; auto. }
    rewrite <- H4 in H6.
    rewrite GMmult_assoc in H6.
    rewrite H6 in H3.
    rewrite <- invertible_left_mult_basis in H3;
      auto with wf_db.
    exists (A' × B).
    split; auto with wf_db.
Qed.

(** internal_direct_sum **)
Definition no_subspace_overlap {n : nat} (P1 P2 : GenVector n -> Prop) :=
  (forall v : GenVector n, P1 v -> P2 v -> v = Zero).

Definition subspace_sum {n : nat} (P1 P2 : GenVector n -> Prop) (v : GenVector n) : Prop :=
  (exists v1 v2 : GenVector n, P1 v1 /\ P2 v2 /\ v = v1 .+ v2).

Lemma no_subspace_overlap_sym : forall {n : nat} (P1 P2 : GenVector n -> Prop),
    no_subspace_overlap P1 P2 -> no_subspace_overlap P2 P1.
Proof. intros n P1 P2 H.
  unfold no_subspace_overlap in *.
  intros v H0 H1.
  auto.
Qed.

Lemma subspace_sum_sym : forall {n : nat} (P1 P2 : GenVector n -> Prop),
    (forall v : GenVector n, subspace_sum P1 P2 v <-> subspace_sum P2 P1 v). 
Proof. intros n P1 P2 v.
  unfold subspace_sum.
  split; intros.
  - destruct H as [v1 [v2 [H [H1 H2]]]].
    exists v2. exists v1. repeat split; auto. rewrite H2. lgma.
  - destruct H as [v1 [v2 [H [H1 H2]]]].
    exists v2. exists v1. repeat split; auto. rewrite H2. lgma.
Qed.

Lemma subspace_sum_is_subspace : forall {n : nat} {P1 P2 : GenVector n -> Prop},
    subspace P1 -> subspace P2 -> subspace (subspace_sum P1 P2).
Proof. intros n P1 P2 H H0.
  unfold subspace in *.
  destruct H as [H [H1 [H2 H3]]].
  destruct H0 as [H0 [H4 [H5 H6]]].
  unfold subspace_sum.
  repeat split.
  - intros v H7.
    destruct H7 as [v1 [v2 [H7 [H8 H9]]]].
    rewrite H9.
    auto with wf_db.
  - exists Zero. exists Zero.
    repeat split; auto.
    lgma.
  - intros v w H7 H8.
    destruct H7 as [v1 [v2 [H7 [H9 H10]]]].
    destruct H8 as [u1 [u2 [H11 [H12 H13]]]].
    exists (v1 .+ u1). exists (v2 .+ u2).
    repeat split; auto.
    rewrite H10, H13.
    lgma.
  - intros v c H7.
    destruct H7 as [v1 [v2 [H7 [H9 H10]]]].
    exists (c .* v1). exists (c .* v2).
    repeat split; auto.
    rewrite H10.
    lgma.
Qed.

(* basis of internal_direct_sum subspaces is union of each basis *)
Lemma subspace_sum_basis_smash : forall {m n1 n2 : nat} (P1 P2 : GenVector m -> Prop) (M1 : GenMatrix m n1) (M2 : GenMatrix m n2),
    basis P1 M1 -> basis P2 M2 -> no_subspace_overlap P1 P2 ->
    basis (subspace_sum P1 P2) (smash M1 M2).
Proof. intros m n1 n2 P1 P2 M1 M2 H H0 H1.
  unfold basis in *.
  destruct H as [H [H2 [H3 H4]]].
  destruct H0 as [H0 [H5 [H6 H7]]].
  split; [idtac | split; [idtac | split]].
  apply subspace_sum_is_subspace; auto.
  - intros i H8.
    unfold subspace_sum.
    bdestruct (i <? n1).
    + exists (get_col M1 i). exists Zero.
      repeat split; auto. 
      unfold subspace in H0. 
      destruct H0 as [H0 [H0' [H0'' H0''']]]; auto.
      rewrite get_col_smash_left; auto.
      lgma.
    + exists Zero. exists (get_col M2 (i - n1)%nat).
      repeat split.
      unfold subspace in H. 
      destruct H as [H [H' [H'' H''']]]; auto.
      apply H5; lia.
      rewrite get_col_smash_right; auto.
      lgma.
  - intros v H8.
    unfold subspace_sum in H8.
    destruct H8 as [v1 [v2 [H8 [H9 H10]]]].
    rewrite H10.
    specialize (H3 v1 H8).
    specialize (H6 v2 H9).
    unfold span.
    unfold span in H3, H6.
    destruct H3 as [a [WFa H3]].
    destruct H6 as [b [WFb H6]].
    exists (fun r c => if r <? n1 then a r c else b (r - n1)%nat c).
    split.
    + unfold WF_GenMatrix.
      intros x y H11.
      bdestruct_all.
      * rewrite WFa; auto; lia.
      * rewrite WFb; auto; lia.
    + rewrite H3, H6.
      unfold smash, GMmult, GMplus.
      prep_genmatrix_equality.
      rewrite big_sum_sum.
      f_equal.
      * apply big_sum_eq_bounded.
        intros x0 H11.
        bdestruct_all; auto.
      * apply big_sum_eq_bounded.
        intros x0 H11.
        bdestruct_all.
        repeat f_equal; lia.
  - unfold no_subspace_overlap in *.
    unfold linearly_independent in *.
    intros a H8 H9.
    assert (@WF_GenMatrix n1 1 (fun r c => if r <? n1 then a r c else 0)).
    { unfold WF_GenMatrix. intros x y H10.
      bdestruct_all; auto. rewrite H8; auto; lia. }
    specialize (H4 (fun r c => if r <? n1 then a r c else 0) H10).
    assert (@WF_GenMatrix n2 1 (fun r c => if r <? n2 then a (n1 + r)%nat c else 0)).
    { unfold WF_GenMatrix. intros x y H11.
      bdestruct_all; auto. rewrite H8; auto; lia. }
    specialize (H7 (fun r c => if r <? n2 then a (n1 + r)%nat c else 0) H11).
    pose (span_in_subspace H H2) as H12.
    pose (span_in_subspace H0 H5) as H13.
    assert (forall v : GenVector m, P1 v <-> span M1 v) by (split; auto).
    assert (forall v : GenVector m, P2 v <-> span M2 v) by (split; auto).
    assert (@GMmult m n1 1 M1 (fun r c : nat => if r <? n1 then a r c else 0) 
            =  (GMopp (@GMmult m n2 1 M2 (fun r c : nat => if r <? n2 then a (n1 + r)%nat c else 0)))).
    { unfold GMopp, GMmult, scale.
      prep_genmatrix_equality.
      unfold smash, GMmult, Zero in H9.
      apply f_equal_inv with (x := x) in H9.
      apply f_equal_inv with (x := y) in H9.
      rewrite big_sum_sum in H9.
      apply Gplus_cancel_r 
        with (a := Σ (fun y0 : nat => M2 x y0 * (if y0 <? n2 then a (n1 + y0)%nat y else 0)) n2).
      assert (- (1) * Σ (fun y0 : nat => M2 x y0 * (if y0 <? n2 then a (n1 + y0)%nat y else 0)) n2 +
                Σ (fun y0 : nat => M2 x y0 * (if y0 <? n2 then a (n1 + y0)%nat y else 0)) n2 = 0) by ring.
      rewrite H16.
      setoid_rewrite <- H9 at 3.
      f_equal.
      - apply big_sum_eq_bounded. intros x0 H17. bdestruct_all. auto.
      - apply big_sum_eq_bounded. intros x0 H17. bdestruct_all. repeat f_equal; lia. }
    unfold GMopp in H16.
    setoid_rewrite <- Mscale_mult_dist_r in H16.
    assert (P1 (M1 × (fun r c : nat => if r <? n1 then a r c else 0))).
    { rewrite H14. unfold span. exists (fun r c : nat => if r <? n1 then a r c else 0). split; auto. }
    assert (P2 (M2 × (- (1) .* (fun r c : nat => if r <? n2 then a (n1 + r)%nat c else 0)))).
    { rewrite H15. unfold span. exists (- (1) .* (fun r c : nat => if r <? n2 then a (n1 + r)%nat c else 0)).
      split; auto with wf_db. }
    rewrite <- H16 in H18.
    specialize (H1 (M1 × (fun r c : nat => if r <? n1 then a r c else 0)) H17 H18).
    specialize (H4 H1).
    rewrite H4 in H16.
    rewrite GMmult_0_r in H16. symmetry in H16.
    rewrite Mscale_mult_dist_r in H16.
    apply Mscale_inj with (c := - 1%F) in H16.
    rewrite Mscale_assoc in H16.
    replace ((- 1%F) * (- 1%F))%G with 1%F in H16 by ring.
    rewrite Mscale_1_l in H16.
    replace ((- 1%F) .* @Zero m 1) with (@Zero m 1) in H16 by lgma.
    specialize (H7 H16).
    prep_genmatrix_equality.
    unfold Zero in *.
    bdestruct (y =? 0).
    + subst.
      bdestruct (x <? n1).
      * apply f_equal_inv with (x := x) in H4.
        apply f_equal_inv with (x := 0) in H4.
        bdestruct (x <? n1); try lia.
        auto.
      * bdestruct (x <? n1 + n2).
        -- apply f_equal_inv with (x := (x - n1)%nat) in H7.
           apply f_equal_inv with (x := 0) in H7.
           bdestruct (x - n1 <? n2); try lia.
           replace (n1 + (x - n1)%nat)%nat with x in H7 by lia.
           auto.
        -- rewrite H8; auto; lia.
    + rewrite H8; auto; lia.
Qed.

(* dim of internal_direct_sum subspaces is sum of each dim *)
Lemma subspace_sum_dimension : forall {m : nat} (P1 P2 : GenVector m -> Prop) (d1 d2 : nat),
    dimension P1 d1 -> dimension P2 d2 -> no_subspace_overlap P1 P2 ->
    dimension (subspace_sum P1 P2) (d1 + d2)%nat.
Proof. intros m P1 P2 d1 d2 H H0 H1.
  unfold dimension in *.
  destruct H as [B1 [WFB1 basis1]].
  destruct H0 as [B2 [WFB2 basis2]].
  pose (subspace_sum_basis_smash P1 P2 B1 B2 basis1 basis2 H1).
  exists (smash B1 B2).
  split; auto with wf_db.
Qed.


(** multi_internal_direct_sum **)
Fixpoint multi_subspace_sum {n : nat} (Ps : list (GenVector n -> Prop)) (v : GenVector n) : Prop := 
  match Ps with 
  | [] => v = Zero
  | Ph :: Pt => (exists vh vt : GenVector n, 
      Ph vh /\ multi_subspace_sum Pt vt /\ v = vh .+ vt)
  end.

Lemma multi_subspace_sum_cons : 
  forall {n : nat} (P : GenVector n -> Prop) (Ps : list (GenVector n -> Prop)),
    (forall v : GenVector n, multi_subspace_sum (P :: Ps) v <-> 
                          subspace_sum P (multi_subspace_sum Ps) v).
Proof. intros. unfold subspace_sum. simpl; split; auto. Qed.

Lemma multi_subspace_sum_app : 
  forall {n : nat} (Ps1 Ps2 : list (GenVector n -> Prop)),
    (forall v : GenVector n, multi_subspace_sum (Ps1 ++ Ps2) v <-> 
                        subspace_sum
                        (multi_subspace_sum Ps1) (multi_subspace_sum Ps2) v).
Proof. intros. 
gen v. induction Ps1; intros.
- simpl. unfold subspace_sum. split; intros.
  + exists Zero. exists v. repeat split; auto. lgma.
  + destruct H as [v1 [v2 [v1zero [multv2 vv1v2]]]].
    rewrite v1zero, GMplus_0_l in vv1v2.
    subst. auto.
- replace ((a :: Ps1) ++ Ps2) with (a :: Ps1 ++ Ps2) by auto.
  rewrite multi_subspace_sum_cons.
  unfold subspace_sum in *.
  simpl; split; intros; auto. 
  + destruct H as [v1 [v2 [av1 [mult_v2 vv1v2]]]].
    rewrite IHPs1 in mult_v2.
    destruct mult_v2 as [v0 [v3 [mult_v0 [mult_v3 v2v0v3]]]].
    exists (v1 .+ v0). exists v3.
    split. 
    * exists v1. exists v0.
      repeat split; auto. 
    * repeat split; auto. 
      rewrite vv1v2, v2v0v3.
      rewrite GMplus_assoc. auto.
  + destruct H as [v1 [v2 [[vh [vt [avh [mult_vt v1vhvt]]]] [mult_v2 vv1v2]]]].
    exists vh. exists (vt .+ v2). split; auto.
    split. rewrite IHPs1.
    exists vt. exists v2. repeat split; auto.
    rewrite vv1v2, v1vhvt. rewrite GMplus_assoc. auto.
Qed.

Lemma multi_subspace_sum_is_subspace : forall {n : nat} {Ps : list (GenVector n -> Prop)},
    Forall subspace Ps -> subspace (multi_subspace_sum Ps).
Proof. intros n Ps H. induction H.
  - simpl. apply zerospace_is_subspace.
  - repeat split; intros; subst; try rewrite multi_subspace_sum_cons in *;
      destruct (subspace_sum_is_subspace H IHForall) as [H' [H'' [H''' H'''']]]; auto.
Qed.

Lemma multi_subspace_sum_dimension_cons : 
  forall {n : nat} (d : nat) (P : GenVector n -> Prop) (Ps : list (GenVector n -> Prop)),
dimension (multi_subspace_sum (P :: Ps)) d <->
  dimension (subspace_sum P (multi_subspace_sum Ps)) d.
Proof. intros n d P Ps.
  unfold dimension.
  split; intros.
  - destruct H as [A [WFA basisA]].
    exists A. split; auto.
  - destruct H as [A [WFA basisA]].
    exists A. split; auto.
Qed.

Lemma multi_subspace_sum_permutation : forall {n : nat} {Ps1 Ps2 : list (GenVector n -> Prop)},
    Permutation Ps1 Ps2 ->
    (forall v : GenVector n, multi_subspace_sum Ps1 v <-> multi_subspace_sum Ps2 v).
Proof. intros n Ps1 Ps2 H.
  induction H as [ | P Ps1 Ps2 | P1 P2 Ps | Ps1 Ps2 Ps3].
  - split; auto.
  - split; simpl; intros.
    + destruct H0 as [vh [vt [Pvh [Ps1vt vvhvt]]]].
      rewrite IHPermutation in Ps1vt.
      exists vh. exists vt. repeat split; auto.
    + destruct H0 as [vh [vt [Pvh [Ps2vt vvhvt]]]].
      rewrite <- IHPermutation in Ps2vt.
      exists vh. exists vt. repeat split; auto.
  - intros v. split; auto; simpl in *; intros.
    + destruct H as [vh [vt [P2vh [[vh0 [vt0 [P1vh0 [Psvt0 vtvh0vt0]]]] vvhvt]]]].
      exists vh0. exists (vh .+ vt0). split; auto. split.
      * exists vh. exists vt0. repeat split; auto.
      * rewrite vvhvt, vtvh0vt0; lgma.
    + destruct H as [vh [vt [P1vh [[vh0 [vt0 [P2vh0 [Psvt0 vtvh0vt0]]]] vvhvt]]]].
      exists vh0. exists (vh .+ vt0). split; auto. split.
      * exists vh. exists vt0. repeat split; auto.
      * rewrite vvhvt, vtvh0vt0; lgma.
  - intros; split; intros.
    + rewrite <- IHPermutation2, <- IHPermutation1; auto.
    +  rewrite IHPermutation1, IHPermutation2; auto.
Qed.

Lemma multi_subspace_sum_span_left_Mmult : 
  forall {m n o : nat} (A : GenMatrix m n) (Lm : list (GenMatrix n o)),
    (forall v : GenVector n,
      multi_subspace_sum (map (fun m : GenMatrix n o => span m) Lm) v ->
      multi_subspace_sum (map (fun m : GenMatrix n o => span (A × m)) Lm) (A × v)).
Proof. intros. gen v. induction Lm; intros.
- simpl in *. subst. rewrite GMmult_0_r. auto.
- simpl in *.
  destruct H as [vh [vt [span_a_vh [mult_vt vvhvt]]]].
  specialize (IHLm vt mult_vt).
  exists (A × vh). exists (A × vt).
  repeat split; auto.
  + unfold span in *.
    destruct span_a_vh as [b [WFb vhab]].
    exists b. split; auto. subst.
    rewrite GMmult_assoc. auto.
  + rewrite vvhvt. distribute_plus. auto.
Qed.


Fixpoint multi_no_subspace_overlap {n : nat} (Ps : list (GenVector n -> Prop)) :=
  match Ps with
  | [] => True
  | P :: Ps' => no_subspace_overlap P (multi_subspace_sum Ps') /\
                multi_no_subspace_overlap Ps'
  end.

Lemma multi_no_subspace_overlap_permutation : 
  forall {n : nat} (Ps1 Ps2 : list (GenVector n -> Prop)),
    Permutation Ps1 Ps2 ->
    Forall subspace Ps1 -> multi_no_subspace_overlap Ps1 -> 
    multi_no_subspace_overlap Ps2.
Proof. intros n Ps1 Ps2 H H0 H1.
  induction H; auto.
  - rewrite Forall_cons_iff in H0. destruct H0.
    simpl in *.
    destruct H1.
    split; auto.
    unfold no_subspace_overlap in *.
    intros v H4 H5.
    rewrite <- (multi_subspace_sum_permutation H) in H5.
    apply H1; auto.
  - rewrite Forall_cons_iff in H0. destruct H0.
    rewrite Forall_cons_iff in H0. destruct H0.
    simpl in *.
    destruct H1 as [H1 [H3 H4]].
    repeat split; auto.
    + unfold no_subspace_overlap in *.
      intros v xv H6. 
      destruct H6 as [vh [vt [yvh [multi_l_vt vvhvt]]]].
      specialize (H1 vh yvh).
      assert (exists vh0 vt : GenVector n,
                 x vh0 /\ multi_subspace_sum l vt /\ vh = vh0 .+ vt).
      { exists v. exists ((- 1%F) .* vt). repeat split; auto; try rewrite vvhvt; try lgma.
        destruct (multi_subspace_sum_is_subspace H2) as [H5 [H5' [H5'' H5''']]].
        apply H5'''; auto. }
      specialize (H1 H5). subst.
      rewrite GMplus_0_l in *.
      apply H3; auto.
    + unfold no_subspace_overlap in *.
      intros v H5 H6.
      destruct H0 as [H0 [H0' [H0'' H0''']]].
      specialize (H1 v H5).
      assert (exists vh vt : GenVector n, x vh /\ multi_subspace_sum l vt /\ v = vh .+ vt).
      { exists Zero. exists v. repeat split; auto; lgma. }
      specialize (H1 H7). auto.
  - apply IHPermutation2.
    + rewrite Forall_forall. intros. apply Permutation_in with (l' := l) in H3.
      * rewrite Forall_forall in H0. apply H0; auto.
      * apply Permutation_sym; auto.
    + apply IHPermutation1; auto.
Qed.  

Lemma multi_subspace_sum_dimension : 
  forall {m : nat} (Ps : list (GenVector m -> Prop)) (Ld : list nat),
    length Ps = length Ld -> 
    Forall (fun p => dimension (fst p) (snd p)) (combine Ps Ld) ->
    multi_no_subspace_overlap Ps ->
    dimension (multi_subspace_sum Ps) (fold_right plus 0%nat Ld)%nat.
Proof. intros m Ps Ld H H0 H1.
  gen Ld. induction Ps; intros.
  - destruct Ld; try discriminate.
    simpl. unfold dimension.
    exists Zero. split; auto with wf_db.
    unfold basis. split. apply zerospace_is_subspace.
    split. intros. unfold get_col, Zero. prep_genmatrix_equality. bdestruct_all; auto.
    split. intros. rewrite H2. unfold span. exists Zero. split; auto with wf_db; lgma.
    unfold linearly_independent. intros a H2 H3.
    prep_genmatrix_equality. unfold Zero. rewrite H2; auto; lia.
  - destruct Ld; try discriminate.
     replace (fold_right Init.Nat.add 0%nat (n :: Ld)) with 
                (n + (fold_right Init.Nat.add 0%nat Ld))%nat by (simpl; auto).
    rewrite multi_subspace_sum_dimension_cons.
    destruct H1.
    simpl in *.
    apply Nat.succ_inj in H.
    inversion H0; subst; clear H0.
    simpl in H5.
    apply subspace_sum_dimension; auto.
Qed.

End SubspacesOverField.

