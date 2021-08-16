Require Import Psatz. 
Require Import Reals.

Require Export Matrix.



(*******************************************************************)
(* Defining properties which are invarient under column operations *)
(*******************************************************************)

Local Open Scope nat_scope.


Inductive invr_col_swap {n m} : (Matrix n m -> Prop) -> Prop :=
| invr_swap : forall (P : Matrix n m -> Prop), 
    (forall (A : Matrix n m) (x y : nat), x < m -> y < m -> P A -> P (col_swap A x y)) 
    -> invr_col_swap P.

Inductive invr_col_scale {n m} : (Matrix n m -> Prop) -> Prop :=
| invr_scale : forall (P : Matrix n m -> Prop), 
    (forall (A : Matrix n m) (x : nat) (c : C), x < m -> c <> C0 -> P A -> P (col_scale A x c)) 
    -> invr_col_scale P.

Inductive invr_col_add {n m} : (Matrix n m -> Prop) -> Prop :=
| invr_add : forall (P : Matrix n m -> Prop), 
    (forall (A : Matrix n m) (x y : nat) (c : C), x <> y -> x < m -> y < m -> P A -> P (col_add A x y c)) 
    -> invr_col_add P.

Inductive invr_col_add_many {n m} : (Matrix n m -> Prop) -> Prop :=
| invr_add_many : forall (P : Matrix n m -> Prop), 
    (forall (A : Matrix n m) (col : nat) (as' : Vector m), 
        col < m -> as' col 0 = C0 -> P A -> P (col_add_many col as' A)) 
    -> invr_col_add_many P.

Inductive invr_col_add_each {n m} : (Matrix n m -> Prop) -> Prop :=
| invr_add_each : forall (P : Matrix n m -> Prop), 
    (forall (A : Matrix n m) (col : nat) (as' : Matrix 1 m), 
        col < m -> WF_Matrix as' -> P A -> P (col_add_each col (make_col_zero col as') A)) 
    -> invr_col_add_each P.


Lemma mat_prop_col_add_many_some : forall (e n m col : nat) (P : Matrix n m -> Prop) 
                                     (T : Matrix n m) (as' : Vector m),
  (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = C0) -> as' col 0 = C0 ->
  invr_col_add P ->
  P T -> P (col_add_many col as' T).
Proof. induction e as [| e].
       - intros. 
         inversion H3; subst. 
         rewrite (col_add_many_col_add _ (skip_count col 0)); 
           try lia; try easy.  
         apply H5; try lia.
         apply skip_count_not_skip.
         assert (H' : (col_add_many col (make_row_zero (skip_count col 0) as') T) = T).
         { prep_matrix_equality. 
           unfold col_add_many, make_row_zero, skip_count, gen_new_vec, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Cplus_0_l.
           rewrite Cplus_comm.
           apply Cplus_simplify; try easy.
           rewrite Msum_Csum.
           apply Csum_0_bounded; intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); try lca. 
           destruct x0; try rewrite H2; try rewrite H1; try lca; try lia. 
           destruct x0; try lca; rewrite H1; try lca; lia. }
         rewrite H'; easy.
         apply skip_count_not_skip.
       - intros. 
         inversion H3; subst. 
         rewrite (col_add_many_col_add _ (skip_count col (S e))); 
           try lia; try easy.
         apply H5; try lia.
         apply skip_count_not_skip.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_row_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H1; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H9, H11. apply H2.
         apply H1; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H1; lia. 
         unfold make_row_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         apply skip_count_not_skip.
Qed.


Lemma invr_col_add_col_add_many : forall {n m} (P : Matrix n m -> Prop),
  invr_col_add P -> invr_col_add_many P.
Proof. intros. 
       inversion H; subst. 
       apply invr_add_many; intros. 
       destruct m; try lia. 
       destruct m.
       - assert (H' : as' == Zero).
         { unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ _ (make_WF as'));
           try apply mat_equiv_make_WF.
         bdestruct (col =? S m).
         + apply (mat_prop_col_add_many_some m); try lia; try easy.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold skip_count in H5; rewrite H4 in H5. 
           bdestruct (m <? S m); try lia. 
           unfold make_WF. 
           bdestruct (i <? S (S m)); bdestruct (0 <? 1); try lia; try easy.
           bdestruct (i =? S m); try lia. 
           rewrite H9, <- H4; easy.
           unfold make_WF. 
           bdestruct_all; auto. 
         + apply (mat_prop_col_add_many_some m); try lia; try easy.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_WF.
           unfold skip_count in H5.
           bdestruct (m <? col); try lia. 
           bdestruct (i <? S (S m)); try lia; try easy.
           unfold make_WF. 
           bdestruct_all; auto. 
Qed.


Lemma mat_prop_col_add_each_some : forall (e n m col : nat) (P : Matrix n m -> Prop)
                                     (as' : Matrix 1 m) (T : Matrix n m),
  WF_Matrix as' -> (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = C0) -> as' 0 col = C0 ->
  invr_col_add P -> 
  P T -> P (col_add_each col as' T).
Proof. induction e as [| e].
       - intros.
         inversion H4; subst.
         rewrite (col_add_each_col_add _ (skip_count col 0)); try lia. 
         apply H6; try lia.
         assert (H' := skip_count_not_skip col 0). auto.
         assert (H' : (make_col_zero (skip_count col 0) as') = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           unfold make_col_zero, skip_count in *.
           destruct i; try lia. 
           destruct col; simpl in *. 
           all : destruct j; try easy; simpl. 
           destruct j; try easy; simpl.  
           all : apply H2; lia. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
         apply skip_count_not_skip.
         intros x. destruct x; try easy.
         apply H; lia.
       - intros.  
         inversion H4; subst.
         rewrite (col_add_each_col_add _ (skip_count col (S e))); try lia. 
         apply H6; try lia.
         assert (H' := skip_count_not_skip col (S e)). auto.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_col_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H2; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H10, H12. apply H3.
         apply H2; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H2; lia. 
         unfold make_col_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         assert (H' := skip_count_not_skip col (S e)). auto.
         intros. destruct x; try easy.
         apply H; lia.
Qed.
       
        
         
Lemma invr_col_add_col_add_each : forall {n m} (P : Matrix n m -> Prop),
  invr_col_add P -> invr_col_add_each P.
Proof. intros.  
       inversion H; subst. 
       apply invr_add_each; intros. 
       destruct m; try lia. 
       destruct m.
       - assert (H' : make_col_zero col as' = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           unfold make_col_zero. 
           easy. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
       - bdestruct (col =? S m).
         + apply (mat_prop_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold make_col_zero. 
           bdestruct (i =? col); try lia; try easy.
           rewrite H4 in H5; unfold skip_count in H5.
           bdestruct (m <? S m); try lia. 
           rewrite H2; try lia; easy.
           unfold make_col_zero. 
           bdestruct (col =? col); try lia; easy.
         + apply (mat_prop_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_col_zero. 
           bdestruct (i =? col); try lia; try easy.
           unfold skip_count in H5.
           bdestruct (m <? col); try lia. 
           apply H2; lia. 
           unfold make_col_zero. 
           bdestruct (col =? col); try lia; easy.
Qed.







(***********************************************************)
(* Defining linear independence, and proving lemmas etc... *)
(***********************************************************)



Definition linearly_independent {n m} (T : Matrix n m) : Prop :=
  forall (a : Vector m), WF_Matrix a -> @Mmult n m 1 T a = Zero -> a = Zero.


Definition linearly_dependent {n m} (T : Matrix n m) : Prop :=
  exists (a : Vector m), WF_Matrix a /\ a <> Zero /\ @Mmult n m 1 T a = Zero.


Lemma lindep_implies_not_linindep : forall {n m} (T : Matrix n m),
  linearly_dependent T -> ~ (linearly_independent T).
Proof. unfold not, linearly_dependent, linearly_independent in *.
       intros. 
       destruct H as [a [H1 [H2 H3]]].
       apply H0 in H1; easy.
Qed.


Lemma not_lindep_implies_linindep : forall {n m} (T : Matrix n m),
  not (linearly_dependent T) -> linearly_independent T.
Proof. unfold not, linearly_dependent, linearly_independent in *.
       intros. 
       destruct (vec_equiv_dec a Zero). 
       - apply mat_equiv_eq; auto with wf_db.
       - assert (H2 : (exists a : Vector m, WF_Matrix a /\ a <> Zero /\ T × a = Zero)).
         { exists a.
           split; auto. 
           split; try easy.  
           unfold not; intros. 
           apply n0.
           rewrite H2.
           easy. }
         apply H in H2.
         easy.
Qed.



Lemma lin_indep_vec : forall {n} (v : Vector n), 
  WF_Matrix v -> v <> Zero -> linearly_independent v.
Proof. intros. 
       unfold linearly_independent.
       intros. 
       assert (H' : v × a = (a 0 0) .* v).
       { apply mat_equiv_eq; auto with wf_db.
         unfold Mmult, scale, mat_equiv. 
         intros. simpl. 
         destruct j; try lia; lca. }
       assert (H1' := H).
       apply nonzero_vec_nonzero_elem in H1'; try easy.
       destruct H1' as [x H1'].
       destruct (Ceq_dec (a 0 0) C0).
       + prep_matrix_equality. 
         destruct x0. destruct y.
         rewrite e; easy.
         all : apply H1; lia.
       + assert (H'' : ((a 0 0) .* v) x 0 = C0).
         { rewrite <- H'. rewrite H2; easy. }
         unfold scale in H''. 
         assert (H3 : (a 0 0 * v x 0)%C <> C0).
         { apply Cmult_neq_0; easy. }
         easy. 
Qed.


Definition e_i {n : nat} (i : nat) : Vector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then C1 else C0). 

Lemma WF_e_i : forall {n : nat} (i : nat),
  WF_Matrix (@e_i n i).
Proof. unfold WF_Matrix, e_i.
       intros; destruct H as [H | H].
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
Qed.

Hint Resolve WF_e_i : wf_db.

Lemma I_is_eis : forall {n} (i : nat),
  get_vec i (I n) = e_i i. 
Proof. intros. unfold get_vec, e_i.
       prep_matrix_equality. 
       bdestruct (x =? i).
       - bdestruct (y =? 0).
         rewrite H. unfold I. simpl. 
         assert (H1 : (i =? i) && (i <? n) = (i <? n) && true).
         { bdestruct (i =? i). apply andb_comm. easy. }
         rewrite H1. reflexivity.
         simpl; rewrite andb_false_r; reflexivity.
       - simpl. destruct (y =? 0). unfold I.
         bdestruct (x =? i). easy.
         reflexivity. reflexivity.
Qed. 


Lemma reduce_mul_0 : forall {n} (A : Square (S n)) (v : Vector (S n)),
  get_vec 0 A = @e_i (S n) 0 -> (reduce A 0 0) × (reduce_row v 0) = reduce_row (A × v) 0.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult, reduce, reduce_row.
       rewrite easy_sub. 
       bdestruct (x <? 0); try lia.  
       rewrite <- Csum_extend_l.
       assert (H' : A (1 + x) 0 = C0).
       { rewrite <- get_vec_conv.  
         rewrite H. unfold e_i. 
         bdestruct (1 + x =? 0); try lia. 
         easy. }
       rewrite H'. 
       rewrite Cmult_0_l. 
       rewrite Cplus_0_l.
       apply Csum_eq_bounded. 
       intros. bdestruct (x0 <? 0); try lia; try easy.
Qed.


Lemma reduce_mul_n : forall {n} (A : Square (S n)) (v : Vector (S n)),
  get_vec n A = @e_i (S n) n -> (reduce A n n) × (reduce_row v n) = reduce_row (A × v) n.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult, reduce, reduce_row.
       assert (H' : S n - 1 = n). { lia. }
       bdestruct (x <? n).  
       - rewrite <- Csum_extend_r.
         assert (H'' : A x n = C0).
         { rewrite <- get_vec_conv.  
           rewrite H. unfold e_i. 
           bdestruct (x =? n); try lia. 
           easy. }
         rewrite H''. rewrite Cmult_0_l. 
         rewrite Cplus_0_r.
         rewrite easy_sub.
         apply Csum_eq_bounded. 
         intros. bdestruct (x0 <? n); try lia; try easy.
       - rewrite <- Csum_extend_r.
         assert (H'' : A (1 + x) n = C0).
         { rewrite <- get_vec_conv.  
           rewrite H. unfold e_i. 
           bdestruct (1 + x =? n); try lia. 
           easy. }
         rewrite H''. rewrite Cmult_0_l. 
         rewrite Cplus_0_r.
         rewrite easy_sub.
         apply Csum_eq_bounded. 
         intros.
         bdestruct (x0 <? n); try lia; try easy.
Qed.
 

(* More general case: 
Lemma reduce_mul : forall {n} (A : Square (S n)) (v : Vector (S n)) (x : nat),
  get_vec x A = @e_i (S n) x -> (reduce A x x) × (reduce_row v x) = reduce_row (A × v) x.
Proof. *)


(* similar lemma for append *) 
Lemma append_mul : forall {n m} (A : Matrix n m) (v : Vector n) (a : Vector m),
  (col_append A v) × (row_append a (@Zero 1 1)) = A × a.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult.
       simpl. 
       assert (H' : (col_append A v x m * row_append a Zero m y = C0)%C). 
       { unfold col_append, row_append.
         bdestruct (m =? m); try lia; lca. }
       rewrite H'. 
       rewrite Cplus_0_r. 
       apply Csum_eq_bounded. 
       intros. 
       unfold col_append, row_append. 
       bdestruct (x0 =? m); try lia; try easy.
Qed.


Lemma invertible_l_implies_linind : forall {n} (A B : Square n),
  A × B = I n -> linearly_independent B.
Proof. intros.
       unfold linearly_independent. intros.
       rewrite <- (Mmult_1_l _ _ a); try easy.
       rewrite <- H.
       rewrite Mmult_assoc, H1.
       rewrite Mmult_0_r.
       reflexivity.
Qed.


Lemma matrix_by_basis : forall {n m} (T : Matrix n m) (i : nat),
  i < m -> get_vec i T = T × e_i i.
Proof. intros. unfold get_vec, e_i, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0). 
       - rewrite (Csum_unique (T x i) _ m); try easy.
         exists i. split.
         apply H. split.
         bdestruct (i =? i); bdestruct (i <? m); try lia; lca. 
         intros.
         bdestruct (x' =? i); try lia; lca. 
       - rewrite Csum_0; try reflexivity.
         intros. rewrite andb_false_r. 
         rewrite Cmult_0_r. reflexivity.
Qed.     


Lemma zero_vec_lin_dep : forall {n m} (T : Matrix n m) (i : nat),
  i < m -> (get_vec i T) = Zero -> linearly_dependent T.
Proof. intros.
       unfold linearly_dependent in *; intros. 
       exists (@e_i m i).
       split. apply WF_e_i.
       split. 
       unfold not; intros. 
       assert (H' : (@e_i m i) i 0 = C0).
       { rewrite H1; easy. }
       unfold e_i in H'; simpl in H'.
       bdestruct (i =? i); bdestruct (i <? m); try lia. 
       simpl in H'.
       apply C1_neq_C0.
       easy.
       rewrite <- matrix_by_basis; easy.
Qed.



Lemma lin_indep_nonzero_cols : forall {n m} (T : Matrix n m),
  linearly_independent T -> (forall i, i < m -> (get_vec i T) <> Zero). 
Proof. intros. unfold not. intros. 
       apply (zero_vec_lin_dep T i) in H0; try easy.
       apply lindep_implies_not_linindep in H0.
       easy. 
Qed.


Lemma lin_indep_col_reduce_n : forall {n m} (A : Matrix n (S m)),
  linearly_independent A -> linearly_independent (reduce_col A m).
Proof. intros. 
       unfold linearly_independent in *. 
       intros. 
       assert (H' : row_append a Zero = Zero).
       { apply H.
         rewrite easy_sub in *.
         apply WF_row_append; try easy.
         prep_matrix_equality. 
         unfold Mmult, row_append, Zero. 
         rewrite <- Csum_extend_r. 
         bdestruct (m =? S m - 1); try lia. 
         autorewrite with C_db.
         assert (H' : (reduce_col A m × a) x y = C0).
         { rewrite H1; easy. }
         rewrite <- H'. 
         unfold Mmult. 
         rewrite easy_sub.
         apply Csum_eq_bounded. 
         intros.
         unfold reduce_col.
         bdestruct (x0 =? m); bdestruct (x0 <? m); try lia. 
         reflexivity. } 
       prep_matrix_equality. 
       assert (H'' : row_append a Zero x y = C0). { rewrite H'. easy. }
       unfold Zero; simpl. rewrite <- H''. 
       unfold row_append.
       rewrite easy_sub. 
       bdestruct (x =? m); try easy.
       unfold WF_Matrix in H0. 
       unfold Zero; simpl. 
       apply H0. lia. 
Qed.


(* more general than lin_indep_col_reduce_n *)
Lemma lin_indep_smash : forall {n m2 m1} (A1 : Matrix n m1) (A2 : Matrix n m2),
  linearly_independent (smash A1 A2) -> linearly_independent A1. 
Proof. induction m2 as [| m2'].
       - intros.  
         unfold linearly_independent in *. 
         intros. assert (H' : m1 + 0 = m1). lia. 
         rewrite H' in *.
         apply H; try easy.
         rewrite <- H1.
         unfold smash, Mmult. 
         prep_matrix_equality. 
         apply Csum_eq_bounded.
         intros. 
         bdestruct (x0 <? m1); try lia; easy.
       - intros. 
         assert (H1 := @lin_indep_col_reduce_n n (m1 + m2') (smash A1 A2)). 
         assert (H' : (Init.Nat.add m1 (S m2')) = (S (Init.Nat.add m1 m2'))). { lia. }
         rewrite H' in H.
         apply H1 in H.
         assert (H1' : S (Nat.add m1 m2') = Nat.add m1 (S m2')). { lia. } 
         rewrite H1' in H. 
         rewrite smash_reduce in H.
         apply (IHm2' m1 A1 (reduce_col A2 m2')).
         rewrite easy_sub in *.
         assert (H2' : (m1 + S m2' - 1) = m1 + m2'). { lia. }
         rewrite H2' in *; easy.
Qed.


Lemma lin_dep_col_append_n : forall {n m} (A : Matrix n m) (v : Vector n),
  linearly_dependent A -> linearly_dependent (col_append A v).
Proof. intros. 
       unfold linearly_dependent in *. 
       destruct H as [a [H [H1 H2]]].
       exists (row_append a (@Zero 1 1)). 
       split; auto with wf_db. 
       split. unfold not; intros; apply H1.
       prep_matrix_equality. 
       assert (H' : row_append a Zero x y = C0). 
       { rewrite H0. easy. }
       unfold row_append in H'.
       bdestruct (x =? m). 
       rewrite H; try easy; lia. 
       rewrite H'; easy.
       rewrite append_mul.
       easy.
Qed.



Lemma lin_indep_swap : forall {n m} (T : Matrix n m) (x y : nat),
  x < m -> y < m -> linearly_independent T -> linearly_independent (col_swap T x y).
Proof. intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite (row_swap_inv a x y) in H3.
       rewrite <- (swap_preserves_mul T (row_swap a x y) x y) in H3; try easy.
       apply H1 in H3.
       rewrite (row_swap_inv a x y).
       rewrite H3.
       prep_matrix_equality.
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); easy.
       apply WF_row_swap; easy.
Qed.


Lemma lin_indep_swap_conv : forall {n m} (T : Matrix n m) (x y : nat),
  x < m -> y < m -> linearly_independent (col_swap T x y) -> linearly_independent T.
Proof. intros. 
       rewrite (col_swap_inv T x y).
       apply lin_indep_swap; easy.
Qed.


Lemma lin_indep_scale : forall {n m} (T : Matrix n m) (x : nat) (c : C),
  c <> C0 -> linearly_independent T -> linearly_independent (col_scale T x c).
Proof. intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite <- scale_preserves_mul in H2.
       apply H0 in H2.
       rewrite (row_scale_inv _ x c); try easy.
       rewrite H2.
       prep_matrix_equality. 
       unfold row_scale.
       bdestruct (x0 =? x);
       lca. 
       apply WF_row_scale; easy.
Qed.


Lemma lin_indep_scale_conv : forall {n m} (T : Matrix n m) (x : nat) (c : C),
  c <> C0 -> linearly_independent (col_scale T x c) -> linearly_independent T.
Proof. intros. 
       rewrite (col_scale_inv T x c); try easy.
       apply lin_indep_scale; try apply nonzero_div_nonzero; easy.
Qed.


Lemma lin_indep_add : forall {n m} (T : Matrix n m) (x y : nat) (c : C),
  x <> y -> x < m -> y < m -> linearly_independent T -> linearly_independent (col_add T x y c).
Proof. intros.
       unfold linearly_independent in *.
       intros.  
       rewrite <- col_add_preserves_mul in H4; try easy.
       apply H2 in H4.
       rewrite (row_add_inv a y x c); try lia.
       rewrite H4.
       prep_matrix_equality. 
       unfold row_add.
       bdestruct (x0 =? y);
       lca. 
       apply WF_row_add; easy.
Qed.




Lemma lin_indep_col_add_many_some : forall (e n m col : nat) (T : Matrix n m) (as' : Vector m),
  (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = C0) -> as' col 0 = C0 ->
  linearly_independent T -> linearly_independent (col_add_many col as' T).
Proof. induction e as [| e].
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col 0)); 
           try lia; try easy.  
         apply lin_indep_add; try lia.
         apply skip_count_not_skip.
         assert (H' : (col_add_many col (make_row_zero (skip_count col 0) as') T) = T).
         { prep_matrix_equality. 
           unfold col_add_many, make_row_zero, skip_count, gen_new_vec, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Cplus_0_l.
           rewrite Cplus_comm.
           apply Cplus_simplify; try easy.
           rewrite Msum_Csum.
           apply Csum_0_bounded; intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); try lca. 
           destruct x0; try rewrite H2; try rewrite H1; try lca; try lia. 
           destruct x0; try lca; rewrite H1; try lca; lia. }
         rewrite H'; easy.
         apply skip_count_not_skip.
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col (S e))); 
           try lia; try easy.
         apply lin_indep_add; try lia.
         apply skip_count_not_skip.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_row_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H1; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H7, H9. apply H2.
         apply H1; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H1; lia. 
         unfold make_row_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         apply skip_count_not_skip.
Qed.


Lemma lin_indep_col_add_many : forall (n m col : nat) (T : Matrix n m) (as' : Vector m),
  col < m -> as' col 0 = C0 -> linearly_independent T -> 
  linearly_independent (col_add_many col as' T).
Proof. intros. 
       destruct m; try lia. 
       destruct m.
       - assert (H' : as' == Zero).
         { unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ _ (make_WF as'));
           try apply mat_equiv_make_WF.
         bdestruct (col =? S m).
         + apply (lin_indep_col_add_many_some m); try lia; try easy.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold skip_count in H3; rewrite H2 in H3. 
           bdestruct (m <? S m); try lia. 
           unfold make_WF. 
           bdestruct (i <? S (S m)); bdestruct (0 <? 1); try lia; try easy.
           bdestruct (i =? S m); try lia. 
           rewrite H7, <- H2; easy.
           unfold make_WF. 
           bdestruct (col =? col); bdestruct (col <? S (S m)); try lia; auto. 
         + apply (lin_indep_col_add_many_some m); try lia; try easy.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_WF.
           unfold skip_count in H3.
           bdestruct (m <? col); try lia. 
           bdestruct (i <? S (S m)); try lia; try easy.
           unfold make_WF. 
           bdestruct (col =? col); bdestruct (col <? S (S m)); try lia; auto. 
Qed.



Lemma lin_indep_col_add_many_conv : forall (n m col : nat) (T : Matrix n m) (as' : Vector m),
  col < m -> as' col 0 = C0 -> 
  linearly_independent (col_add_many col as' T) ->
  linearly_independent T.
Proof. intros. 
       rewrite (col_add_many_inv T col as'); try easy.
       apply lin_indep_col_add_many; try easy. 
       unfold scale; rewrite H0.
       lca. 
Qed.



Lemma lin_indep_col_add_each_some : forall (e n m col : nat) (as' : Matrix 1 m) (T : Matrix n m),
  WF_Matrix as' -> (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = C0) -> as' 0 col = C0 ->
  linearly_independent T -> linearly_independent (col_add_each col as' T).
Proof. induction e as [| e].
       - intros.
         rewrite (col_add_each_col_add _ (skip_count col 0)); try lia. 
         apply lin_indep_add; try lia.
         assert (H' := skip_count_not_skip col 0). auto.
         assert (H' : (make_col_zero (skip_count col 0) as') = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           unfold make_col_zero, skip_count in *.
           destruct i; try lia. 
           destruct col; simpl in *. 
           all : destruct j; try easy; simpl. 
           destruct j; try easy; simpl.  
           all : apply H2; lia. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
         apply skip_count_not_skip.
         intros x. destruct x; try easy.
         apply H; lia.
       - intros.  
         rewrite (col_add_each_col_add _ (skip_count col (S e))); try lia. 
         apply lin_indep_add; try lia.
         assert (H' := skip_count_not_skip col (S e)). auto.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_col_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H2; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H8, H10. apply H3.
         apply H2; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H2; lia. 
         unfold make_col_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         assert (H' := skip_count_not_skip col (S e)). auto.
         intros. destruct x; try easy.
         apply H; lia.
Qed.
       
        
         
Lemma lin_indep_col_add_each : forall (n m col : nat) (as' : Matrix 1 (S m)) 
                                          (T : Matrix n (S m)),
  col < (S m) -> WF_Matrix as' -> linearly_independent T -> 
  linearly_independent (col_add_each col (make_col_zero col as') T).
Proof. intros. 
       destruct m.
       - assert (H' : make_col_zero col as' = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           unfold make_col_zero. 
           easy. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
       - bdestruct (col =? S m).
         + apply (lin_indep_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold make_col_zero. 
           bdestruct (i =? col); try lia; try easy.
           rewrite H2 in H3; unfold skip_count in H3.
           bdestruct (m <? S m); try lia. 
           rewrite H0; try lia; easy.
           unfold make_col_zero. 
           bdestruct (col =? col); try lia; easy.
         + apply (lin_indep_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_col_zero. 
           bdestruct (i =? col); try lia; try easy.
           unfold skip_count in H3.
           bdestruct (m <? col); try lia. 
           apply H0; lia. 
           unfold make_col_zero. 
           bdestruct (col =? col); try lia; easy.
Qed.


Lemma lin_dep_swap : forall {n m} (T : Matrix n m) (x y : nat),
  x < m -> y < m -> linearly_dependent T -> linearly_dependent (col_swap T x y).
Proof. unfold linearly_dependent in *.
       intros. 
       destruct H1 as [a [H1 [H2 H3]]].
       rewrite (row_swap_inv a x y) in H3.
       rewrite (col_swap_inv T x y) in H3.
       rewrite <- (swap_preserves_mul _ (row_swap a x y) x y) in H3; try easy.
       exists (row_swap a x y).
       split; auto with wf_db.
       split; try easy; unfold not in *.
       intros; apply H2.
       rewrite (row_swap_inv a x y).
       rewrite H4.
       prep_matrix_equality. 
       unfold Zero, row_swap. 
       bdestruct (x0 =? x); bdestruct (x0 =? y); easy. 
Qed.
 

Lemma lin_dep_swap_conv : forall {n m} (T : Matrix n m) (x y : nat),
  x < m -> y < m -> linearly_dependent (col_swap T x y) -> linearly_dependent T.
Proof. intros. 
       rewrite (col_swap_inv T x y).
       apply lin_dep_swap; easy.
Qed.


Lemma lin_dep_scale : forall {n m} (T : Matrix n m) (x : nat) (c : C),
  linearly_dependent T -> linearly_dependent (col_scale T x c).
Proof. intros. 
       destruct (Ceq_dec c C0).
       - bdestruct (x <? m).
         + apply (zero_vec_lin_dep _ x); try easy.
           rewrite e; unfold get_vec, col_scale.
           prep_matrix_equality. 
           bdestruct (y =? 0); bdestruct (x =? x); try lia; lca. 
         + unfold linearly_dependent, col_scale in *.
           destruct H as [a [H [H1 H2]]].
           exists a. split; try easy.
           split; try easy.
           rewrite <- H2.
           prep_matrix_equality. 
           unfold Mmult. 
           apply Csum_eq_bounded. 
           intros. 
           bdestruct (x1 =? x); try lia; easy. 
       -  unfold linearly_dependent in *.
          destruct H as [a [H1 [H2 H3]]].
          exists (row_scale a x (/ c)).
          split; auto with wf_db.
          split. unfold not; intros.
          apply H2.
          rewrite (row_scale_inv _ x (/ c)); try easy.
          rewrite H. 
          prep_matrix_equality. 
          unfold row_scale, Zero. 
          bdestruct (x0 =? x); try lia; lca. 
          apply nonzero_div_nonzero; easy.
          rewrite scale_preserves_mul. 
          rewrite <- (col_scale_inv T x c); easy.
Qed.


Lemma lin_dep_scale_conv : forall {n m} (T : Matrix n m) (x : nat) (c : C),
  c <> C0 -> linearly_dependent (col_scale T x c) -> linearly_dependent T. 
Proof. intros. 
       rewrite (col_scale_inv T x c); try easy.
       apply lin_dep_scale; easy. 
Qed.


Lemma lin_dep_add : forall {n m} (T : Matrix n m) (x y : nat) (c : C),
  x <> y -> x < m -> y < m -> linearly_dependent T -> linearly_dependent (col_add T x y c).
Proof. intros.
       unfold linearly_dependent in *.
       destruct H2 as [a [H2 [H3 H4]]].
       exists (row_add a y x (- c)).
       split; auto with wf_db.
       split. unfold not; intros; apply H3.
       rewrite (row_add_inv a y x (- c)); try lia.
       rewrite H5.
       unfold row_add, Zero.
       prep_matrix_equality.
       bdestruct (x0 =? y); lca. 
       rewrite col_add_preserves_mul; try easy.
       rewrite <- (col_add_inv T x y c); try lia; easy.
Qed.


Lemma lin_dep_col_add_many_some : forall (e n m col : nat) (T : Matrix n m) (as' : Vector m),
  (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = C0) -> as' col 0 = C0 ->
  linearly_dependent T -> linearly_dependent (col_add_many col as' T).
Proof. induction e as [| e].
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col 0)); 
           try lia; try easy.  
         apply lin_dep_add; try lia.
         apply skip_count_not_skip.
         assert (H' : (col_add_many col (make_row_zero (skip_count col 0) as') T) = T).
         { prep_matrix_equality. 
           unfold col_add_many, make_row_zero, skip_count, gen_new_vec, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Cplus_0_l.
           rewrite Cplus_comm.
           apply Cplus_simplify; try easy.
           rewrite Msum_Csum.
           apply Csum_0_bounded; intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); try lca. 
           destruct x0; try rewrite H2; try rewrite H1; try lca; try lia. 
           destruct x0; try lca; rewrite H1; try lca; lia. }
         rewrite H'; easy.
         apply skip_count_not_skip.
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col (S e))); 
           try lia; try easy.
         apply lin_dep_add; try lia.
         apply skip_count_not_skip.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_row_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H1; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H7, H9. apply H2.
         apply H1; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H1; lia. 
         unfold make_row_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         apply skip_count_not_skip.
Qed.


Lemma lin_dep_col_add_many : forall (n m col : nat) (T : Matrix n m) (as' : Vector m),
  col < m -> as' col 0 = C0 -> linearly_dependent T -> 
  linearly_dependent (col_add_many col as' T).
Proof. intros. 
       destruct m; try lia. 
       destruct m.
       - assert (H' : as' == Zero).
         { unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ _ (make_WF as'));
           try apply mat_equiv_make_WF.
         bdestruct (col =? S m).
         + apply (lin_dep_col_add_many_some m); try lia; try easy.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold skip_count in H3; rewrite H2 in H3. 
           bdestruct (m <? S m); try lia. 
           unfold make_WF. 
           bdestruct (i <? S (S m)); bdestruct (0 <? 1); try lia; try easy.
           bdestruct (i =? S m); try lia. 
           rewrite H7, <- H2; easy.
           unfold make_WF. 
           bdestruct (col =? col); bdestruct (col <? S (S m)); try lia; auto. 
         + apply (lin_dep_col_add_many_some m); try lia; try easy.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_WF.
           unfold skip_count in H3.
           bdestruct (m <? col); try lia. 
           bdestruct (i <? S (S m)); try lia; try easy.
           unfold make_WF. 
           bdestruct (col =? col); bdestruct (col <? S (S m)); try lia; auto. 
Qed.


Lemma lin_dep_col_add_many_conv : forall (n m col : nat) (T : Matrix n m) (as' : Vector m),
  col < m -> as' col 0 = C0 -> 
  linearly_dependent (col_add_many col as' T) ->
  linearly_dependent T.
Proof. intros. 
       rewrite (col_add_many_inv T col as'); try easy.
       apply lin_dep_col_add_many; try easy. 
       unfold scale; rewrite H0.
       lca. 
Qed.


Lemma lin_dep_col_add_each_some : forall (e n m col : nat) (as' : Matrix 1 m) (T : Matrix n m),
  WF_Matrix as' -> (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = C0) -> as' 0 col = C0 ->
  linearly_dependent T -> linearly_dependent (col_add_each col as' T).
Proof. induction e as [| e].
       - intros.
         rewrite (col_add_each_col_add _ (skip_count col 0)); try lia. 
         apply lin_dep_add; try lia.
         assert (H' := skip_count_not_skip col 0). auto.
         assert (H' : (make_col_zero (skip_count col 0) as') = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           unfold make_col_zero, skip_count in *.
           destruct i; try lia. 
           destruct col; simpl in *. 
           all : destruct j; try easy; simpl. 
           destruct j; try easy; simpl.  
           all : apply H2; lia. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
         assert (H' := skip_count_not_skip col 0). auto.
         intros. destruct x; try easy.
         apply H; lia.
       - intros.  
         rewrite (col_add_each_col_add _ (skip_count col (S e))); try lia. 
         apply lin_dep_add; try lia.
         assert (H' := skip_count_not_skip col (S e)). auto.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_col_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H2; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H8, H10. apply H3.
         apply H2; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H2; lia. 
         unfold make_col_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         apply skip_count_not_skip.
         intros. destruct x; try easy.
         apply H; lia.
Qed.
       
        
         
Lemma lin_dep_col_add_each : forall (n m col : nat) (as' : Matrix 1 (S m)) 
                                          (T : Matrix n (S m)),
  col < (S m) -> WF_Matrix as' -> linearly_dependent T -> 
  linearly_dependent (col_add_each col (make_col_zero col as') T).
Proof. intros. 
       destruct m.
       - assert (H' : make_col_zero col as' = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           unfold make_col_zero. 
           easy. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
       - bdestruct (col =? S m).
         + apply (lin_dep_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold make_col_zero. 
           bdestruct (i =? col); try lia; try easy.
           rewrite H2 in H3; unfold skip_count in H3.
           bdestruct (m <? S m); try lia. 
           rewrite H0; try lia; easy.
           unfold make_col_zero. 
           bdestruct (col =? col); try lia; easy.
         + apply (lin_dep_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_col_zero. 
           bdestruct (i =? col); try lia; try easy.
           unfold skip_count in H3.
           bdestruct (m <? col); try lia. 
           apply H0; lia. 
           unfold make_col_zero. 
           bdestruct (col =? col); try lia; easy.
Qed.



Lemma lin_dep_col_add_each_conv : forall (n m col : nat) (as' : Matrix 1 (S m)) 
                                          (T : Matrix n (S m)),
  col < (S m) -> WF_Matrix as' -> 
  linearly_dependent (col_add_each col (make_col_zero col as') T) ->
  linearly_dependent T.
Proof. intros. 
       rewrite (col_add_each_inv col as').
       apply lin_dep_col_add_each; auto with wf_db.
Qed.


Lemma lin_dep_gen_elem : forall {m n} (T : Matrix n (S m)),
  WF_Matrix T -> linearly_dependent T -> 
  (exists i, i < (S m) /\ 
             (exists v : Vector m, WF_Matrix v /\ 
                 @Mmult n m 1 (reduce_col T i) v = (-C1) .* (get_vec i T))). 
Proof. intros. 
       unfold linearly_dependent in H.
       destruct H0 as [a [H1 [H2 H3]]].
       assert (H4 := H1).
       apply nonzero_vec_nonzero_elem in H4; try easy.
       destruct H4 as [x H4].
       exists x.
       bdestruct (x <? S m).
       - split; try easy.
         exists ( (/ (a x 0)) .* (reduce_row a x)).
         split. rewrite easy_sub.
         apply WF_scale.
         assert (H' := (@WF_reduce_row (S m) 1 x a)).
         rewrite easy_sub in *.
         apply H'; easy.
         apply mat_equiv_eq; auto with wf_db.
         apply WF_mult.
         assert (H' := (@WF_reduce_col n (S m) x T)).
         rewrite easy_sub in *.
         apply H'; try lia; try easy.
         rewrite easy_sub in *.
         apply WF_scale.
         assert (H' := (@WF_reduce_row (S m) 1 x a)).
         rewrite easy_sub in *.
         apply H'; try lia; try easy.
         rewrite easy_sub.
         rewrite Mscale_mult_dist_r.  
         unfold mat_equiv; intros. 
         unfold Mmult, scale.
         assert (H' : (Csum (fun y : nat => reduce_col T x i y * reduce_row a x y j) m +
                       (a x 0) * get_vec x T i j = @Zero n 1 i j)%C).
         { rewrite <- H3. unfold Mmult.
           assert (H'' : m = x + (m - x)). lia. 
           rewrite H''. 
           rewrite Csum_sum.
           rewrite <- H''. 
           assert (H2' : S m = x + S (m - x)). lia. 
           rewrite H2'. 
           rewrite Csum_sum.
           rewrite <- Csum_extend_l.
           rewrite <- Cplus_assoc.
           apply Cplus_simplify. 
           apply Csum_eq_bounded.
           intros. unfold reduce_col, reduce_row. 
           bdestruct (x0 <? x); try lia; easy.
           rewrite Cplus_comm.
           apply Cplus_simplify. 
           unfold get_vec.
           bdestruct (j =? 0); try lia. 
           assert (p0 : x + 0 = x). lia. 
           rewrite p0, H7; lca.
           apply Csum_eq_bounded.
           intros. 
           unfold reduce_col, reduce_row.
           bdestruct (x + x0 <? x); try lia.
           assert (p1 : (1 + (x + x0)) = (x + S x0)). lia. 
           rewrite p1. easy. }
         assert (H1' : (Csum (fun y : nat => reduce_col T x i y * reduce_row a x y j) m +
                       (a x 0) * get_vec x T i j + (a x 0) * (- (get_vec x T i j)) = 
                       (- (a x 0)) * get_vec x T i j)%C).
         { rewrite H'. lca. }
         rewrite <- Cplus_assoc in H1'.
         rewrite <- Cmult_plus_distr_l in H1'.
         rewrite Cplus_opp_r in H1'.
         rewrite Cmult_0_r, Cplus_0_r in H1'.
         rewrite H1'. 
         rewrite Cmult_assoc. 
         rewrite <- Copp_mult_distr_r.
         rewrite Cinv_l; easy. 
       - assert (H' : a x 0 = C0).
         apply H1; try lia.
         easy. 
Qed.


Lemma gt_dim_lindep_ind_step1 : forall {n m} (T : Matrix (S n) (S m)) (col : nat),
  WF_Matrix T -> col <= m -> get_vec col T = @e_i (S n) 0 -> 
  linearly_dependent (reduce_row (reduce_col T col) 0) -> linearly_dependent T.
Proof. intros.  
       apply (lin_dep_col_add_each_conv _ _  col (-C1 .* (get_row 0 T))); 
         auto with wf_db; try lia.
       unfold linearly_dependent in *.
       destruct H2 as [a [H3 [H4 H5]]]. 
       repeat rewrite easy_sub in *.
       exists (row_wedge a (@Zero 1 1) col).
       split. 
       - rewrite easy_sub in *.
         auto with wf_db.
       - split. 
         + unfold not in *. 
           intros. apply H4. 
           prep_matrix_equality.
           bdestruct (x <? col).
           assert (H' : (row_wedge a Zero col) x y = C0 ).
           { rewrite H2. easy. }
           unfold row_wedge in *. 
           bdestruct (x <? col); try lia. easy. 
           assert (H' : (row_wedge a Zero col) (S x) y = C0 ).
           { rewrite H2. easy. }
           unfold row_wedge in *.
           bdestruct (S x <? col); bdestruct (S x =? col); try lia. 
           rewrite easy_sub in *; easy. 
         + repeat rewrite easy_sub in *.
           apply mat_equiv_eq; auto with wf_db.
           apply WF_mult; auto with wf_db.
           unfold mat_equiv; intros. 
           assert (H' : (get_vec col T) i 0 = @e_i (S n) 0 i 0).
           { rewrite H1. easy. }  
           unfold col_add_each, make_col_zero, get_row, Mmult, Mplus, get_vec, 
           scale, row_append, row_wedge.
           destruct i.  
           * unfold get_vec, e_i in H'; simpl in H'. 
             rewrite H'. unfold Zero. 
             apply Csum_0_bounded. 
             intros; simpl.  
             bdestruct (x =? col); bdestruct (x <? col); try lia; lca. 
           * unfold get_vec, e_i in H'; simpl in H'. 
             assert (H0' : (reduce_row (reduce_col T col) 0 × a) i j = @Zero (S n) 1 (S i) j).
             repeat rewrite easy_sub in *; rewrite H5. easy.
             rewrite <- H0'.
             unfold Mmult, reduce_row, reduce_col.
             repeat rewrite easy_sub in *.
             assert (p : S m = col + (S m - col)). lia.
             rewrite p.
             rewrite Csum_sum.
             assert (p1 : S m - col = S (m - col)). lia. 
             rewrite p1. 
             rewrite <- Csum_extend_l. 
             simpl. bdestruct (col + 0 =? col); bdestruct (col + 0 <? col); try lia. 
             assert (p2 : m = col + (m - col)). lia.
             rewrite p2.
             rewrite Csum_sum.
             rewrite <- p2.
             apply Cplus_simplify.
             apply Csum_eq_bounded; intros. 
             bdestruct (x <? col); bdestruct (x =? col); try lia.
             rewrite H'. lca. 
             rewrite <- Cplus_0_l.
             apply Cplus_simplify; try lca.
             apply Csum_eq_bounded; intros.
             bdestruct (col + S x <? col); bdestruct (col + S x =? col); 
               bdestruct (col + x <? col); try lia. 
             assert (p4 : col + S x - 1 = col + x). lia. 
             assert (p5 : S (col + x) = col + S x). lia.  
             rewrite H', p4, p5. lca. 
Qed.             
             


Lemma gt_dim_lindep_ind_step2 : forall {n m} (T : Matrix (S n) (S m)) 
                                       (v : Vector (S m)) (col : nat),
  WF_Matrix T -> col < S m -> v col 0 = C0 ->
  reduce_col (reduce_row T 0) col × (reduce_row v col) = 
                     - C1 .* get_vec col (reduce_row T 0) -> 
  linearly_dependent (reduce_row (reduce_col T col) 0) -> linearly_dependent T.
Proof. intros. 
       assert (H' := @col_add_many_cancel n (S m) (reduce_row T 0) v col).
       assert (H0' : forall i : nat, @col_add_many n (S m) col v  (reduce_row T 0) i col = C0).
       { repeat rewrite easy_sub in *; apply H'; try easy. }
       repeat rewrite easy_sub in *.
       apply (lin_dep_col_add_many_conv _ _ col _ v); try easy.
       destruct (Ceq_dec ((col_add_many col v T) 0 col) C0).
       - apply (zero_vec_lin_dep _ col); try lia. 
         prep_matrix_equality. unfold get_vec.
         destruct y; try easy; simpl. 
         destruct x; try easy. unfold Zero.
         rewrite <- (H0' x).
         unfold col_add_many, reduce_row. 
         bdestruct (col =? col); bdestruct (x <? 0); try lia. 
         apply Cplus_simplify. 
         easy. unfold gen_new_vec.
         do 2 rewrite Msum_Csum.
         apply Csum_eq_bounded; intros. 
         unfold scale, get_vec; lca.  
       - apply (lin_dep_scale_conv _ col (/ (col_add_many col v T 0 col))); 
           try apply nonzero_div_nonzero; try easy.
         apply (gt_dim_lindep_ind_step1 _ col); try lia; auto with wf_db.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         unfold get_vec, e_i.
         bdestruct (j =? 0); bdestruct (i =? 0); bdestruct (i <? S n); 
           try lia; simpl. 
         + unfold col_scale. bdestruct (col =? col); try lia. 
           rewrite H7. rewrite Cinv_l; easy.
         + unfold col_scale. bdestruct (col =? col); try lia. 
           destruct i; try easy.
           assert (r : col_add_many col v T (S i) col = 
                       col_add_many col v (reduce_row T 0) i col).
           { unfold reduce_row, col_add_many, gen_new_vec, get_vec, scale.
             bdestruct (col =? col); bdestruct (i <? 0); try lia. 
             apply Cplus_simplify; try easy.
             do 2 rewrite Msum_Csum. 
             apply Csum_eq_bounded; intros. 
             bdestruct (i <? 0); try lia; easy. }
           rewrite r. 
           rewrite easy_sub in *. 
           rewrite (H0' i); lca. 
         + rewrite col_scale_reduce_col_same; try easy.
           rewrite col_add_many_reduce_col_same. 
           repeat rewrite easy_sub in *. easy.
Qed.

Lemma gt_dim_lindep : forall {m n} (T : Matrix n m),
  n < m -> WF_Matrix T -> linearly_dependent T.
Proof. induction m as [| m'].
       - intros; lia. 
       - intros. 
         destruct n as [| n'].
         + exists (e_i 0).
           split. apply WF_e_i.
           split. unfold not; intros. 
           assert (H' : (@e_i (S m') 0) 0 0 = C0).
           { rewrite H1; easy. }
           unfold e_i in H'; simpl in H'.
           apply C1_neq_C0; easy.
           assert (H' : T = Zero). 
           { prep_matrix_equality. 
             rewrite H0; try easy; try lia. }
           rewrite H'. apply Mmult_0_l.
         + bdestruct (n' <? m'); try lia. 
           assert (H' : linearly_dependent (reduce_row T 0)).
           { rewrite (reduce_append_split (reduce_row T 0)).
             assert (H'' := @lin_dep_col_append_n n' m' 
                                (reduce_col (reduce_row T 0) m') (get_vec m' (reduce_row T 0))).
             do 2 rewrite easy_sub in *.
             apply H''.
             apply IHm'; try easy.
             assert (H0' := (@WF_reduce_col n' (S m'))).
             rewrite easy_sub in *.
             apply H0'; try lia.
             assert (H1' := (@WF_reduce_row (S n') (S m'))).
             rewrite easy_sub in *.
             apply H1'; try lia; easy. 
             assert (H1' := (@WF_reduce_row (S n') (S m'))).
             rewrite easy_sub in *.
             apply H1'; try lia; easy. }
           apply lin_dep_gen_elem in H'. 
           destruct H' as [i [H2 H3]].
           destruct H3 as [v [H3 H4]]. 
           * apply (gt_dim_lindep_ind_step2 _ (row_wedge v (@Zero 1 1) i) i); try easy.
             unfold row_wedge.
             bdestruct (i <? i); bdestruct (i =? i); try lia; easy.
             rewrite row_wedge_reduce_row_same. 
             repeat rewrite easy_sub in *; easy.
             assert (H' := (IHm' n' (reduce_row (reduce_col T i) 0))).
             repeat rewrite easy_sub in *.
             apply H'; try lia. 
             assert (H1' := (@WF_reduce_row (S n') m')).
             rewrite easy_sub in *; apply H1'; try lia. 
             assert (H2' := (@WF_reduce_col (S n') (S m'))).
             rewrite easy_sub in *; apply H2'; try lia; easy. 
           * apply WF_reduce_row; try lia; easy.
Qed.




Definition pad {n : nat} (A : Square n) (c : C) : Square (S n) :=
  col_wedge (row_wedge A Zero 0) (c .* e_i 0) 0.

Lemma pad_conv : forall {n : nat} (A : Square n) (c : C) (i j : nat),
  (pad A c) (S i) (S j) = A i j.
Proof. intros.
       unfold pad, col_wedge, row_wedge, e_i.
       bdestruct (S j <? 0); bdestruct (S j =? 0); try lia.
       bdestruct (S i <? 0); bdestruct (S i =? 0); try lia.
       do 2 rewrite easy_sub.
       easy.
Qed.

Lemma WF_pad : forall {n : nat} (A : Square n) (c : C),
  WF_Matrix A <-> WF_Matrix (pad A c).
Proof. unfold WF_Matrix, pad. split.
       - intros. 
         unfold col_wedge, row_wedge, e_i, scale.
         bdestruct (y <? 0); bdestruct (y =? 0); try lia. 
         destruct H0; try lia. 
         bdestruct (x =? 0); bdestruct (x <? n); try lia; try easy.
         lca.  
         destruct y; try lia. 
         rewrite easy_sub. 
         bdestruct (x <? 0); bdestruct (x =? 0); try lia; try easy. 
         destruct x; try lia. 
         rewrite easy_sub.
         apply H; lia. 
       - intros. 
         unfold col_wedge, row_wedge, e_i in H.
         rewrite <- (H (S x) (S y)); try lia. 
         bdestruct (S y <? 0); bdestruct (S y =? 0); try lia. 
         bdestruct (S x =? 0); bdestruct (S x <? 0); try lia; try easy.
         do 2 rewrite easy_sub; easy.
Qed.

Lemma pad_mult : forall {n : nat} (A B : Square n) (c1 c2 : C),
  pad (A × B) (c1 * c2)%C = (pad A c1) × (pad B c2).
Proof. intros. 
       prep_matrix_equality. 
       unfold pad, Mmult, col_wedge, row_wedge, e_i, scale.
       bdestruct (y <? 0); bdestruct (y =? 0); bdestruct (x <? 0); 
         bdestruct (x =? 0); try lia; try easy.
       bdestruct (x <? S n).
       rewrite <- Csum_extend_l. simpl. 
       rewrite <- (Cplus_0_l (c1 * c2 * C1)).
       rewrite Cplus_comm.
       apply Cplus_simplify; try lca. 
       rewrite Csum_0_bounded; try easy.
       intros. lca. 
       simpl. 
       rewrite Csum_0_bounded; try easy.
       destruct n; try lca. 
       intros. 
       bdestruct (x0 =? 0); try lca. 
       rewrite Csum_0_bounded; try lca.       
       intros. bdestruct (x0 <? 0); bdestruct (x0 =? 0); try lia; lca. 
       rewrite Csum_0_bounded; try lca.
       intros. bdestruct (x0 <? 0); bdestruct (x0 =? 0); try lia; lca. 
       rewrite <- Csum_extend_l. simpl. 
       rewrite Cmult_0_r, Cplus_0_l.
       apply Csum_eq_bounded. 
       intros. 
       rewrite Nat.sub_0_r.
       easy. 
Qed.
 
Lemma pad_I : forall (n : nat), pad (I n) C1 = I (S n).
Proof. intros. 
       unfold pad, I, col_wedge, row_wedge, e_i, scale.
       prep_matrix_equality. 
       bdestruct (y <? 0); bdestruct (y =? 0); bdestruct (x <? 0); bdestruct (x <? S n);
         bdestruct (x =? 0); bdestruct (x =? y); bdestruct (x - 1 =? y - 1); 
         bdestruct (x - 1 <? n); try lia; try lca.
Qed.


Lemma padded : forall {n : nat} (A : Square (S n)) (c : C),
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0) -> A 0 0 = c ->
  exists a : Square n, pad a c = A.
Proof. intros.  
       exists (reduce A 0 0).
       unfold pad, reduce, col_wedge, row_wedge, e_i, scale.
       prep_matrix_equality. 
       bdestruct (y <? 0); bdestruct (y =? 0); bdestruct (x <? 0); bdestruct (x =? 0);
         try lia. 
       rewrite H4, H2, H0. lca. 
       rewrite H; try lia.
       destruct x; try lia. lca. 
       rewrite H; try lia; easy. 
       destruct x; destruct y; try lia. 
       do 2 rewrite easy_sub in *.
       bdestruct (x <? 0); bdestruct (y <? 0); try lia. 
       easy.
Qed.



Lemma lin_indep_pad : forall {n : nat} (A : Square n) (c : C),
  linearly_independent (pad A c) -> linearly_independent A.
Proof. unfold linearly_independent.
       intros. 
       assert (H2 : (pad A c) × (row_wedge a Zero 0) = Zero).
       { prep_matrix_equality. 
         destruct x. unfold Mmult. 
         unfold Zero. apply Csum_0_bounded. 
         intros.
         unfold pad, row_wedge, col_wedge, e_i, scale.
         bdestruct (x <? 0); bdestruct (x =? 0); try lia. lca. 
         lca.
         assert (p : @Zero (S n) 1 (S x) y = C0).
         easy.
         assert (H2' : (A × a) x y = C0). 
         rewrite H1; easy.
         rewrite p. 
         rewrite <- H2'.
         unfold Mmult. rewrite <- Csum_extend_l.  
         rewrite <- Cplus_0_l.
         apply Cplus_simplify.
         unfold pad, row_wedge, col_wedge, e_i.
         bdestruct (x <? 0); bdestruct (x =? 0); try lia. 
         rewrite H3; simpl. lca. 
         rewrite easy_sub. lca. 
         apply Csum_eq_bounded; intros. 
         rewrite pad_conv.
         unfold row_wedge.
         rewrite easy_sub. 
         easy. }
       apply H in H2.
       prep_matrix_equality. 
       assert (H3 : row_wedge a Zero 0 (S x) y = C0).
       rewrite H2. easy.
       unfold Zero. rewrite <- H3.
       unfold row_wedge. 
       rewrite easy_sub.
       easy.
       apply WF_row_wedge; try lia; easy.
Qed.   
         

Lemma lin_indep_ind_step1 : forall {n} (A : Square (S n)), 
  WF_Matrix A -> linearly_independent A -> 
  (exists B : Square (S n), WF_Matrix B /\ linearly_independent (A × B) /\
                            (exists i, i < (S n) /\ get_vec i (A × B) = e_i 0)).
Proof. intros. 
       assert (H1 : WF_Matrix (reduce_row A 0)).
       { assert (H1' := (@WF_reduce_row (S n) (S n))).
         rewrite easy_sub in *.
         apply H1'; try lia; easy. }
       assert (H2 : linearly_dependent (reduce_row A 0)).
       { apply gt_dim_lindep; try lia. 
         apply H1. }
       apply lin_dep_gen_elem in H2; try easy. 
       destruct H2 as [i [H2 H3]]. 
       destruct H3 as [v [H3 H4]].
       apply (lin_indep_col_add_many (S n) (S n) i A (row_wedge v Zero i)) in H0; try easy.
       destruct (Ceq_dec ((col_add_many i (row_wedge v Zero i) A) 0 i) C0).
       - assert (H5 : forall i0 : nat, 
                   col_add_many i (row_wedge v Zero i) (reduce_row A 0) i0 i = C0).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge. 
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         rewrite easy_sub in *.
         easy. 
         assert (H6: get_vec i (col_add_many i (row_wedge v Zero i) A) = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct j; try lia.
           unfold get_vec; simpl. 
           destruct i0.
           rewrite e; easy.
           rewrite col_add_many_reduce_row in H5.
           assert (p : (@Zero (S n) 1 (S i0) 0) = C0). easy.  
           rewrite p.
           rewrite <- (H5 i0).
           unfold reduce_row.
           bdestruct (i0 <? 0); try lia. 
           easy. }
         apply zero_vec_lin_dep in H6; try easy.
         apply lindep_implies_not_linindep in H6.
         easy. 
       - apply (lin_indep_scale (col_add_many i (row_wedge v Zero i) A) i
                 (/ col_add_many i (row_wedge v Zero i) A 0 i)) in H0.
         assert (H6 : forall i0 : nat, 
                   col_add_many i (row_wedge v Zero i) (reduce_row A 0) i0 i = C0).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge.  
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         rewrite easy_sub in *.
         easy. 
         rewrite col_add_many_reduce_row in H6. 
         exists ((row_add_each i (row_wedge v Zero i) (I (S n))) × 
                  (row_scale (I (S n)) i 
                  (/ (col_add_many i (row_wedge v Zero i) A 0 i)))).
         split. apply WF_mult; auto with wf_db.
         apply WF_row_add_each; auto with wf_db.
         apply WF_row_wedge; auto with wf_db; lia.
         rewrite <- Mmult_assoc.
         rewrite <- col_add_many_mult_r; try easy.
         rewrite <- col_scale_mult_r; try easy.
         split; try easy.
         exists i. split; try easy.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         destruct j; try lia. 
         unfold get_vec, col_scale.
         bdestruct (i =? i); simpl; try lia.  
         destruct i0.
         rewrite Cinv_l; try easy.
         assert (H10 : col_add_many i (row_wedge v Zero i) A (S i0) i = C0).
         rewrite <- (H6 i0).
         unfold reduce_row.
         bdestruct (i0 <? 0); try lia; easy.
         rewrite H10. lca. 
         apply WF_col_add_many; auto with wf_db.
         apply WF_row_wedge; auto with wf_db; lia.
         unfold row_wedge.
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         apply nonzero_div_nonzero; easy.
       - unfold row_wedge.
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy.
Qed.         


Lemma lin_indep_ind_step2 : forall {n} (A : Square (S n)), 
  WF_Matrix A -> linearly_independent A -> (exists i, i < (S n) /\ get_vec i A = e_i 0) ->
  (exists B : Square (S n), WF_Matrix B /\ linearly_independent (A × B) /\
                            (exists a : Square n, pad a C1 = (A × B))).
Proof. intros.
       destruct H1 as [i [H1 H2]].
       apply (lin_indep_swap A 0 i) in H0; try lia; try easy.
       apply (lin_indep_col_add_each _ _ 0 
                           (-C1 .* (get_row 0 (col_swap A 0 i))) (col_swap A 0 i)) in H0; try lia.
       exists ((row_swap (I (S n)) 0 i) × (row_add_many 0 
                                (make_col_zero 0 (-C1 .* (get_row 0 (col_swap A 0 i)))) 
                                (I (S n)))).
       split. 
       apply WF_mult. 
       apply WF_row_swap; try lia; auto with wf_db.
       apply WF_row_add_many; try lia; auto with wf_db.
       rewrite <- Mmult_assoc. 
       rewrite <- col_swap_mult_r; try lia; try easy.
       rewrite <- col_add_each_mult_r; try lia; try easy.
       split; try easy.
       apply padded; intros. 
       destruct H3 as [H3 H4].
       destruct H3. 
       + unfold col_add_each, make_col_zero, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale.
         rewrite H3 in *.
         bdestruct (j =? 0); try lia. 
         assert (H' : (get_vec i A) 0 0 = C1).
         { rewrite H2. easy. }
         simpl. bdestruct (j =? i); try lia. 
         all : unfold get_vec in H'; simpl in H'.
         all : rewrite H'; lca. 
       + unfold col_add_each, make_col_zero, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale.
         rewrite H3 in *; simpl. 
         destruct i0; try lia.
         assert (H' : (get_vec i A) (S i0) 0 = C0).
         { rewrite H2. easy. }
         unfold get_vec in H'; simpl in H'. 
         rewrite H'; lca. 
       + unfold col_add_each, make_col_zero, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale; simpl.
         assert (H' : (get_vec i A) 0 0 = C1).
         { rewrite H2. easy. }
         unfold get_vec in H'; simpl in H'.
         rewrite H'; lca.
       + apply WF_col_swap; try lia; easy. 
       + apply WF_make_col_zero.
         apply WF_scale. 
         apply WF_get_row.
         apply WF_col_swap; try lia; easy.
       + apply WF_scale. 
         apply WF_get_row.
         apply WF_col_swap; try lia; easy.
Qed.    


Theorem lin_ind_implies_invertible_r : forall {n} (A : Square n),
  WF_Matrix A -> linearly_independent A -> 
  (exists B, WF_Matrix B /\ A × B = I n).
Proof. induction n as [| n'].
       - intros.  
         exists Zero. split; auto with wf_db.
         rewrite Mmult_0_r.
         apply mat_equiv_eq; auto with wf_db. 
         unfold mat_equiv. lia. 
       - intros. apply lin_indep_ind_step1 in H0; try easy.
         destruct H0 as [B1 [H0 [H1 H2]]].
         destruct H2 as [i [H2 H3]].
         apply lin_indep_ind_step2 in H1; auto with wf_db.
         destruct H1 as [B2 [H1 [H4 H5]]].
         destruct H5 as [a H5].
         rewrite <- H5 in H4.
         apply lin_indep_pad in H4.
         apply IHn' in H4.
         destruct H4 as [B3 [H6 H7]].
         exists (B1 × B2 × (pad B3 C1)).
         split. apply WF_mult. 
         apply WF_mult; easy.
         apply (WF_pad B3 C1). easy.
         do 2 rewrite <- Mmult_assoc. 
         rewrite <- H5.
         rewrite <- pad_mult.
         rewrite Cmult_1_l.
         rewrite H7, pad_I; easy.
         apply (WF_pad a C1). 
         rewrite H5. 
         auto with wf_db.
         exists i; split; try lia. 
         easy.
Qed.


(*******************************)
(* Inverses of square matrices *)
(*******************************)

Definition Minv {n : nat} (A B : Square n) : Prop := A × B = I n /\ B × A = I n.


Definition invertible {n : nat} (A : Square n) : Prop :=
  exists B, Minv A B.


Lemma Minv_unique : forall (n : nat) (A B C : Square n), 
                      WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
                      Minv A B -> Minv A C -> B = C.
Proof.
  intros n A B C WFA WFB WFC [HAB HBA] [HAC HCA].
  replace B with (B × I n) by (apply Mmult_1_r; assumption).
  rewrite <- HAC.  
  replace C with (I n × C) at 2 by (apply Mmult_1_l; assumption).
  rewrite <- HBA.  
  rewrite Mmult_assoc.
  reflexivity.
Qed.

Lemma Minv_symm : forall (n : nat) (A B : Square n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.

(* The left inverse of a square matrix is also its right inverse *)
Lemma Minv_flip : forall (n : nat) (A B : Square n), 
  WF_Matrix A -> WF_Matrix B ->  
  A × B = I n -> B × A = I n.
Proof. intros.   
       assert (H3 := H1).
       apply invertible_l_implies_linind in H1.
       apply lin_ind_implies_invertible_r in H1; try easy.
       destruct H1 as [A' [H2 H4]].
       assert (H' : (A × B) × A' = A').
       { rewrite H3. apply Mmult_1_l; easy. }
       rewrite Mmult_assoc in H'.
       rewrite H4 in H'.
       rewrite Mmult_1_r in H'; try easy.
       rewrite H'; easy.
Qed.

Lemma Minv_left : forall (n : nat) (A B : Square n), 
    WF_Matrix A -> WF_Matrix B -> 
    A × B = I n -> Minv A B.
Proof.
  intros n A B H H0 H1. 
  unfold Minv. split; trivial.
  apply Minv_flip; 
  assumption.
Qed.

Lemma Minv_right : forall (n : nat) (A B : Square n), 
    WF_Matrix A -> WF_Matrix B -> 
    B × A = I n -> Minv A B.
Proof.
  intros n A B H H0. 
  unfold Minv. split; trivial.
  apply Minv_flip;
  assumption.
Qed.


Lemma lin_indep_invertible : forall {n : nat} (A : Square n),
  WF_Matrix A -> (linearly_independent A <-> invertible A).
Proof. intros; split.
       - intros. 
         assert (H1 := H).
         apply lin_ind_implies_invertible_r in H; try easy.
         destruct H as [B [H H2]].
         unfold invertible.
         exists B. unfold Minv.
         split; try easy.
         apply Minv_flip in H2; easy.
       - intros. 
         destruct H0 as [B [H1 H2]].
         apply invertible_l_implies_linind in H2.
         easy.
Qed.


(***********************************************************)
(* Defining and proving lemmas relating to the determinant *)
(***********************************************************)


Fixpoint parity (n : nat) : C := 
  match n with 
  | 0 => C1 
  | S 0 => -C1
  | S (S n) => parity n
  end. 


Lemma parity_S : forall (n : nat),
  (parity (S n) = -C1 * parity n)%C. 
Proof. intros.
       induction n as [| n']; try lca.
       rewrite IHn'.
       simpl. lca. 
Qed.


Fixpoint Determinant (n : nat) (A : Square n) : C :=
  match n with 
  | 0 => C1
  | S 0 => A 0 0
  | S n' => (Csum (fun i => (parity i) * (A i 0) * (Determinant n' (reduce A i 0)))%C n)
  end.


Lemma Det_simplify : forall {n} (A : Square (S (S n))),
  Determinant (S (S n)) A =  
  (Csum (fun i => (parity i) * (A i 0) * (Determinant (S n) (reduce A i 0)))%C (S (S n))).
Proof. intros. easy. Qed.


Lemma Det_simplify_fun : forall {n} (A : Square (S (S (S n)))),
  (fun i : nat => parity i * A i 0 * Determinant (S (S n)) (reduce A i 0))%C =
  (fun i : nat => (Csum (fun j => 
           (parity i) * (A i 0) * (parity j) * ((reduce A i 0) j 0) * 
           (Determinant (S n) (reduce (reduce A i 0) j 0)))%C (S (S n))))%C.
Proof. intros. 
       apply functional_extensionality; intros. 
       rewrite Det_simplify. 
       rewrite Csum_mult_l. 
       apply Csum_eq_bounded; intros. 
       lca. 
Qed.


Lemma reduce_I : forall (n : nat), reduce (I (S n)) 0 0 = I n.
Proof. intros.
       apply mat_equiv_eq.
       apply WF_reduce; try lia; auto with wf_db.
       rewrite easy_sub.
       apply WF_I.
       unfold mat_equiv; intros.
       unfold reduce, I.
       bdestruct (i <? 0); bdestruct (j <? 0); try lia. 
       easy. 
Qed.       

Lemma Det_I : forall (n : nat), Determinant n (I n) = C1.
Proof. intros.
       induction n as [| n'].
       - easy.
       - simpl. destruct n'; try easy.
         rewrite <- Csum_extend_l.
         rewrite <- Cplus_0_r.
         rewrite <- Cplus_assoc.
         apply Cplus_simplify.
         rewrite reduce_I, IHn'.
         lca.
         rewrite Csum_extend_r.
         apply Csum_0_bounded; intros.
         replace (I (S (S n')) (S x) 0) with C0 by easy.
         lca. 
Qed.


Definition M22 : Square 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | _ => C0
  end.


Lemma Det_M22 : (Determinant 2 M22) = (Copp (3%R,0%R))%C.
Proof. lca. Qed.


Lemma Determinant_scale : forall {n} (A : Square n) (c : C) (col : nat),
  col < n -> Determinant n (col_scale A col c) = (c * Determinant n A)%C.
Proof. induction n.
       + intros. easy.
       + intros. simpl.  
         destruct n. 
         - simpl. unfold col_scale. 
           bdestruct (0 =? col); try lia; easy.
         - rewrite Cmult_plus_distr_l.
           apply Cplus_simplify.
           * rewrite Csum_mult_l.
             apply Csum_eq_bounded.
             intros. 
             destruct col. 
             rewrite col_scale_reduce_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_reduce_before; try lia.
             rewrite easy_sub.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca.
           * destruct col. 
             rewrite col_scale_reduce_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_reduce_before; try lia.
             rewrite easy_sub.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca. 
Qed.


(* some helper lemmas *)
Lemma Det_diff_1 : forall {n} (A : Square (S (S (S n)))),
  Determinant (S (S (S n))) (col_swap A 0 1) = 
  Csum (fun i => (Csum (fun j => ((A i 1) * (A (skip_count i j) 0) * (parity i) * (parity j) * 
                             Determinant (S n) (reduce (reduce A i 0) j 0))%C)  
                             (S (S n)))) (S (S (S n))).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply Csum_eq_bounded; intros. 
       apply Csum_eq_bounded; intros. 
       replace (col_swap A 0 1 x 0) with (A x 1) by easy. 
       assert (H' : @reduce (S (S (S n))) (col_swap A 0 1) x 0 x0 0 = A (skip_count x x0) 0).
       { unfold reduce, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'. 
       repeat rewrite easy_sub in *.
       apply Cmult_simplify; try easy. 
       lca. 
Qed.
Lemma Det_diff_2 : forall {n} (A : Square (S (S (S n)))),
  Determinant (S (S (S n))) A = 
  Csum (fun i => (Csum (fun j => ((A i 0) * (A (skip_count i j) 1) * (parity i) * (parity j) * 
                             Determinant (S n) (reduce (reduce A i 0) j 0))%C)  
                             (S (S n)))) (S (S (S n))).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply Csum_eq_bounded; intros. 
       apply Csum_eq_bounded; intros. 
       apply Cmult_simplify; try easy. 
       assert (H' : @reduce (S (S (S n))) A x 0 x0 0 = A (skip_count x x0) 1).
       { unfold reduce, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'. 
       repeat rewrite easy_sub in *.
       lca. 
Qed.
  

Lemma Determinant_swap_01 : forall {n} (A : Square n),
  1 < n -> Determinant n (col_swap A 0 1) = (-C1 * (Determinant n A))%C.
Proof. intros.
       destruct n; try lia.
       destruct n; try lia. 
       destruct n.
       - simpl. unfold col_swap, reduce. lca. 
       - rewrite Det_diff_1, Det_diff_2.
         apply Csum_rearrange; intros.
         + unfold skip_count. 
           bdestruct (x <? (S y)); bdestruct (y <? x); try lia.
           rewrite Cmult_assoc.
           apply Cmult_simplify.
           rewrite parity_S.
           lca. 
           rewrite reduce_reduce_0; easy.
         + unfold skip_count. 
           bdestruct (x <? y); bdestruct (y <? (S x)); try lia.
           rewrite Cmult_assoc.
           apply Cmult_simplify.
           rewrite parity_S.
           lca. 
           rewrite <- reduce_reduce_0; easy.
Qed.

Lemma Determinant_swap_adj : forall {n} (A : Square n) (i : nat),
  S i < n -> Determinant n (col_swap A i (S i)) = (-C1 * (Determinant n A))%C.
Proof. induction n as [| n'].
       - easy.
       - intros. 
         destruct i. 
         + apply Determinant_swap_01; easy.
         + simpl. destruct n'; try lia.
           do 2 rewrite Csum_extend_r.
           rewrite Csum_mult_l.
           apply Csum_eq_bounded; intros. 
           rewrite col_swap_reduce_before; try lia. 
           rewrite IHn'; try lia. 
           replace (col_swap A (S i) (S (S i)) x 0) with (A x 0) by easy.
           lca. 
Qed.


Lemma Determinant_swap_ik : forall {n} (k i : nat) (A : Square n),
  i + (S k) < n -> Determinant n (col_swap A i (i + (S k))) = (-C1 * (Determinant n A))%C.
Proof. induction k as [| k'].
       - intros. 
         replace (i + 1) with (S i) by lia. 
         rewrite Determinant_swap_adj; try lia; lca. 
       - intros. 
         rewrite (col_swap_three A i (i + (S k')) (i + (S (S k')))); try lia. 
         rewrite IHk'; try lia. 
         replace (i + (S (S k'))) with (S (i + (S k'))) by lia. 
         rewrite Determinant_swap_adj; try lia.
         rewrite IHk'; try lia. 
         lca. 
Qed.

Lemma Determinant_swap : forall {n} (A : Square n) (i j : nat),
  i < n -> j < n -> i <> j ->
  Determinant n (col_swap A i j) = (-C1 * (Determinant n A))%C.
Proof. intros. 
       bdestruct (i <? j); bdestruct (j <? i); try lia. 
       - replace j with (i + (S (j - i - 1))) by lia. 
         rewrite Determinant_swap_ik; try lia; easy.
       - replace i with (j + (S (i - j - 1))) by lia. 
         rewrite col_swap_diff_order. 
         rewrite Determinant_swap_ik; try lia; easy.
Qed.


Lemma col_0_Det_0 : forall {n} (A : Square n),
  (exists i, i < n /\ get_vec i A = Zero) -> Determinant n A = C0.
Proof. intros n A [i [H H0]].
       destruct n; try easy.
       destruct n.
       destruct i; try lia. 
       replace C0 with (@Zero 1 1 0 0) by easy.
       rewrite <- H0. easy. 
       destruct i.
       - rewrite Det_simplify.
         apply Csum_0_bounded; intros. 
         replace (A x 0) with (@Zero (S (S n)) 1 x 0) by (rewrite <- H0; easy). 
         unfold Zero; lca.
       - rewrite (col_swap_inv _ 0 (S i)).
         rewrite Determinant_swap; try lia.
         rewrite Det_simplify.
         rewrite Csum_mult_l.
         apply Csum_0_bounded; intros. 
         replace (col_swap A 0 (S i) x 0) with 
                 (@Zero (S (S n)) 1 x 0) by (rewrite <- H0; easy). 
         unfold Zero; lca.
Qed.


Lemma col_same_Det_0 : forall {n} (A : Square n) (i j : nat),
  i < n -> j < n -> i <> j -> 
  get_vec i A = get_vec j A ->
  Determinant n A = C0.
Proof. intros. 
       apply eq_neg_implies_0.
       rewrite <- (Determinant_swap _ i j); try easy.
       rewrite (det_by_get_vec (col_swap A i j) A); try easy; intros. 
       prep_matrix_equality. 
       destruct y; try easy.
       bdestruct (i0 =? i); bdestruct (i0 =? j); try lia.
       - rewrite H3, <- col_swap_get_vec, H2; easy.
       - rewrite H4, col_swap_diff_order, <- col_swap_get_vec, H2; easy.
       - unfold col_swap, get_vec. simpl. 
         bdestruct (i0 =? i); bdestruct (i0 =? j); try lia; easy.
Qed.

Lemma col_scale_same_Det_0 : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> 
  get_vec i A = c .* (get_vec j A) ->
  Determinant n A = C0.
Proof. intros. 
       destruct (Ceq_dec c C0).
       - apply col_0_Det_0.
         exists i.
         split; try easy.
         rewrite H2, e.
         apply Mscale_0_l.
       - rewrite (col_scale_inv A j c); try easy.
         rewrite Determinant_scale; try easy.
         assert (H3 : Determinant n (col_scale A j c) = C0).
         { apply (col_same_Det_0 _ i j); try easy.
           prep_matrix_equality.
           unfold get_vec, col_scale. 
           bdestruct (y =? 0); try easy.
           bdestruct (i =? j); bdestruct (j =? j); try lia. 
           rewrite <- get_vec_conv.
           rewrite H2.
           unfold scale.
           rewrite get_vec_conv. 
           easy. }
         rewrite H3.
         lca. 
Qed.


Lemma Det_col_add_comm : forall {n} (T : Matrix (S n) n) (v1 v2 : Vector (S n)),
  (Determinant (S n) (col_wedge T v1 0) + Determinant (S n) (col_wedge T v2 0) = 
   Determinant (S n) (col_wedge T (v1 .+ v2) 0))%C.
Proof. intros. 
       destruct n; try easy.
       do 3 rewrite Det_simplify.
       rewrite <- Csum_plus.
       apply Csum_eq_bounded; intros. 
       repeat rewrite reduce_is_redcol_redrow.
       repeat rewrite col_wedge_reduce_col_same.
       unfold col_wedge, Mplus.
       bdestruct (0 <? 0); bdestruct (0 =? 0); try lia. 
       lca. 
Qed.



Lemma Determinant_col_add0i : forall {n} (A : Square n) (i : nat) (c : C),
  i < n -> i <> 0 -> Determinant n (col_add A 0 i c) = Determinant n A.     
Proof. intros. 
       destruct n; try easy.
       rewrite col_add_split.
       assert (H' := (@Det_col_add_comm n (reduce_col A 0) (get_vec 0 A) (c .* get_vec i A))).
       rewrite easy_sub in *.
       rewrite <- H'.
       replace (Determinant (S n) A) with (Determinant (S n) A + C0)%C by lca. 
       apply Cplus_simplify. 
       assert (H1 : col_wedge (reduce_col A 0) (get_vec 0 A) 0 = A).
       { prep_matrix_equality.
         unfold col_wedge, reduce_col, get_vec. 
         destruct y; try easy; simpl.  
         replace (y - 0) with y by lia; easy. }
       rewrite easy_sub, H1 in *; easy.
       apply (col_scale_same_Det_0 _ 0 i c); try lia.
       prep_matrix_equality. 
       unfold get_vec, col_wedge, reduce_col, scale; simpl. 
       bdestruct (y =? 0); bdestruct (i =? 0); try lca; try lia. 
       replace (S (i - 1)) with i by lia. 
       easy. 
Qed.


Lemma Determinant_col_add : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> Determinant n (col_add A i j c) = Determinant n A.     
Proof. intros. 
       destruct j.
       - rewrite <- col_swap_col_add_0.
         rewrite Determinant_swap. 
         rewrite Determinant_col_add0i.
         rewrite Determinant_swap. 
         lca. 
         all : easy. 
       - destruct i. 
         rewrite Determinant_col_add0i; try easy.
         rewrite <- col_swap_col_add_Si.
         rewrite Determinant_swap. 
         rewrite Determinant_col_add0i.
         rewrite Determinant_swap. 
         lca. 
         all : try easy; try lia. 
Qed.


Lemma Determinant_col_add_many_some : forall (e n col : nat) (A : Square n) (as' : Vector n),
  (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = C0) -> as' col 0 = C0 ->
  Determinant n A = Determinant n (col_add_many col as' A).
Proof. induction e as [| e].
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col 0)); 
           try lia; try easy.  
         rewrite Determinant_col_add; try lia.
         assert (H' : (col_add_many col (make_row_zero (skip_count col 0) as') A) = A).
         { prep_matrix_equality. 
           unfold col_add_many, make_row_zero, skip_count, gen_new_vec, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Cplus_0_l.
           rewrite Cplus_comm.
           apply Cplus_simplify; try easy.
           rewrite Msum_Csum.
           apply Csum_0_bounded; intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); try lca. 
           destruct x0; try rewrite H2; try rewrite H1; try lca; try lia. 
           destruct x0; try lca; rewrite H1; try lca; lia. }
         rewrite H'; easy.
         all : apply skip_count_not_skip.
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col (S e))); 
           try lia; try easy.
         rewrite Determinant_col_add; try lia.
         apply IHe; try lia; try easy.   
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_row_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H1; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H6, H8. apply H2.
         apply H1; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H1; lia. 
         unfold make_row_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         all : apply skip_count_not_skip.
Qed.


Lemma Determinant_col_add_many : forall (n col : nat) (A : Square n) (as' : Vector n),
  col < n -> as' col 0 = C0 -> 
  Determinant n A = Determinant n (col_add_many col as' A).
Proof. intros. 
       destruct n; try lia. 
       destruct n.
       - assert (H' : as' == Zero).
         { unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ _ (make_WF as'));
           try apply mat_equiv_make_WF.
         apply (Determinant_col_add_many_some n); try lia; try easy.
         unfold skip_count. bdestruct (n <? col); lia. 
         intros. 
         unfold skip_count in H1.
         bdestruct (n <? col).
         bdestruct (col =? S n); try lia. 
         unfold make_WF.
         bdestruct (i <? S (S n)); bdestruct (i =? S n); try lia; try easy. 
         simpl. rewrite H5, <- H3; easy.
         unfold make_WF.
         bdestruct (i <? S (S n)); try lia; easy. 
         unfold make_WF.
         bdestruct (col <? S (S n)); try lia; auto.
         
Qed.

Lemma Determinant_col_add_each_some : forall (e n col : nat) (as' : Matrix 1 n) (A : Square n),
  WF_Matrix as' -> (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = C0) -> as' 0 col = C0 ->
  Determinant n A = Determinant n (col_add_each col as' A).
Proof. induction e as [| e].
       - intros.
         rewrite (col_add_each_col_add _ (skip_count col 0)); try lia. 
         rewrite Determinant_col_add; try lia.
         assert (H' : (make_col_zero (skip_count col 0) as') = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           unfold make_col_zero, skip_count in *.
           destruct i; try lia. 
           destruct col; simpl in *. 
           all : destruct j; try easy; simpl. 
           destruct j; try easy; simpl.  
           all : apply H2; lia. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
         assert (H' := skip_count_not_skip col 0). auto.
         apply skip_count_not_skip.
         intros x. destruct x; try easy.
         assert (H' := skip_count_not_skip col 0). auto.
         apply H; lia.
       - intros. 
         rewrite (col_add_each_col_add _ (skip_count col (S e))); try lia. 
         rewrite Determinant_col_add; try lia.
         apply IHe; try lia; try easy; auto with wf_db. 
         + assert (H' : e < S e). lia. 
           apply (skip_count_mono col) in H'.
           lia. 
         + intros. 
           unfold skip_count, make_col_zero in *. 
           bdestruct (e <? col); bdestruct (S e <? col); try lia.
           bdestruct (i =? S e); try easy; try apply H2; try lia. 
           bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
           bdestruct (S e =? col); try lia. rewrite H7, H9; easy.
           apply H2. lia. 
           bdestruct (i =? S (S e)); try lia; try easy. 
           apply H2. lia. 
         + unfold make_col_zero. 
           bdestruct (col =? skip_count col (S e)); try easy. 
         + assert (H' := skip_count_not_skip col (S e)). auto.
         + apply skip_count_not_skip.
         + intros.
           destruct x; try easy.
           rewrite H; try lia; easy.
Qed.     
        
         
Lemma Determinant_col_add_each : forall (n col : nat) (as' : Matrix 1 n) 
                                          (A : Square n),
  col < n -> WF_Matrix as' -> as' 0 col = C0 ->
  Determinant n A = Determinant n (col_add_each col as' A).
Proof. intros. 
       destruct n; try easy. 
       destruct n.
       - assert (H' : as' = @Zero 1 1).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct i; destruct j; destruct col; try lia. 
           easy. }
         rewrite H'. 
         unfold col_add_each.
         rewrite Mmult_0_r, Mplus_0_r.
         easy. 
       - apply (Determinant_col_add_each_some n); try lia; try easy. 
         unfold skip_count. 
         bdestruct (n <? col); lia. 
         intros.
         unfold skip_count in *.
         + bdestruct (n <? col); bdestruct (col =? S n); try lia.
           bdestruct (i =? S n); try lia.  
           rewrite H5, <- H4; apply H1.
           apply H0; right. 
           bdestruct (i =? S n); try lia. 
           apply H0; right. 
           lia. 
Qed.




Lemma Det_0_lindep : forall {n} (A : Square n), 
  WF_Matrix A -> Determinant n A = C0 -> linearly_dependent A.
Proof. induction n as [| n'].
       - intros. 
         unfold Determinant in H.
         assert (H1 := C1_neq_C0).
         easy.
       - intros.
         destruct (gt_dim_lindep (reduce_row A 0)) as [v [H2 [H3 H4]]].
         lia. 
         apply WF_reduce_row; try lia; auto.
         destruct (nonzero_vec_nonzero_elem v) as [x H5]; auto.
         bdestruct (x <? S n').
         + Admitted.
           (*
           apply (lin_dep_col_add_many_conv _ _ x A (make_row_zero x v)); try easy.
           unfold make_row_zero.
           bdestruct_all; lca. 
           rewrite (Determinant_col_add_many _ x _ (make_row_zero x v)) in H0; try easy. 
            *)
          


