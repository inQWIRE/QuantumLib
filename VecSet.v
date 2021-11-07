Require Import Psatz.  
Require Import Reals.
  
Require Export Matrix.


(************************************)
(* some preliminary defs and lemmas *)
(************************************)

Local Open Scope nat_scope.


Definition e_i {n : nat} (i : nat) : Vector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then C1 else C0). 

Definition pad1 {n m : nat} (A : Matrix n m) (c : C) : Matrix (S n) (S m) :=
  col_wedge (row_wedge A Zero 0) (c .* e_i 0) 0.

Lemma WF_pad1 : forall {n m : nat} (A : Matrix n m) (c : C),
  WF_Matrix A <-> WF_Matrix (pad1 A c).
Proof. unfold WF_Matrix, pad1. split.
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

Lemma WF_e_i : forall {n : nat} (i : nat),
  WF_Matrix (@e_i n i).
Proof. unfold WF_Matrix, e_i.
       intros; destruct H as [H | H].
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
Qed.

Hint Resolve WF_e_i WF_pad1 : wf_db.

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


Lemma pad1_conv : forall {n m : nat} (A : Matrix n m) (c : C) (i j : nat),
  (pad1 A c) (S i) (S j) = A i j.
Proof. intros.
       unfold pad1, col_wedge, row_wedge, e_i.
       bdestruct (S j <? 0); bdestruct (S j =? 0); try lia.
       bdestruct (S i <? 0); bdestruct (S i =? 0); try lia.
       do 2 rewrite easy_sub.
       easy.
Qed.

Lemma pad1_mult : forall {n m o : nat} (A : Matrix n m) (B : Matrix m o) (c1 c2 : C),
  pad1 (A × B) (c1 * c2)%C = (pad1 A c1) × (pad1 B c2).
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       destruct x. 
       - unfold pad1, col_wedge, row_wedge, e_i, scale.
         bdestruct_all. 
         rewrite <- Csum_extend_l; simpl. 
         rewrite <- (Cplus_0_r (c1 * c2 * C1)).
         apply Cplus_simplify; try lca. 
         rewrite Csum_0_bounded; try easy.
         intros; lca. 
         rewrite Csum_0_bounded; try easy.
         simpl; intros. 
         bdestruct_all; lca. 
       - destruct y.
         unfold pad1, col_wedge, row_wedge, e_i, scale. 
         simpl. 
         rewrite Csum_0_bounded; try lca.   
         bdestruct_all; lca. 
         intros. bdestruct_all; lca. 
         rewrite pad1_conv.
         rewrite <- Csum_extend_l.
         rewrite <- (Cplus_0_l (Csum _ _)). 
         apply Cplus_simplify.
         unfold pad1, col_wedge, row_wedge, e_i, scale. 
         bdestruct_all; lca. 
         apply Csum_eq_bounded; intros. 
         do 2 rewrite pad1_conv; easy.
Qed.

Lemma pad1_row_wedge_mult : forall {n m : nat} (A : Matrix n m) (v : Vector m) (c : C),
  pad1 A c × row_wedge v Zero 0 = row_wedge (A × v) Zero 0.
Proof. intros. 
       prep_matrix_equality.
       destruct x.
       - unfold pad1, Mmult, col_wedge, row_wedge, scale, e_i.
         bdestruct_all;
         rewrite Csum_0_bounded; try lca; intros;
         bdestruct_all; lca. 
       - destruct y;
         unfold pad1, Mmult, col_wedge, row_wedge, scale, e_i;
         bdestruct_all;
         rewrite <- Csum_extend_l, <- Cplus_0_l;
         apply Cplus_simplify; try lca;
         apply Csum_eq_bounded; intros;  
         bdestruct_all; do 2 rewrite easy_sub; easy. 
Qed.

Lemma pad1_I : forall (n : nat), pad1 (I n) C1 = I (S n).
Proof. intros. 
       unfold pad1, I, col_wedge, row_wedge, e_i, scale.
       prep_matrix_equality. 
       bdestruct (y <? 0); bdestruct (y =? 0); bdestruct (x <? 0); bdestruct (x <? S n);
         bdestruct (x =? 0); bdestruct (x =? y); bdestruct (x - 1 =? y - 1); 
         bdestruct (x - 1 <? n); try lia; try lca.
Qed.


Lemma pad1ded : forall {n m : nat} (A : Matrix (S n) (S m)) (c : C),
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0) -> A 0 0 = c ->
  exists a : Matrix n m, pad1 a c = A.
Proof. intros.  
       exists (reduce_col (reduce_row A 0) 0).
       unfold pad1, reduce_row, reduce_col, col_wedge, row_wedge, e_i, scale.
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


Lemma reduce_pad1 : forall {n : nat} (A : Square n) (c : C),
  A = reduce (pad1 A c) 0 0.
Proof. intros. 
       prep_matrix_equality.
       unfold reduce, pad1, col_wedge, row_wedge, e_i. 
       bdestruct_all.
       destruct x; destruct y; easy.  
Qed.


Lemma pad1_col_swap : forall {n m : nat} (A : Matrix n m) (x y : nat) (c : C),
  (pad1 (col_swap A x y) c) = col_swap (pad1 A c) (S x) (S y).
Proof. intros. 
       unfold pad1, col_wedge, row_wedge, col_swap, e_i, scale. 
       prep_matrix_equality.
       bdestruct_all; try easy. 
       all : rewrite easy_sub; easy.
Qed.

Lemma pad1_col_scale : forall {n m : nat} (A : Matrix n m) (x : nat) (c1 c2 : C),
  (pad1 (col_scale A x c1) c2) = col_scale (pad1 A c2) (S x) c1.
Proof. intros. 
       unfold pad1, col_wedge, row_wedge, col_scale, e_i, scale. 
       prep_matrix_equality.
       bdestruct_all; try easy. 
       lca. 
Qed.

Lemma pad1_col_add : forall {n m : nat} (A : Matrix n m) (x y : nat) (c1 c2 : C),
  (pad1 (col_add A x y c1) c2) = col_add (pad1 A c2) (S x) (S y) c1.
Proof. intros. 
       unfold pad1, col_wedge, row_wedge, col_add, e_i, scale. 
       prep_matrix_equality.
       bdestruct_all; try easy. 
       all : rewrite easy_sub; try easy.
       lca. 
Qed.

(***************************************************************************)
(* Defining properties which are invarient under column operations, etc... *)
(***************************************************************************)


Inductive invr_col_swap : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| invr_swap : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
    (forall (n m x y : nat) (T : Matrix n m), x < m -> y < m -> P n m T -> P n m (col_swap T x y)) 
    -> invr_col_swap P.

Inductive invr_col_scale : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| invr_scale : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
    (forall (n m x : nat) (T : Matrix n m) (c : C), c <> C0 -> P n m T -> P n m (col_scale T x c)) 
    -> invr_col_scale P.

Inductive invr_col_add : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| invr_add : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
    (forall (n m x y : nat) (T : Matrix n m) (c : C), 
        x <> y -> x < m -> y < m -> P n m T -> P n m (col_add T x y c)) 
    -> invr_col_add P.

Inductive invr_col_add_many : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| invr_add_many : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
    (forall (n m col : nat) (T : Matrix n m) (as' : Vector m), 
        col < m -> as' col 0 = C0 -> P n m T -> P n m (col_add_many col as' T)) 
    -> invr_col_add_many P.

Inductive invr_col_add_each : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| invr_add_each : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
    (forall (n m col : nat) (T : Matrix n m) (as' : Matrix 1 m), 
        col < m -> WF_Matrix as' -> P n m T -> P n m (col_add_each col (make_col_zero col as') T)) 
    -> invr_col_add_each P.

Inductive invr_pad1 : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| invr_p : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
    (forall (n m : nat) (T : Matrix n m) (c : C), c <> C0 -> P (S n) (S m) (pad1 T c) -> P n m T) 
    -> invr_pad1 P.

Inductive prop_zero_true : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| PZT : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
  (forall (n m : nat) (T : Matrix n m), (exists i, i < m /\ get_vec i T = Zero) -> P n m T) ->
  prop_zero_true P.

Inductive prop_zero_false : (forall n m : nat, Matrix n m -> Prop) -> Prop :=
| PZF : forall (P : (forall n m : nat, Matrix n m -> Prop)), 
  (forall (n m : nat) (T : Matrix n m), (exists i, i < m /\ get_vec i T = Zero) -> ~ (P n m T)) ->
  prop_zero_false P.

(* Ltac to help apply these properties of (Mat -> Prop)s *)
Ltac apply_mat_prop tac := 
  let H := fresh "H" in 
  assert (H := tac); inversion H; subst; try apply H. 

Lemma mat_prop_col_add_many_some : forall (e n m col : nat) (P : forall n m : nat, Matrix n m -> Prop)
                                     (T : Matrix n m) (as' : Vector m),
  (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = C0) -> as' col 0 = C0 ->
  invr_col_add P ->
  P n m T -> P n m (col_add_many col as' T).
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


Lemma invr_col_add_col_add_many : forall (P : forall n m : nat, Matrix n m -> Prop),
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

Lemma mat_prop_col_add_each_some : forall (e n m col : nat) (P : forall n m : nat, Matrix n m -> Prop)
                                     (as' : Matrix 1 m) (T : Matrix n m),
  WF_Matrix as' -> (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = C0) -> as' 0 col = C0 ->
  invr_col_add P -> 
  P n m T -> P n m (col_add_each col as' T).
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
              
Lemma invr_col_add_col_add_each : forall (P : forall n m : nat, Matrix n m -> Prop),
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

Lemma mat_prop_col_swap_conv : forall {n m} (P : forall n m : nat, Matrix n m -> Prop) (T : Matrix n m) (x y : nat),
  invr_col_swap P -> 
  x < m -> y < m -> 
  P n m (col_swap T x y) -> P n m T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_swap_inv T x y).
       apply H3; easy.
Qed.

Lemma mat_prop_col_scale_conv : forall {n m} (P : forall n m : nat, Matrix n m -> Prop) 
                                  (T : Matrix n m) (x : nat) (c : C),
  invr_col_scale P ->
  c <> C0 ->
  P n m (col_scale T x c) -> P n m T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_scale_inv T x c); try easy.
       apply H2; try apply nonzero_div_nonzero; easy.
Qed.

Lemma mat_prop_col_add_conv : forall {n m} (P : forall n m : nat, Matrix n m -> Prop)  
                                (T : Matrix n m) (x y : nat) (c : C),
  invr_col_add P ->
  x <> y -> x < m -> y < m -> 
  P n m (col_add T x y c) -> P n m T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_add_inv T x y c); try easy. 
       apply H4; try easy. 
Qed.

Lemma mat_prop_col_add_many_conv : forall {n m} (P : forall n m : nat, Matrix n m -> Prop) 
                                     (T : Matrix n m) (col : nat) (as' : Vector m),
  invr_col_add P ->
  col < m -> as' col 0 = C0 -> 
  P n m (col_add_many col as' T) -> P n m T.
Proof. intros. 
       apply invr_col_add_col_add_many in H.
       inversion H; subst. 
       rewrite (col_add_many_inv T col as'); try easy.
       apply H3; try easy. 
       unfold scale; rewrite H1.
       lca. 
Qed.

Lemma mat_prop_col_add_each_conv : forall {n m} (P : forall n m : nat, Matrix n m -> Prop) 
                                     (T : Matrix n m) (col : nat) (as' : Matrix 1 m),
  invr_col_add P ->
  col < m -> WF_Matrix as' -> 
  P n m (col_add_each col (make_col_zero col as') T) -> P n m T.
Proof. intros. 
       apply invr_col_add_col_add_each in H.
       inversion H; subst. 
       rewrite (col_add_each_inv col as'); try easy.
       apply H3; try easy.
       auto with wf_db.
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

Arguments Determinant {n}.

Lemma Det_simplify : forall {n} (A : Square (S (S n))),
  Determinant A =  
  (Csum (fun i => (parity i) * (A i 0) * (Determinant (reduce A i 0)))%C (S (S n))).
Proof. intros. easy. Qed.


Lemma Det_simplify_fun : forall {n} (A : Square (S (S (S n)))),
  (fun i : nat => parity i * A i 0 * Determinant (reduce A i 0))%C =
  (fun i : nat => (Csum (fun j => 
           (parity i) * (A i 0) * (parity j) * ((reduce A i 0) j 0) * 
           (Determinant (reduce (reduce A i 0) j 0)))%C (S (S n))))%C.
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
       apply WF_I.
       unfold mat_equiv; intros.
       unfold reduce, I.
       bdestruct (i <? 0); bdestruct (j <? 0); try lia. 
       easy. 
Qed.       

Lemma Det_I : forall (n : nat), Determinant (I n) = C1.
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

Lemma Det_make_WF : forall (n : nat) (A : Square n),
  Determinant A = Determinant (make_WF A).
Proof. induction n as [| n'].  
       - easy. 
       - intros. 
         destruct n'; try easy. 
         do 2 rewrite Det_simplify. 
         apply Csum_eq_bounded; intros. 
         assert (H' : (reduce (make_WF A) x 0) = make_WF (reduce A x 0)).
         { prep_matrix_equality.
           unfold reduce, make_WF.
           bdestruct_all; try easy. }
         rewrite H', IHn'.
         unfold make_WF. 
         bdestruct_all; easy. 
Qed.

Lemma Det_Mmult_make_WF_l : forall (n : nat) (A B : Square n),
  Determinant (A × B) = Determinant (make_WF A × B).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ (make_WF A × B)).
       do 2 rewrite <- Mmult_make_WF.
       rewrite <- (eq_make_WF (make_WF A)); auto with wf_db.
Qed.

Lemma Det_Mmult_make_WF_r : forall (n : nat) (A B : Square n),
  Determinant (A × B) = Determinant (A × (make_WF B)).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ (A × make_WF B)).
       do 2 rewrite <- Mmult_make_WF.
       rewrite <- (eq_make_WF (make_WF B)); auto with wf_db.
Qed.

Lemma Det_Mmult_make_WF : forall (n : nat) (A B : Square n),
  Determinant (A × B) = Determinant ((make_WF A) × (make_WF B)).
Proof. intros. 
       rewrite <- Det_Mmult_make_WF_r, <- Det_Mmult_make_WF_l; easy. 
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


Lemma Det_M22 : (Determinant M22) = (Copp (3%R,0%R))%C.
Proof. lca. Qed.


Lemma Determinant_scale : forall {n} (A : Square n) (c : C) (col : nat),
  col < n -> Determinant (col_scale A col c) = (c * Determinant A)%C.
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
  Determinant (col_swap A 0 1) = 
  Csum (fun i => (Csum (fun j => ((A i 1) * (A (skip_count i j) 0) * (parity i) * (parity j) * 
                             Determinant (reduce (reduce A i 0) j 0))%C)  
                             (S (S n)))) (S (S (S n))).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply Csum_eq_bounded; intros. 
       apply Csum_eq_bounded; intros. 
       replace (col_swap A 0 1 x 0) with (A x 1) by easy. 
       assert (H' : @reduce (S (S n)) (col_swap A 0 1) x 0 x0 0 = A (skip_count x x0) 0).
       { unfold reduce, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'.    
       apply Cmult_simplify; try easy. 
       lca. 
Qed.

Lemma Det_diff_2 : forall {n} (A : Square (S (S (S n)))),
  Determinant A = 
  Csum (fun i => (Csum (fun j => ((A i 0) * (A (skip_count i j) 1) * (parity i) * (parity j) * 
                             Determinant (reduce (reduce A i 0) j 0))%C)  
                             (S (S n)))) (S (S (S n))).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply Csum_eq_bounded; intros. 
       apply Csum_eq_bounded; intros. 
       apply Cmult_simplify; try easy. 
       assert (H' : @reduce (S (S n)) A x 0 x0 0 = A (skip_count x x0) 1).
       { unfold reduce, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'. 
       lca. 
Qed.
  

Lemma Determinant_swap_01 : forall {n} (A : Square n),
  1 < n -> Determinant (col_swap A 0 1) = (-C1 * (Determinant A))%C.
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
  S i < n -> Determinant (col_swap A i (S i)) = (-C1 * (Determinant A))%C.
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
  i + (S k) < n -> Determinant (col_swap A i (i + (S k))) = (-C1 * (Determinant A))%C.
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
  Determinant (col_swap A i j) = (-C1 * (Determinant A))%C.
Proof. intros. 
       bdestruct (i <? j); bdestruct (j <? i); try lia. 
       - replace j with (i + (S (j - i - 1))) by lia. 
         rewrite Determinant_swap_ik; try lia; easy.
       - replace i with (j + (S (i - j - 1))) by lia. 
         rewrite col_swap_diff_order. 
         rewrite Determinant_swap_ik; try lia; easy.
Qed.


Lemma col_0_Det_0 : forall {n} (A : Square n),
  (exists i, i < n /\ get_vec i A = Zero) -> Determinant A = C0.
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
  Determinant A = C0.
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
  Determinant A = C0.
Proof. intros. 
       destruct (Ceq_dec c C0).
       - apply col_0_Det_0.
         exists i.
         split; try easy.
         rewrite H2, e.
         apply Mscale_0_l.
       - rewrite (col_scale_inv A j c); try easy.
         rewrite Determinant_scale; try easy.
         assert (H3 : Determinant (col_scale A j c) = C0).
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
  (Determinant (col_wedge T v1 0) + Determinant (col_wedge T v2 0) = 
   Determinant (col_wedge T (v1 .+ v2) 0))%C.
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
  i < n -> i <> 0 -> Determinant (col_add A 0 i c) = Determinant A.     
Proof. intros. 
       destruct n; try easy.
       rewrite col_add_split.
       assert (H' := (@Det_col_add_comm n (reduce_col A 0) (get_vec 0 A) (c .* get_vec i A))).
       rewrite <- H'.
       rewrite <- Cplus_0_r.
       apply Cplus_simplify. 
       assert (H1 : col_wedge (reduce_col A 0) (get_vec 0 A) 0 = A).
       { prep_matrix_equality.
         unfold col_wedge, reduce_col, get_vec. 
         destruct y; try easy; simpl.  
         replace (y - 0) with y by lia; easy. }
       rewrite H1; easy.
       apply (col_scale_same_Det_0 _ 0 i c); try lia.
       prep_matrix_equality. 
       unfold get_vec, col_wedge, reduce_col, scale; simpl. 
       bdestruct (y =? 0); bdestruct (i =? 0); try lca; try lia.
       replace (S (i - 1)) with i by lia. 
       easy. 
Qed.


Lemma Determinant_col_add : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> Determinant (col_add A i j c) = Determinant A.     
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

(* We can now define some invariants for Determinant *)
Definition det_neq_0 {n m : nat} (A : Matrix n m) : Prop :=
  n = m /\ @Determinant n A <> C0.

Definition det_eq_c (c : C) {n m : nat} (A : Matrix n m) : Prop :=
  n = m /\ @Determinant n A = c.


Lemma det_neq_0_swap_invr : invr_col_swap (@det_neq_0).
Proof. apply invr_swap; intros.  
       destruct H1; subst. 
       split; auto.
       bdestruct (x =? y); subst. 
       - rewrite col_swap_same.
         easy. 
       - rewrite Determinant_swap; auto.         
         unfold not; intros.
         apply H2.
         rewrite <- (Cmult_1_l _).
         replace C1 with ((-C1) * (-C1))%C by lca. 
         rewrite <- Cmult_assoc, H3. 
         lca. 
Qed.

Lemma det_neq_0_scale_invr : invr_col_scale (@det_neq_0).
Proof. apply invr_scale; intros.  
       destruct H0; subst. 
       split; auto.
       bdestruct (x <? m).
       - rewrite Determinant_scale; auto. 
         apply Cmult_neq_0; easy. 
       - rewrite Det_make_WF in *. 
         assert (H' : (make_WF T) = (make_WF (col_scale T x c))).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv, make_WF, col_scale; intros. 
           bdestruct_all; easy. }
         rewrite <- H'; easy. 
Qed.

Lemma det_neq_0_add_invr : invr_col_add (@det_neq_0).
Proof. apply invr_add; intros.  
       destruct H2; subst. 
       split; auto. 
       rewrite Determinant_col_add; easy.
Qed.


Lemma det_neq_0_pad1_invr : invr_pad1 (@det_neq_0).  
Proof. apply invr_p; intros. 
       destruct H0; apply eq_add_S in H0; subst. 
       split; auto. 
       destruct m. 
       - apply C1_neq_C0. 
       - unfold not; intros; apply H1.
         rewrite Det_simplify. 
         apply Csum_0_bounded; intros. 
         destruct x. 
         + rewrite <- reduce_pad1, H0; lca. 
         + unfold pad1, col_wedge, row_wedge, e_i, scale.
           bdestruct_all; simpl. 
           lca. 
Qed.

Lemma det_neq_0_pzf : prop_zero_false (@det_neq_0).  
Proof. apply PZF; intros.
       unfold not; intros. 
       destruct H0; subst. 
       apply (col_0_Det_0 T) in H.
       easy. 
Qed.

Lemma det_0_swap_invr : invr_col_swap (@det_eq_c C0).
Proof. apply invr_swap; intros.  
       unfold det_eq_c in *; destruct H1; subst. 
       split; auto.
       bdestruct (x =? y); subst. 
       - rewrite col_swap_same.
         easy. 
       - rewrite Determinant_swap; auto. 
         rewrite H2; lca. 
Qed.

Lemma det_0_scale_invr : invr_col_scale (@det_eq_c C0).
Proof. apply invr_scale; intros. 
       unfold det_eq_c in *; destruct H0; subst. 
       split; auto.
       bdestruct (x <? m).
       - rewrite Determinant_scale; auto. 
         rewrite H1; lca. 
       - rewrite Det_make_WF in *. 
         assert (H' : (make_WF T) = (make_WF (col_scale T x c))).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv, make_WF, col_scale; intros. 
           bdestruct_all; easy. }
         rewrite <- H'; easy. 
Qed.

Lemma det_c_add_invr : forall (c : C), invr_col_add (@det_eq_c c).
Proof. intros. 
       apply invr_add; intros.  
       unfold det_eq_c in *; destruct H2; subst. 
       split; auto. 
       apply Determinant_col_add; easy.
Qed.

Lemma det_0_pad1_invr : invr_pad1 (@det_eq_c C0).
Proof. apply invr_p; intros. 
       destruct H0; apply eq_add_S in H0; subst. 
       split; auto. 
       destruct m. 
       - simpl in H1.         
         unfold pad1, col_wedge, row_wedge, e_i, scale in H1; 
         simpl in H1. 
         rewrite Cmult_1_r in H1. 
         easy.
       - rewrite Det_simplify in H1. 
         assert (H' : (c * Determinant (reduce (pad1 T c) 0 0) = C0)%C).
         { rewrite <- H1, (Csum_unique (c * Determinant (reduce (pad1 T c) 0 0))%C).  
           easy. 
           exists 0. split; try lia. 
           split. simpl parity. 
           apply Cmult_simplify; try easy.  
           unfold pad1, col_wedge, row_wedge, e_i, scale. 
           bdestruct_all; lca. 
           intros. 
           unfold pad1, col_wedge, row_wedge, e_i, scale. 
           bdestruct_all; lca. }
         rewrite <- reduce_pad1 in H'.
         destruct (Ceq_dec (Determinant T) C0); try easy. 
         apply (Cmult_neq_0 c _) in n; easy. 
Qed.

Hint Resolve det_neq_0_swap_invr det_neq_0_scale_invr det_neq_0_add_invr det_neq_0_pad1_invr : invr_db.
Hint Resolve det_neq_0_pzf det_0_swap_invr det_0_scale_invr det_c_add_invr det_0_pad1_invr : invr_db.


Lemma Determinant_col_add_many : forall (n col : nat) (A : Square n) (as' : Vector n),
  col < n -> as' col 0 = C0 -> 
  Determinant A = Determinant (col_add_many col as' A).
Proof. intros.
       assert (H' := det_c_add_invr (Determinant A)).
       apply invr_col_add_col_add_many in H'. 
       inversion H'; subst. 
       apply (H1 n n col A as') in H; try easy.
       unfold det_eq_c in *.
       destruct H; easy. 
Qed.


Lemma Determinant_col_add_each : forall (n col : nat) (as' : Matrix 1 n) 
                                          (A : Square n),
  col < n -> WF_Matrix as' -> as' 0 col = C0 ->
  Determinant A = Determinant (col_add_each col as' A).
Proof. intros. 
       assert (H' := det_c_add_invr (Determinant A)).
       apply invr_col_add_col_add_each in H'. 
       inversion H'; subst. 
       apply (H2 n n col A as') in H; try easy.
       unfold det_eq_c in *.
       destruct H; rewrite <- H3.
       assert (H4 : (make_col_zero col as') = as').
       { apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         unfold make_col_zero.
         destruct i; try lia.
         bdestruct_all; subst; easy. }
       rewrite H4; easy.
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

Lemma lin_indep_col_reduce_n : forall {n m} (A : Matrix n (S m)),
  linearly_independent A -> linearly_independent (reduce_col A m).
Proof. intros. 
       unfold linearly_independent in *. 
       intros. 
       assert (H' : row_append a Zero = Zero).
       { apply H.
         apply WF_row_append; try easy.
         prep_matrix_equality. 
         unfold Mmult, row_append, Zero.  
         rewrite <- Csum_extend_r. 
         bdestruct (m =? m); try lia. 
         autorewrite with C_db.
         assert (H' : (reduce_col A m × a) x y = C0).
         { rewrite H1; easy. }
         rewrite <- H'. 
         unfold Mmult. 
         apply Csum_eq_bounded. 
         intros.
         unfold reduce_col.
         bdestruct (x0 =? m); bdestruct (x0 <? m); try lia. 
         reflexivity. } 
       prep_matrix_equality. 
       assert (H'' : row_append a Zero x y = C0). { rewrite H'. easy. }
       unfold Zero; simpl. rewrite <- H''. 
       unfold row_append.
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
         rewrite <- plus_n_Sm in H.
         apply H1 in H.
         rewrite smash_reduce in H.
         apply (IHm2' m1 A1 (reduce_col A2 m2')).
         easy.
Qed.

Lemma lin_dep_mult_r : forall {n m o} (A : Matrix n m) (B : Matrix m o),
  linearly_dependent B -> linearly_dependent (A × B).
Proof. intros. 
       unfold linearly_dependent in *.
       destruct H as [a [H [H0 H1]]].
       exists a. 
       repeat split; auto.  
       rewrite Mmult_assoc, H1, Mmult_0_r; easy. 
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


(* proving invr properties *)


Lemma lin_indep_swap_invr : invr_col_swap (@linearly_independent). 
Proof. apply invr_swap; intros. 
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

Lemma lin_indep_scale_invr : invr_col_scale (@linearly_independent). 
Proof. apply invr_scale; intros. 
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

Lemma lin_indep_add_invr : invr_col_add (@linearly_independent). 
Proof. apply invr_add; intros. 
       unfold linearly_independent in *.
       intros.  
       rewrite <- add_preserves_mul in H4; try easy.
       apply H2 in H4.
       rewrite (row_add_inv a y x c); try lia.
       rewrite H4.
       prep_matrix_equality. 
       unfold row_add.
       bdestruct (x0 =? y);
       lca. 
       apply WF_row_add; easy.
Qed.

Lemma lin_indep_pad1_invr : invr_pad1 (@linearly_independent).  
Proof. apply invr_p; intros. 
       unfold linearly_independent in *.
       intros. 
       assert (H3 : @Mmult (S n) (S m) 1 (pad1 T c) (row_wedge a Zero 0) = Zero).
       { prep_matrix_equality. 
         destruct x. unfold Mmult. 
         unfold Zero. apply Csum_0_bounded. 
         intros.
         unfold pad1, row_wedge, col_wedge, e_i, scale.
         bdestruct (x <? 0); bdestruct (x =? 0); try lia. lca. 
         lca.
         assert (p : @Zero (S n) 1 (S x) y = C0).
         easy.
         assert (H2' : (T × a) x y = C0). 
         rewrite H2; easy.
         rewrite p. 
         rewrite <- H2'.
         unfold Mmult. rewrite <- Csum_extend_l.  
         rewrite <- Cplus_0_l.
         apply Cplus_simplify.
         unfold pad1, row_wedge, col_wedge, e_i.
         bdestruct (x <? 0); bdestruct (x =? 0); try lia. 
         rewrite H4; simpl. lca. 
         rewrite easy_sub. lca. 
         apply Csum_eq_bounded; intros. 
         rewrite pad1_conv.
         unfold row_wedge.
         rewrite easy_sub. 
         easy. }
       apply H0 in H3.
       prep_matrix_equality. 
       assert (H4 : row_wedge a Zero 0 (S x) y = C0).
       rewrite H3; easy.
       unfold Zero. rewrite <- H4.
       unfold row_wedge. 
       rewrite easy_sub.
       easy.
       apply WF_row_wedge; try lia; easy.
Qed.   

Lemma lin_indep_pzf : prop_zero_false (@linearly_independent).
Proof. apply PZF; intros. 
       unfold not; intros. 
       unfold linearly_independent in *.  
       destruct H as [i [H H1]].
       assert (H2 : T × @e_i m i = Zero).
       { prep_matrix_equality.
         unfold Mmult, Zero, e_i; simpl.  
         apply Csum_0_bounded; intros. 
         bdestruct_all; try lca; 
         rewrite <- get_vec_conv; subst.
         rewrite H1; lca. }
       apply H0 in H2; auto with wf_db.
       assert (H3 : @e_i m i i 0 = C0).
       rewrite H2; easy.
       unfold e_i in H3.
       apply C1_neq_C0.
       rewrite <- H3.
       bdestruct_all; easy.
Qed.

Lemma lin_dep_swap_invr : invr_col_swap (@linearly_dependent).
Proof. apply invr_swap; intros. 
       unfold linearly_dependent in *.
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
 
Lemma lin_dep_scale_invr : invr_col_scale (@linearly_dependent).
Proof. intros. 
       apply invr_scale; intros. 
       unfold linearly_dependent in *.
          destruct H0 as [a [H1 [H2 H3]]].
          exists (row_scale a x (/ c)).
          split; auto with wf_db.
          split. unfold not; intros.
          apply H2.
          rewrite (row_scale_inv _ x (/ c)); try easy.
          rewrite H0. 
          prep_matrix_equality. 
          unfold row_scale, Zero. 
          bdestruct (x0 =? x); try lia; lca. 
          apply nonzero_div_nonzero; easy.
          rewrite scale_preserves_mul. 
          rewrite <- (col_scale_inv T x c); easy.       
Qed.

Lemma lin_dep_add_invr : invr_col_add (@linearly_dependent).
Proof. intros.
       apply invr_add; intros. 
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
       rewrite add_preserves_mul; try easy.
       rewrite <- (col_add_inv T x y c); try lia; easy.
Qed.

Lemma lin_dep_pzt : prop_zero_true (@linearly_dependent).
Proof. apply PZT; intros. 
       unfold linearly_dependent in *; intros. 
       destruct H as [i [H0 H1]].
       exists (@e_i m i).
       split; auto with wf_db. 
       split. 
       unfold not; intros. 
       assert (H' : (@e_i m i) i 0 = C0).
       { rewrite H; easy. }
       unfold e_i in H'; simpl in H'.
       bdestruct (i =? i); bdestruct (i <? m); try lia. 
       simpl in H'.
       apply C1_neq_C0.
       easy.
       rewrite <- matrix_by_basis; easy.
Qed.

Hint Resolve lin_indep_swap_invr lin_indep_scale_invr lin_indep_add_invr lin_indep_pad1_invr : invr_db.
Hint Resolve lin_indep_pzf lin_dep_swap_invr lin_dep_scale_invr lin_dep_add_invr lin_dep_pzt : invr_db.


(* we begin to prove that if n < m, then any Matrix n m is linearly_dependent *)

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
         split; auto with wf_db. 
         apply mat_equiv_eq; auto with wf_db.
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
       apply (mat_prop_col_add_each_conv _ _ col (-C1 .* (get_row 0 T))); 
         auto with wf_db; try lia.
       apply lin_dep_add_invr.
       unfold linearly_dependent in *.
       destruct H2 as [a [H3 [H4 H5]]]. 
       repeat rewrite easy_sub in *.
       exists (row_wedge a (@Zero 1 1) col).
       split; auto with wf_db.
       split. 
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
           rewrite p, Csum_sum.
           assert (p1 : S m - col = S (m - col)). lia. 
           rewrite p1, <- Csum_extend_l. 
           simpl. bdestruct (col + 0 =? col); bdestruct (col + 0 <? col); try lia. 
           assert (p2 : m = col + (m - col)). lia.
           rewrite p2, Csum_sum, <- p2.
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
       assert (H' := @col_add_many_cancel n m (reduce_row T 0) v col).
       assert (H0' : forall i : nat, @col_add_many n (S m) col v  (reduce_row T 0) i col = C0).
       { apply H'; try easy. }
       apply (mat_prop_col_add_many_conv _ _ col v); try easy.
       apply lin_dep_add_invr.
       destruct (Ceq_dec ((col_add_many col v T) 0 col) C0).
       - apply_mat_prop (@lin_dep_pzt). 
         apply H5; exists col. 
         split; auto. 
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
       - apply (mat_prop_col_scale_conv _ _ col (/ (col_add_many col v T 0 col))); 
           try apply nonzero_div_nonzero; try easy.
         apply lin_dep_scale_invr.
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
           rewrite (H0' i); lca. 
         + rewrite col_scale_reduce_col_same; try easy.
           rewrite col_add_many_reduce_col_same. 
           easy.
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
             apply H''.
             apply IHm'; try easy; auto with wf_db.
             apply WF_reduce_col. lia. 
             all : apply WF_reduce_row; try lia; easy. }
           apply lin_dep_gen_elem in H'; auto with wf_db.
           destruct H' as [i [H2 H3]].
           destruct H3 as [v [H3 H4]]. 
           * apply (gt_dim_lindep_ind_step2 _ (row_wedge v (@Zero 1 1) i) i); try easy.
             unfold row_wedge.
             bdestruct (i <? i); bdestruct (i =? i); try lia; easy.
             rewrite row_wedge_reduce_row_same; easy.
             apply (IHm' n' (reduce_row (reduce_col T i) 0)); try lia. 
             apply WF_reduce_row; try apply WF_reduce_col; try lia; easy. 
           * apply WF_reduce_row; try lia; easy.
Qed.

(*****************************************************************************************)
(* defining a new type of matrix which we will show is the lin_indep/invertible matrices *)
(*****************************************************************************************)


Inductive op_to_I {n : nat} : Square n -> Prop :=
| otI_I: op_to_I (I n)
| otI_swap : forall (A : Square n) (x y : nat), x < n -> y < n -> 
                                         op_to_I A -> op_to_I (col_swap A x y)
| otI_scale : forall (A : Square n) (x : nat) (c : C), x < n -> c <> C0 -> 
                                         op_to_I A -> op_to_I (col_scale A x c)
| otI_add : forall (A : Square n) (x y : nat) (c : C), x < n -> y < n -> x <> y -> 
                                         op_to_I A -> op_to_I (col_add A x y c).



Lemma op_to_I_WF : forall {n} (A : Square n),
  op_to_I A -> WF_Matrix A.
Proof. intros.  
       apply op_to_I_ind; auto with wf_db.
Qed.

Hint Resolve op_to_I_WF : wf_db.


Definition otI_multiplicative {n} (A : Square n) : Prop := 
  forall (B : Square n), (op_to_I B -> op_to_I (B × A)).


Lemma otI_implies_otI_multiplicative : forall {n} (A : Square n),
  op_to_I A -> otI_multiplicative A. 
Proof. intros.   
       apply op_to_I_ind; auto. 
       - unfold otI_multiplicative; intros.
         rewrite Mmult_1_r; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         rewrite col_swap_mult_r; auto with wf_db.
         rewrite <- Mmult_assoc. 
         rewrite <- col_swap_mult_r; auto with wf_db.
         apply otI_swap; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         rewrite col_scale_mult_r; auto with wf_db.
         rewrite <- Mmult_assoc. 
         rewrite <- col_scale_mult_r; auto with wf_db.
         apply otI_scale; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         rewrite col_add_mult_r; auto with wf_db.
         rewrite <- Mmult_assoc. 
         rewrite <- col_add_mult_r; auto with wf_db.
         apply otI_add; auto with wf_db.
Qed.


Lemma otI_Mmult : forall {n} (A B : Square n),
  op_to_I A -> op_to_I B ->
  op_to_I (A × B).
Proof. intros. 
       apply otI_implies_otI_multiplicative in H0.
       unfold otI_multiplicative in H0.
       apply H0; easy. 
Qed.

Definition otI_pad1ded {n} (A : Square n) : Prop := 
  forall (c :  C), (c <> C0 -> op_to_I (pad1 A c)).

Lemma otI_implies_otI_pad1ded : forall {n} (A : Square n),
  op_to_I A -> otI_pad1ded A.
Proof. intros. 
       apply op_to_I_ind; auto. 
       - unfold otI_pad1ded; intros. 
         assert (H' : (pad1 (I n) c) = col_scale (I (S n)) 0 c).
         { apply mat_equiv_eq; auto with wf_db.
           apply WF_pad1; apply WF_I.
           unfold mat_equiv; intros. 
           unfold pad1, col_scale, col_wedge, row_wedge, e_i, scale, I.
           bdestruct_all; easy. }
         rewrite H'.
         apply otI_scale; auto; try lia. 
         apply otI_I.
       - intros. 
         unfold otI_pad1ded in *; intros. 
         rewrite pad1_col_swap. 
         apply otI_swap; try lia. 
         apply H3; easy. 
       - intros. 
         unfold otI_pad1ded in *; intros. 
         rewrite pad1_col_scale. 
         apply otI_scale; try lia; try easy. 
         apply H3; easy. 
       - intros. 
         unfold otI_pad1ded in *; intros. 
         rewrite pad1_col_add. 
         apply otI_add; try lia; try easy. 
         apply H4; easy. 
Qed.

Lemma otI_pad1 : forall {n} (A : Square n) (c : C),
  c <> C0 -> op_to_I A -> 
  op_to_I (pad1 A c).
Proof. intros. 
       apply otI_implies_otI_pad1ded in H0.
       unfold otI_pad1ded in H0.
       apply H0; easy. 
Qed.


Lemma otI_lin_indep : forall {n} (A : Square n),
  op_to_I A -> linearly_independent A.
Proof. intros. 
       apply op_to_I_ind; auto. 
       - unfold linearly_independent; intros. 
         rewrite Mmult_1_l in H1; auto with wf_db.
       - intros. 
         apply_mat_prop lin_indep_swap_invr.
         apply H5; auto. 
       - intros. 
         apply_mat_prop lin_indep_scale_invr.
         apply H5; auto. 
       - intros. 
         apply_mat_prop lin_indep_add_invr.
         apply H6; auto. 
Qed.


(* need alternate def to deal with broader n <> m case *)
Definition op_to_I' {n m : nat} (A : Matrix n m) :=
  n = m /\ @op_to_I n A.

Lemma otI_equiv_otI' : forall {n} (A : Square n),
  op_to_I' A <-> op_to_I A.
Proof. intros. split. 
       - intros. 
         destruct H; easy. 
       - intros. 
         split; easy. 
Qed.

Lemma otI'_add_invr : invr_col_add (@op_to_I').
Proof. apply invr_add; intros. 
       destruct H2; split; try easy; subst. 
       apply otI_add; easy. 
Qed.


Lemma otI_col_add_many : forall (n col : nat) (A : Square n) (as' : Vector n),
  col < n -> as' col 0 = C0 -> 
  op_to_I A -> op_to_I (col_add_many col as' A).
Proof. intros. 
       assert (H' := otI'_add_invr).
       apply invr_col_add_col_add_many in H'. 
       inversion H'; subst. 
       apply (H2 n n col A as') in H; try easy. 
       destruct H; easy. 
Qed.


Lemma otI_col_add_each : forall (n col : nat) (A : Square n) (as' : Matrix 1 n),
  col < n -> WF_Matrix as' -> as' 0 col = C0 ->  
  op_to_I A -> op_to_I (col_add_each col as' A).
Proof. intros. 
       assert (H' := otI'_add_invr).
       apply invr_col_add_col_add_each in H'. 
       inversion H'; subst. 
       apply (H3 n n col A as') in H; try easy. 
       assert (H4 : (make_col_zero col as') = as').
       { apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         unfold make_col_zero.
         destruct i; try lia.
         bdestruct_all; subst; easy. }
       rewrite H4 in *.
       destruct H; easy. 
Qed.



(**********************************************)
(* Now we prove more properties of invariants *) 
(**********************************************)

         
(* a case for when we consider (Mat -> Prop)s that are the same as lin_indep, invertible, 
   etc... these props will satisfy 'prop_zero_false P' *)
Lemma mpr_step1_pzf_P : forall {n} (A : Square (S n)) (P : forall m o, Matrix m o -> Prop),
  invr_col_add P -> invr_col_scale P -> 
  prop_zero_false P -> 
  WF_Matrix A -> P (S n) (S n) A ->
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                       (exists i, i < (S n) /\ get_vec i (A × B) = e_i 0)).
Proof. intros.  
       assert (H4 : WF_Matrix (reduce_row A 0)).
       { apply WF_reduce_row; try lia; easy. } 
       assert (H5 : linearly_dependent (reduce_row A 0)).
       { apply gt_dim_lindep; try lia. 
         apply H4. }
       apply lin_dep_gen_elem in H4; try easy. 
       destruct H4 as [i [H6 H4]]. 
       destruct H4 as [v [H4 H7]].
       apply invr_col_add_col_add_many in H.
       inversion H; subst.
       assert (H9 : P (S n) (S n) (col_add_many i (row_wedge v Zero i) A)).
       apply H8; auto. 
       unfold row_wedge; bdestruct_all; easy.
       destruct (Ceq_dec ((col_add_many i (row_wedge v Zero i) A) 0 i) C0).
       - assert (H10 : forall i0 : nat, 
                   col_add_many i (row_wedge v Zero i) (reduce_row A 0) i0 i = C0).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge. 
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         assert (H11: get_vec i (col_add_many i (row_wedge v Zero i) A) = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct j; try lia.
           unfold get_vec; simpl. 
           destruct i0.
           rewrite e; easy.
           rewrite col_add_many_reduce_row in H10.
           replace ((@Zero (S n) 1 (S i0) 0)) with C0 by easy.  
           rewrite <- (H10 i0).
           unfold reduce_row.
           bdestruct (i0 <? 0); try lia. 
           easy. }
         inversion H1; subst.
         assert (H13 : ~ P (S n) (S n) (col_add_many i (row_wedge v Zero i) A)).
         { apply H12.
           exists i; split; auto. }
         easy.
       - inversion H0; subst. 
         assert (n0' := n0).
         apply nonzero_div_nonzero in n0.
         apply (H10 _ _ i (col_add_many i (row_wedge v Zero i) A)
                 (/ col_add_many i (row_wedge v Zero i) A 0 i)) in n0.
         assert (H11 : forall i0 : nat, 
                   col_add_many i (row_wedge v Zero i) (reduce_row A 0) i0 i = C0).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge.  
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         rewrite col_add_many_reduce_row in H11.                
         exists ((row_add_each i (row_wedge v Zero i) (I (S n))) × 
                  (row_scale (I (S n)) i 
                  (/ (col_add_many i (row_wedge v Zero i) A 0 i)))).
         split. 
         apply otI_Mmult.
         rewrite row_each_col_many_invr_I; auto with wf_db.
         apply otI_col_add_many; auto with wf_db. 
         all : try (unfold row_wedge; bdestruct_all; easy).
         apply otI_I.
         apply WF_row_wedge; auto with wf_db; try lia.
         rewrite <- col_row_scale_invr_I.
         apply otI_scale; auto with wf_db.
         apply nonzero_div_nonzero; auto. 
         apply otI_I.
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
         assert (H15 : col_add_many i (row_wedge v Zero i) A (S i0) i = C0).
         rewrite <- (H11 i0).
         unfold reduce_row.
         bdestruct (i0 <? 0); try lia; easy.
         rewrite H15. lca. 
         apply WF_col_add_many; auto with wf_db.
         apply WF_row_wedge; auto with wf_db; lia.
         unfold row_wedge.
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
Qed.   

(* a different case for when we consider (Mat -> Prop)s that are 
   the same as lin_indep, invertible, etc... *)
Lemma mrp_step1_pzt_P0 : forall {n} (A : Square (S n)) (P P0: forall m o, Matrix m o -> Prop),
  invr_col_add P -> invr_col_scale P -> 
  invr_col_add P0 -> prop_zero_true P0 -> 
  WF_Matrix A -> P (S n) (S n) A ->
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                       (exists i, i < (S n) /\ get_vec i (A × B) = e_i 0)) \/ P0 (S n) (S n) A.
Proof. intros. 
       assert (H5 : WF_Matrix (reduce_row A 0)).
       { apply WF_reduce_row; try lia; easy. }
       assert (H6 : linearly_dependent (reduce_row A 0)).
       { apply gt_dim_lindep; try lia. 
         apply H5. }
       apply lin_dep_gen_elem in H5; try easy. 
       destruct H5 as [i [H7 H5]]. 
       destruct H5 as [v [H5 H8]].
       apply invr_col_add_col_add_many in H.
       inversion H; subst.
       assert (H10 : P (S n) (S n) (col_add_many i (row_wedge v Zero i) A)).
       apply H9; auto. 
       unfold row_wedge; bdestruct_all; easy.
       destruct (Ceq_dec ((col_add_many i (row_wedge v Zero i) A) 0 i) C0).
       - right. 
         assert (H11 : forall i0 : nat, 
                   col_add_many i (row_wedge v Zero i) (reduce_row A 0) i0 i = C0).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge. 
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         assert (H12: get_vec i (col_add_many i (row_wedge v Zero i) A) = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct j; try lia.
           unfold get_vec; simpl. 
           destruct i0.
           rewrite e; easy.
           rewrite col_add_many_reduce_row in H11.
           replace ((@Zero (S n) 1 (S i0) 0)) with C0 by easy.  
           rewrite <- (H11 i0).
           unfold reduce_row.
           bdestruct (i0 <? 0); try lia. 
           easy. }
         inversion H2; subst. 
         apply (mat_prop_col_add_many_conv _ _ i (row_wedge v Zero i)); auto. 
         unfold row_wedge; bdestruct_all; easy.
         apply H13.
         exists i. split; auto. 
       - inversion H0; subst. 
         assert (n0' := n0).
         left. 
         apply nonzero_div_nonzero in n0.
         apply (H11 _ _ i (col_add_many i (row_wedge v Zero i) A)
                 (/ col_add_many i (row_wedge v Zero i) A 0 i)) in n0.
         assert (H12 : forall i0 : nat, 
                   col_add_many i (row_wedge v Zero i) (reduce_row A 0) i0 i = C0).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge.  
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         rewrite col_add_many_reduce_row in H12.                
         exists ((row_add_each i (row_wedge v Zero i) (I (S n))) × 
                  (row_scale (I (S n)) i 
                  (/ (col_add_many i (row_wedge v Zero i) A 0 i)))).
         split. 
         apply otI_Mmult.
         rewrite row_each_col_many_invr_I; auto with wf_db.
         apply otI_col_add_many; auto with wf_db. 
         all : try (unfold row_wedge; bdestruct_all; easy).
         apply otI_I.
         apply WF_row_wedge; auto with wf_db; try lia.
         rewrite <- col_row_scale_invr_I.
         apply otI_scale; auto with wf_db.
         apply nonzero_div_nonzero; auto. 
         apply otI_I.
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
         assert (H16 : col_add_many i (row_wedge v Zero i) A (S i0) i = C0).
         rewrite <- (H12 i0).
         unfold reduce_row.
         bdestruct (i0 <? 0); try lia; easy.
         rewrite H16. lca. 
         apply WF_col_add_many; auto with wf_db.
         apply WF_row_wedge; auto with wf_db; lia.
         unfold row_wedge.
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
Qed.   

(* in both cases, we can use mrp_step2 when we get that (exists i, ... ) *) 
Lemma mpr_step2 : forall {n} (A : Square (S n)) (P : forall m o, Matrix m o -> Prop), 
  invr_col_add P -> invr_col_swap P -> 
  WF_Matrix A -> P (S n) (S n) A ->  
  (exists i, i < (S n) /\ get_vec i A = e_i 0) ->
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                            (exists a : Square n, pad1 a C1 = (A × B))).
Proof. intros.
       destruct H3 as [i [H3 H4]].
       inversion H0; subst.
       apply (H5 _ _ 0 i A) in H2; try lia; try easy.
       apply invr_col_add_col_add_each in H.
       inversion H; subst.
       assert (H3' : 0 < S n). lia.
       apply (H6 _ _ 0 (col_swap A 0 i) (-C1 .* (get_row 0 (col_swap A 0 i)))) in H3'; try lia.
       exists ((row_swap (I (S n)) 0 i) × (row_add_many 0 
                                (make_col_zero 0 (-C1 .* (get_row 0 (col_swap A 0 i)))) 
                                (I (S n)))).
       split. 
       apply otI_Mmult.
       rewrite <- col_row_swap_invr_I; try lia. 
       apply otI_swap; try lia; apply otI_I.
       rewrite row_many_col_each_invr_I; try lia; auto.
       apply otI_col_add_each; try lia; auto with  wf_db.
       all : try (apply WF_make_col_zero; apply WF_scale; 
         apply WF_get_row; apply WF_col_swap; try lia; auto).  
       apply otI_I.
       rewrite <- Mmult_assoc. 
       rewrite <- col_swap_mult_r; try lia; try easy.
       rewrite <- col_add_each_mult_r; try lia; try easy.
       split; try easy. 
       apply pad1ded; intros. 
       4 : apply WF_make_col_zero.
       all : try (apply WF_scale; apply WF_get_row).  
       all : try (apply WF_col_swap; try lia; easy).
       destruct H7 as [H7 H8].
       destruct H7. 
       + unfold col_add_each, make_col_zero, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale.
         rewrite H7 in *.
         bdestruct (j =? 0); try lia. 
         assert (H' : (get_vec i A) 0 0 = C1).
         { rewrite H4. easy. }
         simpl. bdestruct (j =? i); try lia. 
         all : unfold get_vec in H'; simpl in H'.
         all : rewrite H'; lca. 
       + unfold col_add_each, make_col_zero, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale.
         rewrite H7 in *; simpl. 
         destruct i0; try lia.
         assert (H' : (get_vec i A) (S i0) 0 = C0).
         { rewrite H4. easy. }
         unfold get_vec in H'; simpl in H'. 
         rewrite H'; lca. 
       + unfold col_add_each, make_col_zero, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale; simpl.
         assert (H' : (get_vec i A) 0 0 = C1).
         { rewrite H4. easy. }
         unfold get_vec in H'; simpl in H'.
         rewrite H'; lca.
       + easy. 
Qed.    


(* these two lemmas allow us to reduce our study of Square (S n) to Square n, allowing 
   us to induct on n. Then, 'invr_pad1 P' allows us to jump from the n case to (S n) *) 
Lemma mat_prop_reduce_pzf_P : forall {n} (A : Square (S n)) (P P0 : forall m o, Matrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> 
  WF_Matrix A -> P (S n) (S n) A -> 
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                            (exists a : Square n, pad1 a C1 = (A × B))). 
Proof. intros. 
       apply (mpr_step1_pzf_P A P) in H5; auto.  
       destruct H5 as [B [H5 [H6 [i [H7 H8]]]]].
         apply (mpr_step2 (A × B) P) in H1; auto with wf_db.  
         destruct H1 as [B0 [H10 [H11 H12]]].
         exists (B × B0); split.  
         apply otI_Mmult; auto. 
         split; rewrite <- Mmult_assoc; easy.  
         exists i. split; easy. 
Qed.

Lemma mat_prop_reduce_pzt_P0 : forall {n} (A : Square (S n)) (P P0 : forall m o, Matrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> 
  invr_pad1 P -> 
  invr_col_add P0 -> prop_zero_true P0 -> 
  WF_Matrix A -> P (S n) (S n) A -> 
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                            (exists a : Square n, pad1 a C1 = (A × B))) \/ P0 (S n) (S n) A.
Proof. intros. 
       apply (mrp_step1_pzt_P0 A P P0) in H6; auto. 
       destruct H6.
       - left. 
         destruct H6 as [B [H6 [H7 [i [H8 H9]]]]].
         apply (mpr_step2 (A × B) P) in H1; auto with wf_db.  
         destruct H1 as [B0 [H10 [H11 H12]]].
         exists (B × B0); split.  
         apply otI_Mmult; auto. 
         split; rewrite <- Mmult_assoc; easy.  
         exists i. split; easy. 
       - right; easy. 
Qed.


(* now, we prove some theorems with these powerful lemmas *)
Theorem invr_P_implies_invertible_r : forall {n} (A : Square n) (P : forall m o, Matrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> 
  WF_Matrix A -> P n n A -> 
  (exists B, op_to_I B /\ A × B = I n).
Proof. induction n as [| n'].
       - intros.  
         exists (I 0). split.
         apply otI_I.
         assert (H' : I 0 = Zero). 
         prep_matrix_equality. 
         unfold I; bdestruct_all; easy. 
         rewrite H', Mmult_0_r.
         apply mat_equiv_eq; auto with wf_db. 
         unfold mat_equiv. lia.  
       - intros. 
         apply mat_prop_reduce_pzf_P in H5; auto. 
         destruct H5 as [B [H5 [H6 [a H7]]]].
         rewrite <- H7 in H6.
         inversion H3; subst. 
         apply H8 in H6. 
         apply IHn' in H6; auto.
         destruct H6 as [B0 [H9 H10]].
         exists (B × (pad1 B0 C1)). 
         split. 
         apply otI_Mmult; auto. 
         apply otI_pad1; auto. 
         all : try apply C1_neq_C0.  
         rewrite <- Mmult_assoc, <- H7.          
         rewrite <- pad1_mult, H10, Cmult_1_l, pad1_I; easy.
         apply (WF_pad1 a C1). 
         rewrite H7; auto with wf_db. 
Qed.


Corollary lin_ind_implies_invertible_r : forall {n} (A : Square n),
  WF_Matrix A ->
  linearly_independent A -> 
  (exists B, op_to_I B /\ A × B = I n).
Proof. intros. 
       apply (invr_P_implies_invertible_r _ (@linearly_independent));
         auto with invr_db.
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
       { rewrite H3. apply Mmult_1_l; auto with wf_db. }
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


Corollary lin_indep_invertible : forall (n : nat) (A : Square n),
  WF_Matrix A -> (linearly_independent A <-> invertible A).
Proof. intros; split.
       - intros. 
         assert (H1 := H).
         apply lin_ind_implies_invertible_r in H; try easy.
         destruct H as [B [H H2]].
         unfold invertible.
         exists B. unfold Minv.
         split; try easy.
         apply Minv_flip in H2; auto with wf_db. 
       - intros. 
         destruct H0 as [B [H1 H2]].
         apply invertible_l_implies_linind in H2.
         easy.
Qed.

Lemma Minv_otI_l : forall (n : nat) (A B : Square n),
  WF_Matrix A -> WF_Matrix B -> 
  Minv A B ->
  op_to_I A.
Proof. intros.           
       assert (H2 := lin_indep_invertible).
       assert (H3 : invertible B).
       { exists A. apply Minv_symm; easy. }
       apply H2 in H3; auto. 
       apply lin_ind_implies_invertible_r in H3; auto. 
       destruct H3 as [B' [H3 H4]].
       apply Minv_left in H4; auto with wf_db.
       apply Minv_symm in H1.
       apply (Minv_unique _ B A B') in H4; auto with wf_db; subst.
       easy. 
Qed.


(*********************************************)
(* We finish proving lemmas about invarients *)
(*********************************************)

(* Finally, we show that if all 6 nice properties are true about two (Mat -> Prop)s, then
   they are equivalent on well formed matrices *)
Theorem invr_P_equiv_otI : forall {n} (A : Square n) (P : forall m o, Matrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> P n n (I n) -> 
  WF_Matrix A -> 
  (P n n A <-> op_to_I A).  
Proof. intros. split. 
       - intros. 
         apply invr_P_implies_invertible_r in H6; auto. 
         destruct H6 as [B [H6 H7]]. 
         apply (Minv_otI_l _ A B); auto with wf_db.
         apply Minv_left; auto with wf_db.
       - intros. 
         apply op_to_I_ind; auto; intros.  
         + inversion H; subst. 
           apply H11; easy. 
         + inversion H0; subst. 
           apply H11; easy. 
         + inversion H1; subst. 
           apply H12; easy.
Qed.

Corollary lin_indep_det_neq_0 : forall {n} (A : Square n),
  WF_Matrix A -> (linearly_independent A <-> det_neq_0 A).
Proof. intros. split.  
       - intros. 
         apply invr_P_equiv_otI in H0; auto with invr_db.      
         apply invr_P_equiv_otI; auto with invr_db.
         split; auto. 
         rewrite Det_I; apply C1_neq_C0.
         unfold linearly_independent; intros. 
         rewrite Mmult_1_l in H3; auto. 
       - intros. 
         apply invr_P_equiv_otI in H0; auto with invr_db.    
         apply invr_P_equiv_otI; auto with invr_db.
         unfold linearly_independent; intros. 
         rewrite Mmult_1_l in H2; auto. 
         split; auto. 
         rewrite Det_I; apply C1_neq_C0.
Qed.

Corollary lin_dep_det_eq_0 : forall {n} (A : Square n), 
  WF_Matrix A -> (linearly_dependent A <-> det_eq_c C0 A).
Proof. induction n as [| n'].
       - intros. split; intros.
         destruct H0 as [v [H0 [H1 H2]]]. 
         assert (H' : v = Zero).
         { apply mat_equiv_eq; auto with wf_db. 
           unfold mat_equiv; easy. }
         easy.          
         destruct H0.
         unfold Determinant in H1.
         assert (H2 := C1_neq_C0).
         easy.
       - intros.
         split; intros.  
         + split; try easy. 
           apply lindep_implies_not_linindep in H0.
           assert (H' : ~  (det_neq_0 A)).
           unfold not; intros; apply H0.
           apply lin_indep_det_neq_0; auto. 
           unfold not in H'. 
           destruct (Ceq_dec (Determinant A) C0); try easy. 
           assert (H'' : False). apply H'.
           split; easy. 
           easy. 
         + apply (mat_prop_reduce_pzt_P0 _ _ (@linearly_dependent)) in H0; 
             auto with invr_db.
           destruct H0; try easy. 
           destruct H0 as [B [H0 [H1 [a H2]]]]. 
           assert (H' : linearly_dependent a).
           { apply IHn'. 
             apply <- (@WF_pad1 n' n' a C1). 
             rewrite H2; auto with wf_db. 
             apply_mat_prop det_0_pad1_invr.           
             apply (H4 n' n' a C1).
             apply C1_neq_C0.
             rewrite H2; easy. }
           unfold linearly_dependent in *.
           destruct H' as [v [H3 [H4 H5]]].
           exists (B × (row_wedge v Zero 0)); split.
           apply WF_mult; auto with wf_db.
           apply WF_row_wedge; try lia; auto with wf_db. split.  
           unfold not; intros; apply H4.
           assert (H7 := H0); apply otI_lin_indep in H7.
           apply lin_indep_invertible in H7; auto with wf_db.
           destruct H7 as [B0 H7].
           assert (H8 : B0 × (B × row_wedge v Zero 0) = Zero). { rewrite H6, Mmult_0_r; easy. } 
           destruct H7. 
           rewrite <- Mmult_assoc, H9, Mmult_1_l in H8. 
           prep_matrix_equality. 
           assert (H' : row_wedge v Zero 0 (S x) y = C0). { rewrite H8; easy. }
           unfold Zero; rewrite <- H'.
           unfold row_wedge; bdestruct_all.  
           rewrite easy_sub; easy. 
           apply WF_row_wedge; try lia;  auto with wf_db.
           rewrite <- Mmult_assoc, <- H2.
           rewrite pad1_row_wedge_mult, H5.
           prep_matrix_equality.
           unfold row_wedge. 
           bdestruct_all; easy. 
Qed.


Corollary lin_dep_indep_dec : forall {n} (A : Square n),
  WF_Matrix A -> { linearly_independent A } + { linearly_dependent A }. 
Proof. intros. 
       destruct (Ceq_dec (Determinant A) C0).
       - right. 
         apply lin_dep_det_eq_0; auto. 
         split; easy. 
       - left. 
         apply lin_indep_det_neq_0; auto.
         split; easy. 
Qed.

(*************************************************************************************)
(* we define another set of invariants to help show that Det A × Det B = Det (A × B) *)
(*************************************************************************************)

Definition Det_mult_comm_l (n m : nat) (A : Matrix n m) :=
  n = m /\ (forall (B : Square n), (Determinant B) * (@Determinant n A) = (@Determinant n (B × A)))%C.


Lemma Dmc_I : forall {n}, Det_mult_comm_l n n (I n).
Proof. intros. 
       unfold Det_mult_comm_l; split; auto.
       intros. 
       rewrite Det_I, Det_make_WF, (Det_make_WF _ (B × I n)).
       rewrite <- Mmult_make_WF.
       rewrite <- (eq_make_WF (I n)); auto with wf_db.
       rewrite Mmult_1_r; auto with wf_db.
       lca. 
Qed.

Lemma Dmc_make_WF : forall {n} (A : Square n),
  Det_mult_comm_l n n (make_WF A) <-> Det_mult_comm_l n n A.
Proof. intros; split; intros. 
       - destruct H; subst. 
         split; auto; intros. 
         rewrite (Det_make_WF _ A), H0.
         rewrite <- Det_Mmult_make_WF_r; easy. 
       - destruct H; subst. 
         split; auto; intros. 
         rewrite <- Det_make_WF.
         rewrite <- Det_Mmult_make_WF_r; easy. 
Qed.

Lemma Dmc_Mmult : forall {n} (A B : Square n),
  Det_mult_comm_l n n A -> Det_mult_comm_l n n B -> 
  Det_mult_comm_l n n (A × B).
Proof. intros. 
       destruct H; destruct H0; subst. 
       split; auto. 
       intros. 
       rewrite <- H2, Cmult_assoc, H1, H2, Mmult_assoc; easy.
Qed.


Lemma Dmc_swap_I : forall (n x y : nat),
  x < n -> y < n -> 
  Det_mult_comm_l n n (row_swap (I n) x y).
Proof. intros.  
       bdestruct (x =? y); subst. 
       - rewrite row_swap_same. 
         apply Dmc_I.
       - split; auto; intros. 
         rewrite Det_Mmult_make_WF_l. 
         rewrite <- col_swap_mult_r; auto with wf_db.
         rewrite <- col_row_swap_invr_I; auto.
         rewrite Determinant_swap, Det_I, Determinant_swap; auto.
         rewrite Det_make_WF; lca. 
Qed.

Lemma Dmc_scale_I : forall (n x : nat) (c : C),
  Det_mult_comm_l n n (row_scale (I n) x c).
Proof. intros.  
       split; auto; intros. 
       rewrite Det_Mmult_make_WF_l. 
       rewrite <- col_scale_mult_r; auto with wf_db.
       rewrite <- col_row_scale_invr_I; auto.
       bdestruct (x <? n).
       - rewrite Determinant_scale, Det_I, Determinant_scale; auto.
         rewrite Det_make_WF; lca. 
       - assert (H' : (col_scale (I n) x c) = I n).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv, col_scale, I; intros. 
           bdestruct_all; easy. }
         assert (H'' : (col_scale (make_WF B) x c) = make_WF B).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv, col_scale, I; intros. 
           bdestruct_all; easy. }
         rewrite H', H''.
         rewrite Det_make_WF, Det_I; lca. 
Qed. 

Lemma Dmc_add_I : forall (n x y : nat) (c : C),
  x <> y -> x < n -> y < n -> Det_mult_comm_l n n (row_add (I n) x y c).
Proof. intros.  
       split; auto; intros. 
       rewrite Det_Mmult_make_WF_l. 
       rewrite <- col_add_mult_r; auto with wf_db.
       rewrite <- col_row_add_invr_I; auto.
       rewrite Determinant_col_add, Det_I, Determinant_col_add; auto.
       rewrite Det_make_WF; lca. 
Qed.

(* proving Dmc invariants *)
Lemma Dmc_swap_invr : invr_col_swap (Det_mult_comm_l).
Proof. apply invr_swap; intros.   
       bdestruct (x =? y); subst.
       - rewrite col_swap_same; easy.
       - bdestruct (n =? m); subst; try (destruct H1; easy).
         apply Dmc_make_WF.       
         rewrite <- col_swap_make_WF; auto.
         rewrite col_swap_mult_r; auto with wf_db. 
         apply Dmc_Mmult.
         apply Dmc_make_WF; easy.
         apply Dmc_swap_I; auto. 
Qed.

Lemma Dmc_scale_invr : invr_col_scale (Det_mult_comm_l).
Proof. apply invr_scale; intros.   
       bdestruct (n =? m); subst; try (destruct H0; easy).
       apply Dmc_make_WF.       
       rewrite <- col_scale_make_WF; auto.
       rewrite col_scale_mult_r; auto with wf_db. 
       apply Dmc_Mmult.
       apply Dmc_make_WF; easy.
       apply Dmc_scale_I; auto. 
Qed.

Lemma Dmc_add_invr : invr_col_add (Det_mult_comm_l).
Proof. apply invr_add; intros.   
       bdestruct (n =? m); subst; try (destruct H2; easy).
       apply Dmc_make_WF.       
       rewrite <- col_add_make_WF; auto.
       rewrite col_add_mult_r; auto with wf_db. 
       apply Dmc_Mmult.
       apply Dmc_make_WF; easy.
       apply Dmc_add_I; auto. 
Qed.

Local Close Scope nat_scope.

Lemma otI_Dmc : forall {n} (A : Square n),
  op_to_I A -> Det_mult_comm_l n n A.
Proof. intros. 
       apply op_to_I_ind; auto. 
       - apply Dmc_I.
       - intros. 
         apply_mat_prop Dmc_swap_invr.
         apply H5; easy. 
       - intros. 
         apply_mat_prop Dmc_scale_invr.
         apply H5; easy. 
       - intros. 
         apply_mat_prop Dmc_add_invr.
         apply H6; easy. 
Qed. 


Lemma Determinant_multiplicative_WF : forall {n} (A B : Square n), 
  WF_Matrix A -> WF_Matrix B -> 
  (Determinant A) * (Determinant B) = Determinant (A × B).
Proof. intros. 
       destruct (lin_dep_indep_dec B); auto. 
       - apply invr_P_equiv_otI in l; auto with invr_db. 
         apply otI_Dmc in l; destruct l. 
         apply H2. 
         unfold linearly_independent; intros. 
         rewrite <- H3, Mmult_1_l; easy. 
       - assert (H' : linearly_dependent (A × B)).
         { apply lin_dep_mult_r; easy. }
         apply lin_dep_det_eq_0 in l; 
         apply lin_dep_det_eq_0 in H'; auto with wf_db. 
         destruct l; destruct H'. 
         rewrite H2, H4; lca. 
Qed.


Theorem Determinant_multiplicative : forall {n} (A B : Square n), 
  (Determinant A) * (Determinant B) = Determinant (A × B).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ B), Determinant_multiplicative_WF;
         auto with wf_db. 
       rewrite <- Det_Mmult_make_WF_l, <- Det_Mmult_make_WF_r; easy. 
Qed.

