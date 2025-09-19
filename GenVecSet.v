

(** In this file, we define more advanced linear algebra concepts such as bases, linear independence, etc... *)


Require Import Psatz.  
Require Import Reals.

Require Export GenRowColOps.


Local Open Scope nat_scope.


                    
Module VecSetOverField
  (FM : FieldModule).

Include RowColOpsOverField FM.


(***************************************************************************)
(** * Defining properties which are invarient under column operations, etc... *)
(***************************************************************************)

Inductive invr_col_swap : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| invr_swap : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
    (forall (n m x y : nat) (T : GenMatrix n m), x < m -> y < m -> P n m T -> P n m (col_swap T x y)) 
    -> invr_col_swap P.

Inductive invr_col_scale : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| invr_scale : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
    (forall (n m x : nat) (T : GenMatrix n m) (c : F), c <> 0%G -> P n m T -> P n m (col_scale T x c)) 
    -> invr_col_scale P.

Inductive invr_col_add : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| invr_add : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
    (forall (n m x y : nat) (T : GenMatrix n m) (c : F), 
        x <> y -> x < m -> y < m -> P n m T -> P n m (col_add T x y c)) 
    -> invr_col_add P.

Inductive invr_col_add_many : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| invr_add_many : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
    (forall (n m col : nat) (T : GenMatrix n m) (as' : GenVector m), 
        col < m -> as' col 0 = 0%G -> P n m T -> P n m (col_add_many T as' col)) 
    -> invr_col_add_many P.

Inductive invr_col_add_each : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| invr_add_each : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
    (forall (n m col : nat) (T : GenMatrix n m) (as' : GenMatrix 1 m), 
        col < m -> WF_GenMatrix as' -> P n m T -> P n m (col_add_each T (make_col_val as' col 0%G) col)) 
    -> invr_col_add_each P.

Inductive invr_pad1 : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| invr_p : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
    (forall (n m : nat) (T : GenMatrix n m) (c : F), c <> 0%G -> P (S n) (S m) (pad1 T c) -> P n m T) 
    -> invr_pad1 P.

Inductive prop_zero_true : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| PZT : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
  (forall (n m : nat) (T : GenMatrix n m), (exists i, i < m /\ get_col T i = Zero) -> P n m T) ->
  prop_zero_true P.

Inductive prop_zero_false : (forall n m : nat, GenMatrix n m -> Prop) -> Prop :=
| PZF : forall (P : (forall n m : nat, GenMatrix n m -> Prop)), 
  (forall (n m : nat) (T : GenMatrix n m), (exists i, i < m /\ get_col T i = Zero) -> ~ (P n m T)) ->
  prop_zero_false P.

(* Ltac to help apply these properties of (Mat -> Prop)s *)
Ltac apply_mat_prop tac := 
  let H := fresh "H" in 
  assert (H := tac); inversion H; subst; try apply H. 

Lemma mat_prop_col_add_many_some : forall (e n m col : nat) (P : forall n m : nat, GenMatrix n m -> Prop)
                                     (T : GenMatrix n m) (as' : GenVector m),
  (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = 0%G) -> as' col 0 = 0%G ->
  invr_col_add P ->
  P n m T -> P n m (col_add_many T as' col).
Proof. induction e as [| e].
       - intros. 
         inversion H3; subst. 
         rewrite (col_add_many_col_add _ _ _ (skip_count col 0)); 
           try lia; try easy.  
         apply H5; try lia.
         apply skip_count_not_skip.
         assert (H' : (col_add_many T (make_row_val as' (skip_count col O) 0%G) col) = T).
         { prep_genmatrix_equality. 
           unfold col_add_many, make_row_val, skip_count, gen_new_col, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Gplus_0_l.
           rewrite Gplus_comm.
           f_equal; try easy.
           rewrite Msum_Fsum.
           apply (@big_sum_0_bounded F R0); intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); simpl; try ring. 
           destruct x0; try rewrite H2; try rewrite H1; simpl; try ring; try lia. 
           destruct x0; simpl; try ring; rewrite H1; try ring; lia. }
         rewrite H'; easy.
         apply skip_count_not_skip.
       - intros. 
         inversion H3; subst. 
         rewrite (col_add_many_col_add _ _ _ (skip_count col (S e))); 
           try lia; try easy.
         apply H5; try lia.
         apply skip_count_not_skip.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_row_val in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H1; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H9, H11. apply H2.
         apply H1; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H1; lia. 
         unfold make_row_val, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         apply skip_count_not_skip.
Qed.


Lemma invr_col_add_col_add_many : forall (P : forall n m : nat, GenMatrix n m -> Prop),
  invr_col_add P -> invr_col_add_many P.
Proof. intros. 
       inversion H; subst. 
       apply invr_add_many; intros. 
       destruct m; try lia. 
       destruct m.
       - assert (H' : as' == Zero).
         { unfold genmat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ (make_WF as'));
           try apply genmat_equiv_make_WF.
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

Lemma mat_prop_col_add_each_some : forall (e n m col : nat) (P : forall n m : nat, GenMatrix n m -> Prop)
                                     (as' : GenMatrix 1 m) (T : GenMatrix n m),
  WF_GenMatrix as' -> (skip_count col e) < m -> col < m -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = 0%G) -> as' 0 col = 0%G ->
  invr_col_add P -> 
  P n m T -> P n m (col_add_each T as' col).
Proof. induction e as [| e].
       - intros.
         inversion H4; subst.
         rewrite (col_add_each_col_add _ _ _ (skip_count col 0)); try lia. 
         apply H6; try lia.
         assert (H' := skip_count_not_skip col 0). auto.
         assert (H' : (make_col_val as' (skip_count col 0) 0%G) = Zero).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv; intros. 
           unfold make_col_val, skip_count in *.
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
         rewrite (col_add_each_col_add _ _ _ (skip_count col (S e))); try lia. 
         apply H6; try lia.
         assert (H' := skip_count_not_skip col (S e)). auto.
         apply IHe; try lia; try easy; auto with wf_db. 
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_col_val in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H2; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H10, H12. apply H3.
         apply H2; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H2; lia. 
         unfold make_col_val, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         assert (H' := skip_count_not_skip col (S e)). auto.
         intros. destruct x; try easy.
         apply H; lia.
Qed.
              
Lemma invr_col_add_col_add_each : forall (P : forall n m : nat, GenMatrix n m -> Prop),
  invr_col_add P -> invr_col_add_each P.
Proof. intros.  
       inversion H; subst. 
       apply invr_add_each; intros. 
       destruct m; try lia. 
       destruct m.
       - assert (H' : make_col_val as' col 0%G = Zero).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           unfold make_col_val. 
           easy. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
       - bdestruct (col =? S m).
         + apply (mat_prop_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count. bdestruct (m <? col); lia. 
           intros. 
           unfold make_col_val. 
           bdestruct (i =? col); try lia; try easy.
           rewrite H4 in H5; unfold skip_count in H5.
           bdestruct (m <? S m); try lia. 
           rewrite H2; try lia; easy.
           unfold make_col_val. 
           bdestruct (col =? col); try lia; easy.
         + apply (mat_prop_col_add_each_some m); try lia; try easy; auto with wf_db.
           unfold skip_count.
           bdestruct (m <? col); try lia. 
           intros. unfold make_col_val. 
           bdestruct (i =? col); try lia; try easy.
           unfold skip_count in H5.
           bdestruct (m <? col); try lia. 
           apply H2; lia. 
           unfold make_col_val. 
           bdestruct (col =? col); try lia; easy.
Qed.

Lemma mat_prop_col_swap_conv : forall {n m} (P : forall n m : nat, GenMatrix n m -> Prop) (T : GenMatrix n m) (x y : nat),
  invr_col_swap P -> 
  x < m -> y < m -> 
  P n m (col_swap T x y) -> P n m T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_swap_inv T x y).
       apply H3; easy.
Qed.

Lemma mat_prop_col_scale_conv : forall {n m} (P : forall n m : nat, GenMatrix n m -> Prop) 
                                  (T : GenMatrix n m) (x : nat) (c : F),
  invr_col_scale P ->
  c <> 0%G ->
  P n m (col_scale T x c) -> P n m T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_scale_inv T x c); try easy.
       apply H2; try apply nonzero_div_nonzero; easy.
Qed.

Lemma mat_prop_col_add_conv : forall {n m} (P : forall n m : nat, GenMatrix n m -> Prop)  
                                (T : GenMatrix n m) (x y : nat) (c : F),
  invr_col_add P ->
  x <> y -> x < m -> y < m -> 
  P n m (col_add T x y c) -> P n m T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_add_inv T x y c); try easy. 
       apply H4; try easy. 
Qed.

Lemma mat_prop_col_add_many_conv : forall {n m} (P : forall n m : nat, GenMatrix n m -> Prop) 
                                     (T : GenMatrix n m) (col : nat) (as' : GenVector m),
  invr_col_add P ->
  col < m -> as' col 0 = 0%G -> 
  P n m (col_add_many T as' col) -> P n m T.
Proof. intros. 
       apply invr_col_add_col_add_many in H.
       inversion H; subst. 
       rewrite (col_add_many_inv T as' col); try easy.
       apply H3; try easy. 
       unfold scale; rewrite H1.
       ring. 
Qed.

Lemma mat_prop_col_add_each_conv : forall {n m} (P : forall n m : nat, GenMatrix n m -> Prop) 
                                     (T : GenMatrix n m) (col : nat) (as' : GenMatrix 1 m),
  invr_col_add P ->
  col < m -> WF_GenMatrix as' -> 
  P n m (col_add_each T (make_col_val as' col 0%G) col) -> P n m T.
Proof. intros. 
       apply invr_col_add_col_add_each in H.
       inversion H; subst. 
       rewrite (col_add_each_inv _ as' col); try easy.
       apply H3; try easy.
       auto with wf_db.
Qed.



(** * We can now define some invariants for Determinant *)
Definition det_neq_0 {n m : nat} (A : GenMatrix n m) : Prop :=
  n = m /\ @Determinant n A <> 0%G.

Definition det_eq_c (c : F) {n m : nat} (A : GenMatrix n m) : Prop :=
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
         rewrite <- (Gmult_1_l (Determinant T)).
         replace 1%G with ((- 1%G) * (- 1%G))%G by ring. 
         rewrite <- Gmult_assoc, H3. 
         ring. 
Qed.

Lemma det_neq_0_scale_invr : invr_col_scale (@det_neq_0).
Proof. apply invr_scale; intros.  
       destruct H0; subst. 
       split; auto.
       bdestruct (x <? m).
       - rewrite Determinant_col_scale; auto. 
         apply Gmult_neq_0; easy. 
       - rewrite Det_make_WF in *. 
         assert (H' : (make_WF T) = (make_WF (col_scale T x c))).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, make_WF, col_scale; intros. 
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
       - apply G1_neq_0. 
       - unfold not; intros; apply H1.
         rewrite Det_simplify. 
         apply (@big_sum_0_bounded F R0); intros. 
         destruct x. 
         + rewrite <- get_minor_pad1, H0; ring. 
         + unfold pad1, col_wedge, row_wedge, e_i, scale.
           bdestruct_all; simpl. 
           ring. contradiction.
Qed.

Lemma det_neq_0_pzf : prop_zero_false (@det_neq_0).  
Proof. apply PZF; intros.
       unfold not; intros. 
       destruct H0; subst. 
       destruct H as [i [H H0]].
       apply H1.
       rewrite (col_0_Det_0 T i);
       easy. 
Qed.

Lemma det_0_swap_invr : invr_col_swap (@det_eq_c 0%G).
Proof. apply invr_swap; intros.  
       unfold det_eq_c in *; destruct H1; subst. 
       split; auto.
       bdestruct (x =? y); subst. 
       - rewrite col_swap_same.
         easy. 
       - rewrite Determinant_swap; auto. 
         rewrite H2; ring. 
Qed.

Lemma det_0_scale_invr : invr_col_scale (@det_eq_c 0%G).
Proof. apply invr_scale; intros. 
       unfold det_eq_c in *; destruct H0; subst. 
       split; auto.
       bdestruct (x <? m).
       - rewrite Determinant_col_scale; auto. 
         rewrite H1; ring. 
       - rewrite Det_make_WF in *. 
         assert (H' : (make_WF T) = (make_WF (col_scale T x c))).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, make_WF, col_scale; intros. 
           bdestruct_all; easy. }
         rewrite <- H'; easy. 
Qed.

Lemma det_c_add_invr : forall (c : F), invr_col_add (@det_eq_c c).
Proof. intros. 
       apply invr_add; intros.  
       unfold det_eq_c in *; destruct H2; subst. 
       split; auto. 
       apply Determinant_col_add; easy.
Qed.

Lemma det_0_pad1_invr : invr_pad1 (@det_eq_c 0%G).
Proof. apply invr_p; intros. 
       destruct H0; apply eq_add_S in H0; subst. 
       split; auto. 
       destruct m. 
       - simpl in H1.         
         unfold pad1, col_wedge, row_wedge, e_i, scale in H1; 
         simpl in H1. 
         rewrite Gmult_1_r in H1. 
         easy.
       - rewrite Det_simplify in H1. 
         assert (H' : (c * Determinant (get_minor (pad1 T c) 0 0) = 0%G)%G).
         { rewrite <- H1, (big_sum_unique (c * Determinant (get_minor (pad1 T c) 0 0))%G).  
           easy. 
           exists 0. split; try lia. 
           split. simpl parity. 
           f_equal; try easy.  
           unfold pad1, col_wedge, row_wedge, e_i, scale. 
           bdestruct_all; simpl; unfold Zero; 
           try ring. contradiction.
           intros. 
           unfold pad1, col_wedge, row_wedge, e_i, scale. 
           bdestruct_all; simpl; try ring.
           contradiction. }
         rewrite <- get_minor_pad1 in H'.
         destruct (Geq_dec (Determinant T) 0%G); try easy. 
         apply (Gmult_neq_0 c _) in n; easy. 
Qed.

#[export] Hint Resolve det_neq_0_swap_invr det_neq_0_scale_invr det_neq_0_add_invr det_neq_0_pad1_invr : invr_db.
#[export] Hint Resolve det_neq_0_pzf det_0_swap_invr det_0_scale_invr det_c_add_invr det_0_pad1_invr : invr_db.


Lemma Determinant_col_add_many : forall (n col : nat) (A : GenSquare n) (as' : GenVector n),
  col < n -> as' col 0 = 0%G -> 
  Determinant A = Determinant (col_add_many A as' col).
Proof. intros.
       assert (H' := det_c_add_invr (Determinant A)).
       apply invr_col_add_col_add_many in H'. 
       inversion H'; subst. 
       apply (H1 n n col A as') in H; try easy.
       unfold det_eq_c in *.
       destruct H; easy. 
Qed.


Lemma Determinant_col_add_each : forall (n col : nat) (as' : GenMatrix 1 n) 
                                          (A : GenSquare n),
  col < n -> WF_GenMatrix as' -> as' 0 col = 0%G ->
  Determinant A = Determinant (col_add_each A as' col).
Proof. intros. 
       assert (H' := det_c_add_invr (Determinant A)).
       apply invr_col_add_col_add_each in H'. 
       inversion H'; subst. 
       assert (H4 : (make_col_val as' col 0%G) = as').
       { apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold make_col_val.
         destruct i; try lia.
         bdestruct_all; subst; easy. }
       apply (H2 n n col A as') in H; try easy.
       unfold det_eq_c in *.
       destruct H; rewrite <- H3.
       rewrite H4; easy.
Qed.


(***********************************************************)
(** * Defining linear independence, and proving lemmas etc... *)
(***********************************************************)


Definition linearly_independent {n m} (T : GenMatrix n m) : Prop :=
  forall (a : GenVector m), WF_GenMatrix a -> @GMmult n m 1 T a = Zero -> a = Zero.

Definition linearly_dependent {n m} (T : GenMatrix n m) : Prop :=
  exists (a : GenVector m), WF_GenMatrix a /\ a <> Zero /\ @GMmult n m 1 T a = Zero.

Lemma lindep_implies_not_linindep : forall {n m} (T : GenMatrix n m),
  linearly_dependent T -> ~ (linearly_independent T).
Proof. unfold not, linearly_dependent, linearly_independent in *.
       intros. 
       destruct H as [a [H1 [H2 H3]]].
       apply H0 in H1; easy.
Qed.

Lemma not_lindep_implies_linindep : forall {n m} (T : GenMatrix n m),
  not (linearly_dependent T) -> linearly_independent T.
Proof. unfold not, linearly_dependent, linearly_independent in *.
       intros. 
       destruct (vec_equiv_dec a Zero). 
       - apply genmat_equiv_eq; auto with wf_db.
       - assert (H2 : (exists a : GenVector m, WF_GenMatrix a /\ a <> Zero /\ T × a = Zero)).
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

Lemma lin_indep_vec : forall {n} (v : GenVector n), 
  WF_GenMatrix v -> v <> Zero -> linearly_independent v.
Proof. intros. 
       unfold linearly_independent.
       intros. 
       assert (H' : v × a = (a 0 0) .* v).
       { apply genmat_equiv_eq; auto with wf_db.
         unfold GMmult, scale, genmat_equiv. 
         intros. simpl. 
         destruct j; try lia; ring. }
       assert (H1' := H).
       apply nonzero_vec_nonzero_elem in H1'; try easy.
       destruct H1' as [x H1'].
       destruct (Geq_dec (a 0 0) 0%G).
       + prep_genmatrix_equality. 
         destruct x0. destruct y.
         rewrite e; easy.
         all : apply H1; lia.
       + assert (H'' : ((a 0 0) .* v) x 0 = 0%G).
         { rewrite <- H'. rewrite H2; easy. }
         unfold scale in H''. 
         assert (H3 : (a 0 0 * v x 0)%G <> 0%G).
         { apply Gmult_neq_0; easy. }
         easy. 
Qed.

Lemma invertible_l_implies_linind : forall {n} (A B : GenSquare n),
  A × B = I n -> linearly_independent B.
Proof. intros.
       unfold linearly_independent. intros.
       rewrite <- (GMmult_1_l _ _ a); try easy.
       rewrite <- H.
       rewrite GMmult_assoc, H1.
       rewrite GMmult_0_r.
       reflexivity.
Qed.

Lemma lin_indep_col_reduce : forall {m n} (A : GenMatrix m (S n)) (i : nat),
  i <= n -> 
  linearly_independent A -> 
  linearly_independent (reduce_col A i).
Proof. intros. 
       unfold linearly_independent in *. 
       intros. 
       apply (row_wedge_zero _ i). 
       apply H0.
       apply WF_row_wedge; try easy.
       prep_genmatrix_equality.
       rewrite <- H2.
       unfold GMmult, row_wedge, Zero.
       replace n with (i + (n - i))%nat by lia.
       replace (S (i + (n - i)))%nat with (i + 1 + (n - i))%nat by lia.
       do 3 rewrite big_sum_sum; simpl.
       bdestruct_all; simpl. 
       rewrite Gmult_0_r, 2 Gplus_0_r.
       apply f_equal_gen; try apply f_equal.
       all : apply big_sum_eq_bounded; intros.
       all : unfold reduce_col.
       all : bdestruct_all; try easy.
       repeat (apply f_equal_gen; try lia). 
       all : easy.
Qed.

(* more general than lin_indep_col_reduce_n *)
Lemma lin_indep_smash : forall {m n2 n1} (A1 : GenMatrix m n1) (A2 : GenMatrix m n2),
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
         bdestruct (x0 <? n1); try lia; easy.
       - intros.  
         assert (H1 := @lin_indep_col_reduce m (n1 + n2') (smash A1 A2) (n1 + n2')). 
         rewrite <- plus_n_Sm in H.
         apply H1 in H; auto.
         rewrite smash_reduce in H.
         apply (IHn2' n1 A1 (reduce_col A2 n2')).
         easy.
Qed.

Lemma lin_dep_mult_r : forall {n m o} (A : GenMatrix n m) (B : GenMatrix m o),
  linearly_dependent B -> linearly_dependent (A × B).
Proof. intros. 
       unfold linearly_dependent in *.
       destruct H as [a [H [H0 H1]]].
       exists a. 
       repeat split; auto.  
       rewrite GMmult_assoc, H1, GMmult_0_r; easy. 
Qed.      

Lemma lin_dep_col_wedge : forall {m n} (A : GenMatrix m n) (v : GenVector m) (i : nat),
  i <= n -> 
  linearly_dependent A -> 
  linearly_dependent (col_wedge A v i).
Proof. intros. 
       unfold linearly_dependent in *. 
       destruct H0 as [a [H0 [H2 H3]]].
       exists (row_wedge a Zero i). 
       split; auto with wf_db. 
       split. unfold not; intros; apply H2.
       apply (row_wedge_zero _ i).
       auto.
       rewrite wedge_mul; auto.
Qed.


(* proving invr properties for linearly_independent *)
Lemma lin_indep_swap_invr : invr_col_swap (@linearly_independent). 
Proof. apply invr_swap; intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite (row_swap_inv a x y) in H3.
       rewrite <- (swap_preserves_mul T (row_swap a x y) x y) in H3; try easy.
       apply H1 in H3.
       rewrite (row_swap_inv a x y).
       rewrite H3.
       prep_genmatrix_equality.
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
       prep_genmatrix_equality. 
       unfold row_scale.
       bdestruct (x0 =? x); simpl; unfold Zero;
       try ring. 
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
       prep_genmatrix_equality. 
       unfold row_add.
       bdestruct (x0 =? y); simpl; unfold Zero;
       ring. 
       apply WF_row_add; easy.
Qed.

Lemma lin_indep_pad1_invr : invr_pad1 (@linearly_independent).  
Proof. apply invr_p; intros. 
       unfold linearly_independent in *.
       intros. 
       assert (H3 : @GMmult (S n) (S m) 1 (pad1 T c) (row_wedge a Zero 0) = Zero).
       { prep_genmatrix_equality. 
         destruct x. unfold GMmult. 
         unfold Zero. apply (@big_sum_0_bounded F R0). 
         intros.
         unfold pad1, row_wedge, col_wedge, e_i, scale.
         bdestruct (x <? 0); bdestruct (x =? 0); try lia. ring.
         simpl. unfold Zero.
         ring.
         assert (p : @Zero (S n) 1 (S x) y = 0%G).
         easy.
         assert (H2' : (T × a) x y = 0%G). 
         rewrite H2; easy.
         rewrite p. 
         rewrite <- H2'.
         unfold GMmult. rewrite <- big_sum_extend_l.  
         rewrite <- Gplus_0_l.
         f_equal.
         unfold pad1, row_wedge, col_wedge, e_i.
         bdestruct (x <? 0); bdestruct (x =? 0); try lia. 
         rewrite H4; simpl. unfold Zero. ring. 
         rewrite Sn_minus_1. unfold Zero. simpl.
         ring. 
         apply big_sum_eq_bounded; intros. 
         rewrite pad1_conv.
         unfold row_wedge.
         rewrite Sn_minus_1. 
         easy. }
       apply H0 in H3.
       prep_genmatrix_equality. 
       assert (H4 : row_wedge a Zero 0 (S x) y = 0%G).
       rewrite H3; easy.
       unfold Zero. rewrite <- H4.
       unfold row_wedge. 
       rewrite Sn_minus_1.
       easy.
       apply WF_row_wedge; try lia; easy.
Qed.   

Lemma lin_indep_pzf : prop_zero_false (@linearly_independent).
Proof. apply PZF; intros. 
       unfold not; intros. 
       unfold linearly_independent in *.  
       destruct H as [i [H H1]].
       assert (H2 : T × @e_i m i = Zero).
       { prep_genmatrix_equality.
         unfold GMmult, Zero, e_i; simpl.  
         apply (@big_sum_0_bounded F R0); intros. 
         bdestruct_all; try ring; 
         rewrite <- get_col_conv; subst;
         try rewrite H1; unfold Zero; simpl; 
         try ring. }
       apply H0 in H2; auto with wf_db.
       assert (H3 : @e_i m i i 0 = 0%G).
       rewrite H2; easy.
       unfold e_i in H3.
       apply G1_neq_0.
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
       prep_genmatrix_equality. 
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
          prep_genmatrix_equality. 
          unfold row_scale, Zero. 
          bdestruct (x0 =? x); try lia; ring. 
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
       prep_genmatrix_equality.
       bdestruct (x0 =? y); ring. 
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
       assert (H' : (@e_i m i) i 0 = 0%G).
       { rewrite H; easy. }
       unfold e_i in H'; simpl in H'.
       bdestruct (i =? i); bdestruct (i <? m); try lia. 
       simpl in H'.
       apply G1_neq_0.
       easy.
       rewrite <- matrix_by_basis; easy.
Qed.

#[export] Hint Resolve lin_indep_swap_invr lin_indep_scale_invr lin_indep_add_invr lin_indep_pad1_invr : invr_db.
#[export] Hint Resolve lin_indep_pzf lin_dep_swap_invr lin_dep_scale_invr lin_dep_add_invr lin_dep_pzt : invr_db.


(** we begin to prove that if n < m, then any GenMatrix n m is linearly_dependent. This is quite useful, as we get a vector that can be used to cancel a column *)

Lemma lin_dep_gen_elem : forall {m n} (T : GenMatrix n (S m)),
  WF_GenMatrix T -> linearly_dependent T -> 
  (exists i, i < (S m) /\ 
             (exists v : GenVector m, WF_GenMatrix v /\ 
                 @GMmult n m 1 (reduce_col T i) v = (-1%G) .* (get_col T i))). 
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
         apply genmat_equiv_eq; auto with wf_db.
         rewrite Mscale_mult_dist_r.  
         unfold genmat_equiv; intros. 
         unfold GMmult, scale.
         assert (H' : (big_sum (fun y : nat => reduce_col T x i y * reduce_row a x y j) m +
                       (a x 0) * get_col T x i j = @Zero n 1 i j)%G).
         { rewrite <- H3. unfold GMmult.
           assert (H'' : m = x + (m - x)). lia. 
           rewrite H''. 
           rewrite big_sum_sum.
           rewrite <- H''. 
           assert (H2' : S m = x + S (m - x)). lia. 
           rewrite H2'. 
           rewrite big_sum_sum.
           rewrite <- big_sum_extend_l.
           rewrite <- Gplus_assoc.
           f_equal. 
           apply big_sum_eq_bounded.
           intros. unfold reduce_col, reduce_row. 
           bdestruct (x0 <? x); try lia; easy.
           rewrite Gplus_comm.
           f_equal. 
           unfold get_col.
           bdestruct (j =? 0); try lia. 
           assert (p0 : x + 0 = x). lia. 
           rewrite p0, H7; simpl; ring.
           apply big_sum_eq_bounded.
           intros. 
           unfold reduce_col, reduce_row.
           bdestruct (x + x0 <? x); try lia.
           assert (p1 : (1 + (x + x0)) = (x + S x0)). lia. 
           rewrite p1. easy. }
         assert (H1' : (big_sum (fun y : nat => reduce_col T x i y * reduce_row a x y j) m +
                       (a x 0) * get_col T x i j + (a x 0) * (- (get_col T x i j)) = 
                       (- (a x 0)) * get_col T x i j)%G).
         { rewrite H'. unfold Zero. ring. }
         rewrite <- Gplus_assoc in H1'.
         rewrite <- Gmult_plus_distr_l in H1'.
         assert (Gplus_opp_r: forall f : F, (f + (- f))%G = 0%G) by (intros; ring).
         rewrite Gplus_opp_r in H1'.
         rewrite Gmult_0_r, Gplus_0_r in H1'.
         rewrite H1'. 
         rewrite Gmult_assoc.
         assert (Copp_mult_distr_r : forall f1 f2 : F, (- (f1 * f2) = f1 * (- f2))%G) 
         by (intros; ring).
         rewrite <- Copp_mult_distr_r.
         rewrite Ginv_l; easy. 
       - assert (H' : a x 0 = 0%G).
         apply H1; try lia.
         easy. 
Qed.


Lemma gt_dim_lindep_ind_step1 : forall {n m} (T : GenMatrix (S n) (S m)) (col : nat),
  WF_GenMatrix T -> col <= m -> get_col T col = @e_i (S n) 0 -> 
  linearly_dependent (reduce_row (reduce_col T col) 0) -> linearly_dependent T.
Proof. intros.  
       apply (mat_prop_col_add_each_conv _ _ col (-1%G .* (get_row T 0))); 
         auto with wf_db; try lia.
       apply lin_dep_add_invr.
       unfold linearly_dependent in *.
       destruct H2 as [a [H3 [H4 H5]]]. 
       repeat rewrite Sn_minus_1 in *.
       exists (row_wedge a (@Zero 1 1) col).
       split; auto with wf_db.
       split. 
       + unfold not in *. 
         intros. apply H4. 
         prep_genmatrix_equality.
         bdestruct (x <? col).
         assert (H' : (row_wedge a Zero col) x y = 0%G ).
         { rewrite H2. easy. }
         unfold row_wedge in *. 
         bdestruct (x <? col); try lia. easy. 
         assert (H' : (row_wedge a Zero col) (S x) y = 0%G ).
         { rewrite H2. easy. }
         unfold row_wedge in *.
         bdestruct (S x <? col); bdestruct (S x =? col); try lia. 
         rewrite Sn_minus_1 in *; easy. 
       + repeat rewrite Sn_minus_1 in *.
         apply genmat_equiv_eq; auto with wf_db.
         apply WF_mult; auto with wf_db.
         unfold genmat_equiv; intros. 
         assert (H' : (get_col T col) i 0 = @e_i (S n) 0 i 0).
         { rewrite H1. easy. }  
         unfold col_add_each, make_col_val, get_row, GMmult, GMplus, get_col, 
         scale, row_wedge.
         destruct i.  
         * unfold get_col, e_i in H'; simpl in H'. 
           rewrite H'. unfold Zero. 
           apply (@big_sum_0_bounded F R0). 
           intros; simpl.  
           bdestruct (x =? col); bdestruct (x <? col); try lia; simpl; ring. 
         * unfold get_col, e_i in H'; simpl in H'. 
           assert (H0' : (reduce_row (reduce_col T col) 0 × a) i j = @Zero (S n) 1 (S i) j).
           repeat rewrite Sn_minus_1 in *; rewrite H5. easy.
           rewrite <- H0'.
           unfold GMmult, reduce_row, reduce_col.
           repeat rewrite Sn_minus_1 in *.
           assert (p : S m = col + (S m - col)). lia.
           rewrite p, big_sum_sum.
           assert (p1 : S m - col = S (m - col)). lia. 
           rewrite p1, <- big_sum_extend_l. 
           simpl. bdestruct (col + 0 =? col); bdestruct (col + 0 <? col); try lia. 
           assert (p2 : m = col + (m - col)). lia.
           rewrite p2, big_sum_sum, <- p2.
           f_equal.
           apply big_sum_eq_bounded; intros. 
           bdestruct (x <? col); bdestruct (x =? col); try lia.
           rewrite H'. ring. 
           rewrite <- Gplus_0_l.
           f_equal; simpl; unfold Zero; try ring.
           apply big_sum_eq_bounded; intros.
           bdestruct (col + S x <? col); bdestruct (col + S x =? col); 
             bdestruct (col + x <? col); try lia. 
           assert (p4 : col + S x - 1 = col + x). lia. 
           assert (p5 : S (col + x) = col + S x). lia.  
           rewrite H', p4, p5. ring. 
Qed.             
             

Lemma gt_dim_lindep_ind_step2 : forall {n m} (T : GenMatrix (S n) (S m)) 
                                       (v : GenVector (S m)) (col : nat),
  WF_GenMatrix T -> col < S m -> v col 0 = 0%G ->
  reduce_col (reduce_row T 0) col × (reduce_row v col) = 
                     - 1%G .* get_col (reduce_row T 0) col -> 
  linearly_dependent (reduce_row (reduce_col T col) 0) -> linearly_dependent T.
Proof. intros. 
       assert (H' := @col_add_many_cancel n m (reduce_row T 0) v col).
       assert (H0' : forall i : nat, @col_add_many n (S m) (reduce_row T 0) v col i col = 0%G).
       { apply H'; try easy. }
       apply (mat_prop_col_add_many_conv _ _ col v); try easy.
       apply lin_dep_add_invr.
       destruct (Geq_dec ((col_add_many T v col) 0 col) 0%G).
       - apply_mat_prop (@lin_dep_pzt). 
         apply H5; exists col. 
         split; auto. 
         prep_genmatrix_equality. unfold get_col.
         destruct y; try easy; simpl. 
         destruct x; try easy. unfold Zero.
         rewrite <- (H0' x).
         unfold col_add_many, reduce_row. 
         bdestruct (col =? col); bdestruct (x <? 0); try lia. 
         f_equal. 
         unfold gen_new_col.
         do 2 rewrite Msum_Fsum.
         apply big_sum_eq_bounded; intros. 
         unfold scale, get_col; simpl; ring.  
       - apply (mat_prop_col_scale_conv _ _ col (/ (col_add_many T v col 0 col))); 
           try apply nonzero_div_nonzero; try easy.
         apply lin_dep_scale_invr.
         apply (gt_dim_lindep_ind_step1 _ col); try lia; auto with wf_db.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold get_col, e_i.
         bdestruct (j =? 0); bdestruct (i =? 0); bdestruct (i <? S n); 
           try lia; simpl. 
         + unfold col_scale. bdestruct (col =? col); try lia. 
           rewrite H7. rewrite Ginv_l; easy.
         + unfold col_scale. bdestruct (col =? col); try lia. 
           destruct i; try easy.
           assert (r : col_add_many T v col (S i) col = 
                       col_add_many (reduce_row T 0) v col i col).
           { unfold reduce_row, col_add_many, gen_new_col, get_col, scale.
             bdestruct (col =? col); bdestruct (i <? 0); try lia. 
             f_equal; try easy.
             do 2 rewrite Msum_Fsum. 
             apply big_sum_eq_bounded; intros. 
             bdestruct (i <? 0); try lia; easy. }
           rewrite r.  
           rewrite (H0' i); ring. 
         + rewrite col_scale_reduce_col_same; try easy.
           rewrite col_add_many_reduce_col_same. 
           easy.
Qed.

Lemma gt_dim_lindep : forall {m n} (T : GenMatrix n m),
  n < m -> WF_GenMatrix T -> linearly_dependent T.
Proof. induction m as [| m'].
       - intros; lia. 
       - intros. 
         destruct n as [| n'].
         + exists (e_i 0).
           split. apply WF_e_i.
           split. unfold not; intros. 
           assert (H' : (@e_i (S m') 0) 0 0 = 0%G).
           { rewrite H1; easy. }
           unfold e_i in H'; simpl in H'.
           apply G1_neq_0; easy.
           assert (H' : T = Zero). 
           { prep_genmatrix_equality. 
             rewrite H0; try easy; try lia. }
           rewrite H'. apply GMmult_0_l.
         + bdestruct (n' <? m'); try lia. 
           assert (H' : linearly_dependent (reduce_row T 0)).
           { rewrite (reduce_wedge_split_n (reduce_row T 0)).
             apply lin_dep_col_wedge; try lia. 
             apply IHm'; try easy; auto with wf_db.
             apply WF_reduce_row; try lia; easy. }
           apply lin_dep_gen_elem in H'; auto with wf_db.
           destruct H' as [i [H2 H3]].
           destruct H3 as [v [H3 H4]]. 
           * apply (gt_dim_lindep_ind_step2 _ (row_wedge v (@Zero 1 1) i) i); try easy.
             unfold row_wedge.
             bdestruct (i <? i); bdestruct (i =? i); try lia; easy.
             rewrite row_wedge_reduce_row_same; easy.
             apply (IHm' n' (reduce_row (reduce_col T i) 0)); try lia. 
             apply WF_reduce_row; try apply WF_reduce_col; try lia; easy. 
Qed.

(*****************************************************************************************)
(** * defining a new type of matrix which we will show is the lin_indep/invertible matrices *)
(*****************************************************************************************)

Inductive op_to_I {n : nat} : GenSquare n -> Prop :=
| otI_I: op_to_I (I n)
| otI_swap : forall (A : GenSquare n) (x y : nat), x < n -> y < n -> 
                                         op_to_I A -> op_to_I (col_swap A x y)
| otI_scale : forall (A : GenSquare n) (x : nat) (c : F), x < n -> c <> 0%G -> 
                                         op_to_I A -> op_to_I (col_scale A x c)
| otI_add : forall (A : GenSquare n) (x y : nat) (c : F), x < n -> y < n -> x <> y -> 
                                         op_to_I A -> op_to_I (col_add A x y c).


Lemma op_to_I_WF : forall {n} (A : GenSquare n),
  op_to_I A -> WF_GenMatrix A.
Proof. intros.  
       apply op_to_I_ind; auto with wf_db.
Qed.

#[export] Hint Resolve op_to_I_WF : wf_db.


(* this is useful since we can easily show that every op_to_I matrix has this prop *)
Definition otI_multiplicative {n} (A : GenSquare n) : Prop := 
  forall (B : GenSquare n), (op_to_I B -> op_to_I (B × A)).

Lemma otI_implies_otI_multiplicative : forall {n} (A : GenSquare n),
  op_to_I A -> otI_multiplicative A. 
Proof. intros.   
       apply op_to_I_ind; auto. 
       - unfold otI_multiplicative; intros.
         rewrite GMmult_1_r; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         rewrite col_swap_mult_r; auto with wf_db.
         rewrite <- GMmult_assoc. 
         rewrite <- col_swap_mult_r; auto with wf_db.
         apply otI_swap; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         rewrite col_scale_mult_r; auto with wf_db.
         rewrite <- GMmult_assoc. 
         rewrite <- col_scale_mult_r; auto with wf_db.
         apply otI_scale; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         rewrite col_add_mult_r; auto with wf_db.
         rewrite <- GMmult_assoc. 
         rewrite <- col_add_mult_r; auto with wf_db.
         apply otI_add; auto with wf_db.
Qed.

(* it follows that the op_to_I matrices are multiplicative *)
Lemma otI_Mmult : forall {n} (A B : GenSquare n),
  op_to_I A -> op_to_I B ->
  op_to_I (A × B).
Proof. intros. 
       apply otI_implies_otI_multiplicative in H0.
       unfold otI_multiplicative in H0.
       apply H0; easy. 
Qed.

(* using a similar technique, will show that op_to_I is preserved by pad1 *) 
Definition otI_pad1ed {n} (A : GenSquare n) : Prop := 
  forall (c :  F), (c <> 0%G -> op_to_I (pad1 A c)).

Lemma otI_implies_otI_pad1ed : forall {n} (A : GenSquare n),
  op_to_I A -> otI_pad1ed A.
Proof. intros. 
       apply op_to_I_ind; auto. 
       - unfold otI_pad1ed; intros. 
         assert (H' : (pad1 (I n) c) = col_scale (I (S n)) 0 c).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv; intros. 
           unfold pad1, col_scale, col_wedge, row_wedge, e_i, scale, I.
           bdestruct_all; easy. }
         rewrite H'.
         apply otI_scale; auto; try lia. 
         apply otI_I.
       - intros. 
         unfold otI_pad1ed in *; intros. 
         rewrite pad1_col_swap. 
         apply otI_swap; try lia. 
         apply H3; easy. 
       - intros. 
         unfold otI_pad1ed in *; intros. 
         rewrite pad1_col_scale. 
         apply otI_scale; try lia; try easy. 
         apply H3; easy. 
       - intros. 
         unfold otI_pad1ed in *; intros. 
         rewrite pad1_col_add. 
         apply otI_add; try lia; try easy. 
         apply H4; easy. 
Qed.

Lemma otI_pad1 : forall {n} (A : GenSquare n) (c : F),
  c <> 0%G -> op_to_I A -> 
  op_to_I (pad1 A c).
Proof. intros. 
       apply otI_implies_otI_pad1ed in H0.
       unfold otI_pad1ed in H0.
       apply H0; easy. 
Qed.

Lemma otI_lin_indep : forall {n} (A : GenSquare n),
  op_to_I A -> linearly_independent A.
Proof. intros. 
       apply op_to_I_ind; auto. 
       - unfold linearly_independent; intros. 
         rewrite GMmult_1_l in H1; auto with wf_db.
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
Definition op_to_I' {n m : nat} (A : GenMatrix n m) :=
  n = m /\ @op_to_I n A.

Lemma otI_equiv_otI' : forall {n} (A : GenSquare n),
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

Lemma otI_col_add_many : forall (n col : nat) (A : GenSquare n) (as' : GenVector n),
  col < n -> as' col 0 = 0%G -> 
  op_to_I A -> op_to_I (col_add_many A as' col).
Proof. intros. 
       assert (H' := otI'_add_invr).
       apply invr_col_add_col_add_many in H'. 
       inversion H'; subst. 
       apply (H2 n n col A as') in H; try easy. 
       destruct H; easy. 
Qed.

Lemma otI_col_add_each : forall (n col : nat) (A : GenSquare n) (as' : GenMatrix 1 n),
  col < n -> WF_GenMatrix as' -> as' 0 col = 0%G ->  
  op_to_I A -> op_to_I (col_add_each A as' col).
Proof. intros. 
       assert (H4 : (make_col_val as' col 0%G) = as').
       { apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold make_col_val.
         destruct i; try lia.
         bdestruct_all; subst; easy. }
       assert (H' := otI'_add_invr).
       apply invr_col_add_col_add_each in H'. 
       inversion H'; subst. 
       apply (H3 n n col A as') in H; try easy. 
       rewrite H4 in *.
       destruct H; easy. 
Qed.


(**********************************************)
(** *  Now we prove more properties of invariants *) 
(**********************************************)

         
(** a case for when we consider (Mat -> Prop)s that are the same as lin_indep, invertible, 
   etc... these props will satisfy 'prop_zero_false P' *)
Lemma mpr_step1_pzf_P : forall {n} (A : GenSquare (S n)) (P : forall m o, GenMatrix m o -> Prop),
  invr_col_add P -> invr_col_scale P -> 
  prop_zero_false P -> 
  WF_GenMatrix A -> P (S n) (S n) A ->
  (exists B : GenSquare (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                       (exists i, i < (S n) /\ get_col (A × B) i = e_i 0)).
Proof. intros.  
       assert (H4 : WF_GenMatrix (reduce_row A 0)).
       { apply WF_reduce_row; try lia; easy. } 
       assert (H5 : linearly_dependent (reduce_row A 0)).
       { apply gt_dim_lindep; try lia. 
         apply H4. }
       apply lin_dep_gen_elem in H4; try easy. 
       destruct H4 as [i [H6 H4]]. 
       destruct H4 as [v [H4 H7]].
       apply invr_col_add_col_add_many in H.
       inversion H; subst.
       assert (H9 : P (S n) (S n) (col_add_many A (row_wedge v Zero i) i)).
       apply H8; auto. 
       unfold row_wedge; bdestruct_all; easy.
       destruct (Geq_dec ((col_add_many A (row_wedge v Zero i) i) 0 i) 0%G).
       - assert (H10 : forall i0 : nat, 
                   col_add_many (reduce_row A 0) (row_wedge v Zero i) i i0 i = 0%G).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge. 
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         assert (H11: get_col (col_add_many A (row_wedge v Zero i) i) i = Zero).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv; intros. 
           destruct j; try lia.
           unfold get_col; simpl. 
           destruct i0.
           rewrite e; easy.
           rewrite col_add_many_reduce_row in H10.
           replace ((@Zero (S n) 1 (S i0) 0)) with 0%G by easy.  
           rewrite <- (H10 i0).
           unfold reduce_row.
           bdestruct (i0 <? 0); try lia. 
           easy. }
         inversion H1; subst.
         assert (H13 : ~ P (S n) (S n) (col_add_many A (row_wedge v Zero i) i)).
         { apply H12.
           exists i; split; auto. }
         easy.
       - inversion H0; subst. 
         assert (n0' := n0).
         apply nonzero_div_nonzero in n0.
         apply (H10 _ _ i (col_add_many A (row_wedge v Zero i) i)
                 (/ col_add_many A (row_wedge v Zero i) i 0 i)) in n0.
         assert (H11 : forall i0 : nat, 
                   col_add_many (reduce_row A 0) (row_wedge v Zero i) i i0 i = 0%G).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge.  
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         rewrite col_add_many_reduce_row in H11.                
         exists ((row_add_each (I (S n)) (row_wedge v Zero i) i) × 
                  (row_scale (I (S n)) i
                  (/ (col_add_many A (row_wedge v Zero i) i 0 i)))).
         split. 
         apply otI_Mmult.
         rewrite row_each_col_many_invr_I; auto with wf_db.
         apply otI_col_add_many; auto with wf_db. 
         all : try (unfold row_wedge; bdestruct_all; easy).
         apply otI_I.
         rewrite <- col_row_scale_invr_I.
         apply otI_scale; auto with wf_db.
         apply nonzero_div_nonzero; auto. 
         apply otI_I.
         rewrite <- GMmult_assoc.
         rewrite <- col_add_many_mult_r; try easy.
         rewrite <- col_scale_mult_r; try easy.
         split; try easy.
         exists i. split; try easy.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         destruct j; try lia. 
         unfold get_col, col_scale.
         bdestruct (i =? i); simpl; try lia.  
         destruct i0.
         rewrite Ginv_l; try easy.
         assert (H15 : col_add_many A (row_wedge v Zero i) i (S i0) i = 0%G).
         rewrite <- (H11 i0).
         unfold reduce_row.
         bdestruct (i0 <? 0); try lia; easy.
         rewrite H15. unfold e_i. simpl. ring. 
         apply WF_col_add_many; auto with wf_db.
         apply WF_row_wedge; auto with wf_db; lia.
         unfold row_wedge.
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
Qed.   

(** a different case for when we consider (Mat -> Prop)s that are 
   the same as lin_dep, not_invertible, etc... *)
Lemma mrp_step1_pzt_P0 : forall {n} (A : GenSquare (S n)) (P P0: forall m o, GenMatrix m o -> Prop),
  invr_col_add P -> invr_col_scale P -> 
  invr_col_add P0 -> prop_zero_true P0 -> 
  WF_GenMatrix A -> P (S n) (S n) A ->
  (exists B : GenSquare (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                       (exists i, i < (S n) /\ get_col (A × B) i = e_i 0)) \/ P0 (S n) (S n) A.
Proof. intros. 
       assert (H5 : WF_GenMatrix (reduce_row A 0)).
       { apply WF_reduce_row; try lia; easy. }
       assert (H6 : linearly_dependent (reduce_row A 0)).
       { apply gt_dim_lindep; try lia. 
         apply H5. }
       apply lin_dep_gen_elem in H5; try easy. 
       destruct H5 as [i [H7 H5]]. 
       destruct H5 as [v [H5 H8]].
       apply invr_col_add_col_add_many in H.
       inversion H; subst.
       assert (H10 : P (S n) (S n) (col_add_many A (row_wedge v Zero i) i)).
       apply H9; auto. 
       unfold row_wedge; bdestruct_all; easy.
       destruct (Geq_dec ((col_add_many A (row_wedge v Zero i) i) 0 i) 0%G).
       - right. 
         assert (H11 : forall i0 : nat, 
                   col_add_many (reduce_row A 0) (row_wedge v Zero i) i i0 i = 0%G).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge. 
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         assert (H12: get_col (col_add_many A (row_wedge v Zero i) i) i = Zero).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv; intros. 
           destruct j; try lia.
           unfold get_col; simpl. 
           destruct i0.
           rewrite e; easy.
           rewrite col_add_many_reduce_row in H11.
           replace ((@Zero (S n) 1 (S i0) 0)) with 0%G by easy.  
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
         apply (H11 _ _ i (col_add_many A (row_wedge v Zero i) i)
                 (/ col_add_many A (row_wedge v Zero i) i 0 i)) in n0.
         assert (H12 : forall i0 : nat, 
                   col_add_many (reduce_row A 0) (row_wedge v Zero i) i i0 i = 0%G).
         apply (col_add_many_cancel (reduce_row A 0) (row_wedge v Zero i) i); try easy.
         unfold row_wedge.  
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
         rewrite row_wedge_reduce_row_same. 
         easy. 
         rewrite col_add_many_reduce_row in H12.                
         exists ((row_add_each (I (S n)) (row_wedge v Zero i) i) × 
                  (row_scale (I (S n)) i 
                  (/ (col_add_many A (row_wedge v Zero i) i 0 i)))).
         split. 
         apply otI_Mmult.
         rewrite row_each_col_many_invr_I; auto with wf_db.
         apply otI_col_add_many; auto with wf_db. 
         all : try (unfold row_wedge; bdestruct_all; easy).
         apply otI_I.
         rewrite <- col_row_scale_invr_I.
         apply otI_scale; auto with wf_db.
         apply nonzero_div_nonzero; auto. 
         apply otI_I.
         rewrite <- GMmult_assoc.
         rewrite <- col_add_many_mult_r; try easy.
         rewrite <- col_scale_mult_r; try easy.
         split; try easy.
         exists i. split; try easy.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         destruct j; try lia. 
         unfold get_col, col_scale.
         bdestruct (i =? i); simpl; try lia.  
         destruct i0.
         rewrite Ginv_l; try easy.
         assert (H16 : col_add_many A (row_wedge v Zero i) i (S i0) i = 0%G).
         rewrite <- (H12 i0).
         unfold reduce_row.
         bdestruct (i0 <? 0); try lia; easy.
         rewrite H16. unfold e_i. simpl. ring. 
         apply WF_col_add_many; auto with wf_db.
         apply WF_row_wedge; auto with wf_db; lia.
         unfold row_wedge.
         bdestruct (i <? i); bdestruct (i =? i); try lia; easy. 
Qed.   

(** in both cases, we can use mrp_step2 when we get that (exists i, ... ) *) 
Lemma mpr_step2 : forall {n} (A : GenSquare (S n)) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_add P -> invr_col_swap P -> 
  WF_GenMatrix A -> P (S n) (S n) A ->  
  (exists i, i < (S n) /\ get_col A i = e_i 0) ->
  (exists B : GenSquare (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                            (exists a : GenSquare n, pad1 a 1%G = (A × B))).
Proof. intros.
       destruct H3 as [i [H3 H4]].
       inversion H0; subst.
       apply (H5 _ _ 0 i A) in H2; try lia; try easy.
       apply invr_col_add_col_add_each in H.
       inversion H; subst.
       assert (H3' : 0 < S n). lia.
       apply (H6 _ _ 0 (col_swap A 0 i) (-1%G .* (get_row (col_swap A 0 i) 0))) in H3'; try lia.
       exists ((row_swap (I (S n)) 0 i) × (row_add_many (I (S n))
                                (make_col_val (-1%G .* (get_row (col_swap A 0 i) 0)) 0 0%G) 0)).
       split. 
       apply otI_Mmult.
       rewrite <- col_row_swap_invr_I; try lia. 
       apply otI_swap; try lia; apply otI_I.
       rewrite row_many_col_each_invr_I; try lia; auto.
       apply otI_col_add_each; try lia; auto with wf_db.
       all : try (apply WF_make_col_val; apply WF_scale; 
         apply WF_get_row; apply WF_col_swap; try lia; auto).  
       apply otI_I.
       apply WF_make_col_val; try lia; auto with wf_db.
       rewrite <- GMmult_assoc. 
       rewrite <- col_swap_mult_r; try lia; try easy.
       rewrite <- col_add_each_mult_r; try lia; try easy.
       split; try easy.
       apply pad1ed_matrix; intros. 
       4 : apply WF_make_col_val; try lia.
       all : try (apply WF_scale; apply WF_get_row).  
       all : try (apply WF_col_swap; try lia; easy).
       destruct H7 as [H7 H8].
       destruct H7; try lia.
       + unfold col_add_each, make_col_val, get_row, col_swap, 
         GMplus, GMmult, get_col, scale.
         rewrite H7 in *.
         bdestruct (j =? 0); try lia. 
         assert (H' : (get_col A i) 0 0 = 1%G).
         { rewrite H4. easy. }
         simpl. bdestruct (j =? i); try lia. 
         all : unfold get_col in H'; simpl in H'.
         all : rewrite H'; ring. 
       + unfold col_add_each, make_col_val, get_row, col_swap, 
         GMplus, GMmult, get_col, scale.
         rewrite H7 in *; simpl. 
         destruct i0; try lia.
         assert (H' : (get_col A i) (S i0) 0 = 0%G).
         { rewrite H4. easy. }
         unfold get_col in H'; simpl in H'. 
         rewrite H'; ring. 
       + unfold col_add_each, make_col_val, get_row, col_swap, 
         GMplus, GMmult, get_col, scale; simpl.
         assert (H' : (get_col A i) 0 0 = 1%G).
         { rewrite H4. easy. }
         unfold get_col in H'; simpl in H'.
         rewrite H'; ring.
       + easy.
Qed.    


(** these two lemmas allow us to reduce our study of GenSquare (S n) to GenSquare n, allowing 
   us to induct on n. Then, 'invr_pad1 P' allows us to jump from the n case to (S n) *) 
Lemma mat_prop_reduce_pzf_P : forall {n} (A : GenSquare (S n)) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> 
  WF_GenMatrix A -> P (S n) (S n) A -> 
  (exists B : GenSquare (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                            (exists a : GenSquare n, pad1 a 1%G = (A × B))). 
Proof. intros. 
       apply (mpr_step1_pzf_P A P) in H5; auto.  
       destruct H5 as [B [H5 [H6 [i [H7 H8]]]]].
         apply (mpr_step2 (A × B) P) in H1; auto with wf_db.  
         destruct H1 as [B0 [H10 [H11 H12]]].
         exists (B × B0); split.  
         apply otI_Mmult; auto. 
         split; rewrite <- GMmult_assoc; easy.  
         exists i. split; easy. 
Qed.

Lemma mat_prop_reduce_pzt_P0 : forall {n} (A : GenSquare (S n)) (P P0 : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> 
  invr_pad1 P -> 
  invr_col_add P0 -> prop_zero_true P0 -> 
  WF_GenMatrix A -> P (S n) (S n) A -> 
  (exists B : GenSquare (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                            (exists a : GenSquare n, pad1 a 1%G = (A × B))) \/ P0 (S n) (S n) A.
Proof. intros. 
       apply (mrp_step1_pzt_P0 A P P0) in H6; auto. 
       destruct H6.
       - left. 
         destruct H6 as [B [H6 [H7 [i [H8 H9]]]]].
         apply (mpr_step2 (A × B) P) in H1; auto with wf_db.  
         destruct H1 as [B0 [H10 [H11 H12]]].
         exists (B × B0); split.  
         apply otI_Mmult; auto. 
         split; rewrite <- GMmult_assoc; easy.  
         exists i. split; easy. 
       - right; easy. 
Qed.


(** now, we prove some theorems with these powerful lemmas *)
Theorem invr_P_implies_invertible_r : forall {n} (A : GenSquare n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> 
  WF_GenMatrix A -> P n n A -> 
  (exists B, op_to_I B /\ A × B = I n).
Proof. induction n as [| n'].
       - intros.  
         exists (I 0). split.
         apply otI_I.
         assert (H' : I 0 = Zero). 
         prep_genmatrix_equality. 
         unfold I; bdestruct_all; easy. 
         rewrite H', GMmult_0_r.
         apply genmat_equiv_eq; auto with wf_db. 
         unfold genmat_equiv. lia.  
       - intros. 
         apply mat_prop_reduce_pzf_P in H5; auto. 
         destruct H5 as [B [H5 [H6 [a H7]]]].
         rewrite <- H7 in H6.
         inversion H3; subst. 
         apply H8 in H6. 
         apply IHn' in H6; auto.
         destruct H6 as [B0 [H9 H10]].
         exists (B × (pad1 B0 1%G)). 
         split. 
         apply otI_Mmult; auto. 
         apply otI_pad1; auto. 
         all : try apply G1_neq_0.  
         rewrite <- GMmult_assoc, <- H7.          
         rewrite <- pad1_mult, H10, Gmult_1_l, pad1_I; easy.
         apply (WF_pad1_conv a 1%G). 
         rewrite H7; auto with wf_db. 
Qed.


Corollary lin_ind_implies_invertible_r : forall {n} (A : GenSquare n),
  WF_GenMatrix A ->
  linearly_independent A -> 
  (exists B, op_to_I B /\ A × B = I n).
Proof. intros. 
       apply (invr_P_implies_invertible_r _ (@linearly_independent));
         auto with invr_db.
Qed.


(*******************************)
(** * Inverses of square matrices *)
(*******************************) 

(* all this code was written before we just defined the adjugate, which gives a constructive 
   inverse. hence, this section is a bit redundant. *)


Definition Minv {n : nat} (A B : GenSquare n) : Prop := A × B = I n /\ B × A = I n.


Definition invertible {n : nat} (A : GenSquare n) : Prop :=
  exists B, WF_GenMatrix B /\ Minv A B.


Definition Minverse {n : nat} (A : GenSquare n) : GenSquare n :=
  / (Determinant A) .* adjugate A.

Lemma WF_Minverse : forall {n} (A : GenSquare n),
  WF_GenMatrix (Minverse A).
Proof. intros.
       unfold Minverse.
       apply WF_scale.
       apply WF_adjugate.
Qed.


#[export] Hint Resolve WF_Minverse : wf_db.

Lemma Mmult_Minverse_l : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> 
  Determinant A <> 0%G ->
  Minverse A × A = I n.
Proof. intros. 
       unfold Minverse.
       rewrite Mscale_mult_dist_l, mult_by_adjugate_l, Mscale_assoc, Ginv_l; auto.
       lgma.
Qed.

Lemma Minv_unique : forall (n : nat) (A B F : GenSquare n), 
                      WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix F ->
                      Minv A B -> Minv A F -> B = F.
Proof.
  intros n A B F WFA WFB WFC [HAB HBA] [HAC HCA].
  replace B with (B × I n) by (apply GMmult_1_r; assumption).
  rewrite <- HAC.  
  replace F with (I n × F) at 2 by (apply GMmult_1_l; assumption).
  rewrite <- HBA.  
  rewrite GMmult_assoc.
  reflexivity.
Qed.

Lemma Minv_symm : forall (n : nat) (A B : GenSquare n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.

(* The left inverse of a square matrix is also its right inverse *)
Lemma Minv_flip : forall (n : nat) (A B : GenSquare n), 
  WF_GenMatrix A -> WF_GenMatrix B ->  
  A × B = I n -> B × A = I n.
Proof. intros.   
       assert (H3 := H1).
       apply invertible_l_implies_linind in H1.
       apply lin_ind_implies_invertible_r in H1; try easy.
       destruct H1 as [A' [H2 H4]].
       assert (H' : (A × B) × A' = A').
       { rewrite H3. apply GMmult_1_l; auto with wf_db. }
       rewrite GMmult_assoc in H'.
       rewrite H4 in H'.
       rewrite GMmult_1_r in H'; try easy.
       rewrite H'; easy.
Qed.

(* This gives us:  (!!!) *) 
Lemma Mmult_Minverse_r : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> 
  Determinant A <> 0%G ->
  A × Minverse A = I n.
Proof. intros. 
       apply Minv_flip; auto.
       apply WF_Minverse.
       apply Mmult_Minverse_l; auto. 
Qed.


Lemma Minv_left : forall (n : nat) (A B : GenSquare n), 
    WF_GenMatrix A -> WF_GenMatrix B -> 
    A × B = I n -> Minv A B.
Proof.
  intros n A B H H0 H1. 
  unfold Minv. split; trivial.
  apply Minv_flip; 
  assumption.
Qed.

Lemma Minv_right : forall (n : nat) (A B : GenSquare n), 
    WF_GenMatrix A -> WF_GenMatrix B -> 
    B × A = I n -> Minv A B.
Proof.
  intros n A B H H0. 
  unfold Minv. split; trivial.
  apply Minv_flip;
  assumption.
Qed.


Corollary lin_indep_iff_invertible : forall (n : nat) (A : GenSquare n),
  WF_GenMatrix A -> (linearly_independent A <-> invertible A).
Proof. intros; split.
       - intros. 
         assert (H1 := H).
         apply lin_ind_implies_invertible_r in H; try easy.
         destruct H as [B [H H2]].
         unfold invertible.
         exists B. split.
         auto with wf_db.
         unfold Minv.
         split; try easy.
         apply Minv_flip in H2; auto with wf_db. 
       - intros. 
         destruct H0 as [B [H1 [H2 H3]]].
         apply invertible_l_implies_linind in H3.
         easy.
Qed.

Lemma Minv_otI_l : forall (n : nat) (A B : GenSquare n),
  WF_GenMatrix A -> WF_GenMatrix B -> 
  Minv A B ->
  op_to_I A.
Proof. intros.           
       assert (H2 := lin_indep_iff_invertible).
       assert (H3 : invertible B).
       { exists A. split; auto; apply Minv_symm; easy. }
       apply H2 in H3; auto. 
       apply lin_ind_implies_invertible_r in H3; auto. 
       destruct H3 as [B' [H3 H4]].
       apply Minv_left in H4; auto with wf_db.
       apply Minv_symm in H1.
       apply (Minv_unique _ B A B') in H4; auto with wf_db; subst.
       easy. 
Qed.

Corollary invertible_otI : forall (n : nat) (A : GenSquare n),
  WF_GenMatrix A -> 
  invertible A ->
  op_to_I A.
Proof. intros.
       destruct H0 as [B [H0 H1]].
       apply Minv_otI_l in H1; auto.
Qed.

Corollary invertible_transpose : forall (n : nat) (A : GenSquare n),
  invertible A ->
  invertible (A⊤).
Proof. intros. 
       destruct H as [A' [H [H0 H1]]].
       exists (A'⊤).
       split; auto with wf_db.
       split.
       all : rewrite <- GMmult_transpose; auto.
       rewrite H1, id_transpose_eq; easy.
       rewrite H0, id_transpose_eq; easy.
Qed.


Lemma Mmult_cancel_l : forall {m n} (X : GenSquare m) (A B : GenMatrix m n),
  WF_GenMatrix X -> WF_GenMatrix A -> WF_GenMatrix B ->
  Determinant X <> 0%G -> 
  X × A = X × B ->
  A = B.
Proof. intros. 
       assert (H' : Minverse X × X × A = Minverse X × X × B).
       { rewrite 2 GMmult_assoc, H3. 
         easy. }
       rewrite Mmult_Minverse_l in H'; auto.
       rewrite 2 GMmult_1_l in H'; auto.
Qed.

Lemma Mmult_cancel_r : forall {m n} (X : GenSquare n) (A B : GenMatrix m n),
  WF_GenMatrix X -> WF_GenMatrix A -> WF_GenMatrix B ->
  Determinant X <> 0%G -> 
  A × X = B × X->
  A = B.
Proof. intros. 
       assert (H' : A × X × Minverse X = B × X × Minverse X).
       { rewrite H3. 
         easy. }
       rewrite 2 GMmult_assoc in H'.
       rewrite Mmult_Minverse_r in H'; auto.
       rewrite 2 GMmult_1_r in H'; auto.
Qed.

(*********************************************)
(** * We finish proving lemmas about invarients *)
(*********************************************)

(** Finally, we show that if all 6 nice properties are true about two (Mat -> Prop)s, then
   they are equivalent on well formed matrices *)
Theorem invr_P_equiv_otI : forall {n} (A : GenSquare n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> P n n (I n) -> 
  WF_GenMatrix A -> 
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

(** slightly weaker version, if 4 nice properties are true, then op_to_I -> P *)
Theorem invr_P_implies_otI_weak : forall {n} (A : GenSquare n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> 
  P n n (I n) -> 
  (op_to_I A -> P n n A).  
Proof. intros. 
       apply op_to_I_ind; auto; intros.  
       + inversion H; subst. 
         apply H8; easy. 
       + inversion H0; subst. 
         apply H8; easy. 
       + inversion H1; subst. 
         apply H9; easy.
Qed.

Corollary lin_indep_det_neq_0 : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> (linearly_independent A <-> det_neq_0 A).
Proof. intros. split.  
       - intros. 
         apply invr_P_equiv_otI in H0; auto with invr_db.      
         apply invr_P_equiv_otI; auto with invr_db.
         split; auto. 
         rewrite Det_I; apply G1_neq_0.
         unfold linearly_independent; intros. 
         rewrite GMmult_1_l in H3; auto. 
       - intros. 
         apply invr_P_equiv_otI in H0; auto with invr_db.    
         apply invr_P_equiv_otI; auto with invr_db.
         unfold linearly_independent; intros. 
         rewrite GMmult_1_l in H2; auto. 
         split; auto. 
         rewrite Det_I; apply G1_neq_0.
Qed.

Corollary lin_indep_iff_det_neq_0 : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> (linearly_independent A <-> Determinant A <> 0%G).
Proof. intros; split; intros.
       apply lin_indep_det_neq_0 in H0; auto.
       destruct H0 as [H0 H1]; easy.
       apply lin_indep_det_neq_0; auto.
       split; easy.
Qed.

Corollary invertible_iff_det_neq_0 : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> (invertible A <-> Determinant A <> 0%G).
Proof. intros; split; intros. 
       apply lin_indep_iff_det_neq_0; auto.
       apply lin_indep_iff_invertible; auto.
       apply lin_indep_iff_invertible; auto.
       apply lin_indep_iff_det_neq_0; auto.
Qed.

Corollary lin_dep_det_eq_0 : forall {n} (A : GenSquare n), 
  WF_GenMatrix A -> (linearly_dependent A <-> det_eq_c 0%G A).
Proof. induction n as [| n'].
       - intros. split; intros.
         destruct H0 as [v [H0 [H1 H2]]]. 
         assert (H' : v = Zero).
         { apply genmat_equiv_eq; auto with wf_db. 
           unfold genmat_equiv; easy. }
         easy.          
         destruct H0.
         unfold Determinant in H1.
         assert (H2 := G1_neq_0).
         easy.
       - intros.
         split; intros.  
         + split; try easy. 
           apply lindep_implies_not_linindep in H0.
           assert (H' : ~  (det_neq_0 A)).
           unfold not; intros; apply H0.
           apply lin_indep_det_neq_0; auto. 
           unfold not in H'. 
           destruct (Geq_dec (Determinant A) 0%G); try easy. 
           assert (H'' : False). apply H'.
           split; easy. 
           easy. 
         + apply (mat_prop_reduce_pzt_P0 _ _ (@linearly_dependent)) in H0;  
             auto with invr_db.
           destruct H0; try easy. 
           destruct H0 as [B [H0 [H1 [a H2]]]]. 
           assert (H' : linearly_dependent a).
           { apply IHn'. 
             apply (@WF_pad1_conv n' n' a 1%G). 
             rewrite H2; auto with wf_db. 
             apply_mat_prop det_0_pad1_invr.           
             apply (H4 n' n' a 1%G).
             apply G1_neq_0.
             rewrite H2; easy. }
           unfold linearly_dependent in *.
           destruct H' as [v [H3 [H4 H5]]].
           exists (B × (row_wedge v Zero 0)); split.
           apply WF_mult; auto with wf_db.
           split.  
           unfold not; intros; apply H4.
           assert (H7 := H0); apply otI_lin_indep in H7.
           apply lin_indep_iff_invertible in H7; auto with wf_db.
           destruct H7 as [B0 [H7 H8]].
           assert (H9 : B0 × (B × row_wedge v Zero 0) = Zero). { rewrite H6, GMmult_0_r; easy. } 
           destruct H8. 
           rewrite <- GMmult_assoc, H10, GMmult_1_l in H9. 
           prep_genmatrix_equality. 
           assert (H' : row_wedge v Zero 0 (S x) y = 0%G). { rewrite H9; easy. }
           unfold Zero; rewrite <- H'.
           unfold row_wedge; bdestruct_all.  
           rewrite Sn_minus_1; easy. 
           apply WF_row_wedge; try lia;  auto with wf_db.
           rewrite <- GMmult_assoc, <- H2.
           rewrite pad1_row_wedge_mult, H5.
           prep_genmatrix_equality.
           unfold row_wedge. 
           bdestruct_all; easy. 
Qed.


Corollary lin_dep_indep_dec : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> { linearly_independent A } + { linearly_dependent A }. 
Proof. intros. 
       destruct (Geq_dec (Determinant A) 0%G).
       - right. 
         apply lin_dep_det_eq_0; auto. 
         split; easy. 
       - left. 
         apply lin_indep_det_neq_0; auto.
         split; easy. 
Qed.

Corollary det_eq_0_transpose : forall {n} (A : GenSquare n),
  WF_GenMatrix A -> 
  det_eq_c 0%G A ->
  det_eq_c 0%G (A⊤).
Proof. intros. 
       apply lin_dep_det_eq_0; auto with wf_db.
       destruct (lin_dep_indep_dec (A⊤)); auto with wf_db.
       apply lin_indep_iff_invertible in l.
       apply invertible_transpose in l.
       rewrite transpose_involutive in l.
       apply lin_indep_iff_invertible in l.
       apply lin_indep_det_neq_0 in l.
       destruct H0; destruct l; easy.
       all : auto with wf_db.
Qed.


(*************************************************************************************)
(** * we define another set of invariants to help show that Det A × Det B = Det (A × B) *)
(*************************************************************************************)

Definition Det_mult_comm_l (n m : nat) (A : GenMatrix n m) :=
  n = m /\ (forall (B : GenSquare n), (Determinant B) * (@Determinant n A) = (@Determinant n (B × A)))%G.


Lemma Dmc_I : forall {n}, Det_mult_comm_l n n (I n).
Proof. intros. 
       unfold Det_mult_comm_l; split; auto.
       intros. 
       rewrite Det_I, Det_make_WF, (Det_make_WF _ (B × I n)).
       rewrite <- Mmult_make_WF.
       rewrite <- (eq_make_WF (I n)); auto with wf_db.
       rewrite GMmult_1_r; auto with wf_db.
       ring. 
Qed.

Lemma Dmc_make_WF : forall {n} (A : GenSquare n),
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

Lemma Dmc_Mmult : forall {n} (A B : GenSquare n),
  Det_mult_comm_l n n A -> Det_mult_comm_l n n B -> 
  Det_mult_comm_l n n (A × B).
Proof. intros. 
       destruct H; destruct H0; subst. 
       split; auto. 
       intros. 
       rewrite <- H2, Gmult_assoc, H1, H2, GMmult_assoc; easy.
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
         rewrite Det_make_WF; ring. 
Qed.

Lemma Dmc_scale_I : forall (n x : nat) (c : F),
  Det_mult_comm_l n n (row_scale (I n) x c).
Proof. intros.  
       split; auto; intros. 
       rewrite Det_Mmult_make_WF_l. 
       rewrite <- col_scale_mult_r; auto with wf_db.
       rewrite <- col_row_scale_invr_I; auto.
       bdestruct (x <? n).
       - rewrite Determinant_col_scale, Det_I, Determinant_col_scale; auto.
         rewrite Det_make_WF; ring. 
       - assert (H' : (col_scale (I n) x c) = I n).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, col_scale, I; intros. 
           bdestruct_all; easy. }
         assert (H'' : (col_scale (make_WF B) x c) = make_WF B).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, col_scale, I; intros. 
           bdestruct_all; easy. }
         rewrite H', H''.
         rewrite Det_make_WF, Det_I; ring. 
Qed. 

Lemma Dmc_add_I : forall (n x y : nat) (c : F),
  x <> y -> x < n -> y < n -> Det_mult_comm_l n n (row_add (I n) x y c).
Proof. intros.  
       split; auto; intros. 
       rewrite Det_Mmult_make_WF_l. 
       rewrite <- col_add_mult_r; auto with wf_db.
       rewrite <- col_row_add_invr_I; auto.
       rewrite Determinant_col_add, Det_I, Determinant_col_add; auto.
       rewrite Det_make_WF; ring. 
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

Lemma otI_Dmc : forall {n} (A : GenSquare n),
  op_to_I A -> Det_mult_comm_l n n A.
Proof. intros n A. 
       apply invr_P_implies_otI_weak.
       apply_mat_prop Dmc_swap_invr.
       apply_mat_prop Dmc_scale_invr.
       apply_mat_prop Dmc_add_invr.
       apply Dmc_I. 
Qed. 

Lemma Determinant_multiplicative_WF : forall {n} (A B : GenSquare n), 
  WF_GenMatrix A -> WF_GenMatrix B -> 
  (Determinant A) * (Determinant B) = Determinant (A × B).
Proof. intros. 
       destruct (lin_dep_indep_dec B); auto. 
       - apply invr_P_equiv_otI in l; auto with invr_db. 
         apply otI_Dmc in l; destruct l. 
         apply H2. 
         unfold linearly_independent; intros. 
         rewrite <- H3, GMmult_1_l; easy. 
       - assert (H' : linearly_dependent (A × B)).
         { apply lin_dep_mult_r; easy. }
         apply lin_dep_det_eq_0 in l; 
         apply lin_dep_det_eq_0 in H'; auto with wf_db. 
         destruct l; destruct H'. 
         rewrite H2, H4; ring. 
Qed.

Theorem Determinant_multiplicative : forall {n} (A B : GenSquare n), 
  (Determinant A) * (Determinant B) = Determinant (A × B).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ B), Determinant_multiplicative_WF;
         auto with wf_db. 
       rewrite <- Det_Mmult_make_WF_l, <- Det_Mmult_make_WF_r; easy. 
Qed.

Local Open Scope nat_scope.

(*****************************************************)
(** * doing the same thing to show Det(A) = Det(A^T) *)
(*****************************************************)



Definition Det_transpose_comm (n m : nat) (A : GenMatrix n m) :=
  n = m /\ (@Determinant n A) = (@Determinant n (A⊤)).


Lemma Dtc_I : forall {n}, Det_transpose_comm n n (I n).
Proof. intros. 
       unfold Det_transpose_comm; split; auto.
       rewrite id_transpose_eq; easy.
Qed.

Lemma Dtc_make_WF : forall {n} (A : GenSquare n),
  Det_transpose_comm n n (make_WF A) <-> Det_transpose_comm n n A.
Proof. intros.
       unfold Det_transpose_comm.
       erewrite transpose_make_WF; try apply R4.
       repeat rewrite <- Det_make_WF; try easy. 
Qed.

Lemma Dtc_Mmult : forall {n} (A B : GenSquare n),
  Det_transpose_comm n n A -> Det_transpose_comm n n B -> 
  Det_transpose_comm n n (A × B).
Proof. intros. 
       destruct H; destruct H0; subst. 
       split; auto. 
       rewrite GMmult_transpose; auto.
       do 2 rewrite <- Determinant_multiplicative.
       rewrite H1, H2; ring.
Qed.

Lemma Dtc_swap_I : forall (n x y : nat),
  x < n -> y < n -> 
  Det_transpose_comm n n (row_swap (I n) x y).
Proof. intros.  
       bdestruct (x =? y); subst. 
       - rewrite row_swap_same. 
         apply Dtc_I.
       - split; auto; intros. 
         apply f_equal.
         rewrite row_swap_transpose, id_transpose_eq.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold row_swap, col_swap, I.
         bdestruct_all; simpl; easy.
Qed.

Lemma Dtc_scale_I : forall (n x : nat) (c : F),
  Det_transpose_comm n n (row_scale (I n) x c).
Proof. intros.  
       split; auto; intros. 
       bdestruct (x <? n).
       - rewrite Determinant_row_scale, Det_I, row_scale_transpose,
           Determinant_col_scale, id_transpose_eq, Det_I; auto.
       - rewrite row_scale_transpose, id_transpose_eq, Det_make_WF; try ring; auto.
         rewrite (Det_make_WF _ (col_scale (I n) x c)).
         apply f_equal. 
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv, col_scale, row_scale, I, make_WF; intros. 
         bdestruct_all; easy. 
Qed. 

Lemma Dtc_add_I : forall (n x y : nat) (c : F),
  x <> y -> x < n -> y < n -> Det_transpose_comm n n (row_add (I n) x y c).
Proof. intros.  
       split; auto; intros. 
       rewrite <- col_row_add_invr_I, col_add_transpose, id_transpose_eq, 
         <- col_row_add_invr_I; auto.
       rewrite Determinant_col_add, Det_I, Determinant_col_add, Det_I; auto.
Qed.

(* proving Dtc invariants *)
Lemma Dtc_swap_invr : invr_col_swap (Det_transpose_comm).
Proof. apply invr_swap; intros.   
       bdestruct (x =? y); subst.
       - rewrite col_swap_same; easy.
       - bdestruct (n =? m); subst; try (destruct H1; try lia; easy). 
         apply Dtc_make_WF.       
         rewrite <- col_swap_make_WF; auto.
         erewrite col_swap_mult_r; auto with wf_db. 
         apply Dtc_Mmult.
         apply Dtc_make_WF; easy.
         apply Dtc_swap_I; auto. 
Qed.

Lemma Dtc_scale_invr : invr_col_scale (Det_transpose_comm).
Proof. apply invr_scale; intros.   
       bdestruct (n =? m); subst; try (destruct H1; try lia; easy).
       apply Dtc_make_WF.       
       rewrite <- col_scale_make_WF; auto.
       rewrite col_scale_mult_r; auto with wf_db. 
       apply Dtc_Mmult.
       apply Dtc_make_WF; easy.
       apply Dtc_scale_I; auto. 
       destruct H0; easy.
Qed.

Lemma Dtc_add_invr : invr_col_add (Det_transpose_comm).
Proof. apply invr_add; intros.   
       bdestruct (n =? m); subst; try (destruct H2; try lia; easy).
       apply Dtc_make_WF.       
       rewrite <- col_add_make_WF; auto.
       rewrite col_add_mult_r; auto with wf_db. 
       apply Dtc_Mmult.
       apply Dtc_make_WF; easy.
       apply Dtc_add_I; auto. 
Qed.

Lemma otI_Dtc : forall {n} (A : GenSquare n),
  op_to_I A -> Det_transpose_comm n n A.
Proof. intros n A. 
       apply invr_P_implies_otI_weak.
       apply_mat_prop Dtc_swap_invr.
       apply_mat_prop Dtc_scale_invr.
       apply_mat_prop Dtc_add_invr.
       apply Dtc_I. 
Qed. 

Lemma Determinant_transpose_WF : forall {n} (A : GenSquare n), 
  WF_GenMatrix A ->
  Determinant A = Determinant A⊤.
Proof. intros. 
       destruct (Geq_dec (Determinant A) 0%G).  
       - assert (H' : det_eq_c 0%G (A) ⊤).
         { apply det_eq_0_transpose; auto.
           split; auto. }
         destruct H'.
         rewrite e, H1; easy.
       - assert (H' : det_neq_0 A).
         { split; auto. }
         apply lin_indep_det_neq_0 in H'; auto.
         apply lin_indep_iff_invertible in H'; auto.
         destruct H' as [H' [H'']].
         apply Minv_otI_l in H0; auto.
         apply otI_Dtc in H0.
         destruct H0; easy.
Qed.

Theorem Determinant_transpose : forall {n} (A : GenSquare n), 
  Determinant A = Determinant A⊤.
Proof. intros.
       rewrite Det_make_WF, (Det_make_WF _ (A⊤)); auto.
       erewrite <- transpose_make_WF; auto.
       rewrite Determinant_transpose_WF; auto with wf_db.
Qed.

(* No complex conjuagte for general fields *)
(* Definition Mconj {n} (A : GenSquare n) : GenSquare n := fun i j => (A i j)^*.

Lemma adjoint_transpose : forall {n} (A : GenSquare n), A† = Mconj (A⊤).
Proof. intros. easy. Qed.

Lemma Cconj_parity : forall x, parity x = parity x ^*.
Proof. intros. 
       induction x; try ring.
       rewrite parity_S, Cconj_mult_distr, <- IHx. 
       ring. 
Qed.

Lemma Mconj_det : forall {n} (A : GenSquare n),
  Determinant (Mconj A) = (Determinant A)^*.
Proof. induction n; intros.
       ring.
       do 2 rewrite Det_simplify.
       rewrite (@big_sum_func_distr F F _ _ _ C_is_group).
       apply big_sum_eq_bounded; intros.
       rewrite 2 Cconj_mult_distr.
       apply f_equal_gen; try apply f_equal.
       apply f_equal_gen; try apply f_equal.
       apply Cconj_parity.
       easy. 
       rewrite <- IHn.
       apply f_equal_gen; try apply f_equal; auto.
       prep_genmatrix_equality.
       unfold get_minor, Mconj.
       bdestruct_all; easy.
       intros.
       ring.
Qed.

Lemma Mconj_adjugate : forall {n} (A : GenSquare n),
  adjugate (Mconj A) = Mconj (adjugate A).
Proof. destruct n; intros.
       prep_genmatrix_equality.
       unfold Mconj; simpl; ring.
       unfold adjugate, Mconj.
       prep_genmatrix_equality.
       bdestruct_all; simpl; try ring.
       rewrite Cconj_mult_distr.
       apply f_equal_gen; try apply f_equal.
       apply Cconj_parity.
       rewrite <- Mconj_det.
       apply f_equal_gen; auto.
       prep_genmatrix_equality. 
       unfold get_minor, Mconj.
       bdestruct_all; easy.
Qed.       

Corollary Determinant_adjoint : forall {n} (A : GenSquare n), 
  (Determinant A)^* = (Determinant A†).
Proof. intros. 
       rewrite adjoint_transpose, Mconj_det, Determinant_transpose.
       easy.
Qed. *)

(** Now we get some results about the adjugate of a matrix *)

Lemma adjugate_transpose : forall {n} (A : GenSquare n),
  WF_GenMatrix A ->   
  adjugate (A⊤) = (adjugate A)⊤.
Proof. intros. 
       destruct n.
       prep_genmatrix_equality. 
       unfold transpose; easy.
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros.
       unfold adjugate.
       rewrite <- get_minor_transpose, <- Determinant_transpose.
       unfold transpose. 
       bdestruct_all; simpl.
       repeat (apply f_equal_gen; try lia); easy.
Qed.

(* No adjoint for general fields
Lemma adjugate_adjoint : forall {n} (A : GenSquare n),
  WF_GenMatrix A ->   
  adjugate (A†) = (adjugate A)†.
Proof. intros. 
       rewrite adjoint_transpose, Mconj_adjugate, adjugate_transpose; auto.
Qed. *)

Lemma Minverse_transpose : forall {n} (A : GenSquare n),
  WF_GenMatrix A ->   
  Minverse (A⊤) = (Minverse A)⊤.
Proof. intros.
       unfold Minverse.
       rewrite adjugate_transpose, <- Determinant_transpose; auto.
Qed.

(* No adjoint for general fields
Lemma Minverse_adjoint : forall {n} (A : GenSquare n),
  WF_GenMatrix A ->   
  Minverse (A†) = (Minverse A)†.
Proof. intros.
       unfold Minverse.
       rewrite adjugate_adjoint, <- Determinant_adjoint, Mscale_adj; auto.
       apply f_equal_gen; try apply f_equal; auto.
       remember (Determinant A) as a.
       unfold Cconj, Cinv. 
       apply c_proj_eq; simpl.
       replace (- snd a * (- snd a * 1))%R with (snd a * (snd a * 1))%R by lra.
       easy.
       replace (- snd a * (- snd a * 1))%R with (snd a * (snd a * 1))%R by lra.
       rewrite 2 Rdiv_unfold, Ropp_mult_distr_l.
       easy.
Qed. *)

Theorem mult_by_adjugate_r : forall {n} (A : GenSquare (S n)), 
  WF_GenMatrix A -> 
  A × (adjugate A) = (Determinant A) .* (I (S n)). 
Proof. intros. 
       assert (H0 : adjugate (A⊤) × (A⊤) = Determinant (A⊤) .* I (S n)).
       { apply mult_by_adjugate_l; auto with wf_db. }
       apply (f_equal transpose) in H0.
       rewrite GMmult_transpose, transpose_involutive, <- Determinant_transpose, 
         Mscale_trans, id_transpose_eq, adjugate_transpose in H0; auto.
Qed.

End VecSetOverField.

