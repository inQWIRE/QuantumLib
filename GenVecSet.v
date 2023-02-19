

(** In this file, we define more advanced linear algebra concepts such as bases, linear independence, etc... *)


Require Import Psatz.   
Require Import Reals.
  
Require Export RowColOps.


(************************************)
(** * some preliminary defs and lemmas *)
(************************************)

Open Scope nat_scope.
Open Scope genmatrix_scope.
Open Scope group_scope.


Section LinAlgOverCommRing3.
  Variables (F : Type).   (* F for ring, too bad R is taken :( *)
  Variable (R0 : Monoid F).
  Variable (R1 : Group F).
  Variable (R2 : Comm_Group F).
  Variable (R3 : Ring F).
  Variable (R4 : Comm_Ring F).
(* TODO: perhaps move this later? *)
  Variable (R5 : Domain F).

(* things that need to be rewritten in order to get the "reopened" section to work *)
(* could maybe use a Module so that this only needs to occur once??? *) 
Lemma F_ring_theory : ring_theory 0%G 1%G Gplus Gmult Gminus Gopp eq.
Proof. apply (@G_ring_theory F _ _ _ _ R4). Qed.

Add Ring F_ring_ring : F_ring_theory.


Notation GenMatrix := (GenMatrix F). 
Notation Square n := (Square F n). 
Notation Vector n := (Vector F n). 

Notation Σ := (@big_sum F R0).  (* we intoduce Σ notation here *) 

(* Create HintDb wf_db. *)
Hint Resolve WF_Zero WF_I WF_I1 WF_e_i WF_mult WF_plus WF_scale WF_transpose
     WF_outer_product WF_big_kron WF_kron_n WF_kron 
     WF_GMmult_n WF_make_WF (* WF_Msum *) : wf_db.
Hint Extern 2 (_ = _) => unify_pows_two : wf_db.


Hint Resolve WF_get_col WF_get_row WF_reduce_row WF_reduce_col WF_reduce_vecn WF_get_minor : wf_db.
Hint Resolve WF_row_wedge WF_col_wedge WF_smash : wf_db.
Hint Resolve WF_col_swap WF_row_swap WF_col_scale WF_row_scale WF_col_add WF_row_add : wf_db.
Hint Resolve WF_gen_new_col WF_gen_new_row WF_col_add_many WF_row_add_many : wf_db.
Hint Resolve WF_col_scale_many WF_row_scale_many WF_col_add_each WF_row_add_each  : wf_db.
Hint Resolve WF_make_col_val WF_make_row_val WF_col_to_front WF_row_to_front 
             col_replace row_replace: wf_db.

Hint Extern 1 (Nat.lt _ _) => lia : wf_db.
Hint Extern 1 (Nat.le _ _) => lia : wf_db.
Hint Extern 1 (lt _ _) => lia : wf_db.
Hint Extern 1 (le _ _) => lia : wf_db.

Hint Resolve WF_pad1 WF_pad1_conv : wf_db.
Hint Resolve WF_adjugate : wf_db.




  

(***************************************************************************)
(** * Defining properties which are invarient under column operations, etc... *)
(***************************************************************************)

Inductive invr_col_swap : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_swap : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n x y : nat) (T : GenMatrix m n), x < n -> y < n -> P m n T -> P m n (col_swap T x y)) 
    -> invr_col_swap P.

Inductive invr_col_scale : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_scale : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n x : nat) (T : GenMatrix m n) (c : F), 
        c <> 0 -> x < n ->
        P m n T -> P m n (col_scale T x c)) 
    -> invr_col_scale P.

(* note that this one assumes T is well formed, but the others do not *)
Inductive invr_col_scale_many : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_scale_many : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n : nat) (T : GenMatrix m n) (as' : GenMatrix 1 n), 
        WF_GenMatrix T ->
        (forall i, i < n -> as' O i <> 0) -> 
        P m n T -> P m n (col_scale_many T as')) 
    -> invr_col_scale_many P.

(* gives machinery for undoing col_scales *)
Inductive invr_scalar_cancel : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_scalar : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n : nat) (T : GenMatrix m n) (c : F), c <> 0 -> P m n (c .* T) -> P m n T) 
    -> invr_scalar_cancel P.

Inductive invr_col_add : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_add : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n x y : nat) (T : GenMatrix m n) (c : F), 
        x <> y -> x < n -> y < n -> P m n T -> P m n (col_add T x y c)) 
    -> invr_col_add P.

Inductive invr_col_add_many : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_add_many : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n col : nat) (T : GenMatrix m n) (as' : Vector n), 
        col < n -> as' col 0 = 0 -> P m n T -> P m n (col_add_many T as' col)) 
    -> invr_col_add_many P.

Inductive invr_col_add_each : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_add_each : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n col : nat) (T : GenMatrix m n) (as' : GenMatrix 1 n), 
        col < n -> WF_GenMatrix as' -> 
        P m n T -> P m n (col_add_each T (make_col_val as' col 0) col)) 
    -> invr_col_add_each P.

Inductive invr_pad1 : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| invr_p : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
    (forall (m n : nat) (T : GenMatrix m n) (c : F), 
        c <> 0 -> P (S m) (S n) (pad1 T c) -> P m n T) 
    -> invr_pad1 P.

Inductive prop_zero_true : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| PZT : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
  (forall (m n : nat) (T : GenMatrix m n), 
      (exists i, i < n /\ get_col T i = Zero) -> P m n T) ->
  prop_zero_true P.

Inductive prop_zero_false : (forall m n : nat, GenMatrix m n -> Prop) -> Prop :=
| PZF : forall (P : (forall m n : nat, GenMatrix m n -> Prop)), 
  (forall (m n : nat) (T : GenMatrix m n), 
      (exists i, i < n /\ get_col T i = Zero) -> ~ (P m n T)) ->
  prop_zero_false P.

(* Ltac to help apply these properties of (Mat -> Prop)s *)
Ltac apply_mat_prop tac := 
  let H := fresh "H" in 
  assert (H := tac); inversion H; subst; try apply H. 



(** showing we can get from the single col invrs to the many col invrs *)

Lemma mat_prop_col_scale_many_some : forall (e m n : nat) (P : forall m n : nat, GenMatrix m n -> Prop)
                                     (T : GenMatrix m n) (as' : GenMatrix 1 n),
  e < n ->  
  WF_GenMatrix T -> 
  (forall i, i < n -> as' O i <> 0) ->
  (forall i : nat, e < i -> i < n -> as' O i = 1) -> 
  invr_col_scale P ->
  P m n T -> P m n (col_scale_many T as').
Proof. induction e as [| e'].
       - intros.
         replace (col_scale_many T as') with (col_scale T 0 (as' 0 0)).
         inversion H3; subst.
         apply H5; auto.
         prep_genmatrix_equality.
         unfold col_scale, col_scale_many.
         bdestruct_all; subst; auto.
         bdestruct (y <? n).
         rewrite H2; try ring; lia.
         rewrite H0; try ring; lia.
       - intros. 
         rewrite (col_scale_many_col_scale _ _ _ _ _ _ _ _ (S e')). 
         inversion H3; subst.
         apply H5; auto.
         apply IHe'; auto; try lia; intros.
         unfold make_col_val.
         bdestruct_all; simpl; auto.
         unfold not; intros. 
         apply H1 in H6.
         apply H6.
         rewrite <- (Gmult_1_l (as' 0%nat i)), H9; ring. 
         unfold make_col_val. 
         bdestruct (0 <? 1); try lia.
         bdestruct_all; simpl; auto.
         apply H2; try lia.
Qed.         
         
Lemma invr_col_scale_col_scale_many : forall (P : forall m n : nat, GenMatrix m n -> Prop),
  invr_col_scale P -> invr_col_scale_many P.
Proof. intros.
       inversion H.
       apply invr_scale_many; intros.
       destruct n.
       - replace (col_scale_many T as') with T; auto.
         prep_genmatrix_equality.
         unfold col_scale_many.
         rewrite H2; try lia; ring.
       - apply (mat_prop_col_scale_many_some n); auto.
         lia.
Qed.

Lemma mat_prop_col_add_many_some : forall (e m n col : nat) (P : forall m n : nat, GenMatrix m n -> Prop)
                                     (T : GenMatrix m n) (as' : Vector n),
  (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = 0) -> as' col 0 = 0 ->
  invr_col_add P ->
  P m n T -> P m n (col_add_many T as' col).
Proof. induction e as [| e].
       - intros. 
         inversion H3; subst. 
         (* TODO: how do I avoid all the _'s without making args explicit for every single 
            lemma in RowColops.v? *)
         rewrite (col_add_many_col_add _ _ _ _ _ _ _ _ (skip_count col 0)); 
           try lia; try easy.  
         apply H5; try lia.
         apply skip_count_not_skip.
         assert (H' : (col_add_many T (make_row_val as' (skip_count col 0) 0) col) = T).
         { prep_genmatrix_equality. 
           unfold col_add_many, make_row_val, skip_count, gen_new_col, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Gplus_0_l, Gplus_comm.
           apply f_equal_gen; try apply f_equal; try easy. 
           rewrite Msum_Fsum.
           apply big_sum_0_bounded; intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); bdestruct (0 <? 1); try lia; simpl; try ring. 
           destruct x0; try rewrite H2; try rewrite H1; try ring; try lia. 
           destruct x0; simpl; try ring; rewrite H1; try ring; lia. }
         rewrite H'; easy.
         apply skip_count_not_skip.
       - intros. 
         inversion H3; subst. 
         rewrite (col_add_many_col_add _ _ _ _ _ _ _ _ (skip_count col (S e))); 
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


Lemma invr_col_add_col_add_many : forall (P : forall m n : nat, GenMatrix m n -> Prop),
  invr_col_add P -> invr_col_add_many P.
Proof. intros. 
       inversion H; subst. 
       apply invr_add_many; intros. 
       destruct n; try lia. 
       destruct n.
       - assert (H' : as' == Zero).
         { unfold genmat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ _ _ _ _ _ (make_WF as'));
           try apply genmat_equiv_make_WF.
         bdestruct (col =? S n).
         + apply (mat_prop_col_add_many_some n); try lia; try easy.
           unfold skip_count. bdestruct (n <? col); lia. 
           intros. 
           unfold skip_count in H5; rewrite H4 in H5. 
           bdestruct (n <? S n); try lia. 
           unfold make_WF. 
           bdestruct (i <? S (S n)); bdestruct (0 <? 1); try lia; try easy.
           bdestruct (i =? S n); try lia. 
           rewrite H9, <- H4; easy.
           unfold make_WF. 
           bdestruct_all; auto. 
         + apply (mat_prop_col_add_many_some n); try lia; try easy.
           unfold skip_count.
           bdestruct (n <? col); try lia. 
           intros. unfold make_WF.
           unfold skip_count in H5.
           bdestruct (n <? col); try lia. 
           bdestruct (i <? S (S n)); try lia; try easy.
           unfold make_WF. 
           bdestruct_all; auto. 
Qed.

Lemma mat_prop_col_add_each_some : forall (e m n col : nat) (P : forall m n : nat, GenMatrix m n -> Prop)
                                     (T : GenMatrix m n) (as' : GenMatrix 1 n),
  WF_GenMatrix as' -> (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = 0) -> as' 0 col = 0 ->
  invr_col_add P -> 
  P m n T -> P m n (col_add_each T as' col).
Proof. induction e as [| e].
       - intros.
         inversion H4; subst.
         rewrite (col_add_each_col_add _ _ _ _ _ _ _ _ _ (skip_count col 0)); try lia. 
         apply H6; try lia.
         assert (H' := skip_count_not_skip col 0). auto.
         assert (H' : (make_col_val as' (skip_count col 0) 0) = Zero).
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
         rewrite (col_add_each_col_add _ _ _ _ _ _ _ _ _ (skip_count col (S e))); try lia. 
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
              
Lemma invr_col_add_col_add_each : forall (P : forall m n : nat, GenMatrix m n -> Prop),
  invr_col_add P -> invr_col_add_each P.
Proof. intros.  
       inversion H; subst. 
       apply invr_add_each; intros. 
       destruct n; try lia. 
       destruct n.
       - assert (H' : make_col_val as' col 0 = Zero).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           unfold make_col_val. 
           easy. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
       - bdestruct (col =? S n).
         + apply (mat_prop_col_add_each_some n); try lia; try easy; auto with wf_db.
           unfold skip_count. bdestruct (n <? col); lia. 
           intros. 
           unfold make_col_val. 
           bdestruct (i =? col); try lia; try easy.
           rewrite H4 in H5; unfold skip_count in H5.
           bdestruct (n <? S n); try lia. 
           rewrite H2; try lia; easy.
           unfold make_col_val. 
           bdestruct (col =? col); try lia; easy.
         + apply (mat_prop_col_add_each_some n); try lia; try easy; auto with wf_db.
           unfold skip_count.
           bdestruct (n <? col); try lia. 
           intros. unfold make_col_val. 
           bdestruct (i =? col); try lia; try easy.
           unfold skip_count in H5.
           bdestruct (n <? col); try lia. 
           apply H2; lia. 
           unfold make_col_val. 
           bdestruct (col =? col); try lia; easy.
Qed.




(** showing that col_invr's are reversible, a bit weak in the case of scale *)


(* SWAP *)

Lemma mat_prop_col_swap_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) (T : GenMatrix m n) (x y : nat),
  invr_col_swap P -> 
  x < n -> y < n -> 
  P m n (col_swap T x y) -> P m n T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_swap_inv _ T x y).
       apply H3; easy.
Qed.





(* SCALE *)

(* quick continuation of gcm lemmas now that F is a domain *)
Lemma gcm_nonzero : forall {m n} (v : GenMatrix m n),
  get_common_multiple v <> 0.
Proof. induction n; intros.
       - simpl.
         apply G1_neq_0'.
       - simpl.
         destruct (Geq_dec (v O n) 0).
         + apply IHn; auto. 
         + apply Gmult_neq_0; auto.
Qed.

(* note how this requires the stronger hypothesis that we can reduce c .* T *)
Lemma mat_prop_col_scale_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                  (T : GenMatrix m n) (x : nat) (c : F),
  WF_GenMatrix T ->
  invr_col_scale P ->
  invr_scalar_cancel P -> 
  c <> 0 ->
  P m n (col_scale T x c) -> P m n T.
Proof. intros. 
       inversion H0; inversion H1; subst.
       apply (H6 _ _ _ c); auto.
       erewrite col_scale_scalar; auto.
       apply invr_col_scale_col_scale_many in H0.
       inversion H0; subst.
       apply H5; auto with wf_db; try apply H3.
       intros. 
       bdestruct_all; try easy.
       apply G1_neq_0'.
Qed.

Lemma mat_prop_col_scale_many_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                       (T : GenMatrix m n) (as' : GenMatrix 1 n), 
  WF_GenMatrix T ->
  invr_col_scale P ->
  invr_scalar_cancel P -> 
  (forall i, i < n -> as' O i <> 0) -> 
  P m n (col_scale_many T as') -> P m n T.
Proof. intros.
       destruct n.
       - replace T with (col_scale_many T as'); auto.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold col_scale_many.
         rewrite H; try ring; lia.
       - inversion H0; inversion H1; subst.
         apply (H6 _ _ _ (as' O O * csm_to_scalar as' O O)); auto. 
         apply Gmult_neq_0.
         apply H2; lia.
         unfold csm_to_scalar.
         apply gcm_nonzero.
         rewrite col_scale_many_scalar; auto.
         apply invr_col_scale_col_scale_many in H0.
         inversion H0; subst.
         apply H5; auto with wf_db.
         intros. 
         unfold csm_to_scalar.
         apply gcm_nonzero.
Qed.         



(* ADD *)

Lemma mat_prop_col_add_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop)  
                                (T : GenMatrix m n) (x y : nat) (c : F),
  invr_col_add P ->
  x <> y -> x < n -> y < n -> 
  P m n (col_add T x y c) -> P m n T.
Proof. intros. 
       inversion H; subst.
       rewrite (col_add_inv _ _ _ _ _ _ T x y c); try easy. 
       apply H4; try easy. 
Qed.

Lemma mat_prop_col_add_many_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                     (T : GenMatrix m n) (as' : Vector n) (col : nat),
  invr_col_add P ->
  col < n -> as' col 0 = 0 -> 
  P m n (col_add_many T as' col) -> P m n T.
Proof. intros. 
       apply invr_col_add_col_add_many in H.
       inversion H; subst. 
       rewrite (col_add_many_inv _ _ _ _ _ _ T as' col); try easy.
       apply H3; try easy. 
       unfold scale; rewrite H1.
       ring.
Qed.

Lemma mat_prop_col_add_each_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                     (T : GenMatrix m n) (col : nat) (as' : GenMatrix 1 n),
  invr_col_add P ->
  col < n -> WF_GenMatrix as' -> 
  P m n (col_add_each T (make_col_val as' col 0) col) -> P m n T.
Proof. intros. 
       apply invr_col_add_col_add_each in H.
       inversion H; subst. 
       erewrite (col_add_each_inv _ _ _ _ _ _ _ as' col); try easy.
       apply H3; try easy.
       auto with wf_db.
Qed.






(** * We can now define some invariants for Determinant *)

(* I use n and m here so that I can take advantage of the above machinery *)
Definition det_neq_0 {m n} (A : GenMatrix m n) : Prop :=
  n = m /\ @Determinant F _ _ _ _ n A <> 0.

Definition det_eq_c (c : F) {m n} (A : GenMatrix m n) : Prop :=
  n = m /\ @Determinant _ _ _ _ _ n A = c.


Lemma det_neq_0_swap_invr : invr_col_swap (@det_neq_0).
Proof. apply invr_swap; intros.  
       destruct H1; subst. 
       split; auto.
       bdestruct (x =? y); subst. 
       - rewrite col_swap_same.
         easy. 
       - rewrite Determinant_swap; auto.         
         rewrite Gopp_neg_1.
         unfold not; intros; apply H2.
         apply Gopp_eq_0; easy.
Qed.


Lemma det_neq_0_scale_invr : invr_col_scale (@det_neq_0).
Proof. apply invr_scale; intros.  
       destruct H1; subst. 
       split; auto.
       bdestruct (x <? m).
       - rewrite Determinant_scale; auto. 
         apply Gmult_neq_0; easy. 
       - rewrite Det_make_WF in *; auto.
         assert (H' : (make_WF T) = (make_WF (col_scale T x c))).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, make_WF, col_scale; intros. 
           bdestruct_all; easy. }
         rewrite <- H'; easy. 
Qed.

Lemma det_neq_0_scalar_invr : invr_scalar_cancel (@det_neq_0).
Proof. apply invr_scalar; intros.  
       destruct H0.
       split; auto.
       contradict H1. 
       rewrite H0 in *.
       rewrite (Determinant_scalar _ _ _ _ _ _). 
       rewrite H1; ring.
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
       unfold not; intros; apply H1.
       destruct m. 
       - simpl in *.
         unfold pad1, col_wedge, row_wedge, e_i, scale; simpl.
         rewrite H0; ring.
       - rewrite Det_simplify; auto.
         apply big_sum_0_bounded; intros. 
         destruct x. 
         + rewrite <- get_minor_pad1, H0; simpl; ring. 
         + unfold pad1, col_wedge, row_wedge, e_i, scale; simpl.
           ring.
Qed.

Lemma det_neq_0_pzf : prop_zero_false (@det_neq_0).  
Proof. apply PZF; intros.
       unfold not; intros. 
       destruct H0; subst. 
       eapply col_0_Det_0 in H; auto.
Qed.

Lemma det_0_swap_invr : invr_col_swap (@det_eq_c 0).
Proof. apply invr_swap; intros.  
       unfold det_eq_c in *; destruct H1; subst. 
       split; auto.
       bdestruct (x =? y); subst. 
       - rewrite col_swap_same.
         easy. 
       - rewrite Determinant_swap; auto. 
         rewrite H2; ring. 
Qed.

Lemma det_0_scale_invr : invr_col_scale (@det_eq_c 0).
Proof. apply invr_scale; intros. 
       unfold det_eq_c in *; destruct H1; subst. 
       split; auto.
       bdestruct (x <? m).
       - rewrite Determinant_scale; auto. 
         rewrite H2; ring. 
       - rewrite Det_make_WF in *; auto.
         assert (H' : (make_WF T) = (make_WF (col_scale T x c))).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, make_WF, col_scale; intros. 
           bdestruct_all; easy. }
         rewrite <- H'; easy. 
Qed.

Lemma det_0_scalar_invr : invr_scalar_cancel (@det_eq_c 0).
Proof. apply invr_scalar; intros. 
       destruct H0; split; auto.
       rewrite H0 in *.
       rewrite (Determinant_scalar _ _ _ _ _ _) in H1. 
       apply Gmult_integral in H1.
       destruct H1; auto.
       apply (Gpow_nonzero _ m) in H.
       easy.
Qed.       

Lemma det_c_add_invr : forall (c : F), invr_col_add (@det_eq_c c).
Proof. intros. 
       apply invr_add; intros.  
       unfold det_eq_c in *; destruct H2; subst. 
       split; auto. 
       apply Determinant_col_add; easy.
Qed.

Lemma det_0_pad1_invr : invr_pad1 (@det_eq_c 0).
Proof. apply invr_p; intros. 
       destruct H0; apply eq_add_S in H0; subst. 
       split; auto. 
       destruct m. 
       - simpl in H1.         
         unfold pad1, col_wedge, row_wedge, e_i, scale in H1; 
         simpl in H1. 
         rewrite Gmult_1_r in H1. 
         easy.
       - rewrite Det_simplify in H1; auto.
         assert (H' : (c * Determinant (get_minor (pad1 T c) 0 0) = 0)%G).
         { rewrite <- H1, (big_sum_unique (c * Determinant (get_minor (pad1 T c) 0 0))).  
           easy. 
           exists 0%nat. split; try lia. 
           split. simpl parity. 
           apply f_equal_gen; try apply f_equal; try easy.  
           unfold pad1, col_wedge, row_wedge, e_i, scale. 
           simpl; ring. 
           intros. 
           unfold pad1, col_wedge, row_wedge, e_i, scale. 
           bdestruct (x' =? 0); try lia; simpl; ring. }
         rewrite <- get_minor_pad1 in H'.
         destruct (Geq_dec (Determinant T) 0); try easy. 
         apply (Gmult_neq_0 c _) in n; easy. 
Qed.

Hint Resolve det_neq_0_swap_invr det_neq_0_scale_invr det_neq_0_scalar_invr 
             det_neq_0_add_invr det_neq_0_pad1_invr det_neq_0_pzf : invr_db.
Hint Resolve det_0_swap_invr det_0_scale_invr det_0_scalar_invr 
             det_c_add_invr det_0_pad1_invr : invr_db.

(* now we get these for free! *)
Lemma Determinant_col_add_many : forall (n col : nat) (A : Square n) (as' : Vector n),
  col < n -> as' col 0 = 0 -> 
  Determinant A = Determinant (col_add_many A as' col).
Proof. intros.
       assert (H' := det_c_add_invr (Determinant A)).
       apply invr_col_add_col_add_many in H'. 
       inversion H'; subst. 
       apply (H1 n n col A as') in H; try easy.
       unfold det_eq_c in *.
       destruct H; easy. 
Qed.


Lemma Determinant_col_add_each : forall (n col : nat) (A : Square n) (as' : GenMatrix 1 n),
  col < n -> WF_GenMatrix as' -> as' 0 col = 0 ->
  Determinant A = Determinant (col_add_each A as' col).
Proof. intros. 
       assert (H' := det_c_add_invr (Determinant A)).
       apply invr_col_add_col_add_each in H'. 
       inversion H'; subst.
       assert (H2' := H).
       apply (H2 n n col A as') in H; try easy.
       unfold det_eq_c in *.
       destruct H; rewrite <- H3.
       assert (H4 : (make_col_val as' col 0) = as').
       { apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold make_col_val.
         destruct i; try lia.
         bdestruct_all; subst; easy. }
       rewrite H4; easy.
Qed.


(***********************************************************)
(** * Defining linear independence, and proving lemmas etc... *)
(***********************************************************)


Definition linearly_independent {m n} (T : GenMatrix m n) : Prop :=
  forall (a : Vector n), WF_GenMatrix a -> T × a = Zero -> a = Zero.

Definition linearly_dependent {m n} (T : GenMatrix m n) : Prop :=
  exists (a : Vector n), WF_GenMatrix a /\ a <> Zero /\ T × a = Zero.

Lemma lindep_implies_not_linindep : forall {m n} (T : GenMatrix m n),
  linearly_dependent T -> ~ (linearly_independent T).
Proof. unfold not, linearly_dependent, linearly_independent in *.
       intros. 
       destruct H as [a [H1 [H2 H3]]].
       apply H0 in H1; easy.
Qed.

Lemma not_lindep_implies_linindep : forall {m n} (T : GenMatrix m n),
  ~ (linearly_dependent T) -> linearly_independent T.
Proof. unfold not, linearly_dependent, linearly_independent in *.
       intros. 
       destruct (vec_equiv_dec _ _ _ _ _ a Zero). 
       - apply genmat_equiv_eq; auto with wf_db.
       - assert (H2 : (exists a : Vector n, WF_GenMatrix a /\ a <> Zero /\ T × a = Zero)).
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
       eapply nonzero_vec_nonzero_elem in H1'; try easy.
       destruct H1' as [x H1']. 
       2 : apply R3.
       destruct (Geq_dec (a 0%nat 0%nat) 0).
       + prep_genmatrix_equality. 
         destruct x0. destruct y.
         rewrite e. easy.
         all : apply H1; lia.
       + assert (H'' : ((a 0 0) .* v) x 0 = 0).
         { rewrite <- H'. rewrite H2; easy. }
         unfold scale in H''. 
         assert (H3 : (a 0 0 * v x 0) <> 0%G).
         { apply Gmult_neq_0; easy. }
         easy. 
Qed.

Lemma lin_dep_row : forall {n} (v : GenMatrix 1 (S (S n))),
  WF_GenMatrix v -> linearly_dependent v.
Proof. intros.   
       destruct (Geq_dec (v O O) 0).
       - exists (e_i O).
         split; auto with wf_db.
         split.
         unfold not; intros; apply G1_neq_0'.
         do 2 apply (f_equal_inv O) in H0.
         unfold Zero in H0; rewrite <- H0.
         unfold e_i; bdestruct_all; easy.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv, GMmult, Zero; intros.
         rewrite <- big_sum_extend_l.
         destruct i; try lia.
         rewrite e, Gmult_0_l, Gplus_0_l.
         apply big_sum_0_bounded; intros.
         unfold e_i. 
         bdestruct_all; simpl; ring.
       - exists (fun i j => if (j =? O) && (i <? S (S n)) 
                    then (if (i =? O) 
                          then - (v O 1%nat) 
                          else 
                            (if (i =? 1%nat) 
                             then (v O O) else 0)) 
                          else 0).
         split.
         unfold WF_GenMatrix; intros.
         bdestruct_all; try easy. 
         split.
         contradict n0.
         apply (f_equal_inv 1%nat) in n0; apply (f_equal_inv O) in n0.
         unfold Zero in n0; rewrite <- n0.
         bdestruct_all; easy.
         apply genmat_equiv_eq; auto with wf_db.
         apply WF_mult; auto with wf_db.
         unfold WF_GenMatrix; intros.
         bdestruct_all; try easy. 
         unfold genmat_equiv, GMmult, Zero; intros.
         do 2 rewrite <- big_sum_extend_l.
         bdestruct_all; simpl.
         destruct i; try lia.
         rewrite Gplus_assoc.
         replace (v O O * - v O 1%nat + v O 1%nat * v O O) with 0 by ring.
         rewrite Gplus_0_l. 
         apply big_sum_0_bounded; intros. 
         bdestruct_all; simpl; ring.
Qed.

  
Lemma invertible_l_implies_linind : forall {n} (A B : Square n),
  A × B = I n -> linearly_independent B.
Proof. intros.
       unfold linearly_independent. intros.
       rewrite <- (GMmult_1_l _ _ _ _ _ _ _ _ a); try easy.
       rewrite <- H.
       rewrite GMmult_assoc, H1.
       erewrite GMmult_0_r; auto.
Qed.

Lemma lin_indep_col_reduce : forall {m n} (A : GenMatrix m (S n)) (i : nat),
  i <= n -> 
  linearly_independent A -> 
  linearly_independent (reduce_col A i).
Proof. intros. 
       unfold linearly_independent in *. 
       intros. 
       apply (row_wedge_zero F R0 _ i). 
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

(* more general than lin_indep_col_reduce *)
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

Lemma lin_dep_col_wedge : forall {m n} (A : GenMatrix m n) (v : Vector m) (i : nat),
  i <= n -> 
  linearly_dependent A -> 
  linearly_dependent (col_wedge A v i).
Proof. intros. 
       unfold linearly_dependent in *. 
       destruct H0 as [a [H0 [H2 H3]]].
       exists (row_wedge a Zero i). 
       split; auto with wf_db. 
       split. unfold not; intros; apply H2.
       apply (row_wedge_zero F R0 _ i).
       auto.
       rewrite wedge_mul; auto.
Qed.

Lemma lin_indep_scale : forall {m n} (A : GenMatrix m n) (c : F),
  c <> 0 ->
  linearly_independent A <-> linearly_independent (c .* A).
Proof. intros.   
       unfold linearly_independent.
       split; intros.
       - rewrite Mscale_mult_dist_l, <- Mscale_mult_dist_r in H2; auto. 
         apply H0 in H2; auto with wf_db.
         prep_genmatrix_equality.
         apply (f_equal_inv x) in H2; apply (f_equal_inv y) in H2.
         unfold Zero, scale in *.
         apply Gmult_integral in H2.
         destruct H2; easy.
       - apply H0; auto.
         rewrite Mscale_mult_dist_l, H2, Mscale_0_r. 
         easy.
Qed.

Lemma lin_dep_scale : forall {m n} (A : GenMatrix m n) (c : F),
  c <> 0 ->
  linearly_dependent A <-> linearly_dependent (c .* A).
Proof. intros.  
       unfold linearly_dependent.
       split; intros.
       - destruct H0 as [a [H0 [H1 H2]]]. 
         exists a; repeat (split; auto).
         rewrite Mscale_mult_dist_l, H2, Mscale_0_r. 
         easy.
       - destruct H0 as [a [H0 [H1 H2]]]. 
         exists a; repeat (split; auto).
         rewrite Mscale_mult_dist_l in H2; auto. 
         prep_genmatrix_equality.
         apply (f_equal_inv x) in H2; apply (f_equal_inv y) in H2.
         unfold Zero, scale in *.
         apply Gmult_integral in H2.
         destruct H2; easy.
Qed.
 
(* proving invr properties for linearly_independent *)
Lemma lin_indep_swap_invr : invr_col_swap (@linearly_independent). 
Proof. apply invr_swap; intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite (@row_swap_inv _ _ _ a x y) in H3.
       rewrite <- swap_preserves_mul in H3; try easy.
       apply H1 in H3; auto with wf_db.
       rewrite (@row_swap_inv _ _ _ a x y).
       rewrite H3.
       prep_genmatrix_equality.
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); easy.
Qed.

Lemma lin_indep_scale_invr : invr_col_scale (@linearly_independent). 
Proof. apply invr_scale; intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite <- scale_preserves_mul in H3; auto.
       apply H1 in H3; auto with wf_db.
       prep_genmatrix_equality.
       apply (f_equal_inv x0) in H3; apply (f_equal_inv y) in H3.
       unfold row_scale, Zero in *.
       bdestruct (x0 =? x); simpl in *; auto.
       apply Gmult_integral in H3.
       destruct H3; try easy.
Qed.

Lemma lin_indep_scalar_cancel : invr_scalar_cancel (@linearly_independent). 
Proof. apply invr_scalar.
       intros. 
       apply (lin_indep_scale T) in H.
       apply H; easy.
Qed.

Lemma lin_indep_add_invr : invr_col_add (@linearly_independent). 
Proof. apply invr_add; intros. 
       unfold linearly_independent in *.
       intros.  
       rewrite <- add_preserves_mul in H4; try easy.
       apply H2 in H4; auto with wf_db.
       rewrite (@row_add_inv _ _ _ _ _ _ _ _ a y x c); try lia.
       rewrite H4.
       prep_genmatrix_equality. 
       unfold row_add, Zero.
       bdestruct (x0 =? y); ring.
Qed.

Lemma lin_indep_pad1_invr : invr_pad1 (@linearly_independent).  
Proof. apply invr_p; intros. 
       unfold linearly_independent in *.
       intros. 
       apply (row_wedge_zero F R0 _ 0).
       apply H0.
       apply WF_row_wedge; auto with wf_db.
       prep_genmatrix_equality. 
       unfold GMmult, Zero. 
       destruct x.
       - apply big_sum_0_bounded; intros.
         unfold pad1, col_wedge, row_wedge, e_i, scale, Zero; simpl.
         bdestruct_all; ring.
       - apply (f_equal_inv x) in H2; apply (f_equal_inv y) in H2.
         unfold Zero in *.
         rewrite <- H2.
         unfold GMmult.
         rewrite <- big_sum_extend_l.
         unfold pad1, col_wedge, row_wedge, e_i, scale, Zero; simpl.
         rewrite Gmult_0_r, Gmult_0_l, Gplus_0_l.
         apply big_sum_eq_bounded; intros.
         repeat (apply f_equal_gen; try lia). 
         all : auto.
Qed.

Lemma lin_indep_pzf : prop_zero_false (@linearly_independent).
Proof. apply PZF; intros.
       unfold not; intros. 
       unfold linearly_independent in *.  
       destruct H as [i [H H1]].
       assert (H2 : T × e_i i = Zero).
       { prep_genmatrix_equality.
         unfold GMmult, Zero, e_i; simpl.  
         apply big_sum_0_bounded; intros. 
         bdestruct_all; simpl; try ring; 
         erewrite <- get_col_conv; subst; simpl.
         rewrite H1; unfold Zero; ring. }
       apply H0 in H2; auto with wf_db.
       apply (f_equal_inv i) in H2; apply (f_equal_inv 0) in H2.  
       unfold e_i, Zero in H2.
       apply G1_neq_0'. 
       rewrite <- H2.
       bdestruct_all; easy.
Qed.

Lemma lin_dep_swap_invr : invr_col_swap (@linearly_dependent).
Proof. apply invr_swap; intros. 
       unfold linearly_dependent in *.
       destruct H1 as [a [H1 [H2 H3]]].
       rewrite (@row_swap_inv _ _ _ a x y) in H3.
       rewrite (@col_swap_inv _ _ _ T x y) in H3. 
       rewrite <- swap_preserves_mul in H3; auto. 
       exists (row_swap a x y).
       split; auto with wf_db.
       split; try easy; unfold not in *.
       intros; apply H2.
       rewrite (row_swap_inv _ a x y).
       rewrite H4.
       prep_genmatrix_equality. 
       unfold Zero, row_swap. 
       bdestruct (x0 =? x); bdestruct (x0 =? y); easy. 
Qed.
 
Lemma lin_dep_scale_invr : invr_col_scale (@linearly_dependent). 
Proof. intros. 
       apply invr_scale; intros. 
       unfold linearly_dependent in *.
       destruct H1 as [a [H1 [H2 H3]]].
       exists (row_scale_many a (make_row_val (make_col_val Zero O c) x 1)). (* a bit inefficient *)
       split; auto with wf_db.
       split. 
       unfold not; intros.
       apply H2.
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv, row_scale_many, make_row_val, make_col_val, Zero in *; intros. 
       apply (f_equal_inv i) in H4; apply (f_equal_inv j) in H4.
       bdestruct (i =? x); bdestruct (0 <? 1); bdestruct (i <? n); simpl in *; try lia.
       rewrite <- H4; ring.
       apply Gmult_integral in H4.
       destruct H4; auto; easy.
       rewrite <- scale_preserves_mul; auto.
       apply (f_equal (scale c)) in H3.
       rewrite <- Mscale_mult_dist_r, Mscale_0_r in H3; auto. 
       rewrite <- H3.
       apply f_equal_gen; auto.
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros.
       unfold row_scale, row_scale_many, make_row_val, make_col_val, scale.
       bdestruct_all; simpl; ring.
Qed.

Lemma lin_dep_scalar_cancel : invr_scalar_cancel (@linearly_dependent). 
Proof. apply invr_scalar.
       intros. 
       apply (lin_dep_scale T) in H.
       apply H; easy.
Qed.

Lemma lin_dep_add_invr : invr_col_add (@linearly_dependent).
Proof. intros.
       apply invr_add; intros. 
       unfold linearly_dependent in *.
       destruct H2 as [a [H2 [H3 H4]]].
       exists (row_add a y x (- c)).
       split; auto with wf_db.
       split. unfold not; intros; apply H3.
       rewrite (row_add_inv _ _ _ _ _ _ a y x (- c)); try lia.
       rewrite H5.
       unfold row_add, Zero.
       prep_genmatrix_equality.
       bdestruct (x0 =? y); simpl; ring. 
       rewrite add_preserves_mul; try easy.
       rewrite <- (col_add_inv _ _ _ _ _ _ T x y c); try lia; easy.
Qed.

Lemma lin_dep_pzt : prop_zero_true (@linearly_dependent).
Proof. intros; apply PZT; intros. 
       unfold linearly_dependent in *; intros. 
       destruct H as [i [H0 H1]].
       exists (e_i i).
       split; auto with wf_db. 
       split. 
       unfold not; intros. 
       apply (f_equal_inv i) in H; apply (f_equal_inv 0) in H.
       apply G1_neq_0'.
       unfold e_i, Zero in H; rewrite <- H. 
       bdestruct_all; easy.
       rewrite <- matrix_by_basis; easy.
Qed.

Hint Resolve lin_indep_swap_invr lin_indep_scale_invr lin_indep_scalar_cancel
             lin_indep_add_invr lin_indep_pad1_invr lin_indep_pzf : invr_db.
Hint Resolve lin_dep_swap_invr lin_dep_scale_invr lin_dep_scalar_cancel 
             lin_dep_add_invr lin_dep_pzt : invr_db.


(*****************************************************************************************)
(** * defining a new type of matrix which we will show is the lin_indep/adj_invertible matrices *)
(*****************************************************************************************)

Inductive op_to_I {n : nat} : Square n -> Prop :=
| otI_I: op_to_I (I n)
| otI_swap : forall (A : Square n) (x y : nat), x < n -> y < n -> 
                                         op_to_I A -> op_to_I (col_swap A x y)
| otI_scale : forall (A : Square n) (x : nat) (c : F), x < n -> c <> 0 -> 
                                         op_to_I A -> op_to_I (col_scale A x c)
| otI_add : forall (A : Square n) (x y : nat) (c : F), x < n -> y < n -> x <> y -> 
                                         op_to_I A -> op_to_I (col_add A x y c).


Lemma op_to_I_WF : forall {n} (A : Square n),
  op_to_I A -> WF_GenMatrix A.
Proof. intros.  
       apply op_to_I_ind; auto with wf_db.
Qed.

Hint Resolve op_to_I_WF : wf_db.


(* this is useful since we can easily show that every op_to_I matrix has this prop *)
Definition otI_multiplicative {n} (A : Square n) : Prop := 
  forall (B : Square n), (op_to_I B -> op_to_I (B × A)).

Lemma otI_implies_otI_multiplicative : forall {n} (A : Square n),
  op_to_I A -> otI_multiplicative A. 
Proof. intros.   
       apply op_to_I_ind; auto. 
       - unfold otI_multiplicative; intros.
         rewrite GMmult_1_r; auto with wf_db.
       - unfold otI_multiplicative; intros. 
         erewrite col_swap_mult_r; auto with wf_db.
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
Lemma otI_Mmult : forall {n} (A B : Square n),
  op_to_I A -> op_to_I B ->
  op_to_I (A × B).
Proof. intros. 
       apply otI_implies_otI_multiplicative in H0.
       unfold otI_multiplicative in H0.
       apply H0; easy. 
Qed.

(* using a similar technique, will show that op_to_I is preserved by pad1 *) 
Definition otI_pad1ed {n} (A : Square n) : Prop := 
  forall (c :  F), (c <> 0 -> op_to_I (pad1 A c)).

Lemma otI_implies_otI_pad1ed : forall {n} (A : Square n),
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
         auto.
       - intros. 
         unfold otI_pad1ed in *; intros. 
         rewrite pad1_col_add. 
         apply otI_add; try lia; try easy. 
         apply H4; easy. 
         auto.
Qed.

Lemma otI_pad1 : forall {n} (A : Square n) (c : F),
  c <> 0 -> op_to_I A -> 
  op_to_I (pad1 A c).
Proof. intros. 
       apply otI_implies_otI_pad1ed in H0.
       unfold otI_pad1ed in H0.
       apply H0; easy. 
Qed.

Lemma otI_lin_indep : forall {n} (A : Square n),
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

Lemma otI_det_neq_0 : forall {n} (A : Square n),
  op_to_I A -> det_neq_0 A. 
Proof. intros. 
       apply op_to_I_ind; auto. 
       - unfold det_neq_0; intros. 
         split; auto.
         rewrite Det_I; auto.
         apply G1_neq_0'.
       - intros. 
         apply_mat_prop det_neq_0_swap_invr. 
         apply H5; auto. 
       - intros. 
         apply_mat_prop det_neq_0_scale_invr.
         apply H5; auto. 
       - intros. 
         apply_mat_prop det_neq_0_add_invr.
         apply H6; auto. 
Qed.

(* need alternate def to deal with broader n <> m case *)
Definition op_to_I' {m n} (A : GenMatrix n m) :=
  n = m /\ @op_to_I n A.

Lemma otI_equiv_otI' : forall {n} (A : Square n),
  op_to_I' A <-> op_to_I A.
Proof. intros. split. 
       - intros. 
         destruct H; easy. 
       - intros. 
         split; easy. 
Qed.

Lemma otI'_scale_invr : invr_col_scale (@op_to_I').
Proof. apply invr_scale; intros. 
       destruct H1; split; try easy; subst. 
       apply otI_scale; easy. 
Qed.

Lemma otI_col_scale_many : forall (n : nat) (A : Square n) (as' : Vector n),
  WF_GenMatrix A ->
  (forall i, i < n -> as' O i <> 0) ->
  op_to_I A -> op_to_I (col_scale_many A as').
Proof. intros. 
       assert (H' := otI'_scale_invr).
       apply invr_col_scale_col_scale_many in H'. 
       inversion H'; subst.
       apply (H2 n n A as'); auto.
       easy.
Qed.

Lemma otI'_add_invr : invr_col_add (@op_to_I').
Proof. apply invr_add; intros. 
       destruct H2; split; try easy; subst. 
       apply otI_add; easy. 
Qed.

Lemma otI_col_add_many : forall (n col : nat) (A : Square n) (as' : Vector n),
  col < n -> as' col 0 = 0 -> 
  op_to_I A -> op_to_I (col_add_many A as' col).
Proof. intros. 
       assert (H' := otI'_add_invr).
       apply invr_col_add_col_add_many in H'. 
       inversion H'; subst. 
       apply (H2 n n col A as') in H; try easy. 
       destruct H; easy. 
Qed.

Lemma otI_col_add_each : forall (n col : nat) (A : Square n) (as' : GenMatrix 1 n),
  col < n -> WF_GenMatrix as' -> as' 0 col = 0 ->  
  op_to_I A -> op_to_I (col_add_each A as' col).
Proof. intros. 
       assert (H' := otI'_add_invr).
       apply invr_col_add_col_add_each in H'. 
       inversion H'; subst. 
       assert (H0' := H).
       apply (H3 n n col A as') in H; try easy. 
       assert (H4 : (make_col_val as' col 0) = as').
       { apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         unfold make_col_val.
         destruct i; try lia.
         bdestruct_all; subst; easy. }
       rewrite H4 in *.
       destruct H; easy. 
Qed.


(** * Building up machinery to reduce first row to e_i *)


(* we eventually want to consider the vector (a0,v) *)
Definition get_equalizing_scalars {m n} (v : GenMatrix m (S (S n))) : GenMatrix 1 (S (S n)) := 
  fun i j => if (i =? 0) && (j <? (S (S n)))
          then if (j =? 0)
               then 1
               else (v O O) * 
                      (@get_common_multiple _ _ _ _ _ m n (reduce_col (reduce_col v j) O))
          else 0.

Definition get_cae_scalars {m n} (v : GenMatrix m (S (S n))) : GenMatrix 1 (S (S n)) :=
  fun i j => if (i =? 0) && (j <? (S (S n)))
          then if (j =? 0)
               then 0 
               else match (Geq_dec (v O j) 0) with
                    | left _ => 0
                    | right _ => 
                        - (@get_common_multiple _ _ _ _ _ m (S n) (reduce_col v O))
                    end
          else 0.



Definition col_ops_row_to_e_i {m n} (T : GenMatrix m (S (S n))) : GenMatrix m (S (S n)) :=
  match (genmat_equiv_dec _ _ _ _ _ (get_row T O) Zero) with
  | left _ => T
  | right _ => (col_add_each 
                 (col_scale_many 
                    (col_swap T O (get_nonzero_entry (get_row T O)⊤)) 
                    (get_equalizing_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))))
                 (get_cae_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))) O)
  end.
  
Definition row_ops_col_to_e_i {m n} (T : GenMatrix (S (S m)) n) : GenMatrix (S (S m)) n :=
  row_add_each (row_scale_many T (get_equalizing_scalars T⊤))⊤ (get_cae_scalars T⊤)⊤ O.

Definition col_ops_to_pad1 {m n} (T : GenMatrix (S (S m)) (S (S n))) : GenMatrix (S (S m)) (S (S n)) := 
  row_ops_col_to_e_i (col_ops_row_to_e_i T).



Lemma WF_get_equalizing_scalars : forall {m n} (a0 : F) (v : GenMatrix m (S (S n))),
  WF_GenMatrix (get_equalizing_scalars v).
Proof. intros.
       unfold WF_GenMatrix, get_equalizing_scalars; intros.
       bdestruct_all; auto.
Qed.       

Lemma WF_get_cae_scalars : forall {m n} (v : GenMatrix m (S (S n))),
  WF_GenMatrix (get_cae_scalars v).
Proof. intros.
       unfold WF_GenMatrix, get_cae_scalars; intros.
       bdestruct_all; auto.
Qed.   

Lemma WF_col_ops_row_to_e_i : forall {m n} (T : GenMatrix m (S (S n))),
  WF_GenMatrix T ->
  WF_GenMatrix (col_ops_row_to_e_i T).
Proof. intros. 
       unfold col_ops_row_to_e_i.
       destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero); auto.
       assert (H' : get_row T O <> Zero).
       { unfold not; intros; apply n0.
         unfold genmat_equiv; intros.
         rewrite H0; easy. }
       apply WF_col_add_each.
       apply WF_col_scale_many.
       apply WF_col_swap; try lia; auto.
       apply get_nonzero_entry_correct_row; auto with wf_db.
       apply WF_get_cae_scalars.
Qed.

Lemma WF_row_ops_col_to_e_i : forall {m n} (T : GenMatrix (S (S m)) n),
  WF_GenMatrix T ->
  WF_GenMatrix (row_ops_col_to_e_i T).
Proof. intros. 
       unfold row_ops_col_to_e_i.
       apply WF_row_add_each; auto with wf_db.
       assert (H' := WF_get_cae_scalars (T⊤)).  
       Set Printing All. 


n m).



Hint Resolve WF_get_equalizing_scalars WF_get_cae_scalars WF_col_ops_row_to_e_i : wf_db.



Lemma get_equalizing_scalars_nonzero : forall {m n} (v : GenMatrix m (S (S n))),
  v O O <> 0 ->
  (forall i, i < (S (S n)) -> (get_equalizing_scalars v) O i <> 0).
Proof. intros. 
       unfold get_equalizing_scalars.
       bdestruct_all; simpl.
       apply G1_neq_0'.
       apply Gmult_neq_0; auto.
       apply gcm_nonzero.
Qed.



(* Now we prove some lemmas about col_ops_row_to_e_i *)
(* TODO: think of better names for these lemmas *)


Opaque get_common_multiple. 


Lemma col_ops_row_to_e_i_base : forall {m n} (T : GenMatrix m (S (S n))), 
  WF_GenMatrix T ->
  get_row 
    (col_add_each 
       (col_scale_many T (get_equalizing_scalars T))
       (get_cae_scalars T) O) 
    O 
  = (T O O) .* (e_i O)⊤.
Proof. intros.   
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros.
       unfold get_equalizing_scalars, get_row, col_add_each,
         reduce_row, col_scale_many, GMplus, GMmult, get_col.
       bdestruct_all; simpl; subst.
       unfold scale, e_i, transpose, get_cae_scalars.
       bdestruct_all; auto; simpl; ring.
       unfold scale, e_i, transpose, get_cae_scalars. 
       destruct (Geq_dec (T 0%nat j) 0%G); simpl. 
       + bdestruct_all; simpl.
         destruct (Geq_dec (T 0%nat j) 0%G); try easy.
         rewrite e.
         ring.
       + bdestruct_all; simpl.
         rewrite <- reduce_col_2x; try lia.  
         rewrite (gcm_reduce_col_nonzero _ _ _ _ _ _ (reduce_col T 0) (j - 1)); try lia.
         replace (reduce_col T O O (j - 1)%nat) with (T O j).
         ring.
         all : unfold reduce_col; bdestruct_all.
         all : replace (1 + (j - 1))%nat with j by lia.
         all : easy.
Qed.

Lemma col_ops_row_to_e_i_O : forall {m n} (T : GenMatrix m (S (S n))), 
  WF_GenMatrix T ->
  get_row T 0 <> Zero ->
  (col_add_each 
     (col_scale_many 
        (col_swap T O (get_nonzero_entry (get_row T O)⊤)) 
        (get_equalizing_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))))
     (get_cae_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))) O) O O <> 0.
Proof. intros. 
       unfold get_equalizing_scalars, get_row, col_add_each,
         reduce_row, col_scale_many, GMplus, GMmult, get_col.
       bdestruct_all; subst.
       unfold scale, e_i, transpose, get_cae_scalars.
       bdestruct_all; auto. 
       unfold not; intros. 
       apply (get_nonzero_entry_correct_row F _ _ _ _ (get_row T 0)); auto with wf_db.
       rewrite <- H5.
       simpl.
       rewrite Gmult_0_r, 2 Gplus_0_r, Gmult_1_l.
       unfold get_row, col_swap, transpose; easy.
Qed.

Lemma col_ops_row_to_e_i_Si : forall {m n} (T : GenMatrix m (S (S n))) (i : nat), 
  WF_GenMatrix T ->
  get_row T 0 <> Zero ->
  (col_add_each 
     (col_scale_many 
        (col_swap T O (get_nonzero_entry (get_row T O)⊤)) 
        (get_equalizing_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))))
     (get_cae_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))) O) O (S i) = 0.
Proof. intros. 
       erewrite <- get_row_conv.
       rewrite col_ops_row_to_e_i_base.
       unfold col_swap, get_row, transpose, scale, e_i.
       bdestruct_all; simpl; try ring.
       apply WF_col_swap; try lia; auto.
       apply get_nonzero_entry_correct_row; auto with wf_db.
Qed.

Lemma col_ops_row_to_e_i_nonzero : forall {m n} (T : GenMatrix m (S (S n))) (i : nat), 
  WF_GenMatrix T ->
  get_row T 0 <> Zero ->
  (col_ops_row_to_e_i T) O O <> 0.
  intros. 
  unfold col_ops_row_to_e_i in *.
  destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero); auto.
  - contradict H0.
    apply genmat_equiv_eq; auto with wf_db.
  - unfold not; intros; eapply col_ops_row_to_e_i_O; try apply H1; auto.
Qed.

Lemma col_ops_row_to_e_i_zero : forall {m n} (T : GenMatrix m (S (S n))) (i : nat), 
  WF_GenMatrix T ->
  (col_ops_row_to_e_i T) O (S i) = 0.
  intros. 
  unfold col_ops_row_to_e_i in *.
  destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero); auto.
  - bdestruct (S i <? S (S n)).
    erewrite <- get_row_conv.
    rewrite g; auto.
    rewrite H; auto.
  - rewrite col_ops_row_to_e_i_Si; auto.
    unfold not; intros; apply n0.
    rewrite H0.
    easy.
Qed.


Lemma col_ops_row_to_e_i_invr : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                  (T : GenMatrix m (S (S n))),
  WF_GenMatrix T ->
  invr_col_swap P -> 
  invr_col_scale P ->
  invr_scalar_cancel P ->
  invr_col_add P ->
  P m (S (S n)) (col_ops_row_to_e_i T) ->
  P m (S (S n)) T.
Proof. intros. 
       unfold col_ops_row_to_e_i in *.
       destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero); auto.
       assert (H' : get_row T 0 <> Zero). 
       { contradict n0.
         rewrite n0; easy. }
       apply (mat_prop_col_swap_conv _ _ 0 (get_nonzero_entry (get_row T 0) ⊤)); 
         auto with invr_db; try lia.
       apply get_nonzero_entry_correct_row; auto with wf_db.
       apply (mat_prop_col_scale_many_conv _ _ 
            (get_equalizing_scalars (col_swap T 0 (get_nonzero_entry (get_row T 0) ⊤))));
         auto with wf_db; auto with invr_db.
       apply WF_col_swap; try lia; auto.
       apply get_nonzero_entry_correct_row; auto with wf_db.
       intros. 
       apply get_equalizing_scalars_nonzero; auto.
       unfold col_swap; bdestruct_all.
       rewrite <- (get_row_conv F R0).
       apply get_nonzero_entry_correct_row; auto with wf_db. 
       apply (mat_prop_col_add_each_conv _ _ O 
             (get_cae_scalars (col_swap T 0 (get_nonzero_entry (get_row T 0) ⊤)))); 
         auto with wf_db; auto with invr_db.
       replace (make_col_val 
                  (get_cae_scalars (col_swap T O (get_nonzero_entry (get_row T O) ⊤))) 
                  O 0) with
         (get_cae_scalars (col_swap T O (get_nonzero_entry (get_row T O) ⊤))).
       easy.
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros. 
       unfold make_col_val.
       bdestruct_all; simpl; auto; subst.
       unfold get_cae_scalars; simpl.
       bdestruct_all; easy.
Qed.


Lemma col_ops_row_to_e_i_lin_dep : forall {m n} (T : GenMatrix m (S (S n))),
  WF_GenMatrix T ->
  linearly_dependent (col_ops_row_to_e_i T) ->
  linearly_dependent T.
Proof. intros. 
       apply_mat_prop lin_dep_swap_invr.
       apply_mat_prop lin_dep_scale_invr.
       apply_mat_prop lin_dep_add_invr.
       apply_mat_prop lin_dep_scalar_cancel.
       apply col_ops_row_to_e_i_invr; auto.
Qed.       

       
Theorem gt_dim_lindep : forall {m n} (T : GenMatrix m n),
  WF_GenMatrix T -> 
  m < n ->
  linearly_dependent T.
Proof. induction m.
       - intros.
         erewrite WF0_Zero_l; auto.
         apply_mat_prop lin_dep_pzt.
         apply H2.
         exists 0; split; auto.
         prep_genmatrix_equality.
         unfold get_col; bdestruct_all; easy.
       - intros. do 2 (destruct n; try lia).
         apply col_ops_row_to_e_i_lin_dep; auto.
         destruct (IHm (S n) (reduce_row (reduce_col (col_ops_row_to_e_i T) O) O))
           as [v [H1 [H2 H3]]]; auto with wf_db.
         exists (row_wedge v Zero O).
         split; auto with wf_db.
         split.
         contradict H2.
         prep_genmatrix_equality.
         apply (f_equal_inv (S x)) in H2; apply (f_equal_inv y) in H2.
         unfold Zero in *; rewrite <- H2.
         unfold row_wedge; bdestruct_all.
         rewrite Sn_minus_1; easy.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         rewrite (reduce_wedge_split_0 _ _ (col_ops_row_to_e_i T)); auto with wf_db.
         rewrite wedge_mul; try lia.
         destruct i.
         + unfold Zero, GMmult.
           apply big_sum_0_bounded; intros.
           unfold reduce_col.
           bdestruct_all; simpl.
           rewrite col_ops_row_to_e_i_zero; auto; ring.
         + apply (f_equal_inv i) in H3; apply (f_equal_inv j) in H3.
           unfold Zero in *; rewrite <- H3.
           destruct j; try lia.
           unfold reduce_col, reduce_row, GMmult.
           apply big_sum_eq_bounded; intros.
           bdestruct_all.
           easy.
Qed.

     



(**********************************************)
(** *  Now we prove more properties of invariants *) 
(**********************************************)

         
(** a case for when we consider (Mat -> Prop)s that are the same as lin_indep, invertible, 
   etc... these props will satisfy 'prop_zero_false P' *)
Lemma mpr_step1_pzf_P : forall {n} (A : Square (S n)) (P : forall m o, GenMatrix m o -> Prop),
  invr_col_add P -> invr_col_scale P -> 
  prop_zero_false P -> 
  WF_GenMatrix A -> P (S n) (S n) A ->
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
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

(** a different case for when we consider (Mat -> Prop)s that are 
   the same as lin_dep, not_invertible, etc... *)
Lemma mrp_step1_pzt_P0 : forall {n} (A : Square (S n)) (P P0: forall m o, GenMatrix m o -> Prop),
  invr_col_add P -> invr_col_scale P -> 
  invr_col_add P0 -> prop_zero_true P0 -> 
  WF_GenMatrix A -> P (S n) (S n) A ->
  (exists B : Square (S n), op_to_I B /\ P (S n) (S n) (A × B) /\
                       (exists i, i < (S n) /\ get_vec i (A × B) = e_i 0)) \/ P0 (S n) (S n) A.
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

(** in both cases, we can use mrp_step2 when we get that (exists i, ... ) *) 
Lemma mpr_step2 : forall {n} (A : Square (S n)) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_add P -> invr_col_swap P -> 
  WF_GenMatrix A -> P (S n) (S n) A ->  
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
                                (make_col_val 0 (-C1 .* (get_row 0 (col_swap A 0 i)))) 
                                (I (S n)))).
       split. 
       apply otI_Mmult.
       rewrite <- col_row_swap_invr_I; try lia. 
       apply otI_swap; try lia; apply otI_I.
       rewrite row_many_col_each_invr_I; try lia; auto.
       apply otI_col_add_each; try lia; auto with  wf_db.
       all : try (apply WF_make_col_val; apply WF_scale; 
         apply WF_get_row; apply WF_col_swap; try lia; auto).  
       apply otI_I.
       rewrite <- Mmult_assoc. 
       rewrite <- col_swap_mult_r; try lia; try easy.
       rewrite <- col_add_each_mult_r; try lia; try easy.
       split; try easy.
       apply pad1ed_matrix; intros. 
       4 : apply WF_make_col_val.
       all : try (apply WF_scale; apply WF_get_row).  
       all : try (apply WF_col_swap; try lia; easy).
       destruct H7 as [H7 H8].
       destruct H7. 
       + unfold col_add_each, make_col_val, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale.
         rewrite H7 in *.
         bdestruct (j =? 0); try lia. 
         assert (H' : (get_vec i A) 0 0 = C1).
         { rewrite H4. easy. }
         simpl. bdestruct (j =? i); try lia. 
         all : unfold get_vec in H'; simpl in H'.
         all : rewrite H'; lca. 
       + unfold col_add_each, make_col_val, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale.
         rewrite H7 in *; simpl. 
         destruct i0; try lia.
         assert (H' : (get_vec i A) (S i0) 0 = C0).
         { rewrite H4. easy. }
         unfold get_vec in H'; simpl in H'. 
         rewrite H'; lca. 
       + unfold col_add_each, make_col_val, get_row, col_swap, 
         Mplus, Mmult, get_vec, scale; simpl.
         assert (H' : (get_vec i A) 0 0 = C1).
         { rewrite H4. easy. }
         unfold get_vec in H'; simpl in H'.
         rewrite H'; lca.
       + easy. 
Qed.    


(** these two lemmas allow us to reduce our study of Square (S n) to Square n, allowing 
   us to induct on n. Then, 'invr_pad1 P' allows us to jump from the n case to (S n) *) 
Lemma mat_prop_reduce_pzf_P : forall {n} (A : Square (S n)) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> prop_zero_false P ->   
  invr_pad1 P -> 
  WF_GenMatrix A -> P (S n) (S n) A -> 
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

Lemma mat_prop_reduce_pzt_P0 : forall {n} (A : Square (S n)) (P P0 : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_col_add P -> 
  invr_pad1 P -> 
  invr_col_add P0 -> prop_zero_true P0 -> 
  WF_GenMatrix A -> P (S n) (S n) A -> 
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


(** now, we prove some theorems with these powerful lemmas *)
Theorem invr_P_implies_invertible_r : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
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

Definition Minv {n : nat} (A B : Square n) : Prop := A × B = I n /\ B × A = I n.


Definition invertible {n : nat} (A : Square n) : Prop :=
  exists B, Minv A B.


Lemma Minv_unique : forall (n : nat) (A B C : Square n), 
                      WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix C ->
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
  WF_GenMatrix A -> WF_GenMatrix B ->  
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
    WF_GenMatrix A -> WF_GenMatrix B -> 
    A × B = I n -> Minv A B.
Proof.
  intros n A B H H0 H1. 
  unfold Minv. split; trivial.
  apply Minv_flip; 
  assumption.
Qed.

Lemma Minv_right : forall (n : nat) (A B : Square n), 
    WF_GenMatrix A -> WF_GenMatrix B -> 
    B × A = I n -> Minv A B.
Proof.
  intros n A B H H0. 
  unfold Minv. split; trivial.
  apply Minv_flip;
  assumption.
Qed.


Corollary lin_indep_invertible : forall (n : nat) (A : Square n),
  WF_GenMatrix A -> (linearly_independent A <-> invertible A).
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
  WF_GenMatrix A -> WF_GenMatrix B -> 
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
(** * We finish proving lemmas about invarients *)
(*********************************************)

(** Finally, we show that if all 6 nice properties are true about two (Mat -> Prop)s, then
   they are equivalent on well formed matrices *)
Theorem invr_P_equiv_otI : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
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
Theorem invr_P_implies_otI_weak : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
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

Corollary lin_indep_det_neq_0 : forall {n} (A : Square n),
  WF_GenMatrix A -> (linearly_independent A <-> det_neq_0 A).
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
  WF_GenMatrix A -> (linearly_dependent A <-> det_eq_c C0 A).
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
           rewrite Sn_minus_1; easy. 
           apply WF_row_wedge; try lia;  auto with wf_db.
           rewrite <- Mmult_assoc, <- H2.
           rewrite pad1_row_wedge_mult, H5.
           prep_matrix_equality.
           unfold row_wedge. 
           bdestruct_all; easy. 
Qed.


Corollary lin_dep_indep_dec : forall {n} (A : Square n),
  WF_GenMatrix A -> { linearly_independent A } + { linearly_dependent A }. 
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
(** * we define another set of invariants to help show that Det A × Det B = Det (A × B) *)
(*************************************************************************************)

Definition Det_mult_comm_l (n m : nat) (A : GenMatrix n m) :=
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
Proof. intros n A. 
       apply invr_P_implies_otI_weak.
       apply_mat_prop Dmc_swap_invr.
       apply_mat_prop Dmc_scale_invr.
       apply_mat_prop Dmc_add_invr.
       apply Dmc_I. 
Qed. 

Lemma Determinant_multiplicative_WF : forall {n} (A B : Square n), 
  WF_GenMatrix A -> WF_GenMatrix B -> 
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

