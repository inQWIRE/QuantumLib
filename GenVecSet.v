

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

Lemma mat_prop_scalar_cancel_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                       (T : GenMatrix m n) (c : F),
  WF_GenMatrix T ->
  c <> 0 ->
  invr_col_scale P ->
  P m n T -> P m n (c .* T).
Proof. intros. 
       replace (c .* T) with (col_scale_many T (fun i j => c)).
       apply invr_col_scale_col_scale_many in H1.
       inversion H1.
       apply H3; auto.
       unfold col_scale_many, scale; easy.
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


Lemma prop_zero_false_get_nonzero : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop)  
                                      (T : GenMatrix m n) (col : nat),
  WF_GenMatrix T -> col < n ->
  prop_zero_false P ->
  P m n T ->
  (forall i, (S i) < m -> T (S i) col = 0) -> 
  T O col <> 0.
Proof. intros. 
       inversion H1; subst.
       unfold not; intros; apply (H4 m n T); auto.
       exists col; split; auto.
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros. 
       unfold get_col, Zero.
       bdestruct_all.
       destruct i.
       rewrite H5; auto.
       apply H3.
       auto.
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
       - rewrite Determinant_col_scale; auto. 
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
       destruct H as [i [H H0]].
       eapply col_0_Det_0 in H0; auto.
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
       - rewrite Determinant_col_scale; auto. 
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


Lemma undo_scalar_zero : forall {m n} (T : GenMatrix m n) (c : F),
  c <> 0 ->
  c.* T = Zero ->
  T = Zero.
Proof. intros.   
       prep_genmatrix_equality.
       apply (f_equal_inv x) in H0; apply (f_equal_inv y) in H0.
       unfold scale, Zero in *.
       apply Gmult_integral in H0.
       destruct H0; easy.
Qed.

Lemma undo_scalar : forall {m n} (T1 T2 : GenMatrix m n) (c : F),
  c <> 0 ->
  c .* T1 = c .* T2 ->
  T1 = T2.
Proof. intros.   
       prep_genmatrix_equality.
       apply (f_equal_inv x) in H0; apply (f_equal_inv y) in H0.
       unfold scale in *.
       apply Gmult_cancel_l in H0; auto.
Qed.


Lemma invertible_l_implies_linind : forall {n} (A B : Square n) (c : F),
  c <> 0 ->
  A × B = c .* I n -> linearly_independent B.
Proof. intros.
       unfold linearly_independent. intros.
       rewrite <- (GMmult_1_l _ _ _ _ _ _ _ _ a); try easy.
       apply (undo_scalar_zero _ c); auto.
       rewrite <- Mscale_mult_dist_l, <- H0.
       rewrite GMmult_assoc, H2.
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

Lemma lin_dep_pad1 : forall {m n} (A : GenMatrix m n) (c : F),
  linearly_dependent A ->
  linearly_dependent (pad1 A c).
Proof. intros. 
       destruct H as [v [H [H0 H1]]].
       exists (row_wedge v Zero O); split.
       auto with wf_db. split.
       contradict H0.
       prep_genmatrix_equality.
       apply (f_equal_inv (S x)) in H0; apply (f_equal_inv y) in H0.
       unfold Zero, row_wedge in *; rewrite <- H0.
       bdestruct_all.
       rewrite Sn_minus_1; easy.
       prep_genmatrix_equality.
       destruct x.
       unfold GMmult, pad1, row_wedge, col_wedge, e_i, scale, Zero.
       apply big_sum_0_bounded; intros.
       bdestruct_all; try ring.
       apply (f_equal_inv x) in H1; apply (f_equal_inv y) in H1.
       unfold Zero in *; rewrite <- H1.
       unfold GMmult.
       rewrite <- big_sum_extend_l.
       rewrite <- Gplus_0_l.
       apply f_equal_gen; try apply f_equal.
       unfold pad1, col_wedge, row_wedge, scale, e_i.
       bdestruct_all; simpl; ring.
       apply big_sum_eq_bounded; intros. 
       rewrite pad1_conv.
       unfold row_wedge.
       bdestruct_all.
       rewrite Sn_minus_1; easy.
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
| otI_scalar_cancel : forall (A : Square n) (c : F), c <> 0 ->
                                         op_to_I (c .* A) -> op_to_I A
| otI_add : forall (A : Square n) (x y : nat) (c : F), x < n -> y < n -> x <> y -> 
                                         op_to_I A -> op_to_I (col_add A x y c).

 
Lemma op_to_I_WF : forall {n} (A : Square n),
  op_to_I A -> WF_GenMatrix A.
Proof. intros.  
       apply op_to_I_ind; auto with wf_db.
       intros. 
       unfold WF_GenMatrix, scale in *; intros.
       apply H2 in H3.
       apply Gmult_integral in H3.
       destruct H3; easy.
Qed.

Hint Resolve op_to_I_WF : wf_db.
 


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

Lemma otI'_swap_invr : invr_col_swap (@op_to_I').
Proof. apply invr_swap; intros. 
       destruct H1; split; try easy; subst.
       apply otI_swap; easy.
Qed.

Lemma otI'_scale_invr : invr_col_scale (@op_to_I').
Proof. apply invr_scale; intros. 
       destruct H1; split; try easy; subst. 
       apply otI_scale; easy. 
Qed.

Lemma otI'_scalar_cancel : invr_scalar_cancel (@op_to_I').
Proof. apply invr_scalar; intros. 
       destruct H0; split; try easy; subst. 
       eapply otI_scalar_cancel; try apply H; easy.
Qed.

Lemma otI'_add_invr : invr_col_add (@op_to_I').
Proof. apply invr_add; intros. 
       destruct H2; split; try easy; subst. 
       apply otI_add; easy. 
Qed.

Hint Resolve otI'_swap_invr otI'_scale_invr otI'_scalar_cancel otI'_add_invr : invr_db.

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

Lemma otI_scalar : forall {n} (A : Square n) (c : F),
  c <> 0 ->
  op_to_I A -> op_to_I (c .* A).
Proof. intros.
       apply otI_equiv_otI' in H0.
       apply (otI_col_scale_many _ A (fun i j => c)); auto.
       all : apply (@otI_equiv_otI' n) in H0.
       apply op_to_I_WF.
       all : easy.
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

Lemma otI_mult_r_invr : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                  (A : GenMatrix m n) (B : Square n),
  WF_GenMatrix A ->
  op_to_I B -> 
  invr_col_swap P -> 
  invr_col_scale P ->
  invr_scalar_cancel P ->
  invr_col_add P ->
  P m n A ->
  P m n (A × B).
Proof. intros.
       apply (op_to_I_ind _ (fun B => P m n (A × B))); auto. 
       - rewrite GMmult_1_r; auto.
       - intros. 
         erewrite col_swap_mult_r, <- GMmult_assoc, <- col_swap_mult_r; auto with wf_db.
         inversion H1.
         apply H10; auto.
       - intros. 
         erewrite col_scale_mult_r, <- GMmult_assoc, <- col_scale_mult_r; auto with wf_db.
         inversion H2.
         apply H10; auto.
       - intros. 
         inversion H3.
         apply (H9 _ _ _ c); auto.
         rewrite <- Mscale_mult_dist_r; auto.
       - intros. 
         erewrite col_add_mult_r, <- GMmult_assoc, <- col_add_mult_r; auto with wf_db.
         inversion H4.
         apply H11; auto.
Qed.

Lemma otI_mult_r_invr_conv : forall {m n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                               (A : GenMatrix m n) (B : Square n),
  WF_GenMatrix A ->
  op_to_I B -> 
  invr_col_swap P -> 
  invr_col_scale P ->
  invr_scalar_cancel P ->
  invr_col_add P ->
  P m n (A × B) -> 
  P m n A.
Proof. intros m n P A B WFA otiB H H0 H1 H2.
       apply (op_to_I_ind _ (fun B => P m n (A × B) -> P m n A)); auto; intros.
       - rewrite GMmult_1_r in H3; auto.
       - erewrite col_swap_mult_r, <- GMmult_assoc, <- col_swap_mult_r in H7; auto with wf_db.
         apply H6.
         apply mat_prop_col_swap_conv in H7; auto.
       - erewrite col_scale_mult_r, <- GMmult_assoc, <- col_scale_mult_r in H7; auto with wf_db.
         apply mat_prop_col_scale_conv in H7; auto with wf_db.
       - apply H5.
         rewrite Mscale_mult_dist_r; auto.
         apply mat_prop_scalar_cancel_conv; auto with wf_db.
         apply WF_mult; auto.
         inversion H1; subst.
         apply otI_scalar_cancel in H4; auto with wf_db.
       - erewrite col_add_mult_r, <- GMmult_assoc, <- col_add_mult_r in H8; auto with wf_db.
         apply mat_prop_col_add_conv in H8; auto with wf_db.
Qed.

   
(* it follows that the op_to_I matrices are multiplicative *)
Lemma otI_Mmult : forall {n} (A B : Square n),
  op_to_I A -> op_to_I B ->
  op_to_I (A × B).
Proof. intros. 
       apply otI_equiv_otI' in H. 
       apply (otI_mult_r_invr (@op_to_I') A B) in H; auto with invr_db.
       all : apply otI_equiv_otI' in H; auto.
       apply op_to_I_WF in H.
       easy.
Qed.


(* TODO: prove otI_pad1 without using this extra def *) 
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
         apply (otI_scalar_cancel _ c); auto.
         rewrite pad1_scale; auto.
         apply H2.
         apply Gmult_neq_0; auto.
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
       apply H0; auto.
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
         apply lin_indep_scale in H2; auto.
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
         apply_mat_prop det_neq_0_scalar_invr.
         eapply H4; try apply H0; auto.
       - intros. 
         apply_mat_prop det_neq_0_add_invr.
         apply H6; auto. 
Qed.



(***********************************************************)
(** * Defining weak right invertibility *)
(***********************************************************)




Definition weak_invertible_r {m n} (T : GenMatrix m n) : Prop :=
  exists (T' : GenMatrix n m) (c : F), c <> 0 /\ T × T' = c .* (I m). 

(* TODO: this should also just be an invariant *)
Lemma weak_invertible_r_pad1 : forall {n} (A : Square n) (c : F),
  c <> 0 ->
  weak_invertible_r A ->
  weak_invertible_r (pad1 A c). 
Proof. intros. 
       destruct H0 as [B [c' [H0 H1]]].
       exists (pad1 (c .* B) c'), (c * c').
       split.
       apply Gmult_neq_0; auto.
       rewrite <- pad1_mult; auto.
       rewrite Mscale_mult_dist_r, H1; auto.
       prep_genmatrix_equality.
       unfold pad1, scale, I, col_wedge, col_scale, row_wedge, e_i, Zero.
       bdestruct_all; simpl; try ring.
Qed.

Lemma weak_invertible_l_WF : forall {m n} (T : GenMatrix m n) (T' : GenMatrix n m) (c : F),
  WF_GenMatrix T' -> c <> 0 ->
  T × T' = c .* (I m) ->
  make_WF T × T' = c .* (I m).
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       rewrite <- H1.
       unfold genmat_equiv, GMmult, make_WF; intros.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; easy.
Qed.       

Lemma weak_invertible_r_WF : forall {m n} (T : GenMatrix m n) (T' : GenMatrix n m) (c : F),
  WF_GenMatrix T -> c <> 0 ->
  T × T' = c .* (I m) ->
  T × make_WF T' = c .* (I m).
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       rewrite <- H1.
       unfold genmat_equiv, GMmult, make_WF; intros.
       apply big_sum_eq_bounded; intros.
       bdestruct_all; easy.
Qed.       

Lemma weak_invertible_r_I : forall (n : nat), weak_invertible_r (I n).
Proof. intros. 
       exists (I n), 1.
       split.
       apply G1_neq_0'.
       rewrite GMmult_1_r, Mscale_1_l; auto with wf_db.
Qed.

(* proving invr properties for weak_invertible_r *)
Lemma weak_invertible_r_swap_invr : invr_col_swap (@weak_invertible_r). 
Proof. apply invr_swap; intros. 
       unfold weak_invertible_r in *.
       destruct H1 as [T' [c [H1 H2] ] ].
       exists (row_swap T' x y), c.
       split; auto.
       rewrite <- swap_preserves_mul; auto.
Qed.

Lemma weak_invertible_r_scale_invr : invr_col_scale (@weak_invertible_r). 
Proof. apply invr_scale; intros. 
       unfold weak_invertible_r in *.
       destruct H1 as [T' [c0 [H1 H2] ] ].
       exists (row_scale_many T' (fun i j => if (i =? x) then 1 else c)), (c * c0).
       split.
       apply Gmult_neq_0; auto.
       rewrite <- Mscale_assoc, <- H2.
       prep_genmatrix_equality.
       unfold col_scale, row_scale_many, GMmult, scale.
       rewrite big_sum_mult_l.
       apply big_sum_eq_bounded; intros. 
       bdestruct_all;
       ring.
Qed.

Lemma weak_invertible_r_scalar_cancel : invr_scalar_cancel (@weak_invertible_r). 
Proof. apply invr_scalar.
       intros. 
       unfold weak_invertible_r in *.
       destruct H0 as [T' [c0 [H1 H2] ] ].
       exists (c .* T'), c0.
       split; auto.
       rewrite Mscale_mult_dist_r; auto.
       rewrite Mscale_mult_dist_l in H2; auto.
Qed.

Lemma weak_invertible_r_add_invr : invr_col_add (@weak_invertible_r). 
Proof. apply invr_add; intros. 
       unfold weak_invertible_r in *.
       destruct H2 as [T' [c0 [H2 H3] ] ].
       exists (row_add T' y x (-c)%G), c0.
       split; auto.
       rewrite <- add_preserves_mul; auto.
       replace c with (- - c)%G by ring.
       replace (- - - c)%G with (- c)%G by ring.
       rewrite <- row_add_inv; auto. 
Qed.


Hint Resolve weak_invertible_r_swap_invr weak_invertible_r_scale_invr 
             weak_invertible_r_scalar_cancel weak_invertible_r_add_invr : invr_db.




(* this definition is pretty akward, but becomes replaced pretty quickly *)
Definition weak_invertible_r_square {m n} (T : GenMatrix m n) : Prop :=
  m = n /\ exists (T' : Square n) (c : F), c <> 0 /\ op_to_I T' /\ T × T' = c .* (I n). 


(* TODO: this should also just be an invariant *)
Lemma weak_invertible_r_square_pad1 : forall {n} (A : Square n) (c : F),
  c <> 0 ->
  weak_invertible_r_square A ->
  weak_invertible_r_square (pad1 A c). 
Proof. intros. 
       destruct H0 as [H0 [B [c' [H1 [H2 H3]]]]].
       split; auto. 
       exists (pad1 (c .* B) c'), (c * c').
       split.
       apply Gmult_neq_0; auto.
       split.
       apply otI_pad1; auto.
       apply otI_scalar; auto with wf_db.
       rewrite <- pad1_mult; auto.
       rewrite Mscale_mult_dist_r, H3; auto.
       prep_genmatrix_equality.
       unfold pad1, scale, I, col_wedge, col_scale, row_wedge, e_i, Zero.  
       bdestruct_all; simpl; try ring.
Qed.


Lemma WIrS_implies_WIr : forall {n} (A : Square n),
  WF_GenMatrix A ->
  weak_invertible_r_square A -> 
  weak_invertible_r A.
Proof. intros.
       destruct H0 as [H0 [T' [c [H1 [H2 H3]]]]].
       exists T', c; split; easy.
Qed.



(** * Building up machinery to reduce first row to e_i *)


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

(* matrix form of the functions above *)  
Definition col_ops_row_to_e_i_otI {m n} (T : GenMatrix m (S (S n))) 
  : GenMatrix (S (S n)) (S (S n)) :=
  match (genmat_equiv_dec _ _ _ _ _ (get_row T O) Zero) with
  | left _ => I (S (S n))
  | right _ => 
  row_swap (I (S (S n))) 0 (get_nonzero_entry (get_row T 0) ⊤)
  × row_scale_many (I (S (S n)))
      (get_equalizing_scalars
         (T × row_swap (I (S (S n))) 0 (get_nonzero_entry (get_row T 0) ⊤))) ⊤
  × row_add_many (I (S (S n)))
      (get_cae_scalars (T × row_swap (I (S (S n))) 0 (get_nonzero_entry (get_row T 0) ⊤))) 0
  end.


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
       apply get_nonzero_entry_bounds; auto with wf_db.
       apply WF_get_cae_scalars.
Qed.
       

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

Lemma col_ops_row_to_e_i_O' : forall {m n} (T : GenMatrix m (S (S n))), 
  WF_GenMatrix T ->
  (col_add_each 
     (col_scale_many 
        (col_swap T O (get_nonzero_entry (get_row T O)⊤)) 
        (get_equalizing_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))))
     (get_cae_scalars (col_swap T O (get_nonzero_entry (get_row T O)⊤))) O) O O = 
  T O (get_nonzero_entry (get_row T O)⊤).
Proof. intros. 
       unfold get_equalizing_scalars, get_row, col_add_each,
         reduce_row, col_scale_many, GMplus, GMmult, get_col.
       bdestruct_all; subst.
       unfold scale, e_i, transpose, get_cae_scalars; simpl.
       rewrite Gmult_0_r, 2 Gplus_0_r, Gmult_1_l.       
       unfold get_row, col_swap, transpose; easy.
Qed.

Lemma col_ops_row_to_e_i_Si' : forall {m n} (T : GenMatrix m (S (S n))) (i : nat), 
  WF_GenMatrix T ->
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
       apply get_nonzero_entry_bounds; auto with wf_db.
Qed.

Lemma col_ops_row_to_e_i_O : forall {m n} (T : GenMatrix m (S (S n))), 
  WF_GenMatrix T ->
  (col_ops_row_to_e_i T) O O = T O (get_nonzero_entry (get_row T O)⊤).
  intros. 
  unfold col_ops_row_to_e_i in *.
  destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero); auto.
  - erewrite <- get_row_conv, g; try lia.
    unfold Zero.
    erewrite <- get_row_conv, g; try lia; auto.
    apply get_nonzero_entry_bounds; auto with wf_db.
  - rewrite col_ops_row_to_e_i_O'; auto.  
Qed.

Lemma col_ops_row_to_e_i_Si : forall {m n} (T : GenMatrix m (S (S n))) (i : nat), 
  WF_GenMatrix T ->
  (col_ops_row_to_e_i T) O (S i) = 0.
  intros. 
  unfold col_ops_row_to_e_i in *.
  destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero); auto.
  - bdestruct (S i <? S (S n)).
    erewrite <- get_row_conv.
    rewrite g; auto.
    rewrite H; auto.
  - rewrite col_ops_row_to_e_i_Si'; auto.
Qed.


Lemma col_ops_row_to_e_i_to_mul : forall {m n} (T : GenMatrix m (S (S n))),
  WF_GenMatrix T ->
  col_ops_row_to_e_i T = T × col_ops_row_to_e_i_otI T.
Proof. intros. 
       unfold col_ops_row_to_e_i, col_ops_row_to_e_i_otI.
       destruct (genmat_equiv_dec _ _ _ _ _ (get_row T O) Zero).
       - rewrite GMmult_1_r; auto with wf_db.
       - rewrite col_add_each_mult_r; auto with wf_db.
         rewrite col_scale_many_mult_r; auto with wf_db.
         erewrite col_swap_mult_r; auto with wf_db.
         repeat rewrite <- GMmult_assoc; easy.
         apply get_nonzero_entry_bounds; auto with wf_db.
         apply WF_col_swap; try lia; auto.
         apply get_nonzero_entry_bounds; auto with wf_db.
         apply WF_col_scale_many; auto with wf_db.
         apply WF_col_swap; try lia; auto.
         apply get_nonzero_entry_bounds; auto with wf_db.
Qed.

Lemma col_ops_row_to_e_i_otI_ver : forall {m n} (T : GenMatrix m (S (S n))),
  WF_GenMatrix T ->
  op_to_I (col_ops_row_to_e_i_otI T). 
Proof. intros. 
       unfold col_ops_row_to_e_i_otI.
       destruct (genmat_equiv_dec _ _ _ _ _ (get_row T 0) Zero).
       apply otI_I.
       repeat apply otI_Mmult.
       rewrite <- col_row_swap_invr_I; try lia.
       apply otI_swap; try lia.
       all : try apply get_nonzero_entry_bounds; auto with wf_db.
       apply otI_I.
       rewrite <- col_row_scale_many_invr_I; try lia; auto.
       apply otI_col_scale_many; auto with wf_db; intros. 
       apply get_equalizing_scalars_nonzero; auto with wf_db.
       rewrite <- col_swap_mult_r; try lia; auto.
       unfold col_swap; bdestruct_all.
       erewrite <- get_row_conv.
       apply get_nonzero_entry_correct_row; auto with wf_db.
       contradict n0.
       rewrite n0; easy.
       apply get_nonzero_entry_bounds; auto with wf_db.
       apply otI_I.
       rewrite row_many_col_each_invr_I; try lia; auto with wf_db.
       apply otI_col_add_each; try lia; auto with wf_db.
       apply otI_I.
Qed.   

Lemma WF_col_ops_row_to_e_i_otI : forall {m n} (T : GenMatrix m (S (S n))),
  WF_GenMatrix T ->
  WF_GenMatrix (col_ops_row_to_e_i_otI T).
Proof. intros. 
       apply op_to_I_WF.
       apply col_ops_row_to_e_i_otI_ver; auto. 
Qed.

Hint Resolve WF_col_ops_row_to_e_i_otI : wf_db.


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
       rewrite col_ops_row_to_e_i_to_mul in H4; auto.
       apply otI_mult_r_invr_conv in H4; auto.
       apply col_ops_row_to_e_i_otI_ver; auto.
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

       

(** * showing that if m < n, then T is lin_indep explicitly, allowing us to reduce by one row *)


Definition lin_dep_vec_base (n : nat) (v : GenMatrix 1 (S (S n))) : Vector (S (S n)) :=
  match (Geq_dec (v O O) 0) with
  | left _ => (e_i O)
  | right _ => (fun i j => if (j =? O) && (i <? S (S n)) 
                    then (if (i =? O) 
                          then - (v O 1%nat) 
                          else 
                            (if (i =? 1%nat) 
                             then (v O O) else 0)) 
                          else 0)
  end.

(* version for n-by-n+1 matrices. TODO: add more general version *)
Fixpoint lin_dep_vec_rect (n : nat) (T : GenMatrix (S n) (S (S n))) : Vector (S (S n)) :=
  match n with 
  | O => lin_dep_vec_base O T
  | S n' => @GMmult _ _ _ _ _ (S (S n)) (S (S n)) 1
      (col_ops_row_to_e_i_otI T)
            (row_wedge (lin_dep_vec_rect 
                          n' 
                          (reduce_row (reduce_col (T × col_ops_row_to_e_i_otI T) O) O)) 
                       Zero O)
  end.


Arguments lin_dep_vec_base {n}. 
Arguments lin_dep_vec_rect {n}. 


Lemma lin_dep_vec_rect_simplify : forall {n} (T : GenMatrix (S (S n)) (S (S (S n)))),
  lin_dep_vec_rect T = 
  @GMmult _ _ _ _ _ (S (S (S n))) (S (S (S n))) 1
      (col_ops_row_to_e_i_otI T)
            (row_wedge (lin_dep_vec_rect 
                          (reduce_row (reduce_col (T × col_ops_row_to_e_i_otI T) O) O)) 
                       Zero O).
Proof. intros. 
       easy.
Qed.


Lemma WF_lin_dep_vec_base : forall {n} (v : GenMatrix 1 (S (S n))),
  WF_GenMatrix (lin_dep_vec_base v).
Proof. intros. 
       unfold lin_dep_vec_base.
       destruct (Geq_dec (v O O) 0); auto with wf_db.
       unfold WF_GenMatrix; intros.
       bdestruct_all; simpl; easy.
Qed.

Lemma WF_lin_dep_vec_rect : forall {n} (T : GenMatrix (S n) (S (S n))), 
  WF_GenMatrix T -> 
  WF_GenMatrix (lin_dep_vec_rect T).
Proof. induction n; intros; simpl.
       - apply WF_lin_dep_vec_base.
       - apply WF_mult.
         apply op_to_I_WF.
         apply col_ops_row_to_e_i_otI_ver; auto.
         apply WF_row_wedge; try lia.
         apply IHn; auto with wf_db.
         auto with wf_db.
Qed.
        
Hint Resolve WF_lin_dep_vec_base WF_lin_dep_vec_rect : wf_db.


Lemma lin_dep_vec_base_nonzero : forall {n} (v : GenMatrix 1 (S (S n))),
  lin_dep_vec_base v <> Zero. 
Proof. intros. 
       unfold lin_dep_vec_base.
       destruct (Geq_dec (v O O) 0).
       - unfold not; intros; apply G1_neq_0'.
         do 2 apply (f_equal_inv O) in H.
         unfold Zero, e_i in H.
         rewrite <- H.
         bdestruct_all; easy.
       - contradict n0.
         apply (f_equal_inv 1%nat) in n0; apply (f_equal_inv O) in n0.
         unfold Zero in n0; rewrite <- n0.
         bdestruct_all; easy.
Qed.


Lemma lin_dep_vec_rect_nonzero : forall {n} (T : GenMatrix (S n) (S (S n))),
  WF_GenMatrix T ->
  lin_dep_vec_rect T <> Zero. 
Proof. induction n; intros.
       - unfold lin_dep_vec_rect.  
         apply lin_dep_vec_base_nonzero. 
       - assert (H0 := H).
         assert (H' : WF_GenMatrix (reduce_row (reduce_col (T × col_ops_row_to_e_i_otI T) 0) 0)).
         { auto with wf_db. }
         apply col_ops_row_to_e_i_otI_ver in H.
         apply otI_lin_indep in H.
         rewrite lin_dep_vec_rect_simplify.
         unfold linearly_independent in H.
         apply IHn in H'.
         unfold not; intros; apply H'.
         apply H in H1; auto with wf_db.
         apply genmat_equiv_eq; auto with wf_db.
         apply WF_lin_dep_vec_rect; auto with wf_db.
         unfold genmat_equiv; intros. 
         apply (f_equal_inv (S i)) in H1; apply (f_equal_inv j) in H1.
         destruct j; try lia.
         unfold Zero in *; rewrite <- H1.
         unfold row_wedge; bdestruct_all.
         rewrite Sn_minus_1; easy. 
         apply WF_row_wedge; auto with wf_db.
         apply WF_lin_dep_vec_rect; auto with wf_db.
Qed.

Lemma lin_dep_vec_rect_mul_0 : forall {n} (T : GenMatrix (S n) (S (S n))),
  WF_GenMatrix T ->
  T × (lin_dep_vec_rect T) = Zero.
Proof. induction n; intros.
       - apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros.
         unfold lin_dep_vec_rect.       
         unfold GMmult, lin_dep_vec_base; simpl.
         destruct i; destruct j; try lia.
         destruct (Geq_dec (T O O) 0).
         rewrite e.
         unfold Zero, e_i; bdestruct_all; simpl; ring.
         bdestruct_all; simpl.
         unfold Zero; simpl; ring.
       - rewrite lin_dep_vec_rect_simplify.
         rewrite <- GMmult_assoc.        
         erewrite (reduce_wedge_split_0 _ _ (T × col_ops_row_to_e_i_otI T)); auto with wf_db.
         rewrite wedge_mul; try lia.
         rewrite col_wedge_reduce_col_same.
         assert (H' : WF_GenMatrix (reduce_row (reduce_col (T × col_ops_row_to_e_i_otI T) 0) 0)).
         { auto with wf_db. }
         apply IHn in H'.
         apply genmat_equiv_eq; auto with wf_db.
         apply WF_mult; auto with wf_db.
         apply WF_lin_dep_vec_rect; auto with wf_db.
         unfold genmat_equiv; intros. 
         destruct i.
         + rewrite <- col_ops_row_to_e_i_to_mul; auto.
           unfold GMmult, reduce_col.
           apply big_sum_0_bounded; intros. 
           bdestruct_all; simpl.
           rewrite col_ops_row_to_e_i_Si; auto; ring.
         + apply (f_equal_inv i) in H'; apply (f_equal_inv j) in H'.
           unfold Zero in *; rewrite <- H'.
           destruct j; try easy.
Qed.




(* can do this more efficiently if lin_dep_vec_rect is generalized *)
Theorem gt_dim_lindep_rect : forall {n} (T : GenMatrix (S n) (S (S n))),
  WF_GenMatrix T -> 
  linearly_dependent T.
Proof. intros. 
       exists (lin_dep_vec_rect T); split; auto with wf_db.
       split. 
       apply lin_dep_vec_rect_nonzero; auto.
       apply lin_dep_vec_rect_mul_0; auto.
Qed.



(* can do this more efficiently if lin_dep_vec_rect is generalized *)
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
           rewrite col_ops_row_to_e_i_Si; auto; ring.
         + apply (f_equal_inv i) in H3; apply (f_equal_inv j) in H3.
           unfold Zero in *; rewrite <- H3.
           destruct j; try lia.
           unfold reduce_col, reduce_row, GMmult.
           apply big_sum_eq_bounded; intros.
           bdestruct_all.
           easy.
Qed.

     

(**********************************************)
(** *  Now we do the same thing to reduce a col to e_i *) 
(**********************************************)



(* TODO: can probably make this more general *)
Definition col_ops_col_to_e_i {n} (T : Square (S (S n))) : Square (S (S n)) :=
  col_swap 
    (col_add_many 
       (col_scale T 
                  (get_nonzero_entry (lin_dep_vec_rect (reduce_row T O))) 
                  ((lin_dep_vec_rect (reduce_row T O)) 
                     (get_nonzero_entry (lin_dep_vec_rect (reduce_row T O))) 
                     O)) 
       (make_row_val 
          (lin_dep_vec_rect (reduce_row T O)) 
          (get_nonzero_entry (lin_dep_vec_rect (reduce_row T O)))
          0%G)
       (get_nonzero_entry (lin_dep_vec_rect (reduce_row T O))))
    O (get_nonzero_entry (lin_dep_vec_rect (reduce_row T O))).

(* matrix form of the above function *)
Definition col_ops_col_to_e_i_otI {n} (T : Square (S (S n))) : Square (S (S n)) :=
  row_scale (I (S (S n))) (get_nonzero_entry (lin_dep_vec_rect (reduce_row T 0)))
       (lin_dep_vec_rect (reduce_row T 0)
          (get_nonzero_entry (lin_dep_vec_rect (reduce_row T 0))) 0)
     × (row_add_each (I (S (S n)))
          (make_row_val (lin_dep_vec_rect (reduce_row T 0))
             (get_nonzero_entry (lin_dep_vec_rect (reduce_row T 0))) 0)
          (get_nonzero_entry (lin_dep_vec_rect (reduce_row T 0)))
        × row_swap (I (S (S n))) 0 (get_nonzero_entry (lin_dep_vec_rect (reduce_row T 0)))).


Lemma WF_col_ops_col_to_e_i : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  WF_GenMatrix (col_ops_col_to_e_i T).
Proof. intros. 
       unfold col_ops_col_to_e_i.
       apply WF_col_swap; try lia. 
       apply get_nonzero_entry_bounds; auto with wf_db.
       apply WF_col_add_many; auto.
       apply get_nonzero_entry_bounds; auto with wf_db.
       apply WF_col_scale; auto.
Qed.

Hint Resolve WF_col_ops_col_to_e_i : wf_db.

Lemma cs_cam_reduce_helper : forall {m n} (T : GenMatrix (S m) n) (col i j : nat) 
                               (as' : Vector n) (c : F),
  WF_GenMatrix T ->
  (col_add_many (col_scale T col c) as' col) (S i) j = 
  (col_add_many (col_scale (reduce_row T O) col c) as' col) i j.  
Proof. intros. 
       unfold col_add_many, col_scale, reduce_row, gen_new_col.
       bdestruct_all; try easy.
       apply f_equal_gen; try easy.
       do 2 rewrite Msum_Fsum.
       apply big_sum_eq_bounded; intros. 
       unfold scale, get_col.
       bdestruct_all; auto.
Qed.

Lemma col_ops_col_to_e_i_Si : forall {n} (T : Square (S (S n))) (i : nat),
  WF_GenMatrix T ->
  (col_ops_col_to_e_i T) (S i) O = 0.
Proof. intros.
       bdestruct (i <? S n).
       - unfold col_ops_col_to_e_i, col_swap.
         bdestruct_all.
         rewrite cs_cam_reduce_helper; auto.
         rewrite <- col_add_many_mul; auto with wf_db.
         rewrite lin_dep_vec_rect_mul_0; auto with wf_db.
         apply get_nonzero_entry_bounds; auto with wf_db.
       - apply WF_col_ops_col_to_e_i; auto with wf_db; try lia.
Qed.

Lemma col_ops_col_to_e_i_to_mul : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  col_ops_col_to_e_i T = T × col_ops_col_to_e_i_otI T.
Proof. intros. 
       unfold col_ops_col_to_e_i. 
       rewrite col_scale_mult_r; auto with wf_db.
       rewrite col_add_many_mult_r; auto with wf_db.
       erewrite col_swap_mult_r; auto with wf_db.
       repeat rewrite GMmult_assoc; easy.
       apply get_nonzero_entry_bounds; auto with wf_db.
       repeat apply WF_mult; auto with wf_db.
       apply WF_row_add_each; auto with wf_db.
       4 : unfold make_row_val; bdestruct_all; easy.
       all : try apply WF_make_row_val; auto with wf_db.
       all : try apply get_nonzero_entry_bounds; auto with wf_db.
Qed.

Lemma col_ops_col_to_e_i_otI_ver : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  op_to_I (col_ops_col_to_e_i_otI T).
Proof. intros. 
       unfold col_ops_col_to_e_i_otI.
       repeat apply otI_Mmult.
       rewrite <- col_row_scale_invr_I; auto. 
       apply otI_scale; try lia.
       apply get_nonzero_entry_bounds; auto with wf_db.
       apply get_nonzero_entry_correct; auto with wf_db.
       apply lin_dep_vec_rect_nonzero; auto with wf_db.
       apply otI_I.
       rewrite row_each_col_many_invr_I; auto with wf_db.
       apply otI_col_add_many.
       apply get_nonzero_entry_bounds; auto with wf_db.
       unfold make_row_val; bdestruct_all; simpl; easy.
       apply otI_I.
       apply WF_make_row_val; auto with wf_db.       
       apply get_nonzero_entry_bounds; auto with wf_db.
       apply get_nonzero_entry_bounds; auto with wf_db.
       unfold make_row_val; bdestruct_all; simpl; easy.
       rewrite <- col_row_swap_invr_I; auto with wf_db.
       apply otI_swap; try lia.
       all : try apply get_nonzero_entry_bounds; auto with wf_db.
       apply otI_I.
Qed.

Lemma WF_col_ops_col_to_e_i_otI : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  WF_GenMatrix (col_ops_col_to_e_i_otI T).
Proof. intros. 
       apply op_to_I_WF.
       apply col_ops_col_to_e_i_otI_ver; auto. 
Qed.

Hint Resolve WF_col_ops_col_to_e_i_otI : wf_db.

Lemma col_ops_col_to_e_i_invr : forall {n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                  (T : Square (S (S n))),
  WF_GenMatrix T ->
  invr_col_swap P -> 
  invr_col_scale P ->
  invr_scalar_cancel P ->
  invr_col_add P ->
  P (S (S n)) (S (S n)) (col_ops_col_to_e_i T) ->
  P (S (S n)) (S (S n)) T.
Proof. intros. 
       rewrite col_ops_col_to_e_i_to_mul in H4; auto.
       apply otI_mult_r_invr_conv in H4; auto.
       apply col_ops_col_to_e_i_otI_ver; auto.
Qed.



(** now we combine everything to reduce to pad *)

Definition col_ops_to_pad1 {n} (T : Square (S (S n))) : Square (S (S n)) :=
  col_ops_row_to_e_i (col_ops_col_to_e_i T).

Definition col_ops_to_pad1_otI {n} (T : Square (S (S n))) : Square (S (S n)) :=
  col_ops_col_to_e_i_otI T × col_ops_row_to_e_i_otI (col_ops_col_to_e_i T).

Lemma WF_col_ops_to_pad1 : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  WF_GenMatrix (col_ops_to_pad1 T).
Proof. intros. 
       unfold col_ops_to_pad1; auto with wf_db.
Qed.

Lemma WF_col_ops_to_pad1_otI : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  WF_GenMatrix (col_ops_to_pad1_otI T).
Proof. intros. 
       unfold col_ops_to_pad1_otI; auto with wf_db.
Qed.

Hint Resolve WF_col_ops_to_pad1 WF_col_ops_to_pad1_otI : wf_db.


Lemma col_ops_to_pad1_O : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  (col_ops_col_to_e_i T) O O <> 0 ->
  (col_ops_to_pad1 T) O O = (col_ops_col_to_e_i T) O O.
Proof. intros. 
       unfold col_ops_to_pad1.
       rewrite col_ops_row_to_e_i_O; auto with wf_db.
       unfold get_nonzero_entry, get_row, transpose.
       bdestruct_all; simpl.
       destruct (Geq_dec (col_ops_col_to_e_i T O O) 0); easy.
Qed.

Lemma col_ops_to_pad1_Si : forall {n} (T : Square (S (S n))) (i j : nat),
  WF_GenMatrix T ->
  (col_ops_col_to_e_i T) O O <> 0 ->
  i = O \/ j = O -> i <> j ->
  (col_ops_to_pad1 T) i j = 0.
Proof. intros.
       unfold col_ops_to_pad1.
       destruct H1; subst.
       - destruct j; try easy.         
         rewrite col_ops_row_to_e_i_Si; auto with wf_db.
       - destruct i; try easy.
         unfold col_ops_row_to_e_i.
         destruct (genmat_equiv_dec _ _ _ _ _ (get_row (col_ops_col_to_e_i T) 0) Zero).
         rewrite col_ops_col_to_e_i_Si; auto with wf_db.
         unfold col_add_each.
         unfold GMplus.
         replace 0 with (0 + 0) by ring.
         apply f_equal_gen; try apply f_equal.
         unfold col_scale_many, get_equalizing_scalars, get_row, transpose.
         bdestruct_all; simpl.
         destruct (Geq_dec (col_ops_col_to_e_i T O O) 0); try easy.
         rewrite col_swap_same, col_ops_col_to_e_i_Si; auto with wf_db.
         ring.
         unfold GMmult.
         apply big_sum_0_bounded; intros.
         unfold get_cae_scalars.
         bdestruct_all; simpl.
         ring.
Qed.

Lemma col_ops_to_pad1_pad1 : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  col_ops_col_to_e_i T 0 0 <> 0 -> 
  col_ops_to_pad1 T = pad1 (get_minor (col_ops_to_pad1 T) O O) (col_ops_to_pad1 T O O).
Proof. intros. 
       erewrite <- pad1_get_minor; auto.
       intros.
       apply col_ops_to_pad1_Si; auto;
       easy.
Qed.

Lemma col_ops_to_pad1_to_mul : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  col_ops_to_pad1 T = T × col_ops_to_pad1_otI T.
Proof. intros. 
       unfold col_ops_to_pad1, col_ops_to_pad1_otI.
       rewrite col_ops_col_to_e_i_to_mul; auto with wf_db.
       rewrite col_ops_row_to_e_i_to_mul; auto with wf_db.
       repeat rewrite GMmult_assoc. 
       easy. 
Qed.

Lemma col_ops_to_pad1_otI_ver : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  op_to_I (col_ops_to_pad1_otI T).
Proof. intros. 
       unfold col_ops_to_pad1_otI.
       apply otI_Mmult; auto with wf_db.
       apply col_ops_col_to_e_i_otI_ver; auto.
       apply col_ops_row_to_e_i_otI_ver; auto with wf_db.
Qed.

Lemma col_ops_to_pad1_invr : forall {n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                  (T : Square (S (S n))),
  WF_GenMatrix T ->
  invr_col_swap P -> 
  invr_col_scale P ->
  invr_scalar_cancel P ->
  invr_col_add P ->
  P (S (S n)) (S (S n)) T ->
  P (S (S n)) (S (S n)) (col_ops_to_pad1 T).
Proof. intros. 
       rewrite col_ops_to_pad1_to_mul; auto.
       apply otI_mult_r_invr; auto.
       apply col_ops_to_pad1_otI_ver; auto.
Qed.

Lemma col_ops_to_pad1_invr_conv : forall {n} (P : forall m n : nat, GenMatrix m n -> Prop) 
                                  (T : Square (S (S n))),
  WF_GenMatrix T ->
  invr_col_swap P -> 
  invr_col_scale P ->
  invr_scalar_cancel P ->
  invr_col_add P ->
  P (S (S n)) (S (S n)) (col_ops_to_pad1 T) ->
  P (S (S n)) (S (S n)) T.
Proof. intros. 
       rewrite col_ops_to_pad1_to_mul in H4; auto.
       apply otI_mult_r_invr_conv in H4; auto.
       apply col_ops_to_pad1_otI_ver; auto.
Qed.

Lemma col_ops_to_pad1_invert : forall {n} (T : Square (S (S n))),
  WF_GenMatrix T ->
  weak_invertible_r_square (col_ops_to_pad1 T) ->
  weak_invertible_r_square T.
Proof. intros. 
       destruct H0 as [H0 [T' [c [H1 [H2 H3]]]]].
       split; subst; auto.
       exists (col_ops_to_pad1_otI T × T'), c.
       split; auto.
       split.
       apply otI_Mmult; auto.
       apply col_ops_to_pad1_otI_ver; auto.
       rewrite <- GMmult_assoc.
       rewrite <- col_ops_to_pad1_to_mul; auto.
Qed.


(**********************************************)
(** *  Now we prove more properties of invariants *) 
(**********************************************)

         

(** now, we prove some theorems with these powerful lemmas *)
Theorem invr_P_implies_det_neq_0 : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> 
  invr_col_scale P -> 
  invr_scalar_cancel P -> 
  invr_col_add P -> 
  prop_zero_false P ->   
  invr_pad1 P -> 
  WF_GenMatrix A -> P n n A -> 
  det_neq_0 A.
Proof. induction n; intros.
       - unfold det_neq_0; split; auto.
         simpl.
         apply G1_neq_0'.
       - destruct n.
         + unfold det_neq_0; simpl.
           split; auto. 
           eapply prop_zero_false_get_nonzero; try apply H3; auto.
           intros; try lia.
         + assert (H7 : (col_ops_col_to_e_i A) O O <> 0).
           { eapply prop_zero_false_get_nonzero; try apply H3; auto with wf_db.
             apply (otI_mult_r_invr _ _ (col_ops_col_to_e_i_otI A)) in H6; auto.
             rewrite <- col_ops_col_to_e_i_to_mul in H6; auto. 
             apply col_ops_col_to_e_i_otI_ver; auto. 
             intros. 
             rewrite col_ops_col_to_e_i_Si; easy. }
           apply col_ops_to_pad1_invr_conv; auto with invr_db. 
           unfold det_neq_0; split; auto.
           rewrite Det_simplify; auto.
           rewrite <- big_sum_extend_l.
           rewrite big_sum_0_bounded, Gplus_0_r.
           apply Gmult_neq_0.
           simpl; rewrite Gmult_1_l; auto.
           rewrite col_ops_to_pad1_O; auto.
           destruct (IHn (get_minor (col_ops_to_pad1 A) 0 0) P); auto with wf_db.
           inversion H4. 
           apply (H8 _ _ _ (col_ops_to_pad1 A O O)); auto.
           rewrite col_ops_to_pad1_O; auto.
           rewrite get_minor_is_redrow_redcol.
           rewrite <- pad1_reduce_colrow; auto.
           apply col_ops_to_pad1_invr; auto with invr_db. 
           intros. 
           apply col_ops_to_pad1_Si; try easy.
           intros. 
           rewrite col_ops_to_pad1_Si; try easy; try ring.
           right; easy.
Qed.           


Theorem invr_P_implies_weak_invertible_r : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> 
  invr_col_scale P -> 
  invr_scalar_cancel P -> 
  invr_col_add P -> 
  prop_zero_false P ->   
  invr_pad1 P -> 
  WF_GenMatrix A -> P n n A -> 
  weak_invertible_r_square A.
Proof. induction n; intros.
       - replace A with (I O); auto.
         split; auto; exists (I O), 1; split.
         apply G1_neq_0'.
         split; try apply otI_I.
         rewrite GMmult_1_l; auto with wf_db.
         rewrite Mscale_1_l; easy.
         apply genmat_equiv_eq; auto with wf_db.
         unfold genmat_equiv; intros. 
         destruct i; destruct j; try easy.
       - destruct n.
         + split; auto. 
           exists (I 1), (A O O).
           split. 
           eapply prop_zero_false_get_nonzero; try apply H3; auto with wf_db.
           split; try apply otI_I.
           apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, GMmult, I, scale; intros; simpl.
           destruct j; try lia.
           bdestruct_all; simpl; subst; ring.
         + assert (H7 : (col_ops_col_to_e_i A) O O <> 0).
           { eapply prop_zero_false_get_nonzero; try apply H3; auto with wf_db.
             apply (otI_mult_r_invr _ _ (col_ops_col_to_e_i_otI A)) in H6; auto.
             rewrite <- col_ops_col_to_e_i_to_mul in H6; auto. 
             apply col_ops_col_to_e_i_otI_ver; auto. 
             intros. 
             rewrite col_ops_col_to_e_i_Si; easy. }
           apply col_ops_to_pad1_invert; auto.
           erewrite pad1_reduce_colrow; auto.
           inversion H4; subst.
           apply weak_invertible_r_square_pad1.
           rewrite col_ops_to_pad1_O; auto.
           eapply IHn; try apply H; auto with wf_db.
           apply (H8 _ _ _ (col_ops_to_pad1 A O O)).
           rewrite col_ops_to_pad1_O; auto.
           rewrite <- pad1_reduce_colrow; auto.
           rewrite col_ops_to_pad1_to_mul; auto.
           apply otI_mult_r_invr; auto with wf_db.
           apply col_ops_to_pad1_otI_ver; auto.
           all : intros; apply col_ops_to_pad1_Si; try easy.
Qed.           



Corollary lin_ind_implies_weak_invertible_r : forall {n} (A : Square n),
  WF_GenMatrix A ->
  linearly_independent A -> 
  weak_invertible_r_square A.
Proof. intros. 
       apply (invr_P_implies_weak_invertible_r _ (@linearly_independent));
         auto with invr_db.
Qed.



(****************************************************)
(** * Inverses and weak inverses of square matrices *)
(****************************************************) 




Definition Minv_weak {n : nat} (A B : Square n) (c : F) : Prop := 
  c <> 0 /\ A × B = c .* I n /\ B × A = c .* I n.


Definition weak_invertible {n : nat} (A : Square n) : Prop :=
  exists B c, WF_GenMatrix B /\ Minv_weak A B c.


Lemma Minv_weak_scale_l : forall {n : nat} (A B : Square n) (c c0 : F),
  c0 <> 0 ->
  Minv_weak A B c -> 
  Minv_weak (c0 .* A) B (c0 * c).
Proof. intros. 
       destruct H0 as [H0 [H1 H2]].
       split.
       apply Gmult_neq_0; auto.
       split.
       rewrite Mscale_mult_dist_l, H1; auto. 
       lgma.
       rewrite Mscale_mult_dist_r, H2; auto. 
       lgma.
Qed.
  
Lemma Minv_weak_scale_r : forall {n : nat} (A B : Square n) (c c0 : F),
  c0 <> 0 ->
  Minv_weak A B c -> 
  Minv_weak A (c0 .* B) (c0 * c).
Proof. intros. 
       destruct H0 as [H0 [H1 H2]].
       split.
       apply Gmult_neq_0; auto.
       split.
       rewrite Mscale_mult_dist_r, H1; auto. 
       lgma.
       rewrite Mscale_mult_dist_l, H2; auto. 
       lgma.
Qed.

Lemma Minv_weak_unique : forall (n : nat) (A B C : Square n) (c : F), 
                      WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix C ->
                      Minv_weak A B c -> Minv_weak A C c -> B = C.
Proof.
  intros n A B C c WFA WFB WFC [H0 [HAB HBA]] [H1 [HAC HCA]].
  replace B with (B × I n) by (apply GMmult_1_r; assumption).
  apply (undo_scalar _ _ c); auto.
  rewrite <- Mscale_mult_dist_r; auto.
  rewrite <- HAC.  
  replace C with (I n × C) at 2 by (apply GMmult_1_l; assumption).
  rewrite <- Mscale_mult_dist_l; auto.
  rewrite <- HBA.  
  rewrite GMmult_assoc.
  reflexivity.
Qed.

Lemma Minv_weak_symm : forall (n : nat) (A B : Square n) (c : F), Minv_weak A B c -> Minv_weak B A c.
Proof. unfold Minv_weak; intuition. Qed.

(* The left inverse of a square matrix is also its right inverse *)
Lemma Minv_weak_flip : forall (n : nat) (A B : Square n) (c : F), 
  WF_GenMatrix A -> WF_GenMatrix B ->  
  c <> 0 ->
  A × B = c .* I n -> B × A = c .* I n.
Proof. intros.   
       assert (H3 := H2).
       apply invertible_l_implies_linind in H2; auto.
       apply lin_ind_implies_weak_invertible_r in H2; try easy. 
       apply WIrS_implies_WIr in H2; auto.
       destruct H2 as [A' [c0 [H2 H4]]].
       apply weak_invertible_r_WF in H4; auto.
       assert (H' : (A × B) × make_WF A' = c .* make_WF A').
       { rewrite H3, Mscale_mult_dist_l, <- Mscale_mult_dist_r; auto.
         rewrite GMmult_1_l; auto with wf_db. }
       rewrite GMmult_assoc in H'.
       rewrite H4, Mscale_mult_dist_r, GMmult_1_r in H'; auto.       
       apply (undo_scalar _ _ c0); auto.
       rewrite <- Mscale_mult_dist_r, H'; auto.
       rewrite Mscale_mult_dist_r, H4; auto.
       unfold I, scale.
       prep_genmatrix_equality.
       bdestruct_all; simpl; ring.
Qed.

Lemma Minv_weak_left : forall (n : nat) (A B : Square n) (c : F), 
    WF_GenMatrix A -> WF_GenMatrix B -> 
    c <> 0 ->
    A × B = c .* I n -> Minv_weak A B c.
Proof.
  intros n A B c H H0 H1 H2.  
  unfold Minv_weak. do 2 (try split; trivial).
  apply Minv_weak_flip; 
  assumption.
Qed.

Lemma Minv_weak_right : forall (n : nat) (A B : Square n) (c : F), 
    WF_GenMatrix A -> WF_GenMatrix B -> 
    c <> 0 ->
    B × A = c .* I n -> Minv_weak A B c.
Proof.
  intros n A B c H H0 H1 H2. 
  unfold Minv_weak. do 2 (split; trivial).
  apply Minv_weak_flip;
  assumption.
Qed.


Corollary lin_indep_weak_invertible : forall (n : nat) (A : Square n),
  WF_GenMatrix A -> (linearly_independent A <-> weak_invertible A).
Proof. intros; split.
       - intros. 
         assert (H1 := H).
         apply lin_ind_implies_weak_invertible_r in H; try easy.
         apply WIrS_implies_WIr in H; auto.
         destruct H as [B [c [H H2]]].
         apply weak_invertible_r_WF in H2; auto.
         unfold weak_invertible.
         exists (make_WF B), c; split; auto with wf_db. 
         unfold Minv_weak.
         split; try easy.
         split; try easy.
         apply Minv_weak_flip in H2; auto with wf_db. 
       - intros. 
         destruct H0 as [B [c [H1 [H2 [H3 H4]]]]].
         apply invertible_l_implies_linind in H4; auto.
Qed.


Lemma Minv_weak_otI_l : forall (n : nat) (A B : Square n) (c : F),
  WF_GenMatrix A -> WF_GenMatrix B -> 
  c <> 0 ->
  Minv_weak A B c ->
  op_to_I A.
Proof. intros.           
       assert (H3 := lin_indep_weak_invertible).
       assert (H4 : weak_invertible B).
       { exists A, c. split; auto. apply Minv_weak_symm; easy. }
       apply H3 in H4; auto. 
       apply lin_ind_implies_weak_invertible_r in H4; auto. 
       destruct H4 as [H4 [B' [c0 [H5 [H6 H7]]]]].
       apply weak_invertible_r_WF in H7; auto.
       apply Minv_weak_left in H7; auto with wf_db.
       apply Minv_weak_symm in H2.
       apply (Minv_weak_scale_r _ _ _ c0) in H2; auto.
       apply (Minv_weak_scale_r _ _ _ c) in H7; auto.
       rewrite Gmult_comm in H2.
       apply (Minv_weak_unique _ B (c0 .* A) (c .* make_WF B')) in H7; 
         auto with wf_db; subst.
       apply (otI_scalar_cancel _ c0); auto.
       rewrite H7.
       replace (make_WF B') with B'.
       apply otI_scalar; auto.
       apply eq_make_WF.
       apply op_to_I_WF.
       auto.
Qed.

Corollary weak_invertible_otI : forall (n : nat) (A : Square n),
  WF_GenMatrix A -> 
  weak_invertible A ->
  op_to_I A.
Proof. intros.
       destruct H0 as [B [c [H0 H1]]].
       apply Minv_weak_otI_l in H1; auto.
       destruct H1; auto.
Qed.

Corollary weak_invertible_transpose : forall (n : nat) (A : Square n),
  weak_invertible A ->
  weak_invertible (A⊤).
Proof. intros. 
       destruct H as [A' [c [H0 [H1 [H2 H3]]]]].
       exists (A'⊤), c.
       split; auto with wf_db.
       split; auto; split.
       all : rewrite <- GMmult_transpose; auto.
       rewrite H3, Mscale_trans, id_transpose_eq; easy.
       rewrite H2, Mscale_trans, id_transpose_eq; easy.
Qed.



(* doing the same thing for strong invertibility *)
Definition Minv {n : nat} (A B : Square n) : Prop := A × B = I n /\ B × A = I n.

Definition invertible {n : nat} (A : Square n) : Prop :=
  exists B, Minv A B.

Lemma Minv_unique : forall (n : nat) (A B C : Square n), 
                      WF_GenMatrix A -> WF_GenMatrix B -> WF_GenMatrix C ->
                      Minv A B -> Minv A C -> B = C.
Proof.
  intros n A B C WFA WFB WFC [HAB HBA] [HAC HCA].
  apply (Minv_weak_unique _ A _ _ 1); auto; 
    split; try apply G1_neq_0'; rewrite Mscale_1_l; auto.
Qed.    
  
Lemma Minv_symm : forall (n : nat) (A B : Square n), Minv A B -> Minv B A.
Proof. unfold Minv; intuition. Qed.

(* The left inverse of a square matrix is also its right inverse *)
Lemma Minv_flip : forall (n : nat) (A B : Square n), 
  WF_GenMatrix A -> WF_GenMatrix B ->  
  A × B = I n -> B × A = I n.
Proof. intros.   
       replace (I n) with (1 .* I n) by apply Mscale_1_l.
       apply Minv_weak_flip; auto.
       apply G1_neq_0'.
       rewrite Mscale_1_l; easy.
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




(*********************************************)
(** * We finish proving lemmas about invarients *)
(*********************************************)

(** Finally, we show that if all 6 nice properties are true about two (Mat -> Prop)s, then
   they are equivalent on well formed matrices *)
Theorem invr_P_equiv_otI : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_scalar_cancel P -> invr_col_add P -> 
  prop_zero_false P ->   
  invr_pad1 P -> P n n (I n) -> 
  WF_GenMatrix A -> 
  (P n n A <-> op_to_I A).  
Proof. intros. split. 
       - intros. 
         apply invr_P_implies_weak_invertible_r in H7; auto. 
         destruct H7 as [H7 [B [c [H8 [H9 H10]]]]]. 
         apply (Minv_weak_otI_l _ A B c); auto with wf_db.
         apply Minv_weak_left; auto with wf_db.
       - intros. 
         apply op_to_I_ind; auto; intros.  
         + inversion H; subst. 
           apply H12; easy. 
         + inversion H0; subst. 
           apply H12; easy. 
         + inversion H1.
           apply (H11 _ _ _ c); auto.
         + inversion H2; subst. 
           apply H13; easy.
Qed.

(** slightly weaker version, if 4 nice properties are true, then op_to_I -> P *)
Theorem invr_P_implies_otI_weak : forall {n} (A : Square n) (P : forall m o, GenMatrix m o -> Prop), 
  invr_col_swap P -> invr_col_scale P -> 
  invr_scalar_cancel P -> invr_col_add P -> 
  P n n (I n) -> 
  (op_to_I A -> P n n A).  
Proof. intros. 
       apply op_to_I_ind; auto; intros.  
       + inversion H; subst. 
         apply H9; easy. 
       + inversion H0; subst. 
         apply H9; easy. 
       + inversion H1.
         apply (H8 _ _ _ c); auto.
       + inversion H2; subst. 
         apply H10; easy.
Qed.

Corollary lin_indep_det_neq_0 : forall {n} (A : Square n),
  WF_GenMatrix A -> (linearly_independent A <-> det_neq_0 A).
Proof. intros. split.  
       - intros. 
         apply invr_P_equiv_otI in H0; auto with invr_db.      
         apply invr_P_equiv_otI; auto with invr_db.
         split; auto. 
         rewrite Det_I; auto; apply G1_neq_0'.
         unfold linearly_independent; intros. 
         rewrite GMmult_1_l in H3; auto. 
       - intros. 
         apply invr_P_equiv_otI in H0; auto with invr_db.    
         apply invr_P_equiv_otI; auto with invr_db.
         unfold linearly_independent; intros. 
         rewrite GMmult_1_l in H2; auto. 
         split; auto. 
         rewrite Det_I; auto; apply G1_neq_0'.
Qed.

(* TODO: this can be shortened a lot *)
Corollary lin_dep_det_eq_0 : forall {n} (A : Square n), 
  WF_GenMatrix A -> (linearly_dependent A <-> det_eq_c 0 A).
Proof. induction n as [| n'].
       - intros. split; intros.
         destruct H0 as [v [H0 [H1 H2]]]. 
         assert (H' : v = Zero).
         { apply genmat_equiv_eq; auto with wf_db. 
           unfold genmat_equiv; easy. }
         easy.          
         destruct H0.
         unfold Determinant in H1.
         assert (H2 := G1_neq_0').
         easy.
       - intros. 
         split; intros.  
         + split; try easy. 
           apply lindep_implies_not_linindep in H0.
           assert (H' : ~  (det_neq_0 A)).
           unfold not; intros; apply H0.
           apply lin_indep_det_neq_0; auto. 
           unfold not in H'. 
           destruct (Geq_dec (Determinant A) 0); try easy. 
           assert (H'' : False). apply H'.
           split; easy. 
           easy. 
         + destruct n'.
           * destruct H0; simpl in H1.
             exists (e_i O).
             split; auto with wf_db.
             split.
             unfold not; intros; apply G1_neq_0'.
             do 2 apply (f_equal_inv O) in H2.
             unfold e_i, Zero in H2; rewrite <- H2.
             bdestruct_all; easy.
             apply genmat_equiv_eq; auto with wf_db.
             unfold genmat_equiv; intros. 
             unfold GMmult, Zero; simpl.
             destruct i; try lia.
             rewrite H1; ring.
           * destruct (Geq_dec (col_ops_col_to_e_i A 0 0) 0).
             ++ apply col_ops_col_to_e_i_invr; auto with invr_db.
                apply_mat_prop lin_dep_pzt.
                apply H2; exists O.
                split; try lia.
                apply genmat_equiv_eq; auto with wf_db.
                unfold genmat_equiv; intros.
                unfold get_col, Zero.
                bdestruct_all.
                destruct i; auto.
                rewrite col_ops_col_to_e_i_Si; auto.
             ++ apply col_ops_to_pad1_invr_conv; auto with invr_db. 
                apply col_ops_to_pad1_invr in H0; auto with invr_db. 
                destruct H0.
                rewrite col_ops_to_pad1_pad1 in H1; auto.
                rewrite Determinant_pad1 in H1; auto.
                apply Gmult_integral in H1; destruct H1.
                rewrite col_ops_to_pad1_O in H1; try easy.
                erewrite pad1_get_minor; auto.
                apply lin_dep_pad1.
                apply IHn'; auto with wf_db.
                split; auto.
                intros.
                apply col_ops_to_pad1_Si; easy.
Qed.            


Corollary lin_dep_indep_dec : forall {n} (A : Square n),
  WF_GenMatrix A -> { linearly_independent A } + { linearly_dependent A }. 
Proof. intros. 
       destruct (Geq_dec (Determinant A) 0).
       - right. 
         apply lin_dep_det_eq_0; auto. 
         split; easy. 
       - left. 
         apply lin_indep_det_neq_0; auto.
         split; easy. 
Qed.

Corollary det_eq_0_transpose : forall {n} (A : Square n),
  WF_GenMatrix A -> 
  det_eq_c 0 A ->
  det_eq_c 0 (A⊤).
Proof. intros. 
       apply lin_dep_det_eq_0; auto with wf_db.
       destruct (lin_dep_indep_dec (A⊤)); auto with wf_db.
       apply lin_indep_weak_invertible in l.
       apply weak_invertible_transpose in l.
       rewrite transpose_involutive in l.
       apply lin_indep_weak_invertible in l.
       apply lin_indep_det_neq_0 in l.
       destruct H0; destruct l; easy.
       all : auto with wf_db.
Qed.

(*************************************************************************************)
(** * we define another set of invariants to help show that Det A × Det B = Det (A × B) *)
(*************************************************************************************)

Definition Det_mult_comm_l (n m : nat) (A : GenMatrix n m) :=
  n = m /\ (forall (B : Square n), 
              (Determinant B) * (@Determinant _ _ _ _ _ n A) = 
                (@Determinant _ _ _ _ _ n (B × A))).


Lemma Dmc_I : forall {n}, Det_mult_comm_l n n (I n).
Proof. intros. 
       unfold Det_mult_comm_l; split; auto.
       intros. 
       rewrite Det_I, Det_make_WF, (Det_make_WF _ _ _ _ _ _ _ (B × I n)); auto.
       rewrite <- GMmult_make_WF.
       rewrite <- (eq_make_WF _ _ (I n)); auto with wf_db.  
       rewrite GMmult_1_r; auto with wf_db.
       ring. 
Qed.

Lemma Dmc_make_WF : forall {n} (A : Square n),
  Det_mult_comm_l n n (make_WF A) <-> Det_mult_comm_l n n A.
Proof. intros; split; intros. 
       - destruct H; subst. 
         split; auto; intros. 
         rewrite (Det_make_WF _ _ _ _ _ _ _ A), H0.
         rewrite <- Det_Mmult_make_WF_r; easy. 
       - destruct H; subst. 
         split; auto; intros. 
         rewrite <- Det_make_WF; auto.
         rewrite <- Det_Mmult_make_WF_r; easy. 
Qed.

Lemma Dmc_Mmult : forall {n} (A B : Square n),
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
         rewrite Det_Mmult_make_WF_l; auto. 
         rewrite <- col_swap_mult_r; auto with wf_db.
         rewrite <- col_row_swap_invr_I; auto.
         rewrite Determinant_swap, Det_I, Determinant_swap; auto. 
         rewrite Det_make_WF; try ring; auto.
Qed.

Lemma Dmc_scale_I : forall (n x : nat) (c : F),
  Det_mult_comm_l n n (row_scale (I n) x c).
Proof. intros.  
       split; auto; intros. 
       rewrite Det_Mmult_make_WF_l; auto.
       rewrite <- col_scale_mult_r; auto with wf_db.
       rewrite <- col_row_scale_invr_I; auto. 
       bdestruct (x <? n).
       - rewrite Determinant_col_scale, Det_I, Determinant_col_scale; auto.
         rewrite Det_make_WF; try ring; auto.
       - assert (H' : (col_scale (I n) x c) = I n).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, col_scale, I; intros. 
           bdestruct_all; easy. }
         assert (H'' : (col_scale (make_WF B) x c) = make_WF B).
         { apply genmat_equiv_eq; auto with wf_db.
           unfold genmat_equiv, col_scale, I; intros. 
           bdestruct_all; easy. }
         rewrite H', H''.
         rewrite Det_make_WF, Det_I; try ring; auto.
Qed. 

Lemma Dmc_add_I : forall (n x y : nat) (c : F),
  x <> y -> x < n -> y < n -> Det_mult_comm_l n n (row_add (I n) x y c).
Proof. intros.  
       split; auto; intros. 
       rewrite Det_Mmult_make_WF_l; auto.
       rewrite <- col_add_mult_r; auto with wf_db.
       rewrite <- col_row_add_invr_I; auto.
       rewrite Determinant_col_add, Det_I, Determinant_col_add; auto.
       rewrite Det_make_WF; auto; ring.
Qed.

(* proving Dmc invariants *)
Lemma Dmc_swap_invr : invr_col_swap (Det_mult_comm_l).
Proof. apply invr_swap; intros.   
       bdestruct (x =? y); subst.
       - rewrite col_swap_same; easy.
       - bdestruct (n =? m); subst; try (destruct H1; try lia; easy). 
         apply Dmc_make_WF.       
         rewrite <- col_swap_make_WF; auto.
         erewrite col_swap_mult_r; auto with wf_db. 
         apply Dmc_Mmult.
         apply Dmc_make_WF; easy.
         apply Dmc_swap_I; auto. 
Qed.

Lemma Dmc_scale_invr : invr_col_scale (Det_mult_comm_l).
Proof. apply invr_scale; intros.   
       bdestruct (n =? m); subst; try (destruct H1; try lia; easy).
       apply Dmc_make_WF.       
       rewrite <- col_scale_make_WF; auto.
       rewrite col_scale_mult_r; auto with wf_db. 
       apply Dmc_Mmult.
       apply Dmc_make_WF; easy.
       apply Dmc_scale_I; auto. 
Qed.

Lemma Dmc_scalar_cancel : invr_scalar_cancel (Det_mult_comm_l).
Proof. apply invr_scalar; intros.   
       bdestruct (n =? m); subst; try (destruct H0; try lia; easy).
       apply Dmc_make_WF; apply Dmc_make_WF in H0.        
       destruct H0; split; auto; intros. 
       apply (Gmult_cancel_l _ _ (c ^ m)); auto.
       apply Gpow_nonzero; auto.
       rewrite <- Determinant_scalar, <- Mscale_mult_dist_r, scalar_make_WF; auto.
       rewrite <- H1, <- scalar_make_WF, Determinant_scalar; auto; ring.
Qed.       

Lemma Dmc_add_invr : invr_col_add (Det_mult_comm_l).
Proof. apply invr_add; intros.   
       bdestruct (n =? m); subst; try (destruct H2; try lia; easy).
       apply Dmc_make_WF.       
       rewrite <- col_add_make_WF; auto.
       rewrite col_add_mult_r; auto with wf_db. 
       apply Dmc_Mmult.
       apply Dmc_make_WF; easy.
       apply Dmc_add_I; auto. 
Qed.

Lemma otI_Dmc : forall {n} (A : Square n),
  op_to_I A -> Det_mult_comm_l n n A.
Proof. intros n A. 
       apply invr_P_implies_otI_weak.
       apply_mat_prop Dmc_swap_invr.
       apply_mat_prop Dmc_scale_invr.
       apply_mat_prop Dmc_scalar_cancel.
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
         rewrite <- H3, GMmult_1_l; easy. 
       - assert (H' : linearly_dependent (A × B)).
         { apply lin_dep_mult_r; easy. }
         apply lin_dep_det_eq_0 in l; 
         apply lin_dep_det_eq_0 in H'; auto with wf_db. 
         destruct l; destruct H'. 
         rewrite H2, H4; ring. 
Qed.

Theorem Determinant_multiplicative : forall {n} (A B : Square n), 
  (Determinant A) * (Determinant B) = Determinant (A × B).
Proof. intros. 
       rewrite Det_make_WF, (Det_make_WF _ _ _ _ _ _ _ B), Determinant_multiplicative_WF;
         auto with wf_db. 
       rewrite <- Det_Mmult_make_WF_l, <- Det_Mmult_make_WF_r; easy. 
Qed.


(*****************************************************)
(** * doing the same thing to show Det(A) = Det(A^T) *)
(*****************************************************)



Definition Det_transpose_comm (n m : nat) (A : GenMatrix n m) :=
  n = m /\ (@Determinant _ _ _ _ _ n A) = (@Determinant _ _ _ _ _ n (A⊤)).


Lemma Dtc_I : forall {n}, Det_transpose_comm n n (I n).
Proof. intros. 
       unfold Det_transpose_comm; split; auto.
       rewrite id_transpose_eq; easy.
Qed.

Lemma Dtc_make_WF : forall {n} (A : Square n),
  Det_transpose_comm n n (make_WF A) <-> Det_transpose_comm n n A.
Proof. intros.
       unfold Det_transpose_comm.
       erewrite transpose_make_WF; try apply R4.
       repeat rewrite <- Det_make_WF; try easy. 
Qed.

Lemma Dtc_Mmult : forall {n} (A B : Square n),
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
         rewrite (Det_make_WF _ _ _ _ _ _ _ (col_scale (I n) x c)).
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
Qed.

Lemma Dtc_scalar_cancel : invr_scalar_cancel (Det_transpose_comm).
Proof. apply invr_scalar; intros.   
       bdestruct (n =? m); subst; try (destruct H0; try lia; easy).
       apply Dtc_make_WF; apply Dtc_make_WF in H0.        
       destruct H0; split; auto; intros. 
       apply (Gmult_cancel_l _ _ (c ^ m)); auto.
       apply Gpow_nonzero; auto.
       rewrite <- 2 Determinant_scalar, <- Mscale_trans, scalar_make_WF; auto. 
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

Lemma otI_Dtc : forall {n} (A : Square n),
  op_to_I A -> Det_transpose_comm n n A.
Proof. intros n A. 
       apply invr_P_implies_otI_weak.
       apply_mat_prop Dtc_swap_invr.
       apply_mat_prop Dtc_scale_invr.
       apply_mat_prop Dtc_scalar_cancel.
       apply_mat_prop Dtc_add_invr.
       apply Dtc_I. 
Qed. 

Lemma Determinant_transpose_WF : forall {n} (A : Square n), 
  WF_GenMatrix A ->
  Determinant A = Determinant A⊤.
Proof. intros. 
       destruct (Geq_dec (Determinant A) 0).  
       - assert (H' : det_eq_c 0 (A) ⊤).
         { apply det_eq_0_transpose; auto.
           split; auto. }
         destruct H'.
         rewrite e, H1; easy.
       - assert (H' : det_neq_0 A).
         { split; auto. }
         apply lin_indep_det_neq_0 in H'; auto.
         apply lin_indep_weak_invertible in H'; auto.
         apply weak_invertible_otI in H'; auto.
         apply otI_Dtc in H'.
         destruct H'; easy.
Qed.

Theorem Determinant_transpose : forall {n} (A : Square n), 
  Determinant A = Determinant A⊤.
Proof. intros.
       rewrite Det_make_WF, (Det_make_WF _ _ _ _ _ _ _ (A⊤)); auto.
       erewrite <- transpose_make_WF; auto.
       rewrite Determinant_transpose_WF; auto with wf_db.
Qed.


(** Now we get some results about the adjugate of a matrix *)

Lemma adjugate_transpose : forall {n} (A : Square (S n)),
  WF_GenMatrix A ->   
  adjugate A⊤ = (adjugate A)⊤.
Proof. intros. 
       apply genmat_equiv_eq; auto with wf_db.
       unfold genmat_equiv; intros.
       unfold adjugate.
       rewrite <- get_minor_transpose, <- Determinant_transpose.
       unfold transpose. 
       bdestruct_all; simpl.
       repeat (apply f_equal_gen; try lia); easy.
Qed.

Theorem mult_by_adjugate_r : forall {n} (A : Square (S n)), 
  WF_GenMatrix A -> 
  A × (adjugate A) = (Determinant A) .* (I (S n)). 
Proof. intros. 
       assert (H0 : adjugate (A⊤) × (A⊤) = Determinant (A⊤) .* I (S n)).
       { apply mult_by_adjugate_l; auto with wf_db. }
       apply (f_equal transpose) in H0.
       rewrite GMmult_transpose, transpose_involutive, <- Determinant_transpose, 
         Mscale_trans, id_transpose_eq, adjugate_transpose in H0; auto.
Qed.


End LinAlgOverCommRing3.
       
    


(* 
 *
 *
 *)
