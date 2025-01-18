
(** This file contains more concepts relevent to quantum computing, as well as some more general linear algebra concepts such as Gram-Schmidt and eigenvectors/eigenvalues. *)
 
Require Import Permutations.
Require Import List.        
Require Export Complex.
Require Export CauchySchwarz.
Require Export Quantum. 
Require Import FTA.

(****************************)
(** * Proving some indentities *)
(****************************)

(* little Ltac for helping with √ 2 *)
Ltac Hhelper :=
   unfold Mmult;
   unfold big_sum;
   unfold I;
   simpl;
   C_field_simplify;
   try lca; 
   C_field.

Lemma Y_eq_iXZ : σy = Ci .* σx × σz. Proof. lma'. Qed.
Lemma H_eq_Hadjoint : hadamard† = hadamard. Proof. lma'. Qed.


#[global] Hint Rewrite Y_eq_iXZ H_eq_Hadjoint : Q_db.

Lemma ItimesIid : I 2 × I 2 = I 2. Proof. lma'. Qed.      
Lemma XtimesXid : σx × σx = I 2. Proof. lma'. Qed.      
Lemma YtimesYid : σy × σy = I 2. Proof. lma'. Qed.
Lemma ZtimesZid : σz × σz = I 2. Proof. lma'. Qed.
Lemma HtimesHid : hadamard × hadamard = I 2. Proof. lma'; Hhelper. Qed.

#[global] Hint Rewrite ItimesIid XtimesXid YtimesYid ZtimesZid HtimesHid : Q_db.

Lemma ZH_eq_HX : σz × hadamard = hadamard × σx. Proof. lma'. Qed.
Lemma XH_eq_HZ : σx × hadamard = hadamard × σz. Proof. lma'. Qed.
Lemma SX_eq_YS : Sgate × σx = σy × Sgate. Proof. lma'; unfold Mmult;
                                                   simpl; rewrite Cexp_PI2; lca. Qed.
Lemma SZ_eq_ZS : Sgate × σz = σz × Sgate. Proof. lma'; unfold Mmult;
                                                   simpl; rewrite Cexp_PI2; lca. Qed.
Lemma cnotX1 : cnot × (σx ⊗ I 2) = (σx ⊗ σx) × cnot. Proof. lma'. Qed.
Lemma cnotX2 : cnot × (I 2 ⊗ σx) = (I 2 ⊗ σx) × cnot. Proof. lma'. Qed.
Lemma cnotZ1 : cnot × (σz ⊗ I 2) = (σz ⊗ I 2) × cnot. Proof. lma'. Qed.
Lemma cnotZ2 : cnot × (I 2 ⊗ σz) = (σz ⊗ σz) × cnot. Proof. lma'. Qed.

#[global] Hint Rewrite ZH_eq_HX XH_eq_HZ SX_eq_YS SZ_eq_ZS cnotX1 cnotX2 cnotZ1 cnotZ2 : Q_db.


(*******************************)
(** * Defining orthonormal matrix *)
(*******************************)


Local Open Scope nat_scope. 

Definition orthogonal {n m} (S : Matrix n m) : Prop := 
  forall i j, i <> j -> inner_product (get_col S i) (get_col S j) = C0.

Definition orthonormal {n m} (S : Matrix n m) : Prop :=
  orthogonal S /\ (forall (i : nat), i < m -> norm (get_col S i) = 1%R).

(* to match WF_Unitary *)
Definition WF_Orthonormal {n m} (S : Matrix n m) : Prop := 
  WF_Matrix S /\ orthonormal S. 

Lemma inner_product_is_mult : forall {m n} (i j : nat) (S : Matrix m n),
  inner_product (get_col S i) (get_col S j) = (S† × S) i j.
Proof. intros. unfold inner_product, get_col, Mmult, adjoint.
       apply big_sum_eq.
       apply functional_extensionality; intros. simpl.
       reflexivity.
Qed.


(* FIXME: this already exists in Cauchyschwarz.v *)
Lemma inner_product_comm_conj : forall {n} (v u : Vector n), 
  inner_product v u = Cconj (inner_product u v).
Proof. intros. 
       unfold inner_product.
       assert (H' : forall A : Matrix 1 1, (A 0 0) ^* = A† 0 0).
       { unfold adjoint, Cconj. 
         easy. }
       rewrite H'. 
       rewrite Mmult_adjoint, adjoint_involutive.
       easy.
Qed.


(***********************************************)
(** * some useful facts about unitary matrices *)
(***********************************************)


Lemma unit_is_orthonormal : forall {n} (U : Square n),
  WF_Unitary U <-> WF_Orthonormal U.
Proof. intros n U. split. 
       - split; try apply H.
         split. 
         * unfold orthogonal. intros.
           rewrite inner_product_is_mult.
           destruct H as [H1 H].   
           rewrite H. 
           unfold I. bdestruct (i =? j); try lia; easy.
         * intros. unfold norm, inner_product.
           assert (H1 : ((get_col U i) † × get_col U i) 0%nat 0%nat = 
                        inner_product (get_col U i) (get_col U i)).
           { unfold inner_product. reflexivity. }
           rewrite H1. rewrite inner_product_is_mult.
           destruct H.
           rewrite H2. unfold I.
           bdestruct (i =? i); bdestruct (i <? n); try lia. 
           simpl. apply sqrt_1. 
       - intros [H1 [H2 H3] ]. 
         split; try easy.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         rewrite <- inner_product_is_mult.
         unfold orthogonal in H2. unfold I.
         bdestruct (i =? j); bdestruct (i <? n); try lia; subst. 
         * unfold norm, inner_product in H3.
           apply H3 in H0.
           apply eq_sym in H0.
           apply sqrt_1_unique in H0.
           unfold RtoC.
           apply c_proj_eq; try easy.
           simpl. 
           apply norm_real. 
         * rewrite H2; try nia; easy.
Qed.

Lemma unitary_abs_le_1 {n} {A : Matrix n n} (HA: WF_Unitary A) :
  forall i j, 
  (Cmod (A i j) <= 1)%R.
Proof.
  intros i j.
  bdestruct (i <? n); bdestruct (j <? n); 
  [|rewrite (proj1 HA); [rewrite ?Cmod_0; lra | auto]..].
  apply normal_matrix_le_1; [easy..|].
  apply (proj1 (unit_is_orthonormal A) HA).
Qed.

Lemma det_by_unit : forall {n} (A B X : Square n),
  WF_Matrix A -> WF_Matrix B -> 
  WF_Unitary X -> (forall i, A × (get_col X i) = B × (get_col X i)) -> A = B.
Proof. intros. assert (H' : A × X = B × X).
       { apply det_by_get_col. intros.
         do 2 (rewrite <- get_col_mult).
         apply H2. }
       rewrite <- Mmult_1_r.
       rewrite <- (Mmult_1_r _ _ A).
       destruct H1.
       apply Minv_flip in H3; auto with wf_db.
       rewrite <- H3.
       do 2 (rewrite <- Mmult_assoc).
       rewrite H'.
       reflexivity. 
       all : easy. 
Qed.

Lemma unit_invertible : forall {n} (U : Square n),
  WF_Unitary U -> invertible U.
Proof. intros.
       destruct H.
       exists (adjoint U).
       split; auto with wf_db.
       split; auto.
       apply Minv_flip; auto with wf_db.
Qed.

Lemma unit_det_neq_0 : forall {n} (U : Square n),
  WF_Unitary U -> Determinant U <> C0.
Proof. intros.
       apply invertible_iff_det_neq_0.
       apply H.
       apply unit_invertible.
       apply H.
Qed.

Lemma unit_det_Cmod_1 : forall {n} (U : Square n),
  WF_Unitary U -> Cmod (Determinant U) = 1%R.
Proof.
  intros n U [HWF Hinv].
  apply (f_equal (fun A => √ (Cmod (Determinant A)))) in Hinv.
  revert Hinv.
  rewrite <- Determinant_multiplicative, <- Determinant_adjoint.
  rewrite Cmod_mult, Cmod_Cconj. 
  let a := constr:(Cmod (Determinant U)) in
  replace (a * a)%R with (a ^ 2)%R by lra.
  rewrite sqrt_pow2 by apply Cmod_ge_0.
  intros ->.
  rewrite Det_I, Cmod_1.
  apply sqrt_1.
Qed.

(***********************************************************************************)
(** * We now define diagonal matrices and diagonizable matrices, proving basic lemmas *)
(***********************************************************************************)

Definition WF_Diagonal {m n : nat} (A : Matrix m n) : Prop := 
  WF_Matrix A /\ forall i j, i <> j -> A i j = C0.


Lemma diag_Zero : forall m n : nat, WF_Diagonal (@Zero m n).
Proof. intros n. split; auto with wf_db. Qed.

Lemma diag_I : forall n : nat, WF_Diagonal (I n). 
Proof. 
  intros.
  split; auto with wf_db.
  intros.
  unfold I. 
  bdestruct (i =? j); try lia; try easy. 
Qed.

Lemma diag_I1 : WF_Diagonal (I 1). Proof. apply diag_I. Qed.

Lemma diag_scale : forall {n : nat} (r : C) (A : Square n), 
  WF_Diagonal A -> WF_Diagonal (r .* A).
Proof.
  intros n r A [H H0]. 
  split; auto with wf_db.
  intros. 
  unfold scale. 
  rewrite H0; try lca; easy.
Qed.

Lemma diag_plus : forall {n} (A B : Square n), 
  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A .+ B).
Proof.
  intros n A B [H H0] [H1 H2]. 
  split; auto with wf_db. 
  intros. 
  unfold Mplus.
  rewrite H0, H2; try easy; lca.
Qed.

Lemma diag_mult : forall {m n o : nat} (A : Matrix m n) (B : Matrix n o), 
  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A × B).
Proof.
  intros m n o A B [H H0] [H1 H2].
  split; auto with wf_db. 
  intros.
  unfold Mmult. 
  apply (@big_sum_0 C C_is_monoid).
  intro.
  bdestruct (x =? i).
  + rewrite H2; try lia; lca. 
  + rewrite H0, Cmult_0_l.    
    reflexivity. auto.
Qed.

Lemma diag_pad1 : forall {m n} (A : Matrix m n) (c : C),
  WF_Diagonal A <-> WF_Diagonal (pad1 A c).
Proof. intros; split; intros; destruct H; split; auto with wf_db; intros.
       destruct i; destruct j; auto; try lia.
       unfold pad1, col_wedge, row_wedge, e_i, scale.
       lca. 
       rewrite pad1_conv, H0; auto.
       eapply WF_pad1_conv.
       apply H.
       erewrite <- pad1_conv.
       rewrite H0; auto.
Qed.

(* short lemma to prove diag_kron *)
Lemma div_mod_eq : forall (a b m : nat),
  m <> 0 -> (a / m = b / m) -> (a mod m = b mod m) -> a = b.
Proof. intros a b m H0 Hdiv Hmod.
       rewrite (Nat.mod_eq a m), (Nat.mod_eq b m) in Hmod.
       rewrite Hdiv in Hmod.
       assert (H : m * (b / m) + (a - m * (b / m)) = m * (b / m) + (b - m * (b / m))).
       { rewrite Hmod. reflexivity. }
       rewrite <- (le_plus_minus'  (m * (b / m)) a) in H.
       rewrite <- (le_plus_minus'  (m * (b / m)) b) in H.
       apply H.
       apply Nat.mul_div_le; apply H0.
       rewrite <- Hdiv; apply Nat.mul_div_le; apply H0.
       apply H0. apply H0.
Qed.

Lemma diag_kron : forall {n m : nat} (A : Square n) (B : Square m), 
                  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A ⊗ B).
Proof.
  intros n m A B [H H0] [H1 H2].
  destruct m.
  rewrite (WF0_Zero_l 0); try easy.
  auto with wf_db.
  split; auto with wf_db.
  unfold kron.
  intros.
  bdestruct (i / (S m) =? j / (S m)).
  - bdestruct (i mod (S m) =? j mod (S m)).
    + apply (div_mod_eq i j (S m)) in H5; try easy.
    + rewrite H2; try lca; easy. 
  - rewrite H0; try lca; easy. 
Qed.

Lemma diag_transpose : forall {n : nat} (A : Square n), 
                     WF_Diagonal A -> WF_Diagonal A⊤. 
Proof. intros n A [H H0]. 
       split; auto with wf_db.
       intros. 
       unfold transpose.  
       apply H0. auto. 
Qed.

Lemma diag_adjoint : forall {n : nat} (A : Square n), 
      WF_Diagonal A -> WF_Diagonal A†. 
Proof. intros n A [H H0]. 
       split; auto with wf_db.
       unfold  adjoint, Cconj. 
       intros. 
       rewrite H0. lca. auto.
Qed.

Lemma diag_kron_n : forall (n : nat) {m : nat} (A : Square m),
   WF_Diagonal A ->  WF_Diagonal (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - rewrite Nat.mul_comm. 
    apply (@diag_kron (m^n) m _ A). 
    apply IHn. apply H. 
Qed.

Lemma diag_big_kron : forall n (l : list (Square n)), 
                        (forall A, In A l -> WF_Diagonal A) ->
                         WF_Diagonal (⨂ l). 
Proof.                         
  intros.
  induction l.
  - simpl. apply diag_I.
  - simpl. apply (@diag_kron _ (n^(length l)) a (⨂ l)). 
    apply H.
    left. easy. 
    apply IHl. 
    intros A H'. apply H.
    simpl. auto.
Qed. 

Lemma diag_Mmult_n : forall n {m} (A : Square m),
   WF_Diagonal A -> WF_Diagonal (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply diag_mult; assumption. 
Qed.

(** defining what it means to be diagonalizable *)
Definition WF_Diagonalizable {n : nat} (A : Square n) : Prop :=
  WF_Matrix A /\ (exists (X X' B: Square n), 
    WF_Diagonal B /\ WF_Matrix X /\ WF_Matrix X' /\ X × X' = I n /\ B = X × A × X').

Lemma diag_imps_diagble : forall {n} (A : Square n),
  WF_Diagonal A -> WF_Diagonalizable A.
Proof. intros n A [H H0]. unfold WF_Diagonalizable.
       split; auto.
       exists (I n), (I n), A. 
       split.
       split; auto. 
       split; auto with wf_db.
       split; auto with wf_db.
       rewrite Mmult_1_l; auto with wf_db.  
       rewrite Mmult_1_l; auto with wf_db.  
       rewrite Mmult_1_r; auto with wf_db.  
Qed.

Lemma diagble_Zero : forall n : nat, WF_Diagonalizable (@Zero n n).
Proof. intros. apply diag_imps_diagble. 
       apply diag_Zero.
Qed.

Lemma diagble_I : forall n : nat, WF_Diagonalizable (I n). 
Proof. intros. apply diag_imps_diagble.
       apply diag_I.
Qed.

Lemma diagble_I1 : WF_Diagonal (I 1). Proof. apply diag_I. Qed.
  
Lemma diagble_scale : forall {n : nat} (r : C) (A : Square n), 
  WF_Diagonalizable A -> WF_Diagonalizable (r .* A).
Proof.
  intros n r A [H H0].  
  split; auto with wf_db.
  do 3 (destruct H0).
  destruct H0 as [H1 [H2 [H3 [H4 H5] ] ] ].
  exists x, x0, (r .* x1); split. 
  apply diag_scale; apply H1. 
  split; try easy.
  split; try easy. 
  split. 
  apply H4.
  rewrite Mscale_mult_dist_r;
  rewrite Mscale_mult_dist_l.
  rewrite H5.
  reflexivity. 
Qed.

Lemma diagble_switch : forall {n : nat} (A B X X' : Square n),
  WF_Matrix A -> WF_Matrix X -> WF_Matrix X' -> 
  X × X' = I n -> B = X × A × X' ->
  A = X' × B × X.
Proof. intros. 
       rewrite H3. 
       repeat rewrite <- Mmult_assoc. 
       apply Minv_flip in H2; auto.
       rewrite H2, Mmult_1_l; auto.
       rewrite Mmult_assoc. 
       rewrite H2, Mmult_1_r; auto. 
Qed.       

(**************************************)
(** * Defining Cprod, similar to big_sum *)
(**************************************)

(* could define this using the multiplicative monoid on C, but this would 
   lead to confusing notation, so I just left it *)
Fixpoint Cprod (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C1
  | S n' => (Cprod f n' *  f n')%C
  end.

Lemma Cprod_1_bounded : forall (f : nat -> C) (n : nat),
  (forall i, i < n -> f i = C1) -> Cprod f n = C1. 
Proof. intros. 
       induction n as [| n'].
       - easy. 
       - simpl.
         rewrite H, IHn'; try lca.
         intros.
         apply H; lia.
         lia.
Qed.

Lemma Cprod_0_bounded : forall (f : nat -> C) (n : nat),
  (exists i, i < n /\ f i = C0) -> Cprod f n = C0. 
Proof. intros. 
       induction n as [| n'].
       - destruct H; lia.
       - destruct H as [i [H1 H2] ].
         bdestruct (i <? n'); bdestruct (i =? n'); try lia. 
         + simpl. rewrite IHn'; try lca.
           exists i. easy.
         + simpl. rewrite <- H0.
           rewrite H2; lca.
Qed.

Lemma Cprod_neq_0_bounded : forall (f : nat -> C) (n : nat),
  (forall i, i < n -> f i <> C0) -> Cprod f n <> C0.
Proof. induction n; intros; simpl.
       apply C1_neq_C0.
       apply Cmult_neq_0.
       apply IHn; intros.
       all : apply H; auto.
Qed.

Lemma Cprod_eq_bounded : forall (f g : nat -> C) (n : nat),
  (forall i : nat, i < n -> f i = g i) -> Cprod f n = Cprod g n.
Proof. intros.
       induction n as [| n'].
       - easy.
       - simpl.
         rewrite IHn', H; try lia; try easy.
         intros. apply H; lia. 
Qed.

Lemma Cprod_extend_r : forall (f : nat -> C) (n : nat),
  (Cprod f n * f n)%C = Cprod f (S n).
Proof. easy. Qed.

Lemma Cprod_extend_l : forall (f : nat -> C) (n : nat),
  (f 0 * (Cprod (fun x => f (S x)) n))%C = Cprod f (S n).
Proof. intros.
       induction n.
       + simpl; lca.
       + simpl.
         rewrite Cmult_assoc.
         rewrite IHn.
         simpl.
         reflexivity.
Qed.

Lemma Cprod_product : forall (f g h : nat -> C) (n : nat),
  (forall i, i < n -> h i = (f i * g i)%C) -> ((Cprod f n) * (Cprod g n))%C = Cprod h n.
Proof. induction n.
       + intros. lca. 
       + intros. simpl. 
         rewrite <- IHn, H; try lca; try lia. 
         intros. apply H; try lia. 
Qed.

(************************************)
(** * Defining upper triangular matrix *) 
(************************************)

Definition upper_triangular {n} (A : Square n) : Prop :=
  forall i j, i > j -> A i j = C0.

Lemma up_tri_Zero : forall n : nat, upper_triangular (@Zero n n).
Proof. intros n. unfold upper_triangular. reflexivity. Qed.

Lemma up_tri_I : forall n : nat, upper_triangular (I n). 
Proof. 
  unfold upper_triangular, I; intros.
  bdestruct (i =? j); try lia; easy.
Qed.

Lemma up_tri_I1 : upper_triangular (I 1). Proof. apply up_tri_I. Qed.

Lemma up_tri_scale : forall {n : nat} (r : C) (A : Square n), 
  upper_triangular A -> upper_triangular (r .* A).
Proof.
  unfold upper_triangular, scale.
  intros.
  rewrite H; try lca; easy.
Qed.

Lemma up_tri_col_scale_many : forall {n} (A : Square n) (as' : Matrix 1 n),
  upper_triangular A -> upper_triangular (col_scale_many A as').
Proof. intros.
       unfold col_scale_many, upper_triangular; intros.
       rewrite H; auto; lca.
Qed.

Lemma up_tri_plus : forall {n} (A B : Square n), 
  upper_triangular A -> upper_triangular B -> upper_triangular (A .+ B).
Proof.
  unfold upper_triangular, Mplus.
  intros n A B H H0 i j H1. 
  rewrite H, H0; try lca; easy. 
Qed.


Lemma up_tri_mult : forall {n : nat} (A B : Square n), 
  upper_triangular A -> upper_triangular B -> upper_triangular (A × B).
Proof.
  unfold upper_triangular, Mmult.
  intros n A B H H0 i j D.
  apply (@big_sum_0 C C_is_monoid).
  intros x.
  bdestruct (x <? i); bdestruct (j <? x); try lia.
  + rewrite H; try lca; lia.
  + rewrite H; try lca; lia.
  + rewrite H0; try lca; lia.
Qed.

Lemma up_tri_get_minor_0 : forall {n : nat} (A : Square (S n)),
  upper_triangular A -> upper_triangular (get_minor A 0 0).
Proof. 
  unfold upper_triangular, get_minor.
  intros. 
  bdestruct (i <? 0); bdestruct (j <? 0); try lia.
  apply H; lia. 
Qed.

Lemma det_up_tri_diags : forall {n : nat} (A : Square n),
  upper_triangular A -> 
  Determinant A = Cprod (fun i => A i i) n.
Proof. induction n as [| n'].
       - easy.
       - intros. simpl. 
         destruct n' as [| n''].
         + lca. 
         + assert (H' : (Cprod (fun i : nat => A i i) (S n'') * A (S n'') (S n'') =
                         A 0 0 * Cprod (fun i : nat => (get_minor A 0 0) i i) (S n''))%C).
           { rewrite <- Cprod_extend_l.
             rewrite <- Cprod_extend_r.  
             rewrite <- Cmult_assoc; easy. }
           rewrite H'.
           rewrite <- big_sum_extend_l.
           rewrite <- Cplus_0_r.
           rewrite <- Cplus_assoc.
           apply Cplus_simplify.
           simpl parity. 
           rewrite IHn'; try lca.
           apply up_tri_get_minor_0; easy.
           unfold upper_triangular in H.
           rewrite H; try lia. 
           rewrite <- Cplus_0_r.
           apply Cplus_simplify; try lca. 
           apply (@big_sum_0_bounded C C_is_monoid).
           intros. 
           rewrite H; try lia; lca. 
Qed.

Lemma up_tri_get_minor_upper_half : forall {n : nat} (A : Square (S n)) (i j : nat),
  i < j -> upper_triangular A -> 
  upper_triangular (get_minor A i j).
Proof. intros. 
       unfold upper_triangular, get_minor.
       intros. 
       bdestruct_all; apply H0; try lia.
Qed.

Lemma up_tri_adjugate : forall {n : nat} (A : Square n),
  upper_triangular A -> upper_triangular (adjugate A).
Proof. intros. 
       unfold adjugate, upper_triangular; intros. 
       destruct n; auto.
       bdestruct_all; simpl; auto.
       rewrite det_up_tri_diags.
       rewrite Cprod_0_bounded.
       lca.
       exists j; split.
       lia.
       unfold get_minor.
       bdestruct_all.
       rewrite H; auto; lia.
       apply up_tri_get_minor_upper_half; auto. 
Qed.

Lemma up_tri_inverse : forall {n : nat} (A : Square n),
  upper_triangular A -> upper_triangular (Minverse A).
Proof. intros. 
       unfold Minverse.
       apply up_tri_scale.
       apply up_tri_adjugate.
       auto.
Qed.


Definition unit_upper_triangular {n} (A : Square n) : Prop :=
  upper_triangular A /\ forall i, i < n -> A i i = C1.


Lemma unit_up_tri_I : forall n : nat, unit_upper_triangular (I n). 
Proof. 
  split. 
  apply up_tri_I.
  intros. 
  unfold I.
  bdestruct_all; easy.
Qed.

Lemma unit_up_tri_mult : forall {n : nat} (A B : Square n), 
  unit_upper_triangular A -> unit_upper_triangular B -> unit_upper_triangular (A × B).
Proof.
  intros n A B [H H0] [H1 H2]; split.
  apply up_tri_mult; auto.
  intros.
  unfold Mmult.
  rewrite (big_sum_unique C1); auto.
  exists i; split; auto; split.
  rewrite H0, H2; auto; lca.
  intros. 
  bdestruct (x' <? i); bdestruct (i <? x'); try lia.
  rewrite H; auto; lca.
  rewrite H1; auto; lca.
Qed.

Lemma unit_up_tri_det_1 : forall {n : nat} (A : Square n), 
  unit_upper_triangular A -> 
  Determinant A = C1.
Proof. intros.  
       rewrite det_up_tri_diags.
       rewrite Cprod_1_bounded; auto.
       intros.
       destruct H.
       rewrite H1; auto.
       apply H.
Qed.



(*****************************************************************************************)
(** * Explicitly Constructing the QR factorization of an invertible matrix *)
(*****************************************************************************************)


(* proj of v onto u *)
Definition proj {n} (u v : Vector n) : Vector n :=
  ((inner_product u v) / (inner_product u u)) .* u.

Definition proj_coef {n} (u v : Vector n) : C :=
  ((inner_product u v) / (inner_product u u)).

Lemma proj_inner_product : forall {n} (u v : Vector n),
  WF_Matrix u -> inner_product u (proj u v) = inner_product u v.
Proof. intros.
       destruct (mat_equiv_dec u Zero).
       - unfold inner_product, Mmult, adjoint, proj.
         repeat rewrite big_sum_0_bounded; auto.
         all : try intros; rewrite m; auto; lca.
       - unfold proj, inner_product. 
         distribute_scale.
         unfold scale. 
         unfold Cdiv.  
         rewrite <- Cmult_assoc. 
         rewrite Cinv_l.
         lca.
         apply inner_product_zero_iff_zero in H.
         contradict n0. 
         unfold norm, inner_product in H.
         apply H in n0.
         rewrite n0. easy. 
Qed.




(*****************************************************************************************)
(** * Defining and verifying the gram_schmidt algorythm and proving v can be part of an onb *)
(*****************************************************************************************)

Definition gram_schmidt_single_col {n} (T : Square n) (i : nat) : Square n :=
  fun x y => if (y =? i) && (x <? i) 
          then - (proj_coef (get_col T x) (get_col T i))
          else I n x y. 

Fixpoint gram_schmidt_until_i {n} (T : Square n) (i : nat) : Square n :=
  match i with 
  | O => I n
  | S i => (gram_schmidt_until_i T i) × 
             gram_schmidt_single_col (T × (gram_schmidt_until_i T i)) (S i)
  end.

Definition gram_schmidt {n} (T : Square n) : Square n :=
  T × gram_schmidt_until_i T (n - 1).


(* this definition makes the above easier to work with *)
Definition gram_schmidt_on_col {n : nat} (T : Square n) (i : nat) :=
   (big_sum (fun j => -C1 .* (proj (get_col T j) (get_col T i))) i) .+ (get_col T i).

Lemma WF_gssc : forall {n} (T : Square n) i, 
  i < n -> WF_Matrix (gram_schmidt_single_col T i).
Proof. intros. 
       unfold gram_schmidt_single_col, WF_Matrix, I; intros.
       bdestruct_all; easy.
Qed.

Lemma WF_gsoc : forall {n} (T : Square n) i, 
  i < n -> WF_Matrix T -> WF_Matrix (gram_schmidt_on_col T i).
Proof. intros.  
       unfold gram_schmidt_on_col.
       apply WF_plus; auto with wf_db.
       apply WF_Msum; intros. 
       unfold proj.
       auto with wf_db.
Qed.

Lemma WF_gsui : forall {n} (T : Square n) i, 
  i < n -> WF_Matrix T -> WF_Matrix (gram_schmidt_until_i T i).
Proof. induction i; intros.
       simpl; auto with wf_db.
       simpl. 
       apply WF_mult.
       apply IHi; auto; lia.
       apply WF_gssc; auto.
Qed.

Lemma WF_gram_schmidt : forall {n} (T : Square n), 
  WF_Matrix T -> WF_Matrix (gram_schmidt T).
Proof. intros. 
       destruct n.
       - unfold gram_schmidt; simpl.
         auto with wf_db.
       - unfold gram_schmidt.
         apply WF_mult; auto.
         apply WF_gsui; auto; lia.
Qed.

Lemma unit_upper_triangular_gsui : forall {n} (T : Square n) i, 
  unit_upper_triangular (gram_schmidt_until_i T i).
Proof. induction i.
       intros; simpl.
       split. 
       apply up_tri_I.
       unfold I; intros; bdestruct_all; lca.
       intros; simpl.
       apply unit_up_tri_mult.
       apply IHi; lia.
       split; unfold upper_triangular, gram_schmidt_single_col, I; intros;       
       bdestruct_all; simpl; auto.
Qed.


Lemma gram_schmidt_single_col_hit : forall {n} (T : Square n) (i : nat),
  WF_Matrix T -> i < n ->
  get_col (T × gram_schmidt_single_col T i) i = gram_schmidt_on_col T i.
Proof. intros. 
       apply mat_equiv_eq.
       auto with wf_db.
       apply WF_get_col; apply WF_mult; auto. 
       apply WF_gssc; auto.
       apply WF_gsoc; auto.
       unfold mat_equiv; intros.
       rewrite <- get_col_mult.
       unfold Mmult, get_col, gram_schmidt_single_col, gram_schmidt_on_col.
       unfold get_col, Mplus, proj, proj_coef, scale.
       bdestruct_all.
       rewrite Msum_Csum.
       replace n with (i + (n-i)) by lia.
       rewrite big_sum_sum.
       apply f_equal_gen; try apply f_equal.
       apply big_sum_eq_bounded; intros. 
       bdestruct_all; simpl; lca.
       apply lt_minus_O_lt in H0.
       destruct (n - i); try lia.
       rewrite <- big_sum_extend_l. 
       bdestruct_all; simpl.
       replace (big_sum _ _) with C0.
       unfold I; bdestruct_all; simpl.
       rewrite <- plus_n_O; lca.
       rewrite big_sum_0_bounded; auto.
       intros. 
       unfold I; bdestruct_all; simpl; lca.
Qed.
     
Lemma gram_schmidt_single_col_miss : forall {n} (T : Square n) (i j : nat),
  WF_Matrix T -> j < n -> i <> j ->  
  get_col (T × gram_schmidt_single_col T i) j = get_col T j.
Proof. intros. 
       prep_matrix_equality.
       unfold get_col, gram_schmidt_single_col, Mmult, I.
       bdestruct_all; auto.
       rewrite (big_sum_unique (T x j)); auto.
       exists j; split; auto; split.
       simpl; bdestruct_all; lca.
       intros. 
       simpl. bdestruct_all; lca.
Qed.

Lemma gram_schmidt_single_col_ver : forall {n} (T : Square n) (i : nat),
  WF_Matrix T -> i < n -> 
  (forall j k, j < i -> k < i -> j <> k -> inner_product (get_col T j) (get_col T k) = C0) ->
  (forall j, j < i -> inner_product (get_col T j) (get_col (T × (gram_schmidt_single_col T i)) i) = C0).
Proof. intros. 
       rewrite gram_schmidt_single_col_hit; auto.
       unfold gram_schmidt_on_col. 
       rewrite inner_product_plus_r, inner_product_big_sum_r.
       erewrite (big_sum_unique _). 
       2 : exists j; split; auto; split.
       2 : reflexivity.
       rewrite inner_product_scale_r, proj_inner_product; auto with wf_db.
       lca.
       intros. 
       unfold proj.
       rewrite 2 inner_product_scale_r, (H1 j x'); auto.
       lca.
Qed.

Lemma gram_schmidt_until_i_ver : forall {n} (i j k : nat) (T : Square n),
  WF_Matrix T -> i < n -> j <= i -> k <= i -> j <> k ->
      inner_product 
        (get_col (T × gram_schmidt_until_i T i) j)
        (get_col (T × gram_schmidt_until_i T i) k) = C0.
Proof. induction i; intros.
       destruct j; destruct k; lia.
       bdestruct (k <? S i).
       - simpl. 
         rewrite <- Mmult_assoc.
         rewrite (gram_schmidt_single_col_miss (T × gram_schmidt_until_i T i) _ k); try lia.
         bdestruct (j <? S i).
         + rewrite gram_schmidt_single_col_miss; try lia.
           apply IHi; auto; try lia.
           apply WF_mult; auto.
           apply WF_gsui; auto; lia.
         + bdestruct (j =? S i); try lia; subst.
           rewrite inner_product_conj_sym.
           rewrite (gram_schmidt_single_col_ver (T × gram_schmidt_until_i T i)); try lia.
           lca.
           apply WF_mult; auto; apply WF_gsui; auto; lia.
           intros. 
           apply IHi; auto; lia.
         + apply WF_mult; auto; apply WF_gsui; auto; lia.
       - bdestruct (k =? S i); try lia; subst.
         simpl.
         rewrite <- Mmult_assoc.
         rewrite gram_schmidt_single_col_miss; try lia.
         rewrite gram_schmidt_single_col_ver; auto; try lia.
         apply WF_mult; auto; apply WF_gsui; auto; lia.
         intros. 
         apply IHi; auto; try lia.
         apply WF_mult; auto; apply WF_gsui; auto; lia.
Qed.

Theorem gram_schmidt_ver : forall {n} (T : Square n),
  WF_Matrix T -> orthogonal (gram_schmidt T).
Proof. intros. 
       destruct n.
       - unfold orthogonal, gram_schmidt; intros; simpl; lca. 
       - unfold orthogonal, gram_schmidt; intros. 
         replace (S n - 1) with n by lia.
         bdestruct (i <? (S n)).
         bdestruct (j <? (S n)).
         rewrite gram_schmidt_until_i_ver; auto; lia.
         rewrite (get_col_over _ j); try lia. 
         3 : rewrite get_col_over; try lia. 
         all : try (unfold inner_product, Mmult, adjoint; 
                    rewrite big_sum_0_bounded; auto; intros; lca).
         all : apply WF_mult; try apply WF_gsui; auto.
Qed.         

Lemma gs_on_lin_indep_nonzero_cols : forall {n} (T : Square n) (i : nat),
  WF_Matrix T -> 
  linearly_independent T -> i < n ->
  get_col (gram_schmidt T) i <> Zero.
Proof. intros. 
       apply lin_indep_det_neq_0 in H0; auto.
       destruct H0.
       contradict H2.
       apply col_0_Det_0 in H2; auto.
       unfold gram_schmidt in H2.
       rewrite <- Determinant_multiplicative in H2. 
       rewrite (unit_up_tri_det_1 (gram_schmidt_until_i T (n - 1))) in H2.
       rewrite <- H2; lca.
       apply unit_upper_triangular_gsui.
Qed.


Definition normalize_cols_scalars {n} (T : Square n) : Matrix 1 n :=
  fun i j => if (i =? 0) && (j <? n) then
            / norm (get_col T j) else C0.

Lemma orthogonal_nonzero_cols_implies_orthonomalizable : forall {n} (T : Square n),
  WF_Matrix T -> orthogonal T -> 
  (forall i, i < n -> get_col T i <> Zero) -> 
  WF_Orthonormal (col_scale_many T (normalize_cols_scalars T)).
Proof. intros. 
       split; auto with wf_db.
       split.
       unfold orthogonal; intros. 
       rewrite 2 get_col_col_scale_many.
       rewrite inner_product_scale_l, inner_product_scale_r.
       rewrite H0; auto; lca.
       intros. 
       rewrite get_col_col_scale_many.
       unfold normalize_cols_scalars.
       bdestruct_all; simpl. 
       apply H1 in H2.
       apply norm_nonzero_iff_nonzero in H2; auto with wf_db.
       apply normalized_norm_1 in H2. 
       easy.
Qed.

(* messy, but the important part is the properties *)
Definition QR_factorization_R_inv {n} (T : Square n) :=
  (col_scale_many (gram_schmidt_until_i T (n - 1)) 
                  (normalize_cols_scalars (T × gram_schmidt_until_i T (n - 1)))).

Definition QR_factorization_R {n} (T : Square n) :=
  Minverse (QR_factorization_R_inv T).

Definition QR_factorization_Q {n} (T : Square n) :=
  T × (QR_factorization_R_inv T).



Lemma WF_Matrix_R_inv : forall {n} (T : Square n),
  WF_Matrix T -> WF_Matrix (QR_factorization_R_inv T).
Proof. intros. 
       unfold QR_factorization_R_inv.
       apply WF_col_scale_many.
       destruct n.
       - simpl. auto with wf_db.
       - apply WF_gsui; auto; try lia.
Qed.

Lemma WF_Matrix_R : forall {n} (T : Square n),
  WF_Matrix (QR_factorization_R T).
Proof. intros. 
       unfold QR_factorization_R, Minverse.
       apply WF_scale; apply WF_adjugate.
Qed.      

Lemma WF_Matrix_Q : forall {n} (T : Square n),
  WF_Matrix T -> WF_Matrix (QR_factorization_Q T).
Proof. intros. 
       unfold QR_factorization_Q, QR_factorization_R_inv.
       destruct n; try easy.
       apply WF_mult; auto.
       apply WF_col_scale_many.
       apply WF_gsui; auto.
       lia. 
Qed.

#[export] Hint Resolve WF_Matrix_R_inv WF_Matrix_R WF_Matrix_Q : wf_db.

Lemma R_inv_upper_tri : forall {n} (T : Square n),
  upper_triangular (QR_factorization_R_inv T).
Proof. intros.
       unfold QR_factorization_R_inv.
       apply up_tri_col_scale_many.
       apply unit_upper_triangular_gsui.
Qed.

Lemma R_upper_tri : forall {n} (T : Square n),
  upper_triangular (QR_factorization_R T).
Proof. intros.
       unfold QR_factorization_R.
       apply up_tri_inverse.
       apply R_inv_upper_tri.
Qed.

Lemma R_inv_det_neq_0 : forall {n} (T : Square n),
  WF_Matrix T -> linearly_independent T -> 
  Determinant (QR_factorization_R_inv T) <> C0.
Proof. intros. 
       rewrite det_up_tri_diags.
       apply Cprod_neq_0_bounded; intros. 
       unfold QR_factorization_R_inv, col_scale_many, normalize_cols_scalars.
       assert (H2 := unit_upper_triangular_gsui T (n-1)).
       destruct H2; rewrite H3; auto.
       bdestruct_all; simpl. 
       apply Cmult_neq_0.
       apply nonzero_div_nonzero.
       apply (gs_on_lin_indep_nonzero_cols T i) in H0; auto.
       apply norm_nonzero_iff_nonzero in H0.
       contradict H0.
       apply RtoC_inj in H0.
       easy.
       apply WF_get_col; apply WF_gram_schmidt; auto.
       apply C1_neq_C0.
       apply R_inv_upper_tri.
Qed.

Lemma Q_is_unitary : forall {n} (T : Square n),
  WF_Matrix T -> linearly_independent T -> 
  WF_Orthonormal (QR_factorization_Q T).
Proof. destruct n; try easy.
       intros. 
       unfold QR_factorization_Q, QR_factorization_R_inv.
       rewrite col_scale_many_mult_r, <- Mmult_assoc, <- col_scale_many_mult_r.
       apply orthogonal_nonzero_cols_implies_orthonomalizable.
       all : try apply WF_mult; auto.
       all : try apply WF_gsui; auto; try lia.
       apply gram_schmidt_ver in H; easy.
       intros. 
       apply (gs_on_lin_indep_nonzero_cols T i) in H0; auto.
Qed.

Theorem QR_factorization : forall {n} (T : Square n),
  WF_Matrix T -> linearly_independent T ->
  T = QR_factorization_Q T × QR_factorization_R T.
Proof. intros. 
       unfold QR_factorization_Q, QR_factorization_R.
       rewrite Mmult_assoc, Mmult_Minverse_r. 
       rewrite Mmult_1_r; auto.
       auto with wf_db.
       apply R_inv_det_neq_0; auto.
Qed.


(* another useful lemma *)
Lemma QR_preserves_first_col : forall {n} (T : Square n),
  WF_Matrix T -> 
  (QR_factorization_R_inv T) O O .* get_col T O = get_col (QR_factorization_Q T) O.
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold QR_factorization_Q, get_col, scale, mat_equiv, Mmult; intros. 
       destruct j; try lia; simpl.
       destruct n; try lia.
       rewrite <- big_sum_extend_l.
       rewrite big_sum_0_bounded.
       lca.
       intros. 
       rewrite R_inv_upper_tri.
       lca.
       lia.
Qed.

Lemma R_inv_00_norm : forall {n} (T : Square n),
  n <> 0 -> 
  WF_Matrix T -> linearly_independent T -> 
  (QR_factorization_R_inv T) O O = / norm (get_col T 0).
Proof. intros. 
       destruct n; try lia.
       unfold QR_factorization_R_inv, col_scale_many.
       assert (H2 := unit_upper_triangular_gsui T (S n - 1)).
       destruct H2.
       rewrite H3; try lia.
       unfold normalize_cols_scalars.
       simpl. 
       rewrite Cmult_1_r.
       do 3 try apply f_equal_gen; auto.
       apply mat_equiv_eq; auto with wf_db.
       apply WF_get_col; apply WF_mult; auto.
       apply WF_gsui; try lia; auto.
       unfold mat_equiv; intros.
       destruct j; try lia.
       unfold get_col, Mmult.
       rewrite <- big_sum_extend_l; simpl.
       rewrite H3, big_sum_0_bounded; auto.
       lca.
       intros.
       rewrite H2; try lia.
       lca.
       lia.
Qed.

Corollary R_inv_00_neq_0 : forall {n} (T : Square n),
  n <> 0 ->
  WF_Matrix T -> linearly_independent T -> 
  (QR_factorization_R_inv T) O O <> C0.
Proof. intros. 
       destruct n; try lia.
       unfold not; intros.  
       apply R_inv_det_neq_0 in H1; auto.
       apply H1.
       rewrite det_up_tri_diags.
       rewrite <- Cprod_extend_l, H2.
       lca.
       apply R_inv_upper_tri.
Qed.

Corollary R_inv_00_real : forall {n} (T : Square n),
  n <> 0 ->
  WF_Matrix T -> linearly_independent T -> 
  snd ((QR_factorization_R_inv T) O O) = 0%R.
Proof. intros.  
       rewrite R_inv_00_norm; auto.
       rewrite div_real; auto.
Qed.

(*
Corollary R_inv_00_pos : forall {n} (T : Square n),
  n <> 0 ->
  WF_Matrix T -> linearly_independent T -> 
  (fst ((QR_factorization_R_inv T) O O) > 0)%R.
Proof. intros. 
       destruct n; try lia.
       unfold QR_factorization_R_inv, col_scale_many.
       assert (H2 := unit_upper_triangular_gsui T (S n - 1)).
       destruct H2.
       rewrite H3; try lia.
       unfold normalize_cols_scalars.
       remember (/ _ ) as a.
       simpl.
       autorewrite with R_db.
       Admitted. 
*)



(************************************)
(** * Lemmas relating to forming bases *)
(************************************)

(* NB: we can do all this constructively (already done in stab_types branch) but since the FTA
   proof isn't constructive (this is possible, but very hard), it doesn't matter too much, 
   since the spectral basis will ultimitely be nonconstructive *)

Definition form_basis {n} (v : Vector n) (non_zero : nat) : Matrix n n :=
  fun x y => if (y =? non_zero) 
             then (v x 0)
             else (@e_i n y x 0).

Lemma WF_form_basis : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> x < n -> WF_Matrix (form_basis v x).
Proof. unfold WF_Matrix, form_basis, e_i. 
       intros. 
       bdestruct (y =? x).
       apply H.
       destruct H1; auto; lia.
       bdestruct (x0 =? y); try easy.
       bdestruct (x0 <? n); try lia; try easy.
Qed.       

Lemma get_v_in_basis : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> get_col (form_basis v x) x = v.
Proof. intros. 
       prep_matrix_equality.
       unfold get_col, form_basis.
       bdestruct (y =? 0).
       rewrite Nat.eqb_refl, H0; easy.
       unfold WF_Matrix in H.
       rewrite H; try easy.
       right. 
       destruct y; try lia; try easy.
Qed.

Lemma get_ei_in_basis : forall {n} (v : Vector n) (x y : nat),
  y < n -> y <> x -> get_col (form_basis v x) y = e_i y.
Proof. intros. 
       prep_matrix_equality.
       unfold get_col, form_basis.
       bdestruct (y0 =? 0).
       bdestruct (y =? x); try easy.
       rewrite H1; easy.
       unfold e_i.
       bdestruct (x0 =? y); bdestruct (x0 <? n); bdestruct (y0 =? 0); try easy. 
Qed.

Lemma form_basis_ver : forall {n} (v : Vector n) (x : nat),
  v <> Zero -> WF_Matrix v -> v x 0 <> C0 -> x < n -> 
  linearly_independent (form_basis v x) /\ get_col (form_basis v x) x = v.
Proof. intros.
       destruct n; try lia. split.
       - apply (mat_prop_col_add_many_conv _ _ x (-C1 .* (make_row_val v x C0))); 
           try easy; auto with invr_db.
         unfold scale, make_row_val. 
         bdestruct (x =? x); try lia; lca. 
         apply (mat_prop_col_scale_conv _ _ x (/ (v x 0))); auto with invr_db.
         apply nonzero_div_nonzero; easy.
         assert (H' : forall A : Square (S n), A = I (S n) -> linearly_independent A).
         { intros. rewrite H3. 
           apply lin_indep_iff_invertible; auto with wf_db.
           unfold invertible. exists (I (S n)).
           split; auto with wf_db.
           unfold Minv. 
           split; rewrite Mmult_1_l; auto with wf_db. }
         apply H'. 
         apply mat_equiv_eq; auto with wf_db. 
         apply WF_col_scale. 
         apply WF_col_add_many; try easy.
         apply WF_form_basis; easy. 
         unfold mat_equiv; intros. 
         unfold col_scale, col_add_many, make_row_val, 
         form_basis, scale, gen_new_col, get_col.
         assert (H0' : forall a b : C, a = C0 -> (b + a = b)%C). 
         { intros. rewrite H5. lca. }
         bdestruct (j =? x); bdestruct (j =? i).
         all : try rewrite Msum_Csum. 
         all : try unfold scale. 
         rewrite H5 in *. rewrite <- H6.
         rewrite H0'. 
         unfold I. 
         bdestruct (x =? x); bdestruct (x <? S n); try lia. 
         rewrite Cinv_l; try easy. 
         rewrite big_sum_0_bounded; try easy.
         unfold e_i.
         intros. 
         bdestruct (x0 =? x); try lia; try lca. 
         bdestruct (x =? x0); try lia; lca.          
         rewrite (big_sum_unique (-C1 * (v i 0))%C).
         unfold I. bdestruct (i =? j); try lia; simpl. 
         lca. exists i. split; try easy. 
         split. simpl. 
         rewrite H5 in *.
         bdestruct (i =? x); try lia. 
         unfold e_i. 
         bdestruct (i =? i); bdestruct (i <? S n); simpl; try lia; lca. 
         intros. 
         bdestruct (x' =? x); try lca. 
         simpl; unfold e_i.
         bdestruct (i =? x'); simpl; try lia; lca. 
         rewrite H6.
         all : unfold e_i, I.
         all : bdestruct (i =? i); bdestruct (i <? S n); simpl; try lia; try easy.  
         bdestruct (i =? j); easy.
       - apply get_v_in_basis; easy.
Qed.

Theorem lin_indep_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero ->
  exists S : Square n, WF_Matrix S /\ linearly_independent S /\ get_col S 0 = v. 
Proof. intros. 
       destruct n. 
       - exists Zero. 
         split. easy. 
         split. 
         unfold linearly_independent.
         intros. unfold WF_Matrix in H1. 
         prep_matrix_equality. 
         apply H1; lia.
         prep_matrix_equality. 
         unfold get_col, Zero.
         unfold WF_Matrix in H. 
         rewrite H; try lia. 
         bdestruct (y =? 0); easy.
       - assert (H' := H).
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         exists (col_swap (form_basis v x) x 0).
         assert (H' : x < S n).
         { bdestruct (x <? S n); try easy. 
           unfold WF_Matrix in H.
           unfold not in H1. 
           assert (H' : v x 0 = C0). 
           { apply H. lia. }
           easy. }
         assert (H'' : linearly_independent (form_basis v x) /\ get_col (form_basis v x) x = v).
         { apply form_basis_ver; try easy. }
         split.
         apply WF_col_swap; try lia; try easy.
         apply WF_form_basis; easy.
         split. 
         + apply_mat_prop lin_indep_swap_invr.  
           apply H3; try lia.
           easy. 
         + rewrite col_swap_diff_order.
           rewrite (col_swap_get_col _ 0 x).
           apply get_v_in_basis. 
           easy. 
Qed.         



(* Given the proof of QR above, we now get this for free! (contrast older branch) *)
Theorem onb_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> 
  exists T : Square n, WF_Orthonormal T /\ get_col T 0 = normalize v.
Proof. intros. 
       destruct n as [| n].
       - assert (H' : v = Zero).
         prep_matrix_equality.
         rewrite H; try lia; easy.
         easy.
       - destruct (lin_indep_out_of_v v) as [X [H2 [H3 H4] ] ]; auto.
         exists (QR_factorization_Q X).
         split.
         apply Q_is_unitary; auto.
         rewrite <- QR_preserves_first_col, R_inv_00_norm; auto. 
         rewrite H4.
         easy.
Qed.


Corollary unit_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> 
  exists S : Square n, WF_Unitary S /\ get_col S 0 = normalize v.
Proof. intros.
       apply onb_out_of_v in H; try easy.
       destruct H as [S [H1 H2] ].
       exists S. split; try easy.
       apply unit_is_orthonormal; easy.
Qed.



(***************************************************)
(** * showing that all matrices have some eigenvector *)
(***************************************************)

(* We first must define a new type to connect polynomials to matrices *)

Definition MatrixP (m n : nat) := nat -> nat -> Polynomial.

Notation SquareP n := (MatrixP n n).

Definition eval_matP {n m} (A : MatrixP n m) (c : C) : Matrix n m :=
  fun x y => (A x y)[[c]]. 

Definition get_minorP {n} (A : SquareP (S n)) (row col : nat) : SquareP n :=
  fun x y => (if x <? row 
              then (if y <? col 
                    then A x y
                    else A x (1+y))
              else (if y <? col 
                    then A (1+x) y
                    else A (1+x) (1+y))).

Lemma get_minorP_eval_mat : forall {n} (A : SquareP (S n)) (c : C) (x y : nat),
  get_minor (eval_matP A c) x y = eval_matP (get_minorP A x y) c.
Proof. intros. 
       prep_matrix_equality.
       unfold get_minor, eval_matP, get_minorP.
       bdestruct_all; easy. 
Qed.

Fixpoint DeterminantP (n : nat) (A : SquareP n) : Polynomial :=
  match n with 
  | 0 => [C1]
  | S 0 => A 0 0
  | S n' => (big_sum (fun i => [(parity i)] *, (A i 0) *, (DeterminantP n' (get_minorP A i 0)))%C n)
  end.

Arguments DeterminantP {n}. 

Lemma DetP_simplify : forall {n} (A : SquareP (S (S n))),
  DeterminantP A =  
  (big_sum (fun i => [(parity i)] *, (A i 0) *, (DeterminantP (get_minorP A i 0)))%C (S (S n))).
Proof. intros. easy. Qed.

Lemma Peval_Det : forall {n} (A : SquareP n) (c : C),
  Determinant (eval_matP A c) = (DeterminantP A)[[c]].
Proof. induction n as [| n']. 
       - intros; lca.  
       - intros. 
         destruct n'. 
         + simpl. easy. 
         + rewrite DetP_simplify, Det_simplify.
           rewrite Psum_eval.
           apply big_sum_eq_bounded; intros.
           rewrite get_minorP_eval_mat, IHn'.
           do 2 rewrite Pmult_eval.
           repeat apply f_equal_gen; try easy.  
           unfold Peval; lca. 
Qed.

(* not really useful except for in the proof of connect *)
Definition prep_mat {n} (A : Square n) : SquareP n := 
  (fun x y => if (x =? y) && (x <? n) then [A x y; -C1] else [A x y]).

(* we must first show that degree (DeterminantP (prep_mat A)) = n *)

Definition deg_elem_leq_1 {n} (A : SquareP n) : Prop :=
  forall i j, degree (A i j) <= 1.
  
Lemma del1_reduce : forall {n} (A : SquareP (S n)) (i j : nat),
  deg_elem_leq_1 A -> deg_elem_leq_1 (get_minorP A i j).
Proof. unfold deg_elem_leq_1, get_minorP in *; intros. 
       bdestruct_all; easy.
Qed.

Lemma bound_deg_matP : forall {n} (A : SquareP n),
  deg_elem_leq_1 A -> degree (DeterminantP A) <= n.
Proof. induction n as [| n'].
       - intros.
         unfold degree, compactify; simpl. 
         destruct (Ceq_dec C1 C0); easy.
       - intros.
         destruct n'.
         + simpl. 
           apply H.
         + rewrite DetP_simplify.
           apply Psum_degree; intros. 
           destruct (Peq_dec (A i 0) []).
           rewrite p, Pmult_0_r.
           unfold degree; simpl; lia. 
           destruct (Peq_dec (DeterminantP (get_minorP A i 0)) []).
           rewrite p, Pmult_0_r.
           unfold degree; simpl; lia. 
           destruct (Peq_dec [parity i] []).
           rewrite p. 
           unfold degree; simpl; lia.
           destruct (Peq_dec ([parity i] *, A i 0) []).
           rewrite p. 
           unfold degree; simpl; lia.
           repeat rewrite Pmult_degree; auto. 
           assert (H' : degree [parity i] = 0).
           { unfold degree, compactify; simpl.  
             destruct (Ceq_dec (parity i) C0); easy. }
           rewrite H', <- (Nat.add_1_l (S n')), Nat.add_0_l.  
           apply Nat.add_le_mono; auto.
           apply IHn'.
           apply del1_reduce; easy. 
Qed.

(* we now prove prepmat is del1 *)
Lemma del1_prep_mat : forall {n} (A : Square n),
  deg_elem_leq_1 (prep_mat A).
Proof. unfold deg_elem_leq_1, prep_mat; intros.
       destruct ((i =? j) && (i <? n)).
       all : unfold degree, compactify; simpl. 
       destruct (Ceq_dec (- C1) C0); simpl; try lia. 
       all : destruct (Ceq_dec (A i j) C0); simpl; lia.
Qed.

Lemma reduce_prep_mat : forall {n} (A : Square (S n)),
  get_minorP (prep_mat A) 0 0 = prep_mat (get_minor A 0 0).
Proof. intros. 
       prep_matrix_equality.
       unfold get_minorP, get_minor, prep_mat.
       bdestruct_all; simpl; try easy. 
Qed.       

(* this got annoyingly long. Probably want to add some helper lemmas at some point *)
Lemma detP_deg : forall {n} (A : Square n),
  degree (DeterminantP (prep_mat A)) = n.
Proof. induction n as [| n'].
       - intros. 
         unfold degree, compactify; simpl. 
         destruct (Ceq_dec C1 C0); easy.
       - intros. 
         destruct n'.  
         + unfold degree, compactify; simpl. 
           destruct (Ceq_dec (- C1) C0); try easy.
           assert (H' : - (- C1) = C0).
           { rewrite e; lca. }
           replace (- - C1) with C1 in H' by lca. 
           apply C1_neq_C0 in H'; easy. 
         + rewrite DetP_simplify.
           assert (H' : forall n f, big_sum f (S n) = f 0 +, big_sum (fun i => f (S i)) n). 
           { intros. 
             induction n. 
             + simpl. 
               destruct (f 0); try easy; simpl. 
             + simpl in *. 
               rewrite IHn, Pplus_assoc; easy. }
           assert (H0 : degree (prep_mat A 0 0) = 1). 
           { unfold prep_mat.
             bdestruct_all; simpl. 
             unfold degree, compactify; simpl. 
             destruct (Ceq_dec (- C1) C0); try easy. 
             assert (H'' := C1_neq_C0).
             replace C1 with (-C1 * -C1)%C in H'' by lca.  
             rewrite e, Cmult_0_l in H''; easy. }
           assert (H1 : degree ([parity 0] *, prep_mat A 0 0 *, 
                                            DeterminantP (get_minorP (prep_mat A) 0 0)) = S (S n')).
           { simpl parity.             
             rewrite Pmult_1_l, Pmult_degree, reduce_prep_mat, H0, IHn'.
             easy.
             destruct (Peq_dec (prep_mat A 0 0) []); auto. 
             rewrite p in H0; easy. 
             destruct (Peq_dec (DeterminantP (get_minorP (prep_mat A) 0 0)) []); auto. 
             rewrite reduce_prep_mat in *.
             assert (H1 := (IHn' (get_minor A 0 0))).
             rewrite p in H1; easy. }
           rewrite H', Pplus_comm, Pplus_degree2; auto. 
           rewrite H1. 
           apply Nat.lt_succ_r.
           apply Psum_degree; intros. 
           assert (H2 : prep_mat A (S i) 0 = [A (S i) 0]).
           { unfold prep_mat. 
             bdestruct_all; easy. }
           rewrite H2. 
           replace ([parity (S i)] *, [A (S i) 0]) with [parity (S i) * A (S i) 0]%C. 
           destruct (Peq_dec [(parity (S i) * A (S i) 0)%C] []).
           rewrite p; simpl. 
           unfold degree, compactify; simpl; try lia. 
           destruct (Peq_dec (DeterminantP (get_minorP (prep_mat A) (S i) 0)) []).
           rewrite p, Pmult_0_r. 
           unfold degree, compactify; simpl; try lia. 
           rewrite Pmult_degree; auto. 
           rewrite <- Nat.add_0_l.
           apply Nat.add_le_mono.
           destruct (parity (S i) * A (S i) 0)%C eqn:E.
           unfold degree, compactify; simpl. 
           destruct (Ceq_dec (r, r0) C0); simpl; lia. 
           apply bound_deg_matP.
           apply del1_reduce.
           apply del1_prep_mat.
           simpl; rewrite Cplus_0_r. easy. 
Qed.


Lemma connect : forall (n : nat) (A : Square (S n)),
  exists (p : Polynomial), (Polynomial.degree p) > 0 /\
    (forall c : C, Determinant (A .+ (-c .* I (S n))) = p[[c]]).
Proof. intros. 
       exists (DeterminantP (prep_mat A)).
       split; intros. 
       rewrite detP_deg; lia. 
       rewrite <- Peval_Det.
       apply f_equal_gen; try easy. 
       prep_matrix_equality.
       unfold prep_mat, eval_matP, Peval, I, Mplus, scale.
       bdestruct_all; simpl; lca. 
Qed.

Lemma connect2 : forall (n : nat) (A : Square (S n)),
  exists (c : C), det_eq_c C0 (A .+ (-c .* I (S n))).
Proof. intros. 
       destruct (connect n A) as [p [H H0] ].
       destruct (Fundamental_Theorem_Algebra p); auto.
       exists x. 
       split; auto. 
       rewrite H0; easy.
Qed.
     
Theorem exists_eigenvector : forall (n : nat) (A : Square (S n)),
  WF_Matrix A -> 
  exists (c : C) (v : Vector (S n)), WF_Matrix v /\ v <> Zero /\ A × v = c.* v.
Proof. intros. 
       destruct (connect2 n A) as [c H0].
       apply lin_dep_det_eq_0 in H0; auto with wf_db.
       destruct H0 as [v [H1 [H2 H3] ] ].
       exists c, v.
       split; auto. 
       split; auto. 
       rewrite Mmult_plus_distr_r, Mscale_mult_dist_l, Mmult_1_l in H3; auto.
       assert (H4 : A × v .+ (-c .* v) .+ (c .* v) = (c .* v)).
       { rewrite H3. lma. }
       rewrite Mplus_assoc in H4.
       rewrite <- Mscale_plus_distr_l in H4. 
       replace (-c + c)%C with C0 in H4 by lca.
       rewrite <- H4.
       lma. 
Qed.

(**************************************************)
(** * Proving that every matrix has a Schur Decomposition *)
(**************************************************)

(* first, two helper defs *)
Definition first_col_e_i {m n} (A : Matrix m n) :=
  forall i, 0 < i -> A i 0 = C0. 

Definition first_row_e_i {m n} (A : Matrix m n) :=
  forall i, 0 < i -> A 0 i = C0. 

Lemma fce_pad1 : forall {m n} (A : Matrix m n) (a : C),
  first_col_e_i (pad1 A a).
Proof. intros. 
       unfold first_col_e_i, pad1, col_wedge, row_wedge, e_i, scale; intros.
       bdestruct_all; lca.
Qed.

Lemma fre_pad1 : forall {m n} (A : Matrix m n) (a : C),
  first_row_e_i (pad1 A a).
Proof. intros. 
       unfold first_row_e_i, pad1, col_wedge, row_wedge, e_i, scale; intros.
       bdestruct_all; lca.
Qed.

Lemma frc_and_fre_pad1 : forall {m n} (A : Matrix m n) (a : C),
  first_col_e_i (pad1 A a) /\ first_row_e_i (pad1 A a).
Proof. intros.
       split.
       apply fce_pad1.
       apply fre_pad1.
Qed.

Lemma fce_mult : forall {m n o} (A : Matrix m n) (B : Matrix n o),
  first_col_e_i A -> first_col_e_i B ->
  first_col_e_i (A × B).
Proof. intros.
       unfold first_col_e_i, Mmult; intros.
       rewrite big_sum_0_bounded; auto.
       intros. 
       destruct x.
       rewrite H; auto.
       lca.
       rewrite H0. 
       lca.
       lia.
Qed.

Lemma fre_mult : forall {m n o} (A : Matrix m n) (B : Matrix n o),
  first_row_e_i A -> first_row_e_i B ->
  first_row_e_i (A × B).
Proof. intros.
       unfold first_row_e_i, Mmult; intros.
       rewrite big_sum_0_bounded; auto.
       intros. 
       destruct x.
       rewrite H0; auto.
       lca.
       rewrite H. 
       lca.
       lia.
Qed.

Lemma fce_and_fre_mult : forall {m n o} (A : Matrix m n) (B : Matrix n o),
  (first_col_e_i A /\ first_row_e_i A) -> 
  (first_col_e_i B /\ first_row_e_i B) -> 
  (first_col_e_i (A × B) /\ first_row_e_i (A × B)).
Proof. intros.
       destruct H; destruct H0.
       split.
       apply fce_mult; auto.
       apply fre_mult; auto.
Qed.

Lemma fce_get_minor_reduction : forall {m n o} (A : Matrix (S m) (S n)) (B : Matrix (S n) (S o)),
  first_col_e_i A -> 
  get_minor (A × B) 0 0 = (get_minor A 0 0) × (get_minor B 0 0).
Proof. intros. 
       prep_matrix_equality.
       unfold get_minor, Mmult.
       bdestruct_all.
       rewrite <- big_sum_extend_l.
       rewrite H; try lia.
       Csimpl.
       apply big_sum_eq_bounded.
       intros. 
       bdestruct_all.
       easy.
Qed.

Lemma fre_get_minor_reduction : forall {m n o} (A : Matrix (S m) (S n)) (B : Matrix (S n) (S o)),
  first_row_e_i B -> 
  get_minor (A × B) 0 0 = (get_minor A 0 0) × (get_minor B 0 0).
Proof. intros. 
       prep_matrix_equality.
       unfold get_minor, Mmult.
       bdestruct_all.
       rewrite <- big_sum_extend_l.
       rewrite H; try lia.
       Csimpl.
       apply big_sum_eq_bounded.
       intros. 
       bdestruct_all.
       easy.
Qed.

Lemma first_col_e_i_ver_weak : forall {m n} (A : Matrix m n) (c : C),
  WF_Matrix A -> get_col A 0 = c .* e_i 0 -> first_col_e_i A.
Proof. intros. 
       unfold first_col_e_i; intros.
       rewrite <- (get_col_conv i 0).
       rewrite H0.
       unfold scale, e_i.
       bdestruct_all; lca.
Qed.       

Lemma first_col_e_i_ver : forall {m n} (A : Matrix m n),
  WF_Matrix A -> (first_col_e_i A <-> get_col A 0 = A 0 0 .* e_i 0).
Proof. intros. 
       split; intros.
       - apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv.
         intros. 
         unfold get_col, e_i, scale.
         bdestruct_all; subst; try lca.
         simpl.
         rewrite H0; try lia.
         lca.
       - eapply first_col_e_i_ver_weak; try apply H0; easy.
Qed.

Lemma first_entry_e_i : forall {m n} (A : Matrix (S m) n) (c : C),
  get_col A 0 = c .* e_i 0 -> A 0 0 = c.
Proof. intros. 
       rewrite <- (get_col_conv 0 0), H.
       unfold scale, e_i.
       bdestruct_all.
       lca.
Qed.

Lemma first_entry_e_i' : forall {m n} (A : Matrix (S m) n) (c : C),
  get_col A 0 = c .* e_i 0 -> 
  get_col A 0 = A 0 0 .* e_i 0.
Proof. intros. 
       rewrite (first_entry_e_i A c); auto.
Qed.

Lemma upper_triangular_reduction : forall {n} (A : Square (S n)),
  first_col_e_i A -> upper_triangular (get_minor A 0 0) -> 
  upper_triangular A.
Proof. intros. 
       unfold upper_triangular in *; intros.
       destruct j.
       rewrite H; auto.
       destruct i; try lia.
       bdestruct (j <? i); try lia.
       apply H0 in H2.
       unfold get_minor in H2.
       simpl in H2.
       easy.
Qed.

Lemma upper_triangular_reduction_conv : forall {n} (A : Square (S n)),
  upper_triangular A -> 
  first_col_e_i A /\ upper_triangular (get_minor A 0 0).
Proof. intros. 
       split.
       unfold first_col_e_i; intros.
       rewrite H; auto; lia.
       unfold upper_triangular, get_minor; intros. 
       bdestruct_all.
       rewrite H; auto; lia.
Qed.

Lemma diagonal_reduction : forall {m n} (A : Matrix (S m) (S n)),
  WF_Matrix A ->
  (first_col_e_i A /\ first_row_e_i A) -> WF_Diagonal (get_minor A 0 0) -> 
  WF_Diagonal A.
Proof. intros. destruct H0. 
       split; auto.
       destruct H1.
       intros. 
       destruct j.
       rewrite H0; auto; lia.
       destruct i.
       rewrite H2; auto; lia. 
       replace (A (S i) (S j)) with (get_minor A 0 0 i j).
       rewrite H3; auto; lia.
       unfold get_minor.
       bdestruct_all. easy.
Qed.


(* this proof works quite nicely on a higher level now that we have build up many matrix tools *)
Lemma Schur_reduction_step : forall {n} (A : Square (S n)),
  WF_Matrix A ->
  exists X, WF_Unitary X /\ first_col_e_i (X†×A×X). 
Proof. intros n A Hwf.
       destruct (exists_eigenvector _ A) as [c [v [H [H0 H1] ] ] ]; auto. 
       assert (H' := H0).
       apply onb_out_of_v in H0; auto.
       destruct H0 as [T [ [H2 H3] H4] ].
       exists T.
       assert (H5 : WF_Unitary T).
       apply unit_is_orthonormal; easy.
       split; auto.  
       apply (first_col_e_i_ver_weak _ c); auto with wf_db.
       rewrite matrix_by_basis; try lia. 
       apply (Mmult_cancel_l T); auto with wf_db.
       apply unit_det_neq_0.  
       apply unit_is_orthonormal.
       split; auto.
       repeat rewrite <- Mmult_assoc. 
       destruct H5.
       apply Minv_flip in H5; auto with wf_db. 
       rewrite H5, Mscale_mult_dist_r, Mmult_1_l; auto.
       rewrite Mmult_assoc, <- matrix_by_basis, H4; try lia.
       unfold normalize.
       rewrite Mscale_mult_dist_r, H1.
       lma'.
Qed. 

(* this one is also not too bad, once we have the obscure lemmas above *)
Theorem Schur_form : forall {n} (A : Square n),
  WF_Matrix A ->
  exists U, WF_Unitary U /\ upper_triangular (U†×A×U).
Proof. induction n; intros.
       - exists Zero.
         split; split; auto with wf_db.
         rewrite Mmult_0_r.
         prep_matrix_equality.
         unfold I; bdestruct_all; easy.
       - destruct (Schur_reduction_step A) as [X [H0 H1] ]; auto.
         destruct (IHn (get_minor (X†×A×X) 0 0)) as [X' [H2 H3] ].
         destruct H0; auto with wf_db. 
         exists (X × pad1 X' C1).
         split.   
         apply Mmult_unitary; auto.
         apply pad1_unitary; auto. 
         lca.
         rewrite Mmult_adjoint.
         rewrite pad1_adjoint, 2 Mmult_assoc, <- (Mmult_assoc _ A), <- (Mmult_assoc _ X).
         apply upper_triangular_reduction.
         + repeat (apply fce_mult; try easy); apply fce_pad1.
         + rewrite 2 fce_get_minor_reduction; auto.
           rewrite <- 2 get_minor_pad1.
           rewrite <- Mmult_assoc.
           easy.
           apply fce_pad1.
Qed.

(* we need a few more lemmas, using the above machinery *)
Lemma normal_tri_is_fce : forall {n} (T : Square n),
  WF_Matrix T ->
  upper_triangular T -> T† × T = T × T† ->
  first_col_e_i (T ⊤).
Proof. intros. 
       unfold first_col_e_i, transpose; intros. 
       destruct n.
       rewrite H; auto; try lia.
       do 2 apply (f_equal_inv 0) in H1.
       unfold adjoint, Mmult in H1.
       bdestruct (i <? S n).
       2 : rewrite H; auto; lia.
       rewrite (big_sum_unique ((T 0 0)^* * (T 0 0))%C) in H1. 
       2 : { exists 0; split. lia. split. lca.
             intros. 
             rewrite H0; try lia.
             lca. }
       rewrite <- big_sum_extend_l in H1.
       replace ((T 0 0) ^* * T 0 0)%C with (T 0 0 * (T 0 0) ^* + C0)%C in H1 by lca.
       apply (@Gplus_cancel_l C _ C_is_group) in H1.
       symmetry in H1. 
       destruct i; try lia.
       eapply big_sum_squeeze in H1. 
       replace (fst (T 0 (S i) * (T 0 (S i)) ^*)%C) with 
                 ((Rsqr (fst (T O (S i))) + Rsqr (snd (T O (S i))))%R) in H1. 
       apply c_proj_eq.
       apply Rplus_sqr_eq_0_l in H1; auto.
       rewrite Rplus_comm in H1.
       apply Rplus_sqr_eq_0_l in H1; auto. 
       unfold Rsqr; simpl. lra.
       intros. 
       rewrite Cmult_comm, <- Cmod_sqr.
       simpl. autorewrite with R_db.  
       replace (Cmod (T 0%nat (S x)) * Cmod (T 0%nat (S x)))%R with (Rsqr (Cmod (T 0%nat (S x)))).
       apply Rle_0_sqr.
       unfold Rsqr; easy. 
       apply Nat.succ_lt_mono in H3.
       easy.
Qed.

(* this is the crucial step of Schur for => spectral theorem *)
Lemma normal_tri_is_diag : forall {n} (T : Square n),
  WF_Matrix T ->
  upper_triangular T -> T† × T = T × T† ->
  WF_Diagonal T.
Proof. induction n; intros. 
       split; auto.
       intros. rewrite H; auto. lia.
       assert (H' : (get_minor T 0 0) † × (get_minor T 0 0) 
                    = (get_minor T 0 0) × (get_minor T 0 0) †).
       { replace ((get_minor T 0 0) †) with (get_minor (T†) 0 0).
         rewrite <- 2 fce_get_minor_reduction.
         rewrite H1; easy.
         apply upper_triangular_reduction_conv; auto.
         apply normal_tri_is_fce in H1; auto.
         unfold first_col_e_i in *; unfold adjoint; unfold transpose in H1; intros.
         rewrite H1; try lca; lia.
         prep_matrix_equality.
         unfold get_minor, adjoint.
         bdestruct_all; easy. }
       apply IHn in H'; auto with wf_db.
       apply normal_tri_is_fce in H1; auto.
       split; auto; intros.
       destruct j.
       apply upper_triangular_reduction_conv in H0; destruct H0.
       rewrite H0; auto; lia.
       destruct i.
       unfold first_col_e_i, transpose in H1.
       apply H1; lia.
       destruct H'.
       rewrite <- (H4 i j); try lia.
       unfold get_minor.
       bdestruct_all.
       easy.
       apply upper_triangular_reduction_conv.
       easy.
Qed.

Corollary Spectral_Theorem : forall {n} (A : Square n),
  WF_Matrix A ->
  A † × A = A × A† -> 
  (exists U, WF_Unitary U /\ WF_Diagonal (U†×A×U)).
Proof. intros.
       destruct (Schur_form A) as [U [H1 H2] ]; auto.
       exists U.
       split; auto. 
       apply normal_tri_is_diag; auto with wf_db.
       destruct H1; auto with wf_db.
       Msimpl.
       repeat rewrite <- Mmult_assoc.
       do 2 (apply f_equal_gen; auto).
       repeat rewrite Mmult_assoc.
       apply f_equal_gen; auto.
       rewrite <- 2 (Mmult_assoc U).
       destruct H1.
       apply Minv_flip in H3; auto with wf_db.
       rewrite H3.
       do 2 (rewrite Mmult_1_l; auto).
       auto with wf_db.
Qed.

Corollary unit_implies_diagble : forall {n} (A : Square n),
  WF_Unitary A -> WF_Diagonalizable A.
Proof. intros.
       split.
       apply H.
       destruct (Spectral_Theorem A).
       apply H.
       destruct H.
       rewrite H0.
       apply Minv_flip in H0.
       rewrite H0; easy.
       all : auto with wf_db.
       destruct H0.
       exists (x†), x, (x† × A × x).
       destruct H0.
       repeat (try split; auto with wf_db).
Qed.

(* TODO: add a def of unitary diagonalizable. add defs of Hermitian and anti Hermitian. Easily,
   we get these matrices are unitary diagonalizable. Perhaps these already exist somewhere *)

Corollary herm_implies_diagble : forall {n} (A : Square n),
  WF_Matrix A -> hermitian A -> WF_Diagonalizable A.
Proof. intros.
       split.
       apply H.
       destruct (Spectral_Theorem A).
       apply H.
       rewrite H0; easy.
       exists (x†), x, (x† × A × x).
       destruct H1.
       destruct H1.
       repeat (try split; auto with wf_db).
Qed.


(***************)
(* Proving SVD *)
(***************)


(* TODO: Reorganize if necessary *)
(* NB: the logic of the first few lemmas here seems a bit random, since I ended up using 
   a different approach, so things are a bit piecemeal *)

Local Open Scope R_scope.

(** facts about Σ *)

Definition WF_Nonnegative {m n} (A : Matrix m n) :=
  WF_Matrix A /\ forall (i j : nat), (Re (A i j) >= 0 /\ Im (A i j) = 0)%R.

Definition ordered_diag {m n} (Σ : Matrix m n) := 
  (forall i j, (i < n)%nat -> (j <= i)%nat -> Cmod (Σ i i) <= Cmod (Σ j j)).

Definition nonzero_cutoff {m n} (Σ : Matrix m n) (r : nat) := 
  (r < n)%nat /\ (forall j, (j < r)%nat -> fst (Σ j j) <> 0) /\ (forall j, (r <= j)%nat -> fst (Σ j j) = 0).

(*
Definition WF_OrderedSigma {m n} (Σ : Matrix m n) := 
  WF_Diagonal Σ /\ WF_Nonnegative Σ /\ 
  (forall i j, (i < j)%nat -> fst (Σ i i) <= fst (Σ j j)).
*)

Corollary perm_mat_preserves_diag : forall {n} (D : Square n) f, 
  WF_Diagonal D -> 
  permutation n f ->
  WF_Diagonal ((perm_mat n f)† × D × ((perm_mat n f))). 
Proof. intros.
       assert (H' : WF_Matrix (adjoint (perm_mat n f) × D × perm_mat n f)).
       destruct H; auto with wf_db.
       split; auto.
       intros. 
       bdestruct (i <? n); bdestruct (j <? n).
       destruct H.
       rewrite perm_mat_conjugate; auto with perm_bounded_db.
       apply H4.
       contradict H1.
       apply (permutation_is_injective n) in H1; auto.
       all : rewrite H'; auto; lia.
Qed.

(* making order_real_function constructive should be doable...  
   It probably even already exists *)
Theorem unitary_orders_diagonal : forall {n} (S : Square n), 
  WF_Diagonal S -> 
  exists U, WF_Unitary U /\ WF_Diagonal (U† × S × U) /\ ordered_diag (U† × S × U).
Proof. intros. 
       destruct (order_real_function n (fun i => Cmod (S i i))) as [l [H0 H1] ].
       exists ((perm_mat n (stack_fswaps Datatypes.id l))).
       split. 
       apply perm_mat_unitary.
       apply stack_fswaps_permutation; auto; apply id_permutation.
       split. 
       apply perm_mat_preserves_diag; auto.
       apply stack_fswaps_permutation; auto; apply id_permutation.
       unfold ordered_diag; intros.
       destruct H.
       rewrite 2 perm_mat_conjugate; auto; try lia.
       apply H1; try lia. 
       all: auto with perm_bounded_db perm_db.
Qed.

Lemma pos_semi_def_diag_implies_nonneg : forall {n} (A : Square n), 
  WF_Diagonal A -> 
  hermitian A ->
  positive_semidefinite A ->
  WF_Nonnegative A.
Proof. intros.
       destruct H. 
       split; auto; intros.
       bdestruct (i =? j)%nat; subst. 
       split.
       bdestruct (j <? n)%nat.
       rewrite get_entry_with_e_i; auto.
       apply H1; auto with wf_db.
       rewrite H. simpl; lra.
       left; easy.
       apply Cconj_eq_implies_real.
       replace ((A j j)^*) with ((A† j j)^* ).
       unfold adjoint.
       lca.
       rewrite H0; easy.
       rewrite H2; auto; split; simpl.
       lra.
       easy.
Qed.

Lemma AAadjoint_zero_implies_A_zero : forall {m n} (A : Matrix m n),
  WF_Matrix A ->
  A† × A = Zero -> A = Zero.
Proof. intros. 
       apply det_by_get_col.
       intros.
       bdestruct (i <? n).
       replace (get_col Zero i) with (@Zero m 1%nat). 
       apply inner_product_zero_iff_zero; auto with wf_db.
       rewrite inner_product_is_mult, H0; easy.
       unfold get_col, Zero. 
       prep_matrix_equality.
       bdestruct_all; easy.       
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv, get_col; intros.
       bdestruct_all. 
       rewrite H; auto.
Qed.

Lemma first_entry_nonzero_if_nonzero_spd : forall {n} (X U : Square n),
  WF_Matrix X -> WF_Unitary U ->
  hermitian X ->  
  positive_semidefinite X -> 
  WF_Diagonal (U† × X × U) -> 
  ordered_diag (U† × X × U) ->
  fst ((U† × X × U) O O) = 0 ->
  X = Zero.
Proof. intros. 
       assert (H' : U†×X×U = Zero).
       { apply mat_equiv_eq; auto with wf_db.
         destruct H0; auto with wf_db.
         unfold mat_equiv; intros. 
         bdestruct (i =? j); subst.
         assert (H'' : (U† × X × U) O O = C0).
         apply c_proj_eq.
         rewrite H5; easy.
         apply pos_semi_def_diag_implies_nonneg in H3.
         destruct H3.
         destruct (H8 O O).
         unfold Im in H10; easy.
         rewrite <- (adjoint_involutive _ _ U).
         replace (U†††) with (U†) by (rewrite adjoint_involutive; easy).
         apply unit_conj_hermitian; auto; auto with unit_db.
         apply positive_semidefinite_unitary_conj; auto.
         unfold Zero; simpl.
         apply Cmod_eq_0.
         unfold ordered_diag in H4.
         apply Rle_antisym.
         replace 0 with (Cmod (((U) † × X × U) O O)).
         apply H4; auto; lia.
         rewrite H'', Cmod_0; easy.
         apply Cmod_ge_0.
         destruct H3.
         rewrite H9; easy. }
       symmetry in H'.
       apply diagble_switch in H'.   
       rewrite H', Mmult_0_r, Mmult_0_l; easy.
       all : destruct H0; auto with wf_db.
Qed.     

Lemma AAadjoint_decomposition : forall {m n} (A : Matrix (S m) (S n)),
  WF_Matrix A -> A <> Zero -> 
  exists (V : Square (S n)), 
    WF_Unitary V /\ WF_Diagonal ((V† × A†) × (A × V)) 
    /\ fst (((V† × A†) × (A × V)) O O) <> 0%R.
Proof. intros. 
       destruct (Spectral_Theorem (A† × A)) as [U [H1 H2] ]; auto with wf_db.
       distribute_adjoint.
       rewrite adjoint_involutive.
       lma.
       destruct (unitary_orders_diagonal (U†×(A†×A)×U)) as [U' [H3 [H4 H5] ] ]; auto.
       exists (U × U'). 
       split; auto with unit_db.
       split.
       rewrite Mmult_adjoint.
       repeat rewrite <- Mmult_assoc in *.
       apply H4.
       rewrite <- (Mmult_assoc _ A).
       contradict H0. 
       apply AAadjoint_zero_implies_A_zero; auto.
       apply (first_entry_nonzero_if_nonzero_spd _ (U × U')); auto with unit_db; auto with wf_db.
       apply AadjointA_hermitian; auto.
       apply positive_semidefinite_AadjointA; auto.
       all : try rewrite Mmult_adjoint in *; repeat rewrite Mmult_assoc in *; try easy. 
Qed.

Lemma SVD_reduction_step : forall {m n} (A : Matrix (S m) (S n)),
  WF_Matrix A ->
  exists U V, WF_Unitary U /\ WF_Unitary V /\ 
           first_col_e_i (U† × A × V) /\ first_row_e_i (U† × A × V).
Proof. intros.
       destruct (mat_equiv_dec Zero A).
       - exists (I (S m)), (I (S n)).
         split; auto with unit_db. 
         split; auto with unit_db.
         replace A with (@Zero (S m) (S n)).
         rewrite Mmult_0_r, Mmult_0_l.
         unfold first_col_e_i, first_row_e_i; split; intros; easy.
         apply mat_equiv_eq; auto with wf_db.
       - destruct (AAadjoint_decomposition A) as [V [H1 [H2 H3] ] ]; auto.
         contradict n0.
         rewrite n0; easy.
         assert (H' : get_col (A × V) O <> Zero).
         { apply fst_inner_product_nonzero_iff_nonzero.
           destruct H1; auto with wf_db.
           rewrite inner_product_is_mult.
           rewrite Mmult_adjoint. 
           easy. }
         destruct (unit_out_of_v (get_col (A × V) O)) as [U [H4 H5] ].
         destruct H1; auto with wf_db.
         easy.
         exists U, V.
         split; auto; split; auto.
         assert (H0' : WF_Matrix ((U) † × A × V)).
         destruct H1; destruct H4; auto with wf_db.
         split.  
         assert (H1' : norm (get_col (A × V) 0) .* get_col U 0 = get_col (A × V) 0).
         { rewrite H5.
           unfold normalize.
           rewrite Mscale_assoc, Cinv_r, Mscale_1_l; auto.
           contradict H'.
           apply RtoC_inj in H'.
           apply norm_zero_iff_zero; auto.
           destruct H1; auto with wf_db. }
         + unfold first_col_e_i; intros. 
           bdestruct (i <? S m).
           2 : rewrite H0'; auto.
           rewrite get_entry_with_e_i; try lia.
           replace (adjoint (e_i i) × ((U) † × A × V) × e_i 0) with 
             (adjoint (U × e_i i) × ((A × V) × e_i 0)).
           apply unit_is_orthonormal in H4.
           destruct H4; destruct H7; unfold orthogonal in H7. 
           rewrite <- 2 matrix_by_basis; auto; try lia.
           rewrite <- H1', Mscale_mult_dist_r.
           unfold scale. 
           unfold inner_product in H7. 
           rewrite (H7 i O); try lia; lca.
           rewrite Mmult_adjoint, <- 4 Mmult_assoc; easy.         
         + unfold first_row_e_i; intros.
           bdestruct (i <? S n).
           2 : rewrite H0'; auto.
           rewrite get_entry_with_e_i; try lia.
           replace (adjoint (e_i 0) × ((U) † × A × V) × e_i i) with 
             (adjoint (U × e_i 0) × ((A × V) × e_i i)).
           rewrite <- 2 matrix_by_basis; auto; try lia.
           rewrite H5.
           unfold normalize.
           rewrite Mscale_adj, Mscale_mult_dist_l.
           unfold scale.
           replace ((adjoint (get_col (A × V) O) × get_col (A × V) i) O O)
             with (⟨ get_col (A × V) O, get_col (A × V) i ⟩) by easy.
           rewrite inner_product_is_mult.
           destruct H2.
           rewrite Mmult_adjoint, H7; try lia; lca.
           rewrite Mmult_adjoint, <- 4 Mmult_assoc; easy.         
Qed.

Lemma SVD_weak : forall {m n} (A : Matrix m n),
  WF_Matrix A ->
  exists (U : Square m) (V : Square n), 
    WF_Unitary U /\ WF_Unitary V /\ WF_Diagonal (U†×A×V).
Proof. induction m; intros.
       - exists (I 0), (I n);
         repeat (split; auto with unit_db). 
         auto with wf_db.
         intros. 
         replace A with (@Zero 0 n).
         rewrite Mmult_0_r, Mmult_0_l; easy.
         prep_matrix_equality.
         rewrite H; auto.
         left; lia.
       - destruct n.
         exists (I (S m)), (I 0);
         repeat (split; auto with unit_db). 
         destruct (SVD_reduction_step A) as [U [V [H0 [H1 H2] ] ] ]; auto.
         destruct (IHm n (get_minor (U†×A×V) 0 0)) as [U' [V' [H3 [H4 H5 ] ] ] ].
         destruct H0; destruct H1; auto with wf_db.
         exists (U × pad1 U' C1).
         exists (V × pad1 V' C1). 
         assert (H' :  WF_Unitary (U × pad1 U' C1)).
         { apply Mmult_unitary; auto.
           apply pad1_unitary; auto.
           lca. }
         assert (H0' :   WF_Unitary (V × pad1 V' C1)). 
         { apply Mmult_unitary; auto.
           apply pad1_unitary; auto.
           lca. }
         split; auto; split; auto.
         destruct H'; destruct H0'.
         apply diagonal_reduction; auto with wf_db.
         rewrite Mmult_adjoint, pad1_adjoint, 2 Mmult_assoc, 
           <- (Mmult_assoc _ A), <- (Mmult_assoc _ V).
         repeat (apply fce_and_fre_mult; try apply frc_and_fre_pad1; try easy). 
         rewrite Mmult_adjoint, pad1_adjoint, 2 Mmult_assoc, fce_get_minor_reduction; auto.
         rewrite <- 2 Mmult_assoc, fre_get_minor_reduction; auto.
         rewrite <- 2 get_minor_pad1. 
         rewrite <- Mmult_assoc; easy.
         apply fre_pad1.
         apply fce_pad1.
Qed.

Definition normalize_diagonal {m n} (A : Matrix m n) : Square n :=
  fun i j => if (i =? j) && (i <? n) then 
            match (Ceq_dec (A i j) C0) with 
            | left _ => C1
            | right _ => ((Cmod (A i j)) / (A i j))%C
            end else C0.

Lemma normalize_diagonal_unit : forall {m n} (A : Matrix m n),
  WF_Unitary (normalize_diagonal A).
Proof. intros. 
       apply unit_is_orthonormal.
       split. 
       unfold WF_Matrix, normalize_diagonal; intros.
       bdestruct_all; simpl; easy.
       split.
       unfold orthogonal, normalize_diagonal; intros. 
       unfold inner_product, Mmult, adjoint, get_col.
       rewrite big_sum_0_bounded; auto.
       intros; simpl.
       bdestruct_all; simpl; lca.
       intros. 
       unfold norm, get_col, inner_product, adjoint, Mmult; simpl.
       rewrite (big_sum_unique C1).
       simpl.
       apply sqrt_1.
       exists i; split; auto.
       split.
       unfold normalize_diagonal.
       bdestruct_all; simpl.
       destruct (Ceq_dec (A i i) 0); try lca.
       unfold Cdiv. 
       rewrite Cconj_mult_distr.
       rewrite <- Cinv_Cconj.
       replace ((Cmod (A i i)) ^*)%C with (RtoC (Cmod (A i i))).
       replace (Cmod (A i i) * / (A i i) ^* * (Cmod (A i i) * / A i i))%C
               with ((Cmod (A i i) * Cmod (A i i)) * ((/ (A i i)^* * / (A i i))))%C by lca.
      rewrite <- Cinv_mult_distr, <- Cmod_sqr; simpl.
      rewrite Cmult_1_r, Cinv_r; auto.
      apply Cmult_neq_0.
      all : try (contradict n0; apply Cmod_eq_0; apply RtoC_inj in n0; auto).
      lca.
      intros. 
      unfold normalize_diagonal.
      bdestruct_all; simpl.
      lca.
Qed.                

Lemma normalize_diagonal_diagonal : forall {m n} (A : Matrix m n),
  WF_Diagonal (normalize_diagonal A).
Proof. intros. 
       split.
       apply normalize_diagonal_unit.
       intros.
       unfold normalize_diagonal.
       bdestruct_all; simpl; easy.
Qed.

Lemma normalize_diagonal_diag_entry : forall {m n} (A : Matrix m n) (i : nat),
  (i < n)%nat ->
  (A × (normalize_diagonal A)) i i = Cmod (A i i).
Proof. intros.   
       unfold Mmult.
       rewrite (big_sum_unique (RtoC (Cmod (A i i)))).
       easy.
       exists i.
       split; auto.
       split.
       unfold normalize_diagonal.
       bdestruct_all; simpl.
       destruct (Ceq_dec (A i i) 0).
       rewrite e, Cmod_0; simpl; lca. 
       replace (A i i * (Cmod (A i i) / A i i))%C with 
         ((A i i) * / (A i i) * (Cmod (A i i)))%C by lca.
       rewrite Cinv_r; try lca; auto.
       intros.
       unfold normalize_diagonal.
       bdestruct_all; simpl.
       lca.
Qed.

Lemma normalize_diagonal_ver : forall {m n} (A : Matrix m n),
  WF_Diagonal A ->
  WF_Nonnegative (A × (normalize_diagonal A)).
Proof. intros.   
       assert (H' : WF_Diagonal (A × (normalize_diagonal A))).
       { apply diag_mult; auto.
         apply normalize_diagonal_diagonal. }
       split. 
       destruct H; destruct H'; auto with wf_db.
       intros.
       bdestruct (i =? j); subst. 
       bdestruct (j <? n); subst. 
       rewrite normalize_diagonal_diag_entry; auto.
       split.
       apply Rle_ge.
       simpl; apply Cmod_ge_0.
       simpl; auto.
       destruct H'.
       rewrite H1; simpl; try easy; try lra.
       right. easy.
       destruct H'.
       rewrite H2.
       split.
       all : simpl; try lra; try easy.
Qed.


(* NB: could easily add that the entries of L are ordered by norm with the above machinery *)
Theorem SVD : forall {m n} (A : Matrix m n),
  WF_Matrix A ->
  exists (U : Square m) (L : Matrix m n) (V : Square n), 
    WF_Unitary U /\ WF_Unitary V /\ 
      WF_Diagonal L /\ WF_Nonnegative L /\ 
      A = U × L × V†. 
Proof. intros. 
       destruct (SVD_weak A) as [U [V [H0 [H1 H2] ] ] ]; auto.
       destruct (normalize_diagonal_ver ((U) † × A × V)); auto. 
       exists U, ((U) † × A × V × normalize_diagonal ((U) † × A × V)), 
         (V × (normalize_diagonal (U† × A × V)) ). 
       split; auto; split.
       apply Mmult_unitary; try apply adjoint_unitary; auto.
       apply normalize_diagonal_unit.
       split. 
       apply diag_mult; auto.
       apply normalize_diagonal_diagonal.
       split. 
       apply normalize_diagonal_ver; auto.
       distribute_adjoint.
       rewrite <- 4 Mmult_assoc.
       destruct H0.
       apply Minv_flip in H5; auto with wf_db.       
       rewrite H5, Mmult_1_l; auto with wf_db.
       rewrite (Mmult_assoc (A × V)).
       destruct (normalize_diagonal_unit (U† × A × V)).
       apply Minv_flip in H7; auto with wf_db.
       rewrite H7, Mmult_1_r; auto with wf_db.
       destruct H1.
       apply Minv_flip in H8; auto with wf_db.
       rewrite Mmult_assoc, H8, Mmult_1_r; auto.
       destruct H1.
       auto with wf_db.
Qed.       


Local Open Scope C_scope.


(***************************)
(* Facts about eigenvalues *)
(***************************)

Local Close Scope nat_scope.

(* these two are a bit redundant with inner_product_scale_x *)
Lemma eigenvalue_inner_product_distr_r : forall {n} (A : Square n) (v : Vector n) (λ : C),
  A × v = λ .* v ->
  ⟨ v, A × v ⟩ = λ * ⟨ v, v ⟩.
Proof. intros. 
       rewrite H.
       unfold inner_product.
       rewrite Mscale_mult_dist_r.
       easy.
Qed.

Lemma eigenvalue_inner_product_distr_l : forall {n} (A : Square n) (v : Vector n) (λ : C),
  A × v = λ .* v ->
  ⟨ A × v, v ⟩ = λ^* * ⟨ v, v ⟩.
Proof. intros. 
       rewrite H, inner_product_scale_l.
       easy.
Qed.

Lemma inner_product_adjoint_switch : forall {n} (A : Square n) (u v : Vector n),
  ⟨ u, A × v ⟩ = ⟨ A† × u, v ⟩.
Proof. intros. 
       unfold inner_product.
       rewrite Mmult_adjoint, Mmult_assoc, adjoint_involutive.
       easy.
Qed.

Lemma hermitian_real_eigenvalues : forall {n} (A : Square n) (v : Vector n) (λ : C),
  WF_Matrix A -> 
  hermitian A -> WF_Matrix v -> 
  v <> Zero ->
  A × v = λ .* v ->
  snd λ = 0%R.
Proof. intros.
       apply Cconj_eq_implies_real.
       apply (Cmult_cancel_r (inner_product v v)).
       contradict H2.
       apply inner_product_zero_iff_zero; auto.
       rewrite <- inner_product_scale_l, <- inner_product_scale_r, <- H3, 
         inner_product_adjoint_switch.
       rewrite H0; easy.
Qed.

#[deprecated(note="Use hermitian_real_eigenvalues instead")]
Notation hermitiam_real_eigenvalues := hermitian_real_eigenvalues.

Lemma unitary_eigenvalues_norm_1 : forall {n} (U : Square n) (v : Vector n) (λ : C),
  WF_Unitary U -> WF_Matrix v -> 
  v <> Zero ->
  U × v = λ .* v ->
  λ * λ^* = C1.
Proof. intros. 
       apply (Cmult_cancel_r (inner_product v v));
         try (contradict H1; apply inner_product_zero_iff_zero; easy).
       rewrite <- Cmult_assoc.
       rewrite <- inner_product_scale_l, <- (inner_product_scale_r _ _ λ), <- H2.
       rewrite inner_product_adjoint_r, <- Mmult_assoc.
       destruct H.
       rewrite H3.
       rewrite Mmult_1_l; auto.
       lca.
Qed.       


           
 (**************************************************)
(** * Defining eignestates to be used in type system *)
(**************************************************)

Local Open Scope nat_scope.

Definition Eigenpair {n : nat} (U : Square n) (p : Vector n * C) : Prop :=
  U × (fst p) = (snd p) .* (fst p).

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
   WF_Matrix v -> Eigenpair (I n) (v, C1).
Proof. intros n v H. unfold Eigenpair. 
       simpl. rewrite Mmult_1_l. lma. 
       easy.
Qed.

Lemma diags_have_basis_eigens : forall (n : nat) (U : Square n) (i : nat),
  (i < n) -> WF_Diagonal U -> Eigenpair U (e_i i, U i i).
Proof. unfold WF_Diagonal, Eigenpair, e_i. intros.
       unfold Mmult, scale.
       prep_matrix_equality.
       eapply big_sum_unique. exists i. 
       destruct H0 as [H0 H1].
       split. apply H.
       split.
       - simpl. bdestruct (x =? i).
         * rewrite H2. bdestruct (i =? i); easy.
         * rewrite H1. lca. lia.  
       - intros. simpl. bdestruct (x' =? i); try lia; lca.
Qed.

Local Close Scope nat_scope.

Lemma eigen_scale : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  Eigenpair A (v, c1) -> Eigenpair (c2 .* A) (v, c1 * c2).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite Mscale_mult_dist_l.
       rewrite H.
       rewrite Mscale_assoc.
       rewrite Cmult_comm.
       reflexivity.
Qed.

Lemma eigen_scale_div : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  c2 <> C0 -> Eigenpair (c2 .* A) (v, Cmult c2 c1) -> Eigenpair A (v, c1).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite <- Mscale_assoc in H0.
       rewrite Mscale_mult_dist_l in H0.
       apply Mscale_div in H0;
       assumption.
Qed.

Lemma eig_unit_invertible : forall {n} (v : Vector n) (c : C) (X X' B : Square n),
  WF_Matrix v -> WF_Matrix X -> WF_Matrix X' -> X' × X = I n ->  
  Eigenpair B (X × v, c) -> Eigenpair (X' × B × X) (v, c).  
Proof. intros. 
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H3.
       distribute_scale. 
       rewrite <- Mmult_assoc.     
       rewrite H2.
       rewrite Mmult_1_l; easy.
Qed.

Lemma eig_unit_conv : forall {n} (v : Vector n) (c : C) (U B : Square n),
  WF_Matrix v -> WF_Unitary U -> 
  Eigenpair B (U × v, c) -> Eigenpair (U† × B × U) (v, c).  
Proof. intros. 
       destruct H0 as [H0 H2].
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H1.
       rewrite Mscale_mult_dist_r.
       rewrite <- Mmult_assoc.     
       rewrite H2.
       rewrite Mmult_1_l; easy.
Qed.

(* potentially redundant with the above *)
Lemma eig_unit_norm1 : forall {n} (U : Square n) (c : C),
  WF_Unitary U -> (exists v, WF_Matrix v /\ v <> Zero /\ Eigenpair U (v, c)) -> (c * c^* = C1)%C.
Proof. intros. destruct H0 as [v [H0 [H1 H2] ] ].
       eapply unitary_eigenvalues_norm_1.
       apply H.
       apply H0.
       easy.
       easy. 
Qed.


Local Open Scope nat_scope.


(************************************************************************************)
(** * Showing that certain types of matrices are equal when their eigenpairs are equal *)
(************************************************************************************)


Definition eq_eigs {n : nat} (U1 U2 : Square n) : Prop := 
  forall p, WF_Matrix (fst p) -> (Eigenpair U1 p -> Eigenpair U2 p). 


Lemma eq_eigs_implies_eq_diag : forall {n} (D1 D2 : Square n),
  WF_Diagonal D1 -> WF_Diagonal D2 -> eq_eigs D1 D2 -> D1 = D2.
Proof. intros n D1 D2 [H1wf H1d] [H2wf H2d] H. 
       assert (H2 : forall x, (x < n)%nat -> D1 x x = D2 x x).
       { intros.
         assert (H1 := H0).
         apply (diags_have_basis_eigens n D1 x) in H1.
         apply H in H1.
         unfold Eigenpair in H1; simpl in H1.
         assert (H' : (D1 x x .* @e_i n x) x O = D1 x x).
         { unfold scale, e_i.
           bdestruct_all; lca. }
         rewrite <- H', <- H1. 
         unfold Mmult. 
         apply (big_sum_unique (D2 x x)). 
         exists x. split; try easy.
         split. unfold e_i. 
         bdestruct_all; lca.
         intros. 
         unfold e_i; bdestruct_all; lca.
         simpl. auto with wf_db.
         split; auto. }
       apply mat_equiv_eq; auto.
       unfold mat_equiv; intros. 
       bdestruct (i =? j).
       - rewrite H3, H2; try lia; easy. 
       - rewrite H1d, H2d; try lia; easy.
Qed.
         

Lemma diagble_eigenpairs_transfer : forall {n} (A B X X' : Square n),
  WF_Matrix A -> WF_Diagonal B -> WF_Matrix X -> WF_Matrix X' ->
  A = X' × B × X -> X × X' = I n ->
  (forall x, x < n -> Eigenpair A (X' × (e_i x), B x x)).
Proof. intros. 
       destruct H0 as [Hwf Hu].
       unfold Eigenpair; simpl.
       rewrite <- Mmult_assoc. 
       rewrite H3.
       do 2 rewrite Mmult_assoc. 
       rewrite <- (Mmult_assoc X), H4, Mmult_1_l; auto with wf_db.
       assert (H' := (diags_have_basis_eigens n B)).
       apply H' in H5. 
       unfold Eigenpair in H5; simpl in H5. 
       rewrite Mmult_assoc, H5. 
       distribute_scale; easy.
       split; auto.
Qed.   

Lemma eq_eigs_implies_eq_diagble : forall {n} (D1 D2 : Square n),
  WF_Diagonalizable D1 -> WF_Diagonalizable D2 -> eq_eigs D1 D2 -> D1 = D2.
Proof. intros n D1 D2 [H1wf H1d] [H2wf H2d] H. 
       destruct H1d as [X1 [X1' [B1 [ [Hb1wf Hb1u] [H12 [H13 [H14 H15] ] ] ] ] ] ].
       destruct H2d as [X2 [X2' [B2 [ [Hb2wf Hb2u] [H22 [H23 [H24 H25] ] ] ] ] ] ].
       apply diagble_switch in H15; apply diagble_switch in H25; auto.
       assert (H0 : D1 × X1' = X1' × B1).
       { rewrite H15.
         repeat rewrite Mmult_assoc.
         rewrite H14, Mmult_1_r; auto. }
       assert (H1 : D2 × X2' = X2' × B2).
       { rewrite H25.
         repeat rewrite Mmult_assoc.
         rewrite H24, Mmult_1_r; auto. }
       assert (H2 : forall i, i < n -> Eigenpair D1 (X1' × (e_i i), B1 i i)).
       { apply (diagble_eigenpairs_transfer D1 B1 X1 X1'); auto. 
         split; auto. }
       assert (H3 : forall i, i < n -> Eigenpair D2 (X1' × (e_i i), B1 i i)).
       { intros. apply H. simpl. 
         auto with wf_db. apply H2; easy. }
       assert (H4 : forall i, i < n -> Eigenpair (X1 × D1 × X1') (e_i i, B1 i i)).
       { intros. apply eig_unit_invertible; auto with wf_db. }
       assert (H5 : forall i, i < n -> Eigenpair (X1 × D2 × X1') (e_i i, B1 i i)).
       { intros. apply eig_unit_invertible; auto with wf_db. }
       assert (H6 : forall i, i < n -> (X1 × D1 × X1' × e_i i = X1 × D2 × X1' × e_i i)).
       { intros. 
         unfold Eigenpair in *; simpl in *.
         rewrite H4, H5; easy. }
       assert (H7 : X1 × D1 × X1' = X1 × D2 × X1').
       { apply det_by_get_col.
         intros. 
         bdestruct (i <? n).
         - rewrite matrix_by_basis.
           rewrite matrix_by_basis. 
           apply H6. 
           all : easy. 
         - assert (H' : forall (A : Square n) (i : nat), i >= n -> WF_Matrix A -> 
                                                  get_col A i = @Zero n 1).  
           { intros. 
             unfold get_col. 
             prep_matrix_equality. 
             bdestruct_all; try easy.
             rewrite H9; try lia; easy. }
           rewrite H'; auto with wf_db.
           rewrite H'; auto with wf_db. }
       assert (H8 : X1' × (X1 × D1 × X1') × X1= X1' × (X1 × D2 × X1') × X1).
       { rewrite H7; easy. }
       repeat rewrite Mmult_assoc in H8.
       apply Minv_flip in H14; auto. 
       rewrite H14 in H8.
       do 2 rewrite Mmult_1_r in H8; auto. 
       do 2 rewrite <- Mmult_assoc in H8.
       rewrite H14 in H8.
       do 2 rewrite Mmult_1_l in H8; auto. 
Qed.

Lemma eq_eigs_implies_eq_unit : forall {n} (U1 U2 : Square n),
  WF_Unitary U1 -> WF_Unitary U2 -> eq_eigs U1 U2 -> U1 = U2.
Proof. intros. 
       apply unit_implies_diagble in H.
       apply unit_implies_diagble in H0.
       apply eq_eigs_implies_eq_diagble; auto. 
Qed.

Theorem eigs_eq_gate : forall {n} (U1 U2 : Square n),
  WF_Unitary U1 -> WF_Unitary U2 -> (U1 = U2 <-> eq_eigs U1 U2).
Proof. intros. split.
       - intros H'; rewrite H'; easy.
       - apply eq_eigs_implies_eq_unit.
         apply H. apply H0.
Qed.

Local Close Scope nat_scope.

(*******************************)
(** * Some actual examples/lemmas *)
(*******************************)


Lemma EigenXp : Eigenpair σx (∣+⟩, C1).
Proof. unfold Eigenpair. simpl. lma'. Qed.

Lemma EigenXm : Eigenpair σx (∣-⟩, -C1).
Proof. unfold Eigenpair. simpl. lma'. Qed.

Lemma EigenYp : Eigenpair σy (∣R⟩, C1).
Proof. unfold Eigenpair. simpl. lma'. Qed.

Lemma EigenYm : Eigenpair σy (∣L⟩, -C1).
Proof. unfold Eigenpair. simpl. lma'. Qed.

Lemma EigenZp : Eigenpair σz (∣0⟩, C1).
Proof. unfold Eigenpair. simpl. lma'. Qed.

Lemma EigenZm : Eigenpair σz (∣1⟩, -C1).
Proof. unfold Eigenpair. simpl. lma'. Qed.

Lemma EigenXXB : Eigenpair (σx ⊗ σx) (∣Φ+⟩, C1).
Proof. unfold Eigenpair. lma'. Qed.

#[export] Hint Resolve EigenXp EigenXm EigenYp EigenYm EigenZp EigenZm EigenXXB all_v_eigen_I : eig_db.
