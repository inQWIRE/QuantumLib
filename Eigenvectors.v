Require Import List.
Require Export Complex.
Require Export Matrix.
Require Export Quantum.



(* Some preliminary lemmas/additions to tactics that could be moved to other files *)



Definition Phase : Matrix 2 2 := phase_shift (PI / 2).

Definition Phase' : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Ci
          | _, _ => C0
          end.

Definition Tgate :=  phase_shift (PI / 4).


Lemma WF_Phase : WF_Matrix Phase. Proof. show_wf. Qed.
Lemma WF_Phase' : WF_Matrix Phase'. Proof. show_wf. Qed.
Lemma WF_Tgate: WF_Matrix Tgate. Proof. show_wf. Qed.
Lemma WF_notc : WF_Matrix notc. Proof. show_wf. Qed.

Lemma WF_ket : forall (x : nat), WF_Matrix ∣x⟩.
Proof. intros x. unfold ket. destruct (x =? 0). show_wf. show_wf. 
Qed. 

Lemma WF_bra : forall (x : nat), WF_Matrix (bra x).
Proof. intros x. unfold bra. destruct (x =? 0). show_wf. show_wf. 
Qed. 


Hint Resolve WF_Phase WF_Phase' WF_Tgate WF_notc WF_ket WF_bra : wf_db.

(* ran into problems with hadamard. Can probably make this more general. *)
Ltac Hhelper :=
   unfold Mmult;
   unfold Csum;
   unfold I;
   simpl;
   C_field_simplify;
   try lca;
   C_field.


Lemma PEqP' : Phase = Phase'.
Proof. lma'. autorewrite with Cexp_db. reflexivity.
Qed.


(* these allow us to bypass WF requirements in every definition, which get annoying *)
(* we could also just make an axiom saying that all Squares are WF... *)
Axiom Mmult_1_r': forall {n m} (A : Matrix n m),
  A × I n = A.

Axiom Mmult_1_l': forall {n m} (A : Matrix n m),
  I n × A = A.

(************************************************************************)
(* Defining a set of vectors, linear independence, other prelims etc... *)
(************************************************************************)

(* a set of m vectors of dimension n *)
Notation VecSet n m := (Matrix n m).

Definition zero_vec (n : nat) : Vector n := @Zero n 1.

Definition vecs_to_vecSet {n} (vs : list (Vector n)) : VecSet n (length vs) := 
  fun x y => (nth y vs (zero_vec n)) x 0%nat.

Definition get_vec {n m} (i : nat) (vs : VecSet n m) : Vector n :=
  fun x y => (if (y =? 0) then vs x i else 0).   


Definition linearly_independent {n m} (S : VecSet n m) :=
  forall (a : Vector n), @Mmult _ _ 1 S a = Zero -> a = Zero.


Definition e_i {n : nat} (i : nat) : Vector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then 1 else 0). 

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

Lemma invertible_implies_linind : forall {n} (X : Square n),
  (exists X', X × X' = I n) -> linearly_independent X.
Proof. intros. destruct H.
       unfold linearly_independent. intros.
       apply Minv_flip in H. 
       rewrite <- (Mmult_1_l' a); 
       rewrite <- H.
       rewrite Mmult_assoc, H0.
       rewrite Mmult_0_r.
       reflexivity.
Qed.

(********************************************************************)
(* Defining unitary matrices and proving some basic lemmas/examples *)
(********************************************************************)

Local Open Scope nat_scope.


Definition unitary {n : nat} (A : Square n) : Prop :=
  A × (A†) = I n. 



Lemma X_unitary : unitary σx. Proof. lma'. Qed.
Lemma Y_unitary : unitary σy. Proof. lma'. Qed.
Lemma Z_unitary : unitary σz. Proof. lma'. Qed.
Lemma P_unitary : unitary Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma cnot_unitary : unitary cnot. Proof. lma'. Qed.
Lemma notc_unitary : unitary notc. Proof. lma'. Qed.

Lemma H_unitary : unitary hadamard.
Proof. assert (H : hadamard † = hadamard). { lma'. }
       unfold unitary; rewrite H.
       lma'; Hhelper.
Qed.

Lemma unit_I : forall (n : nat), unitary (I n).
Proof. intros. unfold unitary. rewrite Mmult_1_l'.
       apply id_adjoint_eq. 
Qed.

Lemma unit_mult : forall {n} (A B : Square n),
  unitary A -> unitary B -> unitary (A × B).
Proof. intros. unfold unitary in *.
       rewrite Mmult_adjoint.
       rewrite Mmult_assoc.
       rewrite <- (Mmult_assoc B _ _).
       rewrite H0. rewrite Mmult_1_l'.
       rewrite H. reflexivity.
Qed.

(***********************************************************************************)
(* We now define diagonal matrices and diagonizable matrices, proving basic lemmas *)
(***********************************************************************************)

Definition diagonal {n : nat} (A : Square n) : Prop := 
  forall i j, i <> j -> A i j = C0.




Lemma diag_Zero : forall n : nat, diagonal (@Zero n n).
Proof. intros n. unfold diagonal. reflexivity. Qed.

Lemma diag_I : forall n : nat, diagonal (I n). 
Proof. 
  unfold diagonal, I; intros.
  bdestruct (i =? j). 
  - easy. 
  - easy.
Qed.

Lemma diag_I1 : diagonal (I 1). Proof. apply diag_I. Qed.

Lemma diag_scale : forall {n : nat} (r : C) (A : Square n), 
  diagonal A -> diagonal (r .* A).
Proof.
  unfold diagonal, scale.
  intros n r A H i j H0. 
  apply H in H0. 
  rewrite H0.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma diag_plus : forall {n} (A B : Square n), 
  diagonal A -> diagonal B -> diagonal (A .+ B).
Proof.
  unfold diagonal, Mplus.
  intros n A B H H0 i j H1. 
  rewrite H, H0. 
  rewrite Cplus_0_l.
  reflexivity.
  apply H1. apply H1. 
Qed.

Lemma diag_mult : forall {n : nat} (A B : Square n), 
  diagonal A -> diagonal B -> diagonal (A × B).
Proof.
  unfold diagonal, Mmult.
  intros n A B H H0 i j D.
  apply Csum_0.
  intros x.
  bdestruct (x =? i).
  + rewrite <- H1 in D. 
    rewrite H0, Cmult_0_r.
    reflexivity.
    apply D.
  + rewrite H, Cmult_0_l.    
    reflexivity. auto.
Qed.

(* short lemma to prove diag_kron *)
Lemma div_mod_eq : forall (a b m : nat),
  m <> 0 -> (a / m = b / m) -> (a mod m = b mod m) -> a = b.
Proof. intros a b m H0 Hdiv Hmod.
       rewrite (Nat.mod_eq a m), (Nat.mod_eq b m) in Hmod.
       rewrite Hdiv in Hmod.
       assert (H : m * (b / m) + (a - m * (b / m)) = m * (b / m) + (b - m * (b / m))).
       { rewrite Hmod. reflexivity. }
       rewrite <- (le_plus_minus  (m * (b / m)) a) in H.
       rewrite <- (le_plus_minus  (m * (b / m)) b) in H.
       apply H.
       apply Nat.mul_div_le; apply H0.
       rewrite <- Hdiv; apply Nat.mul_div_le; apply H0.
       apply H0. apply H0.
Qed.


Lemma diag_kron : forall {m n : nat} (A : Square n) (B : Square m), 
                  m <> 0 -> 
                  diagonal A -> diagonal B -> @diagonal (m * n) (A ⊗ B).
Proof.
  unfold diagonal, kron.
  intros m n A B No H H0 i j H1.
  bdestruct (i / m =? j / m).
  - bdestruct (i mod m =? j mod m).
    + apply (div_mod_eq i j m) in No.
      rewrite No in H1. easy.
      apply H2. apply H3.
    + rewrite H0. rewrite Cmult_0_r. reflexivity.
      apply H3.
  - rewrite H. rewrite Cmult_0_l. reflexivity.
    apply H2.
Qed.


Lemma diag_transpose : forall {n : nat} (A : Square n), 
                     diagonal A -> diagonal A⊤. 
Proof. unfold diagonal, transpose. intros n A H i j H0. 
       apply H. auto. 
Qed.

Lemma diag_adjoint : forall {n : nat} (A : Square n), 
      diagonal A -> diagonal A†. 
Proof. unfold diagonal, adjoint, Cconj. intros n A H i j H0.
       rewrite H. lca. auto.
Qed.


Lemma diag_kron_n : forall (n : nat) {m : nat} (A : Square m),
   m <> 0 -> diagonal A ->  diagonal (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply (@diag_kron m (m^n) _ A). 
    apply H. apply IHn. apply H0.
Qed.

Lemma diag_big_kron : forall n (l : list (Square n)), 
                        n <> 0 -> (forall A, In A l -> diagonal A) ->
                         diagonal (⨂ l). 
Proof.                         
  intros n l nNeq0 H.
  induction l.
  - simpl. apply diag_I.
  - simpl. apply (@diag_kron _ (n^(length l)) a (⨂ l)). 
    apply Nat.pow_nonzero; apply nNeq0.
    apply H. simpl. auto. 
    apply IHl. 
    intros A H'. apply H.
    simpl. auto.
Qed. 


Lemma diag_Mmult_n : forall n {m} (A : Square m),
   diagonal A -> diagonal (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply diag_mult; assumption. 
Qed.

(* defining what it means to be diagonalizable *)
Definition diagonalizable {n : nat} (A : Square n) : Prop :=
  exists (X X' B: Square n), 
    diagonal B /\ X × X' = I n /\ B = X × A × X'.

Lemma diag_imps_diagble : forall {n} (A : Square n),
  diagonal A -> diagonalizable A.
Proof. intros. unfold diagonalizable.
       exists (I n), (I n), A. 
       split.
       apply H.  
       do 2 (rewrite Mmult_1_l'). 
       rewrite Mmult_1_r'.
       auto.
Qed.


Lemma diagble_Zero : forall n : nat, diagonalizable (@Zero n n).
Proof. intros. apply diag_imps_diagble. 
       apply diag_Zero.
Qed.


Lemma diagble_I : forall n : nat, diagonalizable (I n). 
Proof. intros. apply diag_imps_diagble.
       apply diag_I.
Qed.

Lemma diagble_I1 : diagonal (I 1). Proof. apply diag_I. Qed.
  


Lemma diagble_scale : forall {n : nat} (r : C) (A : Square n), 
  diagonalizable A -> diagonalizable (r .* A).
Proof.
  unfold diagonalizable.
  intros. do 3 (destruct H).
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  exists x, x0, (r .* x1); split. 
  apply diag_scale; apply H1. split.
  apply H2.
  rewrite Mscale_mult_dist_r;
  rewrite Mscale_mult_dist_l.
  rewrite H3.
  reflexivity. 
Qed.


(* Now, we build up the main important theorem *)
Theorem unit_implies_diagble : forall {n} (A : Square n),
  unitary A -> diagonalizable A.
Proof. Admitted. 



(**************************************************)
(* Defining eignestates to be used in type system *)
(**************************************************)


Definition Eigenstate {n : nat} (U : Square n) (v : Vector n) : Prop :=
  exists (λ : C), U × v = λ .* v.

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
   Eigenstate (I n) v.
Proof. intros n v. exists C1. rewrite Mmult_1_l'. lma. 
Qed.


Lemma diags_have_basis_eigens : forall (n : nat) (U : Square n) (i : nat),
  (i < n) -> diagonal U -> Eigenstate U (e_i i).
Proof. unfold diagonal, Eigenstate, e_i. intros.
       exists (U i i). unfold Mmult, scale.
       prep_matrix_equality.
       eapply Csum_unique. exists i. 
       split. apply H.
       split.
       - bdestruct (x =? i).
         * rewrite H1. bdestruct (i =? i). 
           reflexivity. easy. 
         * simpl. rewrite H0.
           rewrite Cmult_0_l, Cmult_0_r. 
           reflexivity. apply H1.
       - intros. bdestruct (x' =? i).
         * rewrite H2 in H1. easy.
         * simpl. rewrite Cmult_0_r.
           reflexivity.
Qed.


(* we want to prove *)

Theorem eigs_def_unit : forall (n : nat) (U1 U2 : Square n),
  unitary U1 -> unitary U2 -> 
  (forall v, Eigenstate U1 v <-> Eigenstate U2 v) ->
  exists c, c .* U1 = U2.
Proof. intros. Admitted.


Local Close Scope nat_scope.

(*******************************)
(* Some actual examples/lemmas *)
(*******************************)



Definition qubitP : Vector 2 := / (√ 2) .* (∣0⟩ .+ ∣1⟩).
Definition qubitM : Vector 2 := / (√ 2) .* (∣0⟩ .+ ((-1) .* ∣1⟩)).
Definition EPRpair : Vector 4 := / (√ 2) .* (∣0,0⟩ .+ ∣1,1⟩).

Lemma EPRpair_creation : cnot × (hadamard ⊗ I 2) × ∣0,0⟩ = EPRpair.
Proof. unfold EPRpair. lma'.
Qed.

                                                                 
Notation "∣+⟩" := qubitP.
Notation "∣-⟩" := qubitM.
Notation "∣Φ+⟩" := EPRpair.

Lemma WF_qubitP : WF_Matrix ∣+⟩. Proof. show_wf. Qed.
Lemma WF_qubitM : WF_Matrix ∣-⟩. Proof. show_wf. Qed.
Lemma WF_EPRpair : WF_Matrix ∣Φ+⟩. Proof. unfold EPRpair. auto with wf_db.  Qed.

Hint Resolve WF_qubitP WF_qubitM WF_EPRpair : wf_db. 

Lemma EigenXp : Eigenstate σx ∣+⟩.
Proof. unfold Eigenstate. exists (C1). lma'.
Qed.

Lemma EigenXm : Eigenstate σx ∣-⟩.
Proof. unfold Eigenstate. exists (-C1). lma'.
Qed.

Lemma EigenZ0 : Eigenstate σz ∣0⟩.
Proof. unfold Eigenstate. exists (C1). lma'.
Qed.

Lemma EigenZ1 : Eigenstate σz ∣1⟩.
Proof. unfold Eigenstate. exists (-C1). lma'.
Qed.

Lemma EigenXXB : Eigenstate (σx ⊗ σx) ∣Φ+⟩.
Proof. unfold Eigenstate. exists C1. lma'.
Qed.


Hint Resolve EigenXp EigenXm EigenZ0 EigenZ1 EigenXXB all_v_eigen_I : eig_db.


(***********************************************************)
(* Important lemmas about eigenvectors of unitary matrices *)
(***********************************************************)

Fixpoint list_eq {X : Type} (l1 l2 : list X) : Prop :=
  match l1 with
  | [] => l2 = []
  | h1 :: l1' => 
      match l2 with
      | [] => False
      | h2 :: l2' => h1 = h2 /\ list_eq l1' l2'
      end
  end.

Lemma list_eq_same : forall {X} (ls : list X),
  list_eq ls ls. 
Proof. induction ls as [| h].
       * easy.
       * easy.
Qed.

Lemma list_eq_implies_eq : forall {X} (l1 l2 : list X),
  list_eq l1 l2 -> l1 = l2.
Proof. induction l1 as [| h1].
       - easy.
       - intros. destruct l2 as [| h2].
         * easy.
         * simpl in H; destruct H as [H1 H2].
           apply IHl1 in H2. 
           rewrite H1, H2; reflexivity.
Qed.

Lemma list_eq_is_eq : forall {X} (l1 l2 : list X),
  l1 = l2 <-> list_eq l1 l2.  
Proof. intros. split. 
       - intros H; rewrite H; apply list_eq_same.
       - apply list_eq_implies_eq.
Qed.


Definition det2 (U : Square 2) : C := 
  ((U 0%nat 0%nat) * (U 1%nat 1%nat)) - 
  ((U 0%nat 1%nat) * (U 1%nat 0%nat)).

(* must figure out a good way to do this... *) 
Definition sqrtC (c : C) : C :=
  sqrt (fst c).


Definition quad_solver (a b c : C) : list C :=
  [(-b + sqrtC (b^2 - 4%C * a * c)) / (2*a) ; 
   (-b - sqrtC (b^2 - 4%C * a * c)) / (2*a)].


Definition get_eig_vals (U : Square 2) : list C :=
  quad_solver 1 (- (U 0%nat 0%nat + U 1%nat 1%nat)) (det2 U).

Lemma helper : sqrtC 4 = 2.
Proof. unfold sqrtC. simpl. apply c_proj_eq. simpl. 
       assert (H : 2%R ^2 = 4%R). { simpl. lca. } 
       unfold RtoC in H. apply sqrt_lem_1. lra. lra. lra. easy. 
Qed.

Lemma evs_σx : get_eig_vals σx = [C1 ; - C1].
Proof. unfold get_eig_vals. 
       unfold det2. 
       unfold quad_solver.
       apply list_eq_is_eq.
       simpl. Csimpl. 
       assert (H: (- 0 * - 0 - 4 * (0 - 1)) = 4).
       { lca. }
       rewrite H; rewrite helper. 
       split.
       - lca. 
       - split. lca. easy. 
Qed.


Definition eq_eigs {n : nat} (U1 U2 : Square n) : Prop := 
  forall (v : Vector n), Eigenstate U1 v <-> Eigenstate U2 v. 


(* this is the main lemma we will need to assume *)
Lemma eq_eigs_implies_eq : forall {n} (U1 U2 : Square n),
  eq_eigs U1 U2 -> U1 = U2.
Proof. Admitted.


Theorem eigs_eq_gate : forall {n} (U1 U2 : Square n),
  U1 = U2 <-> eq_eigs U1 U2.
Proof. intros. split.
       - intros H; rewrite H; easy.
       - apply eq_eigs_implies_eq.
Qed.

