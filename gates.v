Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.
Require Import Matrix.



Notation "√ n" := (sqrt n) (at level 20) : R_scope.

Infix "∘" := dot (at level 40, left associativity) : matrix_scope.
Infix ".+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix ".*" := scale (at level 40, left associativity) : matrix_scope.
Infix "×" := Mmult (at level 40, left associativity) : matrix_scope.
Infix "⊗" := kron (at level 40, left associativity) : matrix_scope.
Infix "≡" := mat_equiv (at level 70) : matrix_scope.
Notation "A ⊤" := (transpose A) (at level 0) : matrix_scope. 
Notation "A †" := (adjoint A) (at level 0) : matrix_scope. 
Notation "Σ^ n f" := (Csum f n) (at level 60) : matrix_scope.
Notation "n ⨂ A" := (kron_n n A) (at level 30, no associativity) : matrix_scope.
Notation "⨂ A" := (big_kron A) (at level 60): matrix_scope.
Notation "n ⨉ A" := (Mmult_n n A) (at level 30, no associativity) : matrix_scope.

Definition Xgate : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 0; RtoC 1];
    [RtoC 1; RtoC 0]]).


Definition Ygate : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 0; - Ci];
    [Ci; RtoC 0]]).


Definition Zgate : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 0];
    [RtoC 0; - RtoC 1]]).


Definition Hraw : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 1];
    [RtoC 1; - RtoC 1]]).

Definition Hgate : Matrix 2 2 :=
  / (√ 2) .* Hraw. 


Definition Pgate : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 0];
    [RtoC 0; Ci]]).


Definition CNOT1 : Matrix 4 4 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 0; RtoC 0; RtoC 0];
    [RtoC 0; RtoC 1; RtoC 0; RtoC 0];
    [RtoC 0; RtoC 0; RtoC 0; RtoC 1];
    [RtoC 0; RtoC 0; RtoC 1; RtoC 0]]).

Definition CNOT2 : Matrix 4 4 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 0; RtoC 0; RtoC 0];
    [RtoC 0; RtoC 0; RtoC 0; RtoC 1];
    [RtoC 0; RtoC 0; RtoC 1; RtoC 0];
    [RtoC 0; RtoC 1; RtoC 0; RtoC 0]]).

Definition X (n : nat) : Matrix 4 4 :=
  match n with 
  | 2 => I 2 ⊗ Xgate
  | 1 => Xgate ⊗ I 2
  | _ => I 4
  end. 

Definition Z (n : nat) : Matrix 4 4 :=
  match n with 
  | 2 => I 2 ⊗ Zgate
  | 1 => Zgate ⊗ I 2
  | _ => I 4
  end.

(* Lemmas about Pauli and other common matrices *) 

Lemma Propff : forall (b : bool), 
  (if b then false else false) = false.
Proof. destruct b; reflexivity; reflexivity.
Qed.


Lemma XtimesXid : Xgate × Xgate = I 2.
Proof. compute. prep_matrix_equality. do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma YtimesYid : Ygate × Ygate = I 2.
Proof. compute. prep_matrix_equality. do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma ZtimesZid : Zgate × Zgate = I 2.
Proof. compute. prep_matrix_equality. do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.



Lemma Y_eq_iXZ : Ygate = Ci .* Xgate × Zgate.
Proof. compute. prep_matrix_equality. do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : lca. 
Qed.


Lemma ZH_eq_HX : Zgate × Hgate = Hgate × Xgate.
Proof. assert (H : Zgate × Hraw = Hraw × Xgate). 
       { compute. prep_matrix_equality. 
         do 3 (try destruct x; try destruct y; simpl; trivial).
         all : lca. }
       unfold Hgate. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l. rewrite H. 
       reflexivity. 
Qed.



Lemma PX_eq_YP : Pgate × Xgate = Ygate × Pgate.
Proof. compute. prep_matrix_equality. do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : lca. 
Qed.

Lemma HtimesHid : Hgate × Hgate = I 2.
Proof. assert (H : Hraw × Hraw = 2 .* I 2). 
       { compute. prep_matrix_equality. 
         do 3 (try destruct x; try destruct y; simpl; trivial).
         all : (try lca). rewrite -> Propff. lca. }
       unfold Hgate. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l.
       rewrite H. rewrite Mscale_assoc. rewrite Cinv_sqrt2_sqrt. rewrite Mscale_assoc.
       assert (H': / 2 * 2 = 1). { lca. } rewrite H'. rewrite Mscale_1_l. reflexivity.
Qed.

Lemma XH_eq_HZ : Xgate × Hgate = Hgate × Zgate.
Proof. assert (H : Xgate × Hraw = Hraw × Zgate). 
       { compute. prep_matrix_equality. 
         do 3 (try destruct x; try destruct y; simpl; trivial).
         all : lca. }
       unfold Hgate. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l. rewrite H. 
       reflexivity.
Qed.
 
(* Showing that the basic operators we use are unitary *)

Definition is_unitary {n : nat} (A : Square n) : Prop :=
  A × (A†) = I n. 

Lemma X_unitary : is_unitary Xgate.
Proof. unfold is_unitary. compute. prep_matrix_equality. 
       do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma Y_unitary : is_unitary Ygate.
Proof. unfold is_unitary. compute. prep_matrix_equality. 
       do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma Z_unitary : is_unitary Zgate.
Proof. unfold is_unitary. compute. prep_matrix_equality. 
       do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma H_unitary : is_unitary Hgate.
Proof. assert (H: Hgate† = Hgate). 
       { unfold adjoint. compute. prep_matrix_equality.
         do 3 (try destruct x; try destruct y; simpl; trivial). all : (try lca). }
       unfold is_unitary. rewrite H. apply HtimesHid.
Qed.

Lemma P_unitary : is_unitary Pgate.
Proof. unfold is_unitary. compute. prep_matrix_equality. 
       do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma CNOT1_unitary : is_unitary CNOT1.
Proof. unfold is_unitary. compute. prep_matrix_equality. 
       do 5 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma CNOT2_unitary : is_unitary CNOT2.
Proof. unfold is_unitary. compute. prep_matrix_equality. 
       do 5 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.



(* defining Heisenberg representation *)

Definition gate_type {n : nat} (U A B : Square n) : Prop :=
  U × A = B × U.

Definition gate_app {n : nat} (U A : Square n) : Square n :=
  U × A × U†.

Notation "U : A ~> B" := (gate_type U A B) (at level 0) : matrix_scope. 
Notation "U ( A )" := (gate_app U A) (at level 0) : matrix_scope. 



(* how do I get rid of this?? I don't want to have to include that matrices 
   are well formed every time, although perhaps it is neccesary... *)

Axiom Mmult_1_r: forall (n : nat) (A : Square n),
  A × I n = A.

Lemma type_is_app : forall (n: nat) (U A B : Square n),
  is_unitary U -> (U : A ~> B <-> U(A) = B).
Proof. intros n U A B H. split.
       - unfold gate_type; unfold gate_app. intros H'. unfold is_unitary in H. rewrite H'.
         rewrite Mmult_assoc. rewrite H. rewrite Mmult_1_r. reflexivity. 
       - unfold gate_type; unfold gate_app. intros H'. rewrite <- H'. rewrite Mmult_assoc.
         unfold is_unitary in H. apply Minv_flip in H. rewrite H. rewrite Mmult_assoc.
         rewrite Mmult_1_r. reflexivity. 
Qed.


(* Formal statements of all the transformations listed in figure 1 of Gottesman*)


Definition H_app := gate_app Hgate.

Definition P_app_ := gate_app Hgate.

Definition CNOT1_app := gate_app CNOT1.

Definition CNOT2_app := gate_app CNOT2.


Lemma HonX : Hgate : Xgate ~> Zgate.
Proof. unfold gate_type. rewrite ZH_eq_HX. easy.
Qed.

Lemma HonZ : Hgate : Zgate ~> Xgate.
Proof. unfold gate_type. symmetry. apply XH_eq_HZ.
Qed.

Lemma PonX : Pgate : Xgate ~> Ygate.
Proof. unfold gate_type. apply PX_eq_YP.
Qed.



Lemma PonZ : Pgate : Zgate ~> Zgate.
Proof. unfold gate_type. lma. (* did not prove above *)
       compute. prep_matrix_equality. do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : lca.
Qed.

Lemma CNOT1onX1 : CNOT1 : (X 1) ~> (X 1 × X 2). 
Proof. do 3 (try destruct x; try destruct y; simpl; trivial). 

Lemma CNOT1onX2 : CNOT1 : (X 2) ~> (X 2). 
Proof. Admitted.

Lemma CNOT1onZ1 : CNOT1 : (Z 1) ~> (Z 1). 
Proof. Admitted.

Lemma CNOT1onZ2 : CNOT1 : (Z 2) ~> (Z 1 × Z 2). 
Proof. Admitted.


Lemma CNOT2onX1 : CNOT2 : (X 1) ~> (X 1). 
Proof. Admitted.

Lemma CNOT2onX2 : CNOT2 : (X 2) ~> (X 1 × X 2). 
Proof. Admitted.

Lemma CNOT2onZ1 : CNOT2 : (Z 1) ~> (Z 1 × Z 2). 
Proof. Admitted.

Lemma CNOT2onZ2 : CNOT2 : (Z 2) ~> (Z 1). 
Proof. Admitted.

(* lemmas about heisenberg representation *)

Lemma app_comp : forall (n : nat) (U A B C : Square n),
  U(A) = B -> U(B) = C -> (U×U) (A) = C.
Proof. unfold gate_app. intros n U A B C H1 H2. rewrite Mmult_adjoint. do 2 rewrite Mmult_assoc.
       assert (H: U × (A × (U† × U†)) = U × A × U† × U† ). { do 2 rewrite Mmult_assoc. reflexivity. }
       rewrite H. rewrite H1. rewrite <- Mmult_assoc. rewrite H2. reflexivity.
Qed.

Lemma app_mult : forall (n : nat) (U A1 B1 A2 B2 : Square n),
  is_unitary U -> U(A1) = B1 -> U(A2) = B2 -> U(A1 × A2) = B1×B2.
Proof. intros n U A1 B1 A2 B2. unfold gate_app. intros H0 H1 H2. rewrite <- H1. rewrite <- H2.
       assert (H: U† × (U × A2 × U†) = U† × U × A2 × U†). { do 2 rewrite <- Mmult_assoc. reflexivity. }
       do 3 rewrite Mmult_assoc. rewrite H. unfold is_unitary in H0.
       apply Minv_flip in H0. rewrite H0. do 4 rewrite <- Mmult_assoc. assert (H': U × A1 × I n = U × A1).
       { rewrite Mmult_assoc. rewrite Mmult_1_r. reflexivity. } rewrite H'. reflexivity.
       
Qed. 



(* Example 1 *)

Definition U1 : Matrix 4 4 := CNOT1 × CNOT2 × CNOT1.

Lemma U1onX1 : U1 : (X 1) ~> (X 2).
Proof. unfold gate_app. unfold U1. (rewrite <- Mmult_1_r) X 1. rewrite <- Mmult_1_r.



unfold is_unitary. compute. prep_matrix_equality. 
       do 3 (try destruct x; try destruct y; simpl; trivial). 
       all : (try lca). rewrite -> Propff. lca.
Qed.

Lemma 

Definition Zgatetwo : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 0];
    [RtoC 0; - RtoC 1]]).
