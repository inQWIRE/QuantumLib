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

Definition X1 : Matrix 4 4 := 
  list2D_to_matrix  
  ([[RtoC 0; RtoC 0; RtoC 1; RtoC 0];
    [RtoC 0; RtoC 0; RtoC 0; RtoC 1];
    [RtoC 1; RtoC 0; RtoC 0; RtoC 0];
    [RtoC 0; RtoC 1; RtoC 0; RtoC 0]]).

Definition X2 : Matrix 4 4 := 
  list2D_to_matrix  
  ([[RtoC 0; RtoC 1; RtoC 0; RtoC 0];
    [RtoC 1; RtoC 0; RtoC 0; RtoC 0];
    [RtoC 0; RtoC 0; RtoC 0; RtoC 1];
    [RtoC 0; RtoC 0; RtoC 1; RtoC 0]]).


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







(****************************)
(* ATTEMPTS AT REFINING LMA *)
(****************************)



(* we need this for some reason... I assume there is a built in tactic that does this*)
Lemma Propff : forall (b : bool), 
  (if b then false else false) = false.
Proof. destruct b; reflexivity; reflexivity.
Qed.



(* added extra tactic to prevent stuckness at if _ then false else false lines *)
Ltac destruct_m_eq2 := repeat (destruct_m_1; simpl; try lca; try (rewrite -> Propff)).

Ltac lma2 :=
  compute;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq2;
  try lca.



(*stuff to deal with divmod problems*)

Lemma divmod_eq : forall x y n z, 
  fst (Nat.divmod x y n z) = (n + fst (Nat.divmod x y 0 z))%nat.
Proof.
  induction x.
  + intros. simpl. lia.
  + intros. simpl. 
    destruct z.
    rewrite IHx.
    rewrite IHx with (n:=1%nat).
    lia.
    rewrite IHx.
    reflexivity.
Qed.

Lemma divmod_S : forall x y n z, 
  fst (Nat.divmod x y (S n) z) = (S n + fst (Nat.divmod x y 0 z))%nat.
Proof. intros. apply divmod_eq. Qed.

Ltac destruct_m_1' :=
  match goal with
  | [ |- context[match ?x with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  | [ |- context[match fst (Nat.divmod ?x _ _ _) with 
                 | 0   => _
                 | S _ => _
                 end] ] => is_var x; destruct x
  end.

Lemma divmod_0q0 : forall x q, fst (Nat.divmod x 0 q 0) = (x + q)%nat. 
Proof.
  induction x.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHx. lia.
Qed.

Lemma divmod_0 : forall x, fst (Nat.divmod x 0 0 0) = x. 
Proof. intros. rewrite divmod_0q0. lia. Qed.



(*must prove but is definitely true. Will do later... may be difficult*)
(*also I probably shouldn't have to prove this random thing, but it works*)
(*does it generalize? Kron makes this very bad...*) 
Lemma resolve_divmod : forall y : nat,
    Nat.divmod y 1 2 0 = ((2 + y / 2 + (y mod 2%nat))%nat, y mod 2%nat).
Proof. Admitted.




Ltac destruct_m_eq' := repeat 
                         (progress (try destruct_m_1'; try rewrite divmod_0; try rewrite divmod_S ; try rewrite resolve_divmod; simpl)).



Ltac destruct_m_eq_super := repeat (destruct_m_eq'; destruct_m_eq2).  

Ltac lma_super :=
  compute;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq2;
  destruct_m_eq_super;    (* <---- For some reason adding this broke things... *)
  try lca. 
                                    







Ltac solve_end :=
  match goal with
  | H : lt _ O |- _ => apply Nat.nlt_0_r in H; contradict H
  end.
                
Ltac by_cell := 
  intros;
  let i := fresh "i" in 
  let j := fresh "j" in 
  let Hi := fresh "Hi" in 
  let Hj := fresh "Hj" in 
  intros i j Hi Hj; try solve_end;
  repeat (destruct i as [|i]; simpl; [|apply lt_S_n in Hi]; try solve_end); clear Hi;
  repeat (destruct j as [|j]; simpl; [|apply lt_S_n in Hj]; try solve_end); clear Hj.

Ltac lma3 := by_cell; try lca.






(*another approach but might be antithesis to the 'matrix is  function paradigm'
  This can probably be made better with less helper functions that make the axiom
  hard to prove  *)

Fixpoint get_ps1 (n m : nat) : list (nat * nat) :=
  match m with
  | O    => [(n, m)]
  | S m' => (n, m) :: get_ps1 n m'
  end.

Fixpoint get_ps (n m : nat) : list (nat * nat) :=
  match n with
  | O    => get_ps1 n m
  | S n' => get_ps1 n m ++ get_ps n' m
  end.

Definition mtol {n m : nat} (M : Matrix n m) : list C :=
  map (fun p =>  M (fst p) (snd p)) (get_ps (n - 1) (m - 1)). 


Axiom mat_eq_list : forall {m n : nat} (A B : Matrix m n),
  mtol A = mtol B <-> mat_equiv A B.







(*                     *)










(* Lemmas about Pauli and other common matrices *) 


Lemma XtimesXid : Xgate × Xgate = I 2. 
Proof. lma_super. (*now it almost seems like I am doing no work? It this the convention? Perhaps for computations...*)
Qed.      

Lemma YtimesYid : Ygate × Ygate = I 2.
Proof. lma_super.
Qed.

Lemma ZtimesZid : Zgate × Zgate = I 2.
Proof. lma_super.
Qed.



Lemma Y_eq_iXZ : Ygate = Ci .* Xgate × Zgate.
Proof. lma_super.
Qed.


Lemma ZH_eq_HX : Zgate × Hgate = Hgate × Xgate.
Proof. assert (H : Zgate × Hraw = Hraw × Xgate). 
       { lma_super. }
       unfold Hgate. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l. rewrite H. 
       reflexivity. 
Qed.



Lemma PX_eq_YP : Pgate × Xgate = Ygate × Pgate.
Proof. lma_super.
Qed.

Lemma HtimesHid : Hgate × Hgate = I 2.
Proof. assert (H : Hraw × Hraw = 2 .* I 2). 
       { lma_super. }
       unfold Hgate. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l.
       rewrite H. rewrite Mscale_assoc. rewrite Cinv_sqrt2_sqrt. rewrite Mscale_assoc.
       assert (H': / 2 * 2 = 1). { lca. } rewrite H'. rewrite Mscale_1_l. reflexivity.
Qed.

Lemma XH_eq_HZ : Xgate × Hgate = Hgate × Zgate.
Proof. assert (H : Xgate × Hraw = Hraw × Zgate). 
       { lma_super. }
       unfold Hgate. rewrite Mscale_mult_dist_r. rewrite Mscale_mult_dist_l. rewrite H. 
       reflexivity.
Qed.
 
(* Showing that the basic operators we use are unitary *)

Definition is_unitary {n : nat} (A : Square n) : Prop :=
  A × (A†) = I n. 

Lemma X_unitary : is_unitary Xgate.
Proof. lma_super. 
Qed.

Lemma Y_unitary : is_unitary Ygate.
Proof. lma_super. 
Qed.

Lemma Z_unitary : is_unitary Zgate.
Proof. lma_super.
Qed.

Lemma H_unitary : is_unitary Hgate.
Proof. assert (H: Hgate† = Hgate). 
       { lma_super. }
       unfold is_unitary. rewrite H. apply HtimesHid.
Qed.

Lemma P_unitary : is_unitary Pgate.
Proof. lma_super.
Qed.

Lemma CNOT1_unitary : is_unitary CNOT1.
Proof. lma_super.
Qed.

Lemma CNOT2_unitary : is_unitary CNOT2.
Proof. lma_super.
Qed.


(* defining Heisenberg representation *)

Definition gate_type {n : nat} (U A B : Square n) : Prop :=
  U × A = B × U.

Definition gate_app {n : nat} (U A : Square n) : Square n :=
  U × A × U†.




Notation "U : A → B" := (gate_type U A B) (at level 0) : matrix_scope. 
Notation "U [ A ]" := (gate_app U A) (at level 0) : matrix_scope. 



(* how do I get rid of this?? I don't want to have to include that matrices 
   are well formed every time, although perhaps it is neccesary... *)

Axiom Mmult_1_r: forall (n : nat) (A : Square n),
  A × I n = A.

Axiom Mmult_1_l: forall (n : nat) (A : Square n),
  I n × A = A.



  
Lemma type_is_app : forall (n: nat) (U A B : Square n),
  is_unitary U -> (U : A → B <-> U[A] = B).
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


Lemma HonX : Hgate : Xgate → Zgate.
Proof. unfold gate_type. rewrite ZH_eq_HX. easy.
Qed.

Lemma HonZ : Hgate : Zgate → Xgate.
Proof. unfold gate_type. symmetry. apply XH_eq_HZ.
Qed.

Lemma PonX : Pgate : Xgate → Ygate.
Proof. unfold gate_type. apply PX_eq_YP.
Qed.



Lemma PonZ : Pgate : Zgate → Zgate.
Proof. unfold gate_type. lma_super. 
Qed.


Lemma X2iscorrect : X2 = X 2.
Proof. lma_super. rewrite Propff. lca. 
Qed.       


Lemma CNOT1onX1 : CNOT1 : (X 1) → (X 1 × X 2). 
Proof. Admitted. 

Lemma CNOT1onX2 : CNOT1 : (X 2) → (X 2). 
Proof. Admitted. 
       
Lemma CNOT1onZ1 : CNOT1 : (Z 1) → (Z 1). 
Proof. Admitted.

Lemma CNOT1onZ2 : CNOT1 : (Z 2) → (Z 1 × Z 2). 
Proof. Admitted.


Lemma CNOT2onX1 : CNOT2 : (X 1) → (X 1). 
Proof. Admitted.

Lemma CNOT2onX2 : CNOT2 : (X 2) → (X 1 × X 2). 
Proof. Admitted.

Lemma CNOT2onZ1 : CNOT2 : (Z 1) → (Z 1 × Z 2). 
Proof. Admitted.

Lemma CNOT2onZ2 : CNOT2 : (Z 2) → (Z 1). 
Proof. Admitted.

(* lemmas about heisenberg representation *)

Lemma app_comp : forall (n : nat) (U1 U2 A B C : Square n),
  U1[A] = B -> U2[B] = C -> (U2×U1) [A] = C.
Proof. unfold gate_app. intros n U1 U2  A B C H1 H2. rewrite <- H2. rewrite <- H1.
       rewrite Mmult_adjoint. do 3 rewrite <- Mmult_assoc. reflexivity. 
Qed.

Lemma app_mult : forall (n : nat) (U A1 B1 A2 B2 : Square n),
  is_unitary U -> U[A1] = B1 -> U[A2] = B2 -> U[A1 × A2] = B1×B2.
Proof. intros n U A1 B1 A2 B2. unfold gate_app. intros H0 H1 H2.
       rewrite <- H1. rewrite <- H2.
       assert (H: U† × (U × A2 × U†) = U† × U × A2 × U†).
         { do 2 rewrite <- Mmult_assoc. reflexivity. }
       do 3 rewrite Mmult_assoc. rewrite H. unfold is_unitary in H0.
       apply Minv_flip in H0. rewrite H0. do 4 rewrite <- Mmult_assoc.
       assert (H': U × A1 × I n = U × A1).
         { rewrite Mmult_assoc. rewrite Mmult_1_r. reflexivity. }
       rewrite H'. reflexivity.       
Qed. 



(* these lemmas seemed excessive. For some reason I could    *)
(* not rewrite (Xgate ⊗ I 2) × (Xgate ⊗ I 2)without them..   *)
Lemma X1timesX1id :  (Xgate ⊗ I 2) × (Xgate ⊗ I 2) = I 4.
Proof. unfold X. rewrite kron_mixed_product. rewrite XtimesXid. rewrite Mmult_1_r.
       rewrite id_kron. simpl. easy.
Qed.

Lemma X2timesX2id :  (I 2 ⊗ Xgate) × (I 2 ⊗ Xgate) = I 4.
Proof. unfold X. rewrite kron_mixed_product. rewrite XtimesXid. rewrite Mmult_1_r.
       rewrite id_kron. simpl. easy.
Qed.


Lemma XntimesXnid : forall (n : nat), X n × X n = I 4.
Proof. destruct n. simpl. rewrite Mmult_1_r. reflexivity.
       destruct n. rewrite <- X1timesX1id. unfold X. reflexivity.
       destruct n. rewrite <- X2timesX2id. unfold X. reflexivity.
       simpl. rewrite Mmult_1_r. reflexivity.
Qed. 

 



(* Example 1 *)

Definition U1 : Matrix 4 4 := CNOT1 × CNOT2 × CNOT1.

Lemma U1onX1 : U1 : (X 1) → (X 2).
Proof. unfold U1. assert (H1: CNOT1[X 1] = (X 1 × X 2)).
       { apply type_is_app. apply CNOT1_unitary. apply CNOT1onX1. }
       assert (H2: CNOT2[X 1] = (X 1)).
       { apply type_is_app. apply CNOT2_unitary. apply CNOT2onX1. }
       assert (H3: CNOT2[X 2] = (X 1 × X 2)).
       { apply type_is_app. apply CNOT2_unitary. apply CNOT2onX2. }
       assert (H4: CNOT2[(X 1) × (X 2)] = (X 1) × (X 1 × X 2)).
       { apply app_mult. apply CNOT2_unitary. apply H2. apply H3. }
       assert (H5: X 1 × (X 1 × X 2) = X 2). 
       { rewrite <- Mmult_assoc. rewrite XntimesXnid. rewrite Mmult_1_l. reflexivity. }   
       rewrite H5 in H4. assert (H6: (CNOT2 × CNOT1)[X 1] = X 2).
       { apply (app_comp 4 CNOT1 CNOT2 (X 1) (X 1 × X 2)). apply H1. apply H4. }
       assert (H7: CNOT1[X 2] = (X 2)).
       { apply type_is_app. apply CNOT1_unitary. apply CNOT1onX2. }
       rewrite Mmult_assoc. apply type_is_app.
       - unfold is_unitary. lma2.
       - apply (app_comp 4 (CNOT2 × CNOT1) CNOT1 (X 1) (X 2) (X 2)).
         apply H6. apply H7.
Qed.
       
    

Definition Zgatetwo : Matrix 2 2 := 
  list2D_to_matrix  
  ([[RtoC 1; RtoC 0];
    [RtoC 0; - RtoC 1]]).
