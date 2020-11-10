Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.
Require Export Matrix.
Require Import Quantum.





Definition X (n : nat) : Matrix 4 4 :=
  match n with 
  | 2 => I 2 ⊗ σx
  | 1 => σx ⊗ I 2
  | _ => I 4
  end. 

Definition Z (n : nat) : Matrix 4 4 :=
  match n with 
  | 2 => I 2 ⊗ σz
  | 1 => σz ⊗ I 2
  | _ => I 4
  end.


Definition Phase : Matrix 2 2 := phase_shift (PI / 2).

Definition Phase' : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Ci
          | _, _ => C0
          end.




(*                     *)




(* Lemmas about well formedness of pauli gates. Commented out *)
(* lemmas are already implemented in Quantam.v *)


 
(*
Lemma WF_σx : WF_Matrix σx. Proof. show_wf. Qed.
Lemma WF_σy : WF_Matrix σy. Proof. show_wf. Qed.
Lemma WF_σz : WF_Matrix σx. Proof. show_wf. Qed.
Lemma WF_hadamard : WF_Matrix hadamard. Proof. show_wf. Qed.
Lemma WF_cnot : WF_Matrix cnot. Proof. show_wf. Qed. 
*)


Lemma WF_Phase : WF_Matrix Phase. Proof. show_wf. Qed.
Lemma WF_Phase' : WF_Matrix Phase'. Proof. show_wf. Qed.
Lemma WF_notc : WF_Matrix notc. Proof. show_wf. Qed.


(* todo: must automate this *)
Lemma WF_Xn : forall (n : nat), WF_Matrix (X n).
Proof. unfold X.
       destruct n as [|n]. simpl. auto with wf_db. 
       destruct n as [|n]. simpl. auto with wf_db.
       destruct n as [|n]. simpl. auto with wf_db.
       auto with wf_db.
Qed.

Lemma WF_Zn : forall (n : nat), WF_Matrix (Z n).
Proof. unfold Z. 
       destruct n as [|n]. simpl. auto with wf_db. 
       destruct n as [|n]. simpl. auto with wf_db.
       destruct n as [|n]. simpl. auto with wf_db.
       auto with wf_db.
Qed.



Hint Resolve WF_Xn WF_Zn WF_Phase WF_Phase' WF_notc  : wf_db.


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

Lemma XtimesXid : σx × σx = I 2. Proof. lma'. Qed.      
Lemma YtimesYid : σy × σy = I 2. Proof. lma'. Qed.
Lemma ZtimesZid : σz × σz = I 2. Proof. lma'. Qed.
Lemma Y_eq_iXZ : σy = Ci .* σx × σz. Proof. lma'. Qed.
Lemma ZH_eq_HX : σz × hadamard = hadamard × σx. Proof. lma'. Qed.
Lemma PX_eq_YP : Phase × σx = σy × Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma HtimesHid : hadamard × hadamard = I 2. Proof. lma'; Hhelper. Qed.
Lemma H_eq_Hadjoint : hadamard = hadamard†. Proof. lma'. Qed.
Lemma XH_eq_HZ : σx × hadamard = hadamard × σz. Proof. lma'. Qed.




(* Showing that the basic operators we use are unitary *)

Definition is_unitary {n : nat} (A : Square n) : Prop :=
  A × (A†) = I n. 

Lemma X_unitary : is_unitary σx. Proof. lma'. Qed.
Lemma Y_unitary : is_unitary σy. Proof. lma'. Qed.
Lemma Z_unitary : is_unitary σz. Proof. lma'. Qed.
Lemma P_unitary : is_unitary Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma cnot_unitary : is_unitary cnot. Proof. lma'. Qed.
Lemma notc_unitary : is_unitary notc. Proof. lma'. Qed.

Lemma H_unitary : is_unitary hadamard.
Proof.  unfold is_unitary. rewrite <- H_eq_Hadjoint. rewrite HtimesHid. reflexivity.
Qed.


(* defining Heisenberg representation *)


Declare Scope heisenberg_scope.
Delimit Scope heisenberg_scope with H.
Open Scope heisenberg_scope.


Definition gate_type {n : nat} (U A B : Square n) : Prop :=
  U × A = B × U.

Definition gate_app {n : nat} (U A : Square n) : Square n :=
  U × A × U†.


Notation "U :: A → B" := (gate_type U A B) (at level 0) : heisenberg_scope. 
Notation "U [ A ]" := (gate_app U A) (at level 0) : heisenberg_scope. 


(* how do I get rid of this?? I don't want to have to include that matrices 
   are well formed every time, although perhaps it is neccesary... *)

Axiom Mmult_1_r': forall (n : nat) (A : Square n),
  A × I n = A.

Axiom Mmult_1_l': forall (n : nat) (A : Square n),
  I n × A = A.



  
Lemma type_is_app : forall (n: nat) (U A B : Square n),
  is_unitary U -> (U :: A → B <-> U[A] = B).
Proof. intros n U A B H. split.
       - unfold gate_type; unfold gate_app. intros H'. unfold is_unitary in H. rewrite H'.
         rewrite Mmult_assoc. rewrite H. rewrite Mmult_1_r'. reflexivity. 
       - unfold gate_type; unfold gate_app. intros H'. rewrite <- H'. rewrite Mmult_assoc.
         unfold is_unitary in H. apply Minv_flip in H. rewrite H. rewrite Mmult_assoc.
         rewrite Mmult_1_r'. reflexivity. 
Qed.


(* Formal statements of all the transformations listed in figure 1 of Gottesman*)


Definition H_app := gate_app hadamard.
Definition P_app_ := gate_app hadamard.
Definition cnot_app := gate_app cnot.
Definition notc_app := gate_app notc.


Lemma HonX : hadamard :: σx → σz.
Proof. unfold gate_type. rewrite ZH_eq_HX. easy.
Qed.

Lemma HonZ : hadamard :: σz → σx.
Proof. unfold gate_type. symmetry. apply XH_eq_HZ.
Qed.

Lemma PonX : Phase :: σx → σy.
Proof. unfold gate_type. apply PX_eq_YP.
Qed.



Lemma PonZ : Phase :: σz → σz.
Proof. unfold gate_type. rewrite PEqP'. lma'. 
Qed.







(* will optimize these into Ltac *)
Lemma cnotonX1 : cnot :: (X 1) → (X 1 × X 2). 
Proof. apply mat_equiv_eq'; auto with wf_db. by_cell; lca.
Qed.
    

Lemma cnotonX2 : cnot :: (X 2) → (X 2). 
Proof. lma'.
Qed.       

Lemma cnotonZ1 : cnot :: (Z 1) → (Z 1). 
Proof. lma'.
Qed.

Lemma cnotonZ2 : cnot :: (Z 2) → (Z 1 × Z 2). 
Proof. lma'.
Qed.


Lemma notconX1 : notc :: (X 1) → (X 1). 
Proof. lma'.
Qed.
       
Lemma notconX2 : notc :: (X 2) → (X 1 × X 2). 
Proof. lma'.
Qed.

Lemma notconZ1 : notc :: (Z 1) → (Z 1 × Z 2). 
Proof. lma'.
Qed.

Lemma notconZ2 : notc :: (Z 2) → (Z 2). 
Proof. lma'.
Qed.

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
         { rewrite Mmult_assoc. rewrite Mmult_1_r'. reflexivity. }
       rewrite H'. reflexivity.       
Qed. 



(* Could write this using other method, but good to see use of kron_mixed_product *)
Lemma X1timesX1id :  (σx ⊗ I 2) × (σx ⊗ I 2) = I 4.
Proof. lma'.
Qed.

Lemma X2timesX2id :  (I 2 ⊗ σx) × (I 2 ⊗ σx) = I 4.
Proof. lma'.
Qed.

Lemma XntimesXnid : forall (n : nat), X n × X n = I 4.
Proof. destruct n. simpl. rewrite Mmult_1_r. reflexivity.
       apply WF_I.
       destruct n. rewrite <- X1timesX1id. unfold X. reflexivity.
       destruct n. rewrite <- X2timesX2id. unfold X. reflexivity.
       simpl. rewrite Mmult_1_r. reflexivity. apply WF_I.
Qed. 

 



(* Example 1 *)

Definition U1 : Matrix 4 4 := cnot × notc × cnot.

Lemma U1onX1 : U1 :: (X 1) → (X 2). 
Proof. unfold U1. assert (H1: cnot[X 1] = (X 1 × X 2)).
       { apply type_is_app. apply cnot_unitary. apply cnotonX1. }
       assert (H2: notc[X 1] = (X 1)).
       { apply type_is_app. apply notc_unitary. apply notconX1. }
       assert (H3: notc[X 2] = (X 1 × X 2)).
       { apply type_is_app. apply notc_unitary. apply notconX2. }
       assert (H4: notc[(X 1) × (X 2)] = (X 1) × (X 1 × X 2)).
       { apply app_mult. apply notc_unitary. apply H2. apply H3. }
       assert (H5: X 1 × (X 1 × X 2) = X 2). 
       { rewrite <- Mmult_assoc. rewrite XntimesXnid. rewrite Mmult_1_l. reflexivity.
       auto with wf_db. }   
       rewrite H5 in H4. assert (H6: (notc × cnot)[X 1] = X 2).
       { apply (app_comp 4 cnot notc (X 1) (X 1 × X 2)). apply H1. apply H4. }
       assert (H7: cnot[X 2] = (X 2)).
       { apply type_is_app. apply cnot_unitary. apply cnotonX2. }
       rewrite Mmult_assoc. apply type_is_app.
       - unfold is_unitary. lma'.
       - apply (app_comp 4 (notc × cnot) cnot (X 1) (X 2) (X 2)).
         apply H6. apply H7.
Qed.



Definition Eigenstate {n : nat} (U : Square n) (v : Vector n) : Prop :=
  exists (λ : C), U × v = λ .* v.

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
    WF_Matrix v -> Eigenstate (I n) v.
Proof. intros n v H. exists C1. rewrite Mmult_1_l. lma. apply H.
Qed.


Lemma Proposition1 : forall (n : nat) (U A B : Square n) (v : Vector n),
    is_unitary U -> U :: A → B -> Eigenstate A v -> Eigenstate B (U × v).
Proof. unfold Eigenstate. intros n U A B v isU ty [λ Eig].
       unfold gate_type in ty. rewrite <- Mmult_assoc. rewrite <- ty.
       rewrite Mmult_assoc. rewrite Eig. exists λ. rewrite Mscale_mult_dist_r.
       reflexivity.
Qed.

(* Lemma Proposition2 : forall (n : nat) (U : Square 2) (u : Vector 2) (v : Vector (2^(n-1))),
    Eigenstate U u <-> Eigenstate (U ⊗ ((n-1) ⨂ (I 2))) (u ⊗ v).
Proof. intros n U u v. split.
       - intros [λ Eig]. unfold Eigenstate. exists λ.
         rewrite kron_n_I. rewrite kron_mixed_product.   *)
         


Definition qubitP : Vector 2 := / (√ 2) .* (∣0⟩ .+ ∣1⟩).

Definition qubitM : Vector 2 := / (√ 2) .* (∣0⟩ .+ ((-1) .* ∣1⟩)).

Notation "∣+⟩" := qubitP.
Notation "∣-⟩" := qubitM.

Lemma WF_qubitP : WF_Matrix ∣+⟩. Proof. show_wf. Qed.
Lemma WF_qubitM : WF_Matrix ∣-⟩. Proof. show_wf. Qed.


Hint Resolve WF_qubitP WF_qubitM : wf_db. 


Definition EPRpair : Vector 4 := / (√ 2) .* (∣0,0⟩ .+ ∣1,1⟩).

Lemma EPRpair_creation : cnot × (hadamard ⊗ I 2) × ∣0,0⟩ = EPRpair.
Proof. unfold EPRpair. lma'.
Qed.

Lemma EigenXp : Eigenstate σx ∣+⟩.
Proof. unfold Eigenstate. exists (1). lma'.
Qed.

Lemma EigenXm : Eigenstate σx ∣-⟩.
Proof. unfold Eigenstate. exists (-1). lma'.
Qed.

Lemma EigenZ0 : Eigenstate σz ∣0⟩.
Proof. unfold Eigenstate. exists (1). lma'.
Qed.

Lemma EigenZ1 : Eigenstate σz ∣1⟩.
Proof. unfold Eigenstate. exists (-1). lma'.
Qed.









(****************************)
(* ATTEMPTS AT REFINING LMA *)
(****************************)

(*

(* we need this for some reason... I assume there is a built in tactic that does this*)
Lemma Propiff : forall (b : bool), 
  (if b then false else false) = false.
Proof. destruct b; reflexivity; reflexivity.
Qed.



(* added extra tactic to prevent stuckness at if _ then false else false lines *)
Ltac destruct_m_eq_piff := repeat (destruct_m_1; simpl; try lca; try (rewrite -> Propiff)).


Ltac lma1 := 
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq; 
  lca.


Ltac lma2 :=
  compute;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq_piff;
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


Ltac destruct_m_eq' := repeat 
                         (progress (try destruct_m_1'; try rewrite divmod_0; try rewrite divmod_S ; simpl)).



Ltac destruct_m_eq_piff' := repeat (destruct_m_eq'; destruct_m_eq_piff).  

Ltac lma3 :=
  compute;
  autounfold with U_db;
  prep_matrix_equality;
  destruct_m_eq_piff;
  try destruct_m_eq_piff';    (* <---- For some reason adding this broke things... *)
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

Ltac lma4 := by_cell; try lca.






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



*)

