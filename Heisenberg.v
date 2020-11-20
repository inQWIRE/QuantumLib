Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.
Require Export Matrix.
Require Import Quantum.





Definition Xn (n : nat) : Matrix 4 4 :=
  match n with 
  | 2 => I 2 ⊗ σx
  | 1 => σx ⊗ I 2
  | _ => I 4
  end. 

Definition Zn (n : nat) : Matrix 4 4 :=
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



(*****************************************************************)
(* Lemmas about well formedness of pauli gates and some vectors. *)
(* Commented out lemmas are already implemented in Quantam.v     *)
(*****************************************************************)

 
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

Lemma WF_ket : forall (x : nat), WF_Matrix ∣x⟩.
Proof. intros x. unfold ket. destruct (x =? 0). show_wf. show_wf. 
Qed. 

Lemma WF_bra : forall (x : nat), WF_Matrix (bra x).
Proof. intros x. unfold bra. destruct (x =? 0). show_wf. show_wf. 
Qed. 


(* todo: must automate this *)
Lemma WF_Xn : forall (n : nat), WF_Matrix (Xn n).
Proof. unfold Xn.
       destruct n as [|n]. simpl. auto with wf_db. 
       destruct n as [|n]. simpl. auto with wf_db.
       destruct n as [|n]. simpl. auto with wf_db.
       auto with wf_db.
Qed.

Lemma WF_Zn : forall (n : nat), WF_Matrix (Zn n).
Proof. unfold Zn. 
       destruct n as [|n]. simpl. auto with wf_db. 
       destruct n as [|n]. simpl. auto with wf_db.
       destruct n as [|n]. simpl. auto with wf_db.
       auto with wf_db.
Qed.



Hint Resolve WF_Xn WF_Zn WF_Phase WF_Phase' WF_notc WF_ket WF_bra : wf_db.



(***************************************************************)
(* Proving some indentities and that certain gates are unitary *)
(***************************************************************)


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







(**************************************************)
(* Defining eignestates to be used in type system *)
(**************************************************)


Definition Eigenstate {n : nat} (U : Square n) (v : Vector n) : Prop :=
  exists (λ : C), U × v = λ .* v.

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
    WF_Matrix v -> Eigenstate (I n) v.
Proof. intros n v H. exists C1. rewrite Mmult_1_l. lma. apply H.
Qed.


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

Lemma EigenXXB : Eigenstate (σx ⊗ σx) ∣Φ+⟩.
Proof. unfold Eigenstate. exists 1. lma'.
Qed.


Hint Resolve EigenXp EigenXm EigenZ0 EigenZ1 EigenXXB all_v_eigen_I : eig_db.





(**************************************)
(* defining Heisenberg representation *)
(**************************************)


Declare Scope heisenberg_scope.
Delimit Scope heisenberg_scope with H.
Open Scope heisenberg_scope.


(* should do this eventually: 

(* this establishes the paradigm for the type system *)
Inductive mType {X : Type} : Type :=
  | sing (U : X)
  | cap  (U : X) (l : mType).

Notation "A → B" := (A,B) (at level 60, right associativity).
Notation "A ∩ B" := (cap A (sing B)) (at level 60, no associativity).

Notation vectType n := (mType (Square n)).
Notation gateType n := (mType (Square n * Square n)).


*)

Notation vectType n := (list (Square n)).


Definition singVectType {n : nat} (v : Vector n) (A: Square n) : Prop :=
  Eigenstate A v. 


Fixpoint vectHasType {n : nat} (v : Vector n) (ts: vectType n) : Prop := 
  match ts with  
  | [] => True
  | (t :: ts') => (singVectType v t) /\ vectHasType v ts'
  end.


Notation "v :' T" := (vectHasType v T) (at level 61) : heisenberg_scope. 


Notation "A ∩ B" := (A ++ B) (at level 60, no associativity) : heisenberg_scope.



(* how do I get rid of this?? I don't want to have to include that matrices 
   are well formed every time, although perhaps it is neccesary... *)

Axiom Mmult_1_r': forall (n : nat) (A : Square n),
  A × I n = A.

Axiom Mmult_1_l': forall (n : nat) (A : Square n),
  I n × A = A.





(*****************************)
(* Basic vectType operations *)
(*****************************)


(* Singleton says if a vectType is able to be multiplied, scaled, or kronned  *)
Definition Singleton {n : nat} (A : vectType n) :=
  match A with
  | [a] => True
  | _ => False
  end. 

(* mul assumes that vectTypes are singleton. Otherwise, there is undefined behavior *)
Definition mul {n : nat} (A B : vectType n) := 
  match A with
  | [] => []
  | (a :: _) => 
      match B with
      | [] => []
      | (b :: _) => [a × b]
      end  
  end.

(* similarly, scale does the same *)
Definition scale {n : nat} (c : C) (A : vectType n) := 
  match A with
  | [] => []
  | (a :: _) => [c .* a]
  end.

Definition i {n : nat} (A : vectType n) :=
  scale Ci A.

Definition neg {n : nat} (A : vectType n) :=
  scale (-1) A.

(* same with kron *)
Definition tensor {n m : nat} (A : vectType n) (B : vectType m) := 
  match A with
  | [] => []
  | (a :: _) => 
      match B with
      | [] => []
      | (b :: _) => [a ⊗ b]
      end  
  end.


Notation "- T" := (neg T) : heisenberg_scope. 
Infix "*'" := mul (at level 40, left associativity) : heisenberg_scope. 
Infix "⊗'" := tensor (at level 51, right associativity) : heisenberg_scope. 



(* Singleton laws *)

Definition X : vectType 2 := [σx].
Definition Z : vectType 2 := [σz].
Definition I : vectType 2 := [I 2].


Lemma SI : Singleton I. Proof. easy. Qed.
Lemma SX : Singleton X. Proof. easy. Qed.
Lemma SZ : Singleton Z. Proof. easy. Qed.

Lemma S_neg : forall (n : nat) (A : vectType n), Singleton A -> Singleton (neg A).
Proof. intros n A. 
       destruct A. easy.
       destruct A. easy.
       easy.
Qed.

Lemma S_i : forall (n : nat) (A : vectType n), Singleton A -> Singleton (i A).
Proof. intros n A. 
       destruct A. easy.
       destruct A. easy.
       easy.
Qed.

Lemma S_mul : forall (n : nat) (A B : vectType n), 
  Singleton A -> Singleton B -> Singleton (A *' B).
Proof. intros n A B. 
       destruct A. easy.
       destruct A. destruct B. easy.
       destruct B. easy. easy. easy.
Qed. 

Hint Resolve SI SX SZ S_neg S_i S_mul : sing_db.

Notation Y := (i (X *' Z)).

Lemma SY : Singleton Y.
Proof. auto with sing_db. Qed.

(* Multiplication laws *)


(* for a lot of these, there could be an initial supposition
that the types are singleton, but we can get away without doing
this for most of the lemmas *)

Lemma mul_assoc : forall (n : nat) (A B C : vectType n), A *' (B *' C) = A *' B *' C.
Proof. intros n A B C. 
       destruct A. reflexivity. simpl.
       destruct B. reflexivity. simpl.
       destruct C. reflexivity. rewrite Mmult_assoc. reflexivity.
Qed.

(* these two would rely on Axioms anyways so they should just be axioms here too *)
(* We are assuming matrices are well formed anyways... *)
Axiom mul_I_l : forall A, I *' A = A.
Axiom mul_I_r : forall A, A *' I = A.

Lemma Xsqr : X *' X = I.
Proof. simpl. unfold I. rewrite XtimesXid. reflexivity.
Qed.

Lemma Zsqr : Z *' Z = I.
Proof. simpl. unfold I. rewrite ZtimesZid. reflexivity.
Qed.

Lemma ZmulX : Z *' X = - (X *' Z).
Proof. simpl. assert (H : σz × σx = -1 .* (σx × σz)). 
       { lma'. } rewrite H. reflexivity.
Qed.

Lemma neg_inv : forall (n : nat) (A : vectType n), 
  Singleton A -> - - A = A.
Proof. intros n A.
       destruct A. easy.
       destruct A. simpl. rewrite Mscale_assoc. 
       assert (H: -1 * -1 .* m = m). { lma. }
       rewrite H. easy. easy.
Qed.                                    

Lemma neg_dist_l : forall (n : nat) (A B : vectType n), -A *' B = - (A *' B).
Proof. intros n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_mult_dist_l. reflexivity.
Qed.       
       
Lemma neg_dist_r : forall (n : nat) (A B : vectType n), A *' -B = - (A *' B).
Proof. intros n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_mult_dist_r. reflexivity.
Qed.

Lemma i_sqr : forall (n : nat) (A : vectType n), i (i A) = -A.
Proof. intros n A. 
       destruct A. reflexivity. simpl.
       rewrite Mscale_assoc. assert (H: Ci * Ci = -1). { lca. } 
       rewrite H. reflexivity.
Qed. 


Lemma i_dist_l : forall (n : nat) (A B : vectType n), i A *' B = i (A *' B).
Proof. intros n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_mult_dist_l. reflexivity.
Qed.

Lemma i_dist_r : forall (n : nat) (A B : vectType n), A *' i B = i (A *' B).
Proof. intros n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_mult_dist_r. reflexivity.
Qed.

Lemma i_neg_comm : forall (n : nat) (A : vectType n), i (-A) = -i A.
Proof. intros n A. 
       destruct A. reflexivity. simpl. 
       do 2 rewrite Mscale_assoc. assert (H: Ci * -1 = -1 * Ci). 
       { lca. } rewrite H. reflexivity.
Qed.

Hint Rewrite mul_I_l mul_I_r Xsqr Zsqr ZmulX neg_inv neg_dist_l neg_dist_r i_sqr i_dist_l i_dist_r i_neg_comm : mul_db.



(** ** Tensor Laws *)

Lemma tensor_assoc : forall (m n o: nat) (A : vectType n) (B : vectType n) (C : vectType n),  
  A ⊗' (B ⊗' C) = (A ⊗' B) ⊗' C.  
Proof. intros m n o A B C. 
       destruct A. reflexivity. simpl.
       destruct B. reflexivity. simpl.
       destruct C. reflexivity. rewrite kron_assoc. reflexivity. 
Qed.

Lemma neg_tensor_dist_l : forall (m n : nat) (A : vectType n) (B : vectType n),
  -A ⊗' B = - (A ⊗' B).
Proof. intros m n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_kron_dist_l. reflexivity.
Qed.

Lemma neg_tensor_dist_r : forall (m n : nat) (A : vectType n) (B : vectType n),
  A ⊗' -B = - (A ⊗' B).
Proof. intros m n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_kron_dist_r. reflexivity.
Qed.

Lemma i_tensor_dist_l : forall (m n : nat) (A : vectType n) (B : vectType n),
  i A ⊗' B = i (A ⊗' B).
Proof. intros m n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_kron_dist_l. reflexivity.
Qed.

Lemma i_tensor_dist_r : forall (m n : nat) (A : vectType n) (B : vectType n), 
  A ⊗' i B = i (A ⊗' B).
Proof. intros m n A B. 
       destruct A. reflexivity.
       destruct B. reflexivity. simpl. 
       rewrite Mscale_kron_dist_r. reflexivity.
Qed.

(** ** Multiplication & Tensor Laws *)

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Lemma mul_tensor_dist : forall (m n : nat) 
  (A : vectType m) (B : vectType n) (C : vectType m) (D : vectType n),
    (A ⊗' B) *' (C ⊗' D) = (A *' C) ⊗' (B *' D).
Proof. intros m n A B C D.
       destruct A. reflexivity.
       destruct B. destruct C. reflexivity. reflexivity.
       destruct C. reflexivity. 
       destruct D. reflexivity. simpl.
       rewrite kron_mixed_product. reflexivity.
Qed.

Lemma decompose_tensor : forall A B,
    Singleton A ->
    Singleton B ->
    A ⊗' B = (A ⊗' I) *' (I ⊗' B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall (A B : vectType 2),
    Singleton A ->
    Singleton B ->
    (A *' B) ⊗' I = (A ⊗' I) *' (B ⊗' I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall (A B : vectType 2),
    I ⊗' (A *' B) = (I ⊗' A) *' (I ⊗' B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.
  
Hint Rewrite neg_tensor_dist_l neg_tensor_dist_r i_tensor_dist_l i_tensor_dist_r : tensor_db.



(* subset lemmas *) 


Fixpoint subset {X : Type} (l1 l2 : list X) :=
  match l1 with
  | [] => True
  | (l :: l1') => In l l2 /\ subset l1' l2
  end.

Infix "⊆" := subset (at level 30, no associativity) : heisenberg_scope.


Lemma subset_cons : forall (X : Type) (l1 l2 : list X) (x : X),
  l1 ⊆ l2 -> l1 ⊆ (x :: l2).
Proof. intros X l1 l2 x. induction l1 as [| t].
       - easy. 
       - simpl. intros [H H']. split.
         * right. apply H.
         * apply IHl1. apply H'.
Qed.

Lemma subset_concat_l : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l1 ++ l2).
Proof. intros X l1 l2. induction l1 as [| t].
       - easy.  
       - simpl. split. left. easy. apply subset_cons. apply IHl1.
Qed.



Lemma in_middle : forall (X : Type) (l1 l2 : list X) (x : X),
  In x (l1 ++ (x :: l2)).
Proof. intros X l1 l2 x. induction l1 as [| t].
       - simpl. left. reflexivity. 
       - simpl. right. apply IHl1. 
Qed.

Lemma subset_concat_r : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l2 ++ l1).
Proof. intros X l1. induction l1 as [| t].
       - easy.  
       - intros l2. split. 
         * apply in_middle. 
         * assert (H: t :: l1 = [t] ++ l1). { reflexivity. }
           rewrite H. rewrite <- app_ass. apply IHl1.
Qed.


Corollary subset_self : forall (X : Type) (l1 : list X),
  l1 ⊆ l1. 
Proof. intros X l1. assert (H: l1 ⊆ (l1 ++ [])). { apply subset_concat_l. }
       rewrite <- app_nil_end in H. apply H. 
Qed.


Lemma subsets_add : forall (X : Type) (l1 l2 l3: list X),
  l1 ⊆ l3 -> l2 ⊆ l3 -> (l1 ++ l2) ⊆ l3.
Proof. intros X l1 l2 l3. induction l1 as [| t].
       - simpl. easy. 
       - simpl. intros [H H'] H1. split. apply H.
         apply IHl1. apply H'. apply H1.
Qed.


Hint Resolve subset_concat_l subset_concat_r subset_self subsets_add : sub_db.


(** ** Intersection Laws *)

Lemma subset_helper : forall (n : nat) (v : Vector n) (t : Square n) (ts : vectType n),
  In t ts -> v :' ts -> singVectType v t.
Proof. intros n v t. induction ts as [| t']. 
       - easy.
       - simpl. intros [H1 | H1'] [H2 H3].
         * rewrite H1 in H2. apply H2.
         * apply IHts. apply H1'. apply H3.
Qed.


Lemma has_type_subset : forall (n : nat) (v : Vector n) (t1s t2s : vectType n),
  t1s ⊆ t2s -> v :' t2s -> v :' t1s.
Proof. intros n v t1s t2s. 
       induction t1s as [| t].
       - destruct t2s. easy. simpl. easy.
       - simpl. intros [H1 H1'] H2. split.
         * apply (subset_helper n v t t2s). apply H1.  apply H2. 
         * apply IHt1s. apply H1'. apply H2.
Qed.



Definition eqType {n : nat} (T1 T2 : vectType n) := 
  (T1 ⊆ T2) /\ (T2 ⊆ T1).


Infix "≡" := eqType (at level 70, no associativity) : heisenberg_scope.


(* converse of this is true as well since matrices are unitary? *)
(* probably hard to prove on coq *) 
Lemma eqTypes_are_Eq : forall (n : nat) (v : Vector n) (T1 T2 : vectType n),
  (T1 ≡ T2) -> (v :' T1 <-> v:' T2).
Proof. intros n v T1 T2. unfold eqType. intros [H H']. split.
       - intros H1. apply (has_type_subset n v T2 T1). apply H'. apply H1.
       - intros H1. apply (has_type_subset n v T1 T2). apply H. apply H1.
Qed.


Lemma cap_idem : forall (n : nat) (A : vectType n), A ∩ A ≡ A.
Proof. intros n A. split. 
       - auto with sub_db.
       - auto with sub_db.
Qed. 

Lemma cap_comm : forall (n : nat) (A B : vectType n), A ∩ B ≡ B ∩ A.
Proof. intros n A B. split.
       - auto with sub_db.
       - auto with sub_db.
Qed.

Lemma cap_assoc_eq : forall (n : nat) (A B C : vectType n), A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof. intros n A B C. rewrite app_ass. reflexivity.
Qed.

Lemma cap_assoc : forall (n : nat) (A B C : vectType n), A ∩ (B ∩ C) ≡ (A ∩ B) ∩ C.
Proof. intros n A B C. rewrite cap_assoc_eq. split. 
       auto with sub_db. auto with sub_db.
Qed.


Axiom cap_I_l : forall A,
  Singleton A ->
  I ∩ A = A.

Lemma cap_I_r : forall A,
  Singleton A ->
  A ∩ I = A.
Proof. Admitted. (* intros; rewrite cap_comm, cap_I_l; easy. Qed. *)

(* another important lemma about ∩ *)
Lemma types_add : forall (n : nat) (v : Vector n) (A B : vectType n),
  v :' A -> v :' B -> v :' (A ∩ B).
Proof. intros n v A B. induction A as [| a].
       - simpl. easy. 
       - simpl. intros [Ha Ha'] Hb. split. apply Ha.
         apply IHA. apply Ha'. apply Hb.
Qed.
         
(* first test of the new paradigm *)
Ltac normalize_mul :=
  repeat match goal with
  | |- context[(?A ⊗ ?B) ⊗ ?C] => rewrite <- (tensor_assoc A B C)
  end;
  repeat (rewrite mul_tensor_dist by auto with sing_db);
  repeat rewrite mul_assoc;
  repeat (
      try rewrite <- (mul_assoc _ X Z _);
      autorewrite with mul_db tensor_db;
      try rewrite mul_assoc).

Lemma Ysqr : Y *' Y = I. Proof. normalize_mul; auto with sing_db. Qed.
Lemma XmulZ : X *' Z = - Z *' X. Proof. normalize_mul; auto with sing_db. Qed.
Lemma XmulY : X *' Y = i Z. Proof. normalize_mul; auto with sing_db. Qed.
Lemma YmulX : Y *' X = -i Z. Proof. normalize_mul; auto with sing_db. Qed.
Lemma ZmulY : Z *' Y = -i X. Proof. normalize_mul; auto with sing_db. Qed.
Lemma YmulZ : Y *' Z = i X. Proof. normalize_mul; auto with sing_db. Qed.


(* some more lemmas about specific vectors *)


Ltac vectHasType := simpl; unfold singVectType; auto with eig_db.


Lemma all_hastype_I : forall (v : Vector 2),
  WF_Matrix v -> v :' I.
Proof. intros v H. simpl. split. vectHasType. easy. 
Qed.
  
Lemma p_hastype_X : ∣+⟩ :' X. Proof. vectHasType. Qed. 
Lemma m_hastype_X : ∣-⟩ :' X. Proof. vectHasType. Qed.
Lemma O_hastype_Z : ∣0⟩ :' Z. Proof. vectHasType. Qed.
Lemma i_hastype_Z : ∣1⟩ :' Z. Proof. vectHasType. Qed.

Lemma B_hastype_XX : Eigenstate (σx ⊗ σx) ∣Φ+⟩. Proof. vectHasType. Qed.


Hint Resolve all_hastype_I p_hastype_X m_hastype_X O_hastype_Z i_hastype_Z B_hastype_XX : vht_db.



(***************************)
(* Writing actual programs *)
(***************************)



Notation gateType n := (list (Square n * Square n)).


Definition singGateType {n : nat} (U : Square n) (p : Square n * Square n) : Prop :=
  U × (fst p) = (snd p) × U.


Fixpoint gateHasType {n : nat} (U : Square n) (ts: gateType n) : Prop := 
  match ts with  
  | [] => True
  | (t :: ts') => (singGateType U t) /\ gateHasType U ts'
  end.


Notation "U :> F" := (gateHasType U F) (at level 61) : heisenberg_scope.


(* Given two singleton vectTypes, forms a gateType. Returns error if not singleton *)
Definition formGateType {n : nat} (A B : vectType n) :=
  match A with
  | []  => []  
  | (a :: _) => 
    match B with
    | [] => []
    | (b :: _) => [(a,b)]
    end
  end.



Notation "A → B" := (formGateType A B) (at level 60, no associativity) : heisenberg_scope. 




Definition gateApp {n : nat} (U A : Square n) : Square n :=
  U × A × U†.

Notation "U [ A ]" := (gateApp U A) (at level 0) : heisenberg_scope. 



  
Lemma type_is_app : forall (n: nat) (U A B : Square n),
  is_unitary U -> (U :> ([A] → [B])  <-> U[A] = B).
Proof. intros n U A B H. split.
       - unfold gateHasType; unfold gateApp. intros [H'  T]. unfold is_unitary in H.
         unfold singGateType in H'. simpl in H'. rewrite H'. 
         rewrite Mmult_assoc. rewrite H. rewrite Mmult_1_r'. reflexivity. 
       - unfold gateHasType; unfold gateApp. intros H'. split. rewrite <- H'. rewrite Mmult_assoc.
         unfold is_unitary in H. apply Minv_flip in H. unfold singGateType. simpl.
         rewrite <- Mmult_assoc. rewrite Mmult_assoc. rewrite H.
         rewrite Mmult_1_r'. reflexivity. trivial.
Qed.


(* Gate definitions *)

Definition H := hadamard.
Definition CNOT :=  cnot.


Definition seq {n : nat} (U1 U2 : Square n) := U2 × U1. 

Infix ";" := seq (at level 51, right associativity).


Lemma Htypes : H :> (Z → X) ∩ (X → Z).
Proof. simpl. unfold singGateType. simpl. split.
       lma'. split. lma'. easy.
Qed.






(* Formal statements of all the transformations listed in figure 1 of Gottesman*)


Definition H_app := gateApp hadamard.
Definition P_app_ := gateApp hadamard.
Definition cnot_app := gateApp cnot.
Definition notc_app := gateApp notc.


Ltac Hsimpl := unfold gateHasType; 
               split; unfold singGateType; simpl.


Lemma HonX : hadamard ::: σx → σz.
Proof. Hsimpl. lma'. easy. 
Qed.

Lemma HonZ : hadamard ::: σz → σx.
Proof. Hsimpl. lma'. easy. 
Qed.

Lemma PonX : Phase ::: σx → σy.
Proof. Hsimpl. apply PX_eq_YP. easy.
Qed.


Lemma PonZ : Phase ::: σz → σz.
Proof. Hsimpl. lma'. easy. 
Qed.





(* will optimize these into Ltac *)
Lemma cnotonX1 : cnot ::: (X 1) → (X 1 × X 2). 
Proof. Hsimpl. apply mat_equiv_eq'; auto with wf_db. by_cell; lca. easy.
Qed.
    

Lemma cnotonX2 : cnot ::: (X 2) → (X 2). 
Proof. Hsimpl. lma'. easy.
Qed.       

Lemma cnotonZ1 : cnot ::: (Z 1) → (Z 1). 
Proof. Hsimpl. lma'. easy.
Qed.

Lemma cnotonZ2 : cnot ::: (Z 2) → (Z 1 × Z 2). 
Proof. Hsimpl. lma'. easy.
Qed.


Lemma notconX1 : notc ::: (X 1) → (X 1). 
Proof. Hsimpl. lma'. easy.
Qed.
       
Lemma notconX2 : notc ::: (X 2) → (X 1 × X 2). 
Proof. Hsimpl. lma'. easy.
Qed.

Lemma notconZ1 : notc ::: (Z 1) → (Z 1 × Z 2). 
Proof. Hsimpl. lma'. easy.
Qed.

Lemma notconZ2 : notc ::: (Z 2) → (Z 2). 
Proof. Hsimpl. lma'. easy.
Qed.

(* lemmas about heisenberg representation *)

Lemma app_comp : forall (n : nat) (U1 U2 A B C : Square n),
  U1[A] = B -> U2[B] = C -> (U2×U1) [A] = C.
Proof. unfold gateApp. intros n U1 U2  A B C H1 H2. rewrite <- H2. rewrite <- H1.
       rewrite Mmult_adjoint. do 3 rewrite <- Mmult_assoc. reflexivity. 
Qed.

Lemma app_mult : forall (n : nat) (U A1 B1 A2 B2 : Square n),
  is_unitary U -> U[A1] = B1 -> U[A2] = B2 -> U[A1 × A2] = B1×B2.
Proof. intros n U A1 B1 A2 B2. unfold gateApp. intros H0 H1 H2.
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
