Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Import List.
Require Export Matrix.
Require Import Quantum.
Require Import Setoid.




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


Definition Tgate :=  phase_shift (PI / 4).



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
Lemma WF_Tgate: WF_Matrix Tgate. Proof. show_wf. Qed.
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
       destruct n; simpl; auto with wf_db.
       destruct n; simpl; auto with wf_db.
       destruct n; simpl; auto with wf_db. 
Qed.

Lemma WF_Zn : forall (n : nat), WF_Matrix (Zn n).
Proof. unfold Zn. 
       destruct n; simpl; auto with wf_db.
       destruct n; simpl; auto with wf_db.
       destruct n; simpl; auto with wf_db. 
Qed.



Hint Resolve WF_Xn WF_Zn WF_Phase WF_Phase' WF_Tgate WF_notc WF_ket WF_bra : wf_db.



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



(* how do I get rid of this?? I don't want to have to include that matrices 
   are well formed every time, although perhaps it is neccesary... *)
Axiom Mmult_1_r': forall (n m : nat) (A : Matrix n m),
  A × I n = A.

Axiom Mmult_1_l': forall (n m : nat) (A : Matrix n m),
  I n × A = A.


Definition Eigenstate {n : nat} (U : Square n) (v : Vector n) : Prop :=
  exists (λ : C), U × v = λ .* v.

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
   Eigenstate (I n) v.
Proof. intros n v. exists C1. rewrite Mmult_1_l'. lma. 
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


Notation vecType n := (list (Square n)).


Definition singVecType {n : nat} (v : Vector n) (A: Square n) : Prop :=
  Eigenstate A v. 


Definition vecHasType {n : nat} (v : Vector n) (ts: vecType n) : Prop := 
  forall (A : Square n), In A ts -> singVecType v A.

(* an alternate definition which helps with singleton tactics later *)
Fixpoint vecHasType' {n : nat} (v : Vector n) (ts: vecType n) : Prop := 
  match ts with  
  | [] => True
  | (t :: ts') => (singVecType v t) /\ vecHasType' v ts'
  end.

Lemma vecHasType_is_vecHasType' : forall (n : nat) (v : Vector n) (A : vecType n),
  vecHasType v A <-> vecHasType' v A.
Proof. intros n v A. split.
       - induction A as [| h]. 
         * easy. 
         * intros H.  
           simpl. split.
           + unfold vecHasType in H.
             apply H. 
             simpl; left; reflexivity. 
           + apply IHA. 
             unfold vecHasType in H. 
             unfold vecHasType; intros.
             apply H; simpl; right; apply H0.
       - induction A as [| h]. 
         * easy. 
         * intros [H1 H2].
           unfold vecHasType; intros.
           apply IHA in H2. 
           unfold vecHasType in H2. 
           destruct H as [H3 | H4].
           rewrite <- H3; apply H1.
           apply H2; apply H4.
Qed.


Notation "v :' T" := (vecHasType v T) (at level 61) : heisenberg_scope. 


Notation "A ∩ B" := (A ++ B) (at level 60, no associativity) : heisenberg_scope.




(*****************************)
(* Basic vectType operations *)
(*****************************)


(* Singleton says if a vectType is able to be multiplied, scaled, or kronned  *)
Definition Singleton {n : nat} (A : vecType n) :=
  match A with
  | [a] => True
  | _ => False
  end. 


(* helper lemma to immediatly turn singleton vecType into [a] form *)
Lemma singleton_simplify : forall {n} (A : vecType n),
  Singleton A -> exists (a : Square n), A = [a].
Proof. intros; destruct A. 
       easy. 
       destruct A.
       exists m. 
       reflexivity. 
       easy.
Qed.



(* multiplies every combination of lists A and B *)
Fixpoint mul {n : nat} (A B : vecType n) := 
  match A with
  | [] => [] 
  | (a :: as') => List.map (fun b => a × b) B ++ mul as' B
  end.


(* similarly, scale does the same *)
Fixpoint scale {n : nat} (c : C) (A : vecType n) := 
  match A with
  | [] => []
  | (a :: as') => (c .* a) :: (scale c as')
  end.

Definition i {n : nat} (A : vecType n) :=
  scale Ci A.

Definition neg {n : nat} (A : vecType n) :=
  scale (-1) A.

(* same with kron *)
Fixpoint tensor {n m : nat} (A : vecType n) (B : vecType m) := 
  match A with
  | [] => [] 
  | (a :: as') => List.map (fun b => a ⊗ b) B ++ tensor as' B
  end.


Fixpoint tensor_n n {m} (A : vecType m) :=
  match n with
  | 0    => [I 1]
  | S n' => tensor (tensor_n n' A) A
  end.



Notation "- T" := (neg T) : heisenberg_scope. 
Infix "*'" := mul (at level 40, left associativity) : heisenberg_scope. 
Infix "⊗'" := tensor (at level 51, left associativity) : heisenberg_scope. 
Infix "·" := scale (at level 45, left associativity) : heisenberg_scope. 
Notation "n ⨂' A" := (tensor_n n A) (at level 30, no associativity) : heisenberg_scope.

(* Singleton laws *)

Definition X : vecType 2 := [σx].
Definition Z : vecType 2 := [σz].
Definition I : vecType 2 := [I 2].


Lemma SI : Singleton I. Proof. easy. Qed.
Lemma SX : Singleton X. Proof. easy. Qed.
Lemma SZ : Singleton Z. Proof. easy. Qed.

Lemma S_neg : forall (n : nat) (A : vecType n), Singleton A -> Singleton (neg A).
Proof. intros n A. 
       destruct A. easy.
       destruct A. easy.
       easy.
Qed.

Lemma S_i : forall (n : nat) (A : vecType n), Singleton A -> Singleton (i A).
Proof. intros n A. 
       destruct A. easy.
       destruct A. easy.
       easy.
Qed.

Lemma S_mul : forall (n : nat) (A B : vecType n), 
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


(* some helper lemmas *)
Lemma cons_conc : forall (X : Type) (x : X) (ls : list X),
    x :: ls = [x] ++ ls.
Proof. reflexivity. Qed.

Lemma mul_sing : forall (n : nat) (a b : Square n),
    [a] *' [b] = [a × b].
Proof. reflexivity.
Qed.

Lemma mul_nil_l : forall (n : nat) (A : vecType n), [] *' A = [].
Proof. simpl. reflexivity. 
Qed.

Lemma mul_nil_r : forall (n : nat) (A : vecType n), A *' [] = [].
Proof. intros n A. induction A as [| a].
       - simpl. reflexivity. 
       - simpl. apply IHA.
Qed.

Lemma cons_into_mul_l : forall (n : nat) (a : Square n) (A B : vecType n),
    (a :: A) *' B = ([a] *' B) ++ (A *' B). 
Proof. intros n a A B. simpl.
       rewrite <- app_nil_end.
       reflexivity.
Qed.       

Lemma concat_into_mul_l : forall (n : nat) (A B C : vecType n),
    (A ++ B) *' C = (A *' C) ++ (B *' C). 
Proof. intros n A B C. induction A as [| a].
       - simpl. reflexivity. 
       - rewrite cons_into_mul_l.
         rewrite cons_conc. rewrite app_ass.
         rewrite <- cons_conc.
         rewrite cons_into_mul_l.
         rewrite IHA. rewrite app_ass.
         reflexivity.
Qed.


Lemma sing_concat_into_mul_r : forall (n : nat) (a : Square n) (B C : vecType n),
    [a] *' (B ++ C) = ([a] *' B) ++ ([a] *' C).
Proof. intros n a B C. simpl.
       do 3 (rewrite <- app_nil_end).
       rewrite map_app.
       reflexivity.
Qed.


Lemma sing_mul_assoc : forall (n : nat) (a b : Square n) (C : vecType n),
    [a] *' [b] *' C = [a] *' ([b] *' C). 
Proof. intros n a b C. induction C as [| c].
       - simpl. reflexivity. 
       - rewrite (cons_conc _ c C).
         rewrite (sing_concat_into_mul_r n b [c] C).
         do 2 (rewrite mul_sing).
         rewrite (sing_concat_into_mul_r n _ [c] C).
         rewrite (sing_concat_into_mul_r n a _ _).
         rewrite <- IHC.
         do 3 (rewrite mul_sing).
         rewrite Mmult_assoc.
         reflexivity.
Qed.

Lemma sing_mul_assoc2 : forall (n : nat) (a : Square n) (B C : vecType n),
    [a] *' B *' C = [a] *' (B *' C). 
Proof. intros n a B C. induction B as [| b].
       - simpl. reflexivity. 
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_mul_r. 
         do 2 (rewrite concat_into_mul_l).
         rewrite sing_concat_into_mul_r.
         rewrite sing_mul_assoc.
         rewrite IHB.
         reflexivity.
Qed.         


Theorem mul_assoc : forall (n : nat) (A B C : vecType n), A *' (B *' C) = A *' B *' C.
Proof. intros n A B C. induction A as [| a].
       - simpl. reflexivity. 
       - rewrite cons_conc.
         do 3 (rewrite concat_into_mul_l). 
         rewrite IHA.
         rewrite sing_mul_assoc2.
         reflexivity.
Qed.

Lemma mul_I_l : forall (A : vecType 2), I *' A = A.
Proof. intros A. unfold I. induction A as [| a].
       - reflexivity.
       - rewrite (cons_conc _ a A). 
         rewrite sing_concat_into_mul_r.
         rewrite IHA.
         simpl.
         rewrite Mmult_1_l'.
         reflexivity.
Qed.

Lemma mul_I_r : forall (A : vecType 2), A *' I = A.
Proof. intros A. unfold I. induction A as [| a].
       - reflexivity.
       - rewrite cons_into_mul_l.
         rewrite IHA.
         simpl.
         rewrite Mmult_1_r'.
         reflexivity.
Qed.
  
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

Lemma scale_1_l : forall (n : nat) (A : vecType n), 1 · A = A.
Proof. intros n A. induction A as [|a].
       - reflexivity.
       - simpl. rewrite IHA.
         rewrite Mscale_1_l.
         reflexivity. 
Qed.

Lemma scale_assoc : forall (n : nat) (a b : C) (A : vecType n),
    a · (b · A) = (a * b) · A.
Proof. intros n a b A. induction A as [| h].
       - reflexivity.
       - simpl. rewrite IHA.
         rewrite Mscale_assoc.
         reflexivity.
Qed.
         

Lemma neg_inv : forall (n : nat) (A : vecType n),  - - A = A.
Proof. intros n A. unfold neg.
       rewrite scale_assoc.
       assert (H: -1 * -1 = 1). { lca. }
       rewrite H. rewrite scale_1_l. 
       reflexivity.
Qed.                                    

Lemma concat_into_scale : forall (n : nat) (c : C) (A B : vecType n),
    c · (A ++ B) = (c · A) ++ (c · B).
Proof. intros n c A B. induction A as [|a].
       - reflexivity.
       - simpl. rewrite IHA.
         reflexivity.
Qed.

Lemma scale_sing : forall (n : nat) (c : C) (a : Square n),
    c · [a] = [c .* a].
Proof. reflexivity.
Qed.

Lemma sing_scale_dist_l : forall (n : nat) (c : C) (a : Square n) (B : vecType n),
    (c · [a]) *' B = c · ([a] *' B).
Proof. intros n c a B. induction B as [|b].
       - reflexivity.
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_mul_r.
         rewrite concat_into_scale.
         rewrite scale_sing.
         rewrite sing_concat_into_mul_r.
         rewrite <- IHB. rewrite scale_sing.
         do 2 (rewrite mul_sing).
         rewrite scale_sing.
         rewrite Mscale_mult_dist_l.
         reflexivity.
Qed.

 
Lemma scale_dist_l : forall (n : nat) (c : C) (A B : vecType n), (c · A) *' B = c · (A *' B).
Proof. intros n c A B. induction A as [|a].
       - reflexivity.
       - rewrite cons_into_mul_l. rewrite cons_conc.
         do 2 (rewrite concat_into_scale).
         rewrite concat_into_mul_l.
         rewrite IHA. rewrite sing_scale_dist_l.
         reflexivity.
Qed.


(* note that this is slightly different than what we would expect. *)
(* scaling is on right, but singleton is still left list *)
Lemma sing_scale_dist_r : forall (n : nat) (c : C) (a : Square n) (B : vecType n),
    [a] *' (c · B) = c · ([a] *' B).
Proof. intros n c a B. induction B as [| b].
       - reflexivity.
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_mul_r.
         do 2 (rewrite concat_into_scale).
         rewrite sing_concat_into_mul_r.
         rewrite IHB.
         rewrite scale_sing.
         do 2 (rewrite mul_sing).
         rewrite scale_sing.
         rewrite Mscale_mult_dist_r.
         reflexivity.
Qed.

Lemma scale_dist_r : forall (n : nat) (c : C) (A B : vecType n), A *' (c · B) = c · (A *' B).
Proof. intros n c A B. induction A as [|a].
       - reflexivity.
       - rewrite cons_into_mul_l.
         rewrite (cons_into_mul_l n a A B).
         rewrite concat_into_scale.
         rewrite IHA.
         rewrite sing_scale_dist_r.
         reflexivity.
Qed.


Lemma neg_dist_l : forall (n : nat) (A B : vecType n), -A *' B = - (A *' B).
Proof. intros n A B.
       unfold neg.
       rewrite scale_dist_l. reflexivity.
Qed.       
       
Lemma neg_dist_r : forall (n : nat) (A B : vecType n), A *' -B = - (A *' B).
Proof. intros n A B.
       unfold neg.
       rewrite scale_dist_r. reflexivity.
Qed.

Lemma i_sqr : forall (n : nat) (A : vecType n), i (i A) = -A.
Proof. intros n A. unfold neg. unfold i.
       rewrite scale_assoc.
       assert (H: Ci * Ci = -1). { lca. }
       rewrite H. 
       reflexivity.
Qed. 


Lemma i_dist_l : forall (n : nat) (A B : vecType n), i A *' B = i (A *' B).
Proof. intros n A B.
       unfold i.
       rewrite scale_dist_l. reflexivity.
Qed.

Lemma i_dist_r : forall (n : nat) (A B : vecType n), A *' i B = i (A *' B).
Proof. intros n A B.
       unfold i.
       rewrite scale_dist_r. reflexivity.
Qed.

Lemma i_neg_comm : forall (n : nat) (A : vecType n), i (-A) = -i A.
Proof. intros n A. unfold neg; unfold i.
       do 2 (rewrite scale_assoc).
       assert (H: Ci * -1 = -1 * Ci). 
       { lca. } rewrite H. reflexivity.
Qed.

Hint Rewrite  mul_sing mul_nil_r mul_I_l mul_I_r Xsqr Zsqr ZmulX neg_inv scale_dist_l scale_dist_r neg_dist_l neg_dist_r i_sqr i_dist_l i_dist_r i_neg_comm : mul_db.


(** ** Tensor Laws *)


(* basically, we need the same helper lemmas for tensoring *)
(* should all WF conditions, but I will assume all gates are well formed *)

Lemma tensor_sing : forall (m n : nat) (a : Square n) (b : Square m),
    [a] ⊗' [b] = [a ⊗ b].
Proof. reflexivity.
Qed.


Lemma cons_into_tensor_l : forall (m n : nat) (a : Square n) (A : vecType n) (B : vecType m),
    (a :: A) ⊗' B = ([a] ⊗' B) ++ (A ⊗' B). 
Proof. intros m n a A B. simpl.
       rewrite <- app_nil_end.
       reflexivity.
Qed.       

Lemma concat_into_tensor_l : forall (m n : nat) (A B : vecType n) (C : vecType m),
    (A ++ B) ⊗' C = (A ⊗' C) ++ (B ⊗' C). 
Proof. intros m n A B C. induction A as [| a].
       - simpl. reflexivity. 
       - rewrite cons_into_tensor_l.
         rewrite cons_conc. rewrite app_ass.
         rewrite <- cons_conc.
         rewrite cons_into_tensor_l.
         rewrite IHA. rewrite app_ass.
         reflexivity.
Qed.


Lemma sing_concat_into_tensor_r : forall (m n : nat) (a : Square m) (B C : vecType n),
    [a] ⊗' (B ++ C) = ([a] ⊗' B) ++ ([a] ⊗' C).
Proof. intros m n a B C. simpl.
       do 3 (rewrite <- app_nil_end).
       rewrite map_app.
       reflexivity.
Qed.


Lemma sing_tensor_assoc : forall (m n o : nat) (a : Square m) (b : Square n) (C : vecType o),
    [a] ⊗' [b] ⊗' C = [a] ⊗' ([b] ⊗' C). 
Proof. intros m n o a b C. induction C as [| c].
       - simpl. reflexivity. 
       - rewrite (cons_conc _ c C).
         rewrite (sing_concat_into_tensor_r n o b [c] C).
         do 2 (rewrite tensor_sing).
         rewrite (sing_concat_into_tensor_r _ o _ [c] C).
         rewrite (sing_concat_into_tensor_r _ _ a _ _).
         rewrite <- IHC.
         do 3 (rewrite tensor_sing).
         rewrite kron_assoc.
         reflexivity.
Qed.

Lemma sing_tensor_assoc2 : forall (m n o: nat) (a : Square m) (B : vecType n) (C : vecType o),
    [a] ⊗' B ⊗' C = [a] ⊗' (B ⊗' C). 
Proof. intros m n o a B C. induction B as [| b].
       - simpl. reflexivity. 
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_tensor_r. 
         do 2 (rewrite concat_into_tensor_l).
         rewrite sing_concat_into_tensor_r.
         rewrite sing_tensor_assoc.
         rewrite IHB.
         reflexivity.
Qed.         


Theorem tensor_assoc : forall (m n o: nat) (A : vecType n) (B : vecType n) (C : vecType n),  
  A ⊗' (B ⊗' C) = (A ⊗' B) ⊗' C. 
Proof. intros m n o A B C. induction A as [| a].
       - simpl. reflexivity. 
       - rewrite cons_conc.
         do 3 (rewrite concat_into_tensor_l). 
         rewrite IHA.
         rewrite sing_tensor_assoc2.
         reflexivity.
Qed.



Lemma sing_scale_tensor_dist_l : forall (n m : nat) (c : C) (a : Square n) (B : vecType m),
    (c · [a]) ⊗' B = c · ([a] ⊗' B).
Proof. intros n m c a B. induction B as [|b].
       - reflexivity.
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_tensor_r.
         rewrite concat_into_scale.
         rewrite scale_sing.
         rewrite sing_concat_into_tensor_r.
         rewrite <- IHB. rewrite scale_sing.
         do 2 (rewrite tensor_sing).
         rewrite scale_sing.
         rewrite Mscale_kron_dist_l.
         reflexivity.
Qed.

 
Lemma scale_tensor_dist_l : forall (n m : nat) (c : C) (A : vecType n) (B : vecType m),
    (c · A) ⊗' B = c · (A ⊗' B).
Proof. intros n m c A B. induction A as [|a].
       - reflexivity.
       - rewrite cons_into_tensor_l. rewrite cons_conc.
         do 2 (rewrite concat_into_scale).
         rewrite concat_into_tensor_l.
         rewrite IHA. rewrite sing_scale_tensor_dist_l.
         reflexivity.
Qed.


(* note that this is slightly different than what we would expect. *)
(* scaling is on right, but singleton is still left list *)
Lemma sing_scale_tensor_dist_r : forall (m n : nat) (c : C) (a : Square n) (B : vecType m),
    [a] ⊗' (c · B) = c · ([a] ⊗' B).
Proof. intros m n c a B. induction B as [| b].
       - reflexivity.
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_tensor_r.
         do 2 (rewrite concat_into_scale).
         rewrite sing_concat_into_tensor_r.
         rewrite IHB.
         rewrite scale_sing.
         do 2 (rewrite tensor_sing).
         rewrite scale_sing.
         rewrite Mscale_kron_dist_r.
         reflexivity.
Qed.

Lemma scale_tensor_dist_r : forall (m n : nat) (c : C) (A : vecType n) (B : vecType m),
    A ⊗' (c · B) = c · (A ⊗' B).
Proof. intros m n c A B. induction A as [|a].
       - reflexivity.
       - rewrite cons_into_tensor_l.
         rewrite (cons_into_tensor_l m n a A B).
         rewrite concat_into_scale.
         rewrite IHA.
         rewrite sing_scale_tensor_dist_r.
         reflexivity.
Qed.



Lemma neg_tensor_dist_l : forall (m n : nat) (A : vecType n) (B : vecType m),
  -A ⊗' B = - (A ⊗' B).
Proof. intros m n A B. unfold neg.
       rewrite scale_tensor_dist_l.
       reflexivity.
Qed.

Lemma neg_tensor_dist_r : forall (m n : nat) (A : vecType n) (B : vecType m),
  A ⊗' -B = - (A ⊗' B).
Proof. intros m n A B. unfold neg.
       rewrite scale_tensor_dist_r.
       reflexivity.
Qed.

Lemma i_tensor_dist_l : forall (m n : nat) (A : vecType n) (B : vecType m),
  i A ⊗' B = i (A ⊗' B).
Proof. intros m n A B. unfold i.
       rewrite scale_tensor_dist_l.
       reflexivity.
Qed.

Lemma i_tensor_dist_r : forall (m n : nat) (A : vecType n) (B : vecType m), 
  A ⊗' i B = i (A ⊗' B).
Proof. intros m n A B. unfold i.
       rewrite scale_tensor_dist_r.
       reflexivity.
Qed.


Hint Rewrite concat_into_tensor_l scale_tensor_dist_r scale_tensor_dist_l  neg_tensor_dist_l neg_tensor_dist_r i_tensor_dist_l i_tensor_dist_r : tensor_db.



(** ** Multiplication & Tensor Laws *)


Lemma mul_tensor_dist_sing : forall (m n : nat) 
  (a : Square m) (b : Square n) (c : Square m) (D : vecType n),
    ([a] ⊗' [b]) *' ([c] ⊗' D) = ([a] *' [c]) ⊗' ([b] *' D).
Proof. intros m n a b c D. induction D as [| d].
       - reflexivity.
       - rewrite (cons_conc _ d D).
         rewrite sing_concat_into_tensor_r, sing_concat_into_mul_r.
         rewrite mul_sing, tensor_sing.
         rewrite sing_concat_into_tensor_r.
         rewrite sing_concat_into_mul_r.
         rewrite <- mul_sing. rewrite <- tensor_sing.
         assert (H: ([a] ⊗' [b]) *' ([c] ⊗' [d]) = [a] *' [c] ⊗' [b] *' [d]).
         { simpl. rewrite kron_mixed_product. reflexivity. }
         rewrite H, IHD.
         reflexivity. 
Qed.         


Lemma mul_tensor_dist_sing2 : forall (m n : nat) 
  (a : Square m) (B : vecType n) (c : Square m) (D : vecType n),
    ([a] ⊗' B) *' ([c] ⊗' D) = ([a] *' [c]) ⊗' (B *' D).
Proof. intros m n a B c D. induction B as [| b].
       - reflexivity.
       - rewrite (cons_conc _ b B).
         rewrite sing_concat_into_tensor_r.
         rewrite concat_into_mul_l.
         rewrite concat_into_mul_l.
         rewrite mul_sing.
         rewrite sing_concat_into_tensor_r.
         rewrite <- mul_sing.
         rewrite IHB, mul_tensor_dist_sing.
         reflexivity.
Qed.

         

Lemma mul_tensor_dist : forall (m n : nat) 
  (A : vecType m) (B : vecType n) (C : vecType m) (D : vecType n),
    Singleton A ->
    Singleton C ->
    (A ⊗' B) *' (C ⊗' D) = (A *' C) ⊗' (B *' D).
Proof. intros m n A B C D. unfold Singleton. intros H1 H2.
       destruct A. destruct H1.
       destruct A.
       - destruct C. destruct H2.
         destruct C. rewrite mul_tensor_dist_sing2.
         reflexivity. 
         destruct H2.
       - destruct H1.
Qed.


Lemma decompose_tensor : forall (A B : vecType 2),
    Singleton A ->
    Singleton B ->
    A ⊗' B = (A ⊗' I) *' (I ⊗' B).
Proof.
  intros.
  rewrite mul_tensor_dist;  auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall (A B : vecType 2),
    Singleton A ->
    Singleton B ->
    (A *' B) ⊗' I = (A ⊗' I) *' (B ⊗' I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall (A B : vecType 2),
    I ⊗' (A *' B) = (I ⊗' A) *' (I ⊗' B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.
  


(* subset lemmas *) 


Definition subset {X : Type} (l1 l2 : list X) :=
  forall (x : X), In x l1 -> In x l2.


(* an alternate version of subset *)
Fixpoint subset' {X : Type} (l1 l2 : list X) :=
  match l1 with
  | [] => True
  | (l :: l1') => In l l2 /\ subset' l1' l2
  end.


Lemma subset_is_subset' : forall (X : Type) (l1 l2 : list X),
    subset' l1 l2 <-> subset l1 l2.
Proof. intros X l1 l2. split.
       - induction l1 as [| l].
         * easy.
         * simpl. intros [H1 H2].
           unfold subset'. intros x. simpl. intros [H3 | H4].
           + rewrite H3 in H1. apply H1.
           + apply IHl1 in H2. unfold subset' in H2. 
             apply H2. apply H4.
       - induction l1 as [| l].
         * easy. 
         * unfold subset'. intros H.
           simpl. split.
           + apply H. simpl. left. reflexivity.
           + apply IHl1. unfold subset'. 
             intros x H'. apply H. simpl. 
             right. apply H'.
Qed.           
           
  
Infix "⊆" := subset (at level 30, no associativity) : heisenberg_scope.


Lemma subset_cons : forall (X : Type) (l1 l2 : list X) (x : X),
  l1 ⊆ l2 -> l1 ⊆ (x :: l2).
Proof. intros X l1 l2 x.
       unfold subset; intros H.
       intros x0 H0.
       simpl; right.
       apply H; apply H0.
Qed.


Lemma subset_concat_l : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l1 ++ l2).
Proof. intros X l1 l2.
       unfold subset; intros x H.
       apply in_or_app.
       left; apply H.
Qed.


Lemma subset_concat_r : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l2 ++ l1).
Proof. intros X l1 l2.
       unfold subset; intros x H.
       apply in_or_app.
       right; apply H.
Qed.


Corollary subset_self : forall (X : Type) (l1 : list X),
  l1 ⊆ l1. 
Proof. intros X l1. assert (H: l1 ⊆ (l1 ++ [])). { apply subset_concat_l. }
       rewrite <- app_nil_end in H. apply H. 
Qed.


Lemma subsets_add : forall (X : Type) (l1 l2 l3 : list X),
  l1 ⊆ l3 -> l2 ⊆ l3 -> (l1 ++ l2) ⊆ l3.
Proof. intros X l1 l2 l3.
       unfold subset; intros H1 H2 x H.
       apply in_app_or in H.
       destruct H as [Hl1 | Hl2].
       - apply H1; apply Hl1.
       - apply H2; apply Hl2.
Qed.


Lemma subset_trans : forall (X : Type) (l1 l2 l3 : list X),
    l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3.
Proof. intros X l1 l2 l3.
       unfold subset; intros H1 H2. 
       intros x H.
       apply H1 in H; apply H2 in H.
       apply H.
Qed.

Hint Resolve subset_concat_l subset_concat_r subset_self subsets_add subset_trans : sub_db.


(** ** Intersection Laws *)

Lemma has_type_subset : forall (n : nat) (v : Vector n) (t1s t2s : vecType n),
  t1s ⊆ t2s -> v :' t2s -> v :' t1s.
Proof. intros n v t1s t2s.
       unfold subset; unfold vecHasType.
       intros H H0 A H1.
       apply H0; apply H; apply H1.
Qed.


(* converges of previous statement. Impossible to prove as long as list is multiset *)
Axiom has_type_subset_conv : forall {n} (t1s t2s : vecType n),
  (forall (v : Vector n), v :' t2s -> v :' t1s) -> t1s ⊆ t2s.


Definition eq_type {X : Type} (T1 T2 : list X) := 
  (T1 ⊆ T2) /\ (T2 ⊆ T1).


Infix "≡" := eq_type (at level 70, no associativity) : heisenberg_scope.

(* will now show this is an equivalence relation *)
Lemma eq_type_refl : forall {n} (A : vecType n), A ≡ A.
Proof. intros n A. split; auto with sub_db. Qed.

Lemma eq_type_sym : forall {n} (A B : vecType n), A ≡ B -> B ≡ A.
Proof.
  intros n A B [H1 H2]. split.
  apply H2. apply H1.
Qed.

Lemma eq_type_trans : forall {n} (A B C : vecType n),
    A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros n A B C [HAB1 HAB2] [HBC1 HBC2].
  split. 
  - apply (subset_trans _ A B C). 
    apply HAB1. apply HBC1.
  - apply (subset_trans _ C B A). 
    apply HBC2. apply HAB2.
Qed.

Add Parametric Relation n : (vecType n) (@eq_type (Square n))
  reflexivity proved by eq_type_refl
  symmetry proved by eq_type_sym
  transitivity proved by eq_type_trans
    as eq_type_rel.



(* converse of this is true as well since matrices are unitary? *)
(* probably hard to prove on coq *) 
Lemma eq_types_same_type : forall (n : nat) (v : Vector n) (T1 T2 : vecType n),
  (T1 ≡ T2) -> (v :' T1 <-> v:' T2).
Proof. intros n v T1 T2. unfold eq_type. intros [H H']. split.
       - intros H1. apply (has_type_subset n v T2 T1). apply H'. apply H1.
       - intros H1. apply (has_type_subset n v T1 T2). apply H. apply H1.
Qed.



(* essentially using functional extensionality to say this is true. *)
(* note that this is not actually true, eg: [I] =\= [I; I] but both clearly have same type *)
Axiom functional_type_equality : forall (n : nat) (T1 T2 : vecType n),
  (forall v, v :' T1 <-> v:' T2) -> T1 = T2.

Corollary eq_types_Eq : forall (n : nat) (T1 T2 : vecType n),
  (T1 ≡ T2) -> T1 = T2.
Proof. intros n T1 T2 H.
       apply functional_type_equality.
       intros v.
       apply eq_types_same_type.
       apply H.
Qed.

(* Basically, we have introduces two notions for vecTypes which we will call "equal".     *)
(* Either, they are subsets of each other which means they are equal up to rearrangements *)
(* and duplicates. We don't care about either of these technicallities, so we will just   *)
(* call them equal (with an axiom). The second notion is that vecTypes are "equal" if     *)
(* they have the same set of eigenvectors. Since, for example, I and -I have the same     *)
(* eigenvectors, we cannot prove functional_type_equality on Coq without making a lot     *)
(* of restirctions, (matrices have to be unitary and must have same eigenvalues, etc...)  *)
(* so we make functional_type_equality an axiom as well                                   *)



Lemma cap_idem : forall (n : nat) (A : vecType n), A ∩ A = A.
Proof. intros n A.
       apply eq_types_Eq.
       split. 
       - auto with sub_db.
       - auto with sub_db.
Qed. 

Lemma cap_comm : forall (n : nat) (A B : vecType n), A ∩ B = B ∩ A.
Proof. intros n A B.
       apply eq_types_Eq.
       split.
       - auto with sub_db.
       - auto with sub_db.
Qed.

Lemma cap_assoc_eq : forall (n : nat) (A B C : vecType n), A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof. intros n A B C. rewrite app_ass. reflexivity.
Qed.


Lemma cap_I_l : forall (A : vecType 2),
  I ∩ A = A.
Proof. intros A.
       apply functional_type_equality.
       intros v; split.
       - apply has_type_subset.
         auto with sub_db.
       - intros H.
         unfold vecHasType; intros A0.
         simpl.
         intros [H1 | H1'].
         + rewrite <- H1.
           unfold singVecType.
           auto with eig_db.
         + apply H; apply H1'.
Qed.

       
Lemma cap_I_r : forall A,
  A ∩ I = A.
Proof. intros.
       rewrite cap_comm.
       rewrite cap_I_l.
       reflexivity. 
Qed.

(* these were origionall for gates, but I provided versions for vectors as well *)
Lemma cap_elim_l : forall {n} (g : Vector n) (A B : vecType n),
  g :' A ∩ B -> g :' A.
Proof. intros n g A B H. 
       apply (has_type_subset _ _ A (A ∩ B)).
       auto with sub_db.
       apply H.
Qed.

Lemma cap_elim_r : forall {n} (g : Vector n) (A B : vecType n),
  g :' A ∩ B -> g :' B.
Proof. intros n g A B H. 
       apply (has_type_subset _ _ B (A ∩ B)).
       auto with sub_db. 
       apply H.
Qed.



(* another important lemma about ∩ *)
Lemma types_add : forall (n : nat) (v : Vector n) (A B : vecType n),
  v :' A -> v :' B -> v :' (A ∩ B).
Proof. intros n v A B.
       unfold vecHasType; intros H1 H2.
       intros A0 H.
       apply in_app_or in H.
       destruct H as [HA | HB].
       - apply H1; apply HA.
       - apply H2; apply HB.
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


(* note that vecHasType_is_vecHasType' makes this nice since       *)
(* vecHasType' works well with singletons as opposed to vecHasType *)
Ltac solveType := apply vecHasType_is_vecHasType'; 
                  simpl; unfold singVecType; auto with eig_db.


Lemma all_hastype_I : forall (v : Vector 2), v :' I.
Proof. intros. solveType. 
Qed.
  
Lemma p_hastype_X : ∣+⟩ :' X. Proof. solveType. Qed. 
Lemma m_hastype_X : ∣-⟩ :' X. Proof. solveType. Qed.
Lemma O_hastype_Z : ∣0⟩ :' Z. Proof. solveType. Qed.
Lemma i_hastype_Z : ∣1⟩ :' Z. Proof. solveType. Qed.

Lemma B_hastype_XX : ∣Φ+⟩ :' X ⊗' X. Proof. solveType. Qed.


Hint Resolve all_hastype_I p_hastype_X m_hastype_X O_hastype_Z i_hastype_Z B_hastype_XX : vht_db.



(***************************)
(* Writing actual programs *)
(***************************)


Notation gateType n := (list (Square n * Square n)).


Definition singGateType {n : nat} (U : Square n) (p : Square n * Square n) : Prop :=
  U × (fst p) = (snd p) × U.


(* as before, two defs of gateHasType that are useful in different areas *)

Definition gateHasType {n : nat} (U : Square n) (ts : gateType n) : Prop := 
  forall (A : Square n * Square n), In A ts -> singGateType U A.

Fixpoint gateHasType' {n : nat} (U : Square n) (ts: gateType n) : Prop := 
  match ts with  
  | [] => True
  | (t :: ts') => (singGateType U t) /\ gateHasType' U ts'
  end.

Lemma gateHasType_is_gateHasType' : forall (n : nat) (U : Square n) (A : gateType n),
  gateHasType U A <-> gateHasType' U A.
Proof. intros n U A. split.
       - induction A as [| h]. 
         * easy. 
         * intros H.  
           simpl. split.
           + unfold gateHasType in H.
             apply H. 
             simpl; left; reflexivity. 
           + apply IHA. 
             unfold gateHasType in H. 
             unfold gateHasType; intros.
             apply H; simpl; right; apply H0.
       - induction A as [| h]. 
         * easy. 
         * intros [H1 H2].
           unfold gateHasType; intros.
           apply IHA in H2. 
           destruct H as [H3 | H4].
           rewrite <- H3; apply H1.
           apply H2; apply H4.
Qed.


(* NOTE!! We use the second def, formGateType', here since it works better with singletons *)
Notation "U :> F" := (gateHasType' U F) (at level 61) : heisenberg_scope.


(* Most of the time, we assume that A is singleton. When A and B are not singleton, *)
(* formGateType A B will actually be more restrictive that A → B or even A zipped with B *)
(* since every possible combination of As and Bs must be satisfies by the gate *) 
(* As stated, we mostly assume A is singleton so these problems don't arrise... *)
Fixpoint formGateType {n : nat} (A B : vecType n) :=
  match A with
  | []  => []  
  | (a :: as') => List.map (fun b => (a,b)) B ++ formGateType as' B
  end.


Notation "A → B" := (formGateType A B) (at level 60, no associativity) : heisenberg_scope. 


Definition gateApp {n : nat} (U A : Square n) : Square n :=
  U × A × U†.

Notation "U [ A ]" := (gateApp U A) (at level 0) : heisenberg_scope. 

  
Lemma type_is_app : forall (n: nat) (U A B : Square n),
  is_unitary U -> (U :> ([A] → [B])  <-> U[A] = B).
Proof. intros n U A B H. split.
       - unfold gateHasType'; unfold gateApp. 
         intros [H'  T]. 
         unfold is_unitary in H; unfold singGateType in H'. 
         simpl in H'; rewrite H'. 
         rewrite Mmult_assoc. 
         rewrite H. 
         rewrite Mmult_1_r'; reflexivity. 
       - unfold gateHasType'; unfold gateApp. 
         intros H'; split. 
         rewrite <- H'; rewrite Mmult_assoc.
         unfold is_unitary in H. 
         apply Minv_flip in H. 
         unfold singGateType; simpl.
         rewrite <- Mmult_assoc. 
         rewrite Mmult_assoc. 
         rewrite H.
         rewrite Mmult_1_r'; reflexivity. 
         simpl; trivial.
Qed.


(* Gate definitions *)

Definition H := hadamard.
Definition S := Phase'.
Definition T := phase_shift (PI / 4).
Definition CNOT :=  cnot.


Definition seq {n : nat} (U1 U2 : Square n) := U2 × U1. 

Infix ";" := seq (at level 52, right associativity).


Lemma Htypes : H :> (Z → X) ∩ (X → Z).
Proof. simpl. unfold singGateType. simpl. split.
       lma'. split. lma'. easy.
Qed.

Lemma STypes : S :> (X → Y) ∩ (Z → Z).
Proof. simpl. unfold singGateType. simpl. split.
       lma'. split. lma'. easy.
Qed.

Lemma CNOTTypes : CNOT :> (X ⊗' I → X ⊗' X) ∩ (I ⊗' X → I ⊗' X) ∩
                          (Z ⊗' I → Z ⊗' I) ∩ (I ⊗' Z → Z ⊗' Z).
Proof. simpl. unfold singGateType. simpl.  
       split. lma'. 
       split. lma'. 
       split. lma'. 
       split. lma'.
       easy.
Qed.


(* T only takes Z → Z *)
Lemma TTypes : T :> (Z → Z).
Proof. simpl. unfold singGateType. simpl. split.
       lma'. easy.
Qed.


(* lemmas about seq*)
Lemma app_comp : forall (n : nat) (U1 U2 A B C : Square n),
  U1[A] = B -> U2[B] = C -> (U2×U1) [A] = C.
Proof. unfold gateApp. intros n U1 U2  A B C H1 H2. rewrite <- H2. rewrite <- H1.
       rewrite Mmult_adjoint. do 3 rewrite <- Mmult_assoc. reflexivity. 
Qed.

Lemma SeqTypes : forall {n} (g1 g2 : Square n) (A B C : vecType n),
    Singleton A -> Singleton B -> Singleton C ->
    g1 :> A → B ->
    g2 :> B → C ->
    g1 ; g2 :> A → C.
Proof. intros n g1 g2 A B C HA HB HC. 
       apply singleton_simplify in HA; destruct HA;
       apply singleton_simplify in HB; destruct HB;
       apply singleton_simplify in HC; destruct HC.
       rewrite H0, H1, H2.
       simpl; unfold singGateType; simpl.
       intros [HAB _] [HBC _].
       assert (H: g2 × (g1 × x) = g2 × (x0 × g1) ).
       { rewrite HAB. reflexivity. }
       do 2 (rewrite <- Mmult_assoc in H).
       rewrite HBC in H.
       rewrite (Mmult_assoc x1 _ _) in H.
       split. 
       unfold seq; rewrite H.
       reflexivity.
       easy.
Qed.
       

Lemma seq_assoc : forall {n} (p1 p2 p3 : Square n) (A : gateType n),
    p1 ; (p2 ; p3) :> A <-> (p1 ; p2) ; p3 :> A.
Proof. intros n p1 p2 p3 A. unfold seq. split.
       - rewrite Mmult_assoc. easy.
       - rewrite Mmult_assoc. easy.
Qed.


Lemma In_eq_Itensor : forall (n : nat),
  n ⨂' I = [Matrix.I (2^n)].
Proof. intros n. assert (H : n ⨂' I = [n ⨂ Matrix.I 2]).
       { induction n as [| n']. 
         - reflexivity.
         - simpl. rewrite IHn'. simpl. reflexivity. }
       rewrite H. rewrite kron_n_I.
       reflexivity.
Qed.


(* Note that this doesn't restrict # of qubits referenced by p. *)
Lemma TypesI1 : forall (p : Square 2), p :> I → I.
Proof. intros p. simpl. unfold singGateType. simpl.
       rewrite Mmult_1_r', Mmult_1_l'. easy.
Qed.

Lemma TypesI2 : forall (p : Square 4), p :> I ⊗' I → I ⊗' I.
Proof. intros p. simpl. unfold singGateType. simpl.
       rewrite id_kron. simpl.
       rewrite Mmult_1_r', Mmult_1_l'. easy.
Qed.


Lemma TypesIn : forall (n : nat) (p : Square (2^n)), p :> n ⨂' I → n ⨂' I.
Proof. intros n p. rewrite In_eq_Itensor. 
       simpl. unfold singGateType. simpl.
       rewrite Mmult_1_r', Mmult_1_l'. easy.
Qed.

Hint Resolve TypesI1 TypesI2 TypesIn : base_types_db.


(* Formal statements of all the transformations listed in figure 1 of Gottesman*)



(*********************)
(** Structural rules *)
(*********************)


(* Subtyping rules *)

(* must prove same lemmas for gateTypes as for vectTypes. *)
(* Could probably find way to get rid of repeated code... *)

Lemma has_type_subset_gate : forall (n : nat) (g : Square n) (t1s t2s : gateType n),
  t1s ⊆ t2s -> g :> t2s -> g :> t1s.
Proof. intros n v t1s t2s H H0. 
       apply gateHasType_is_gateHasType'; unfold gateHasType.
       apply gateHasType_is_gateHasType' in H0; unfold gateHasType in H0.
       intros A H2.
       apply H0. 
       apply H; apply H2.
Qed.
       

(* again, we will show this is an equivalence relation *)
Lemma eq_type_refl_gate : forall {n} (A : gateType n), A ≡ A.
Proof. intros n A. split; auto with sub_db. Qed.

Lemma eq_type_sym_gate : forall {n} (A B : gateType n), A ≡ B -> B ≡ A.
Proof.
  intros n A B [H1 H2]. split.
  apply H2. apply H1.
Qed.

Lemma eq_type_trans_gate : forall {n} (A B C : gateType n),
    A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros n A B C [HAB1 HAB2] [HBC1 HBC2].
  split. 
  - apply (subset_trans _ A B C). 
    apply HAB1. apply HBC1.
  - apply (subset_trans _ C B A). 
    apply HBC2. apply HAB2.
Qed.

Add Parametric Relation n : (gateType n) (@eq_type (Square n * Square n))
  reflexivity proved by eq_type_refl_gate
  symmetry proved by eq_type_sym_gate
  transitivity proved by eq_type_trans_gate
    as eq_type_rel_gate.


(* again, some form of converse is true, but not exactly *) 
Lemma eq_types_are_Eq_gate : forall (n : nat) (g : Square n) (T1 T2 : gateType n),
  (T1 ≡ T2) -> (g :> T1 <-> g :> T2).
Proof. intros n v T1 T2. unfold eq_type. intros [H H']. split.
       - intros H1. apply (has_type_subset_gate n v T2 T1). apply H'. apply H1.
       - intros H1. apply (has_type_subset_gate n v T1 T2). apply H. apply H1.
Qed.



Lemma cap_elim_l_gate : forall {n} (g : Square n) (A B : gateType n),
  g :> A ∩ B -> g :> A.
Proof. intros n g A B H. 
       apply (has_type_subset_gate _ _ A (A ∩ B)).
       auto with sub_db.
       apply H.
Qed.

Lemma cap_elim_r_gate : forall {n} (g : Square n) (A B : gateType n),
  g :> A ∩ B -> g :> B.
Proof. intros n g A B H. 
       apply (has_type_subset_gate _ _ B (A ∩ B)).
       auto with sub_db. 
       apply H.
Qed.

Lemma cap_intro : forall {n} (g : Square n) (A B : gateType n),
  g :> A -> g :> B -> g :> A ∩ B.
Proof. intros n g A B. 
       induction A as [| a].
       - simpl; easy. 
       - simpl; intros [Ha Ha'] Hb; split. 
         * apply Ha.
         * apply IHA. 
           apply Ha'. 
           apply Hb.
Qed.


Lemma cap_arrow : forall {n} (g : Square n) (A B C : vecType n),
  Singleton A ->
  g :> (A → B) ∩ (A → C) ->
  g :> A → (B ∩ C).
Proof. intros n g A B C H. 
       apply singleton_simplify in H.
       destruct H.
       rewrite H0; intros H1.
       apply gateHasType_is_gateHasType'; unfold gateHasType.
       apply gateHasType_is_gateHasType' in H1; unfold gateHasType in H1. 
       intros; apply H1. 
       assert (H' : [x] → (B ∩ C) = ([x] → B) ∩ ([x] → C)).
       { simpl. do 3 (rewrite <- app_nil_end). apply map_app. }
       rewrite <- H'; apply H2.
Qed. 



(* so show arrow_sub, we need this axiom about function subtypes *)
Axiom func_subtype : forall {n} (A A' B B' : vecType n),
  A' ⊆ A -> B ⊆ B' -> (A → B) ⊆ (A' → B').


(* I think impossible to show without showing converse of has_type_subset *)
Lemma arrow_sub : forall {n} (g : Square n) (A A' B B' : vecType n),
  (forall l, l :' A' -> l :' A) ->
  (forall r, r :' B -> r :' B') ->
  g :> A → B ->
  g :> A' → B'.
Proof. intros n g A A' B B' H1 H2.
       apply has_type_subset_conv in H1.
       apply has_type_subset_conv in H2.
       apply has_type_subset_gate.
       apply func_subtype.
       apply H1. apply H2.
Qed.


(* Note that both cap_elim and cap_elim_gate are here. Might want to be more organized... *)
Hint Resolve cap_elim_l cap_elim_r cap_elim_l_gate cap_elim_r_gate cap_intro cap_arrow arrow_sub : subtype_db.


Lemma cap_elim : forall {n} (g : Square n) (A B : gateType n),
  g :> A ∩ B -> g :> A /\ g :> B.
Proof. eauto with subtype_db. Qed.


Lemma cons_into_arrow_l : forall {n} (a : Square n) (A B : vecType n),
    (a :: A) → B = ([a] → B) ∩ (A → B). 
Proof. intros n a A B. simpl.
       rewrite <- app_nil_end.
       reflexivity.
Qed.       


Lemma strong_cap_arrow : forall {n} (g : Square n) (A B C : vecType n),
  g :> (A → B) ∩ (A → C) ->
  g :> A → (B ∩ C).
Proof. intros. induction A as [| h].
       - easy.
       - apply cap_elim in H0.
         destruct H0 as [HA HB].
         rewrite cons_into_arrow_l in HA;
         rewrite cons_into_arrow_l in HB;
         rewrite cons_into_arrow_l.
         apply cap_elim in HA; destruct HA as [HA1 HA2];
         apply cap_elim in HB; destruct HB as [HB1 HB2].
         apply cap_intro.
         apply cap_arrow. easy.         
         eauto with subtype_db.
         apply IHA.
         eauto with subtype_db.
Qed.

Hint Resolve cap_elim strong_cap_arrow : subtype_db.

(* this is killed by eauto with subtype_db *)
Lemma cap_arrow_distributes : forall {n} (g : Square n) (A A' B B' : vecType n),
  g :> (A → A') ∩ (B → B') ->
  g :> (A ∩ B) → (A' ∩ B').
Proof.
  intros; apply strong_cap_arrow.
  apply cap_intro; eauto with subtype_db.
Qed.

(* my own proof, using func_subtype as workaround for arrow_sub *)
Lemma cap_arrow_distributes' : forall {n} (g : Square n) (A A' B B' : vecType n),
  g :> (A → A') ∩ (B → B') ->
  g :> (A ∩ B) → (A' ∩ B').
intros.
  apply cap_elim in H0 as [TA TB].
  apply strong_cap_arrow.
  apply cap_intro.
  - assert (H1 : ((A ∩ B) → A') ⊆ (A → A')).
    { apply func_subtype; 
      auto with sub_db. }
    apply (has_type_subset_gate _ _ _ (A → A')).
    apply H1. 
    apply TA.
  - assert (H2 : ((A ∩ B) → B') ⊆ (B → B')).
    { apply func_subtype; 
      auto with sub_db. }
    apply (has_type_subset_gate _ _ _ (B → B')).
    apply H2. 
    apply TB.
Qed.


(* "Full explicit proof", as in Programs.v *)
Lemma cap_arrow_distributes'' : forall {n} (g : Square n) (A A' B B' : vecType n),
  g :> (A → A') ∩ (B → B') ->
  g :> (A ∩ B) → (A' ∩ B').
Proof.
  intros.
  apply strong_cap_arrow.
  apply cap_intro.
  - eapply arrow_sub; intros.
    + eapply cap_elim_l. apply H1.
    + apply H1.
    + eapply cap_elim_l_gate. apply H0.
  - eapply arrow_sub; intros.
    + eapply cap_elim_r. apply H1.
    + apply H1.
    + eapply cap_elim_r_gate. apply H0.
Qed.



(** Typing Rules for Tensors *)

Notation s := Datatypes.S.


Local Open Scope nat_scope.


Definition testKron (g : Square 2) (n : nat) : Square (2*n) := 
  (g ⊗ Matrix.I n).

Lemma testKron' : forall (n m : nat) (g x : Square (2*n)) (x1 : Square m),
  (g ⊗ Matrix.I m) × (x ⊗ x1) = (g × x) ⊗ (Matrix.I m × x1). 
Proof. intros. rewrite kron_mixed_product. reflexivity.
Qed.

Lemma testKron2 : forall (n : nat) (g : Square 2),
  exists (A : Square (2*n)), A = (g ⊗ Matrix.I n).
Proof. intros. exists (g ⊗ Matrix.I n). reflexivity.
Qed.


Lemma tensor_base : forall {n m} (g : Square 2) (A A' : vecType (2 * n)) (E : vecType m),
    Singleton A -> Singleton A' -> Singleton E ->
    (testKron g n) :> (A → A') ->
    (g ⊗ Matrix.I (n * m)) :>  A ⊗' E → A' ⊗' E.
Proof. intros.
       apply singleton_simplify in H0; destruct H0;
       apply singleton_simplify in H1; destruct H1;
       apply singleton_simplify in H2; destruct H2.
       rewrite H0, H1 in H3; simpl in H3; 
       destruct H3 as [H3 _]; 
       unfold singGateType in H3; 
       simpl in H3.
       rewrite H0, H1, H2; simpl;
       unfold singGateType; split; simpl.
       rewrite <- id_kron. 
       rewrite <- kron_assoc. 
       assert (H: exists (A : Square (2*n)), A = (g ⊗ Matrix.I n)).
       { intros. exists (g ⊗ Matrix.I n). reflexivity. }
       destruct H. rewrite <- H4.
       rewrite (testKron' n m x2 x x1) .


  

g ⊗ Matrix.I n ⊗ Matrix.I m × (x ⊗ x1) = x0 ⊗ x1 × (g ⊗ Matrix.I n ⊗ Matrix.I m)


Axiom tensor_inc : forall g n E A A',
    Singleton E ->
    g n :: (A → A') ->
    g (s n) ::  E ⊗ A → E ⊗ A'.

Axiom tensor_base2 : forall g E A A' B B',
    Singleton A ->
    Singleton B ->
    g 0 1 :: (A ⊗ B → A' ⊗ B') ->
    g 0 1 :: (A ⊗ B ⊗ E → A' ⊗ B' ⊗ E).

Axiom tensor_base2_inv : forall g E A A' B B',
    Singleton A ->
    Singleton B ->
    g 0 1 :: (B ⊗ A → B' ⊗ A') ->
    g 1 0 :: (A ⊗ B ⊗ E → A' ⊗ B' ⊗ E).

Axiom tensor_inc2 : forall (g : nat -> nat -> prog) m n E A A' B B',
    Singleton E ->
    g m n :: (A ⊗ B → A' ⊗ B') ->
    g (s m) (s n) ::  E ⊗ A ⊗ B → E ⊗ A' ⊗ B'.

Axiom tensor_inc_l : forall (g : nat -> nat -> prog) m E A A' B B',
    Singleton A ->
    Singleton E ->
    g m 0 :: (A ⊗ B → A' ⊗ B') ->
    g (s m) 0 ::  A ⊗ E ⊗ B → A' ⊗ E ⊗ B'.

Axiom tensor_inc_r : forall (g : nat -> nat -> prog) n E A A' B B',
    Singleton A ->
    Singleton E ->
    g 0 n :: (A ⊗ B → A' ⊗ B') ->
    g 0 (s n) ::  A ⊗ E ⊗ B → A' ⊗ E ⊗ B'.

(* For flipping CNOTs. Could have CNOT specific rule. *)
Axiom tensor2_comm : forall (g : nat -> nat -> prog) A A' B B',
    Singleton A ->
    Singleton B ->
    g 0 1 :: A ⊗ B → A' ⊗ B' ->
    g 1 0 :: B ⊗ A → B' ⊗ A'.




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
    U :> [A] → [B] -> v :' [A] -> (U × v) :' [B].
Proof. intros n U A B v ty H. 
       apply vecHasType_is_vecHasType'; simpl; split.
       apply vecHasType_is_vecHasType' in H; simpl in H. 
       destruct H as [H _]; unfold singVecType in H. 
       destruct H as [λ Eig].
       simpl in ty;
       unfold singGateType in ty; 
       simpl in ty; destruct ty as [ty _].
       unfold singVecType.
       unfold Eigenstate; exists λ.
       rewrite <- Mmult_assoc. rewrite <- ty.
       rewrite Mmult_assoc. 
       rewrite Eig.  
       rewrite Mscale_mult_dist_r.
       reflexivity.
       easy.
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
