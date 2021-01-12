Require Import Psatz. 
Require Import String. 
Require Import Program.
Require Import List.
Require Import Setoid.

Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.



(* Some helpers *)

Lemma kill_false : forall P : Prop,
  P \/ False <-> P.
Proof. split. intros [H | F]. easy. easy.
       intros. left. easy.
Qed.

Lemma kill_true : forall P : Prop,
  P /\ True <-> P.
Proof. split. intros [H _]. easy.
       intros. split. easy. easy.
Qed.

Lemma in_simplify : forall {X} (x x1 : X),
  In x1 [x] -> x1 = x.
Proof. intros. simpl in H. 
       apply (kill_false (x = x1)) in H.
       easy.
Qed.

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



Hint Resolve WF_Xn WF_Zn : wf_db.



(****************************)
(* Proving some indentities *)
(****************************)


Lemma XtimesXid : σx × σx = I 2. Proof. lma'. Qed.      
Lemma YtimesYid : σy × σy = I 2. Proof. lma'. Qed.
Lemma ZtimesZid : σz × σz = I 2. Proof. lma'. Qed.
Lemma Y_eq_iXZ : σy = Ci .* σx × σz. Proof. lma'. Qed.
Lemma ZH_eq_HX : σz × hadamard = hadamard × σx. Proof. lma'. Qed.
Lemma PX_eq_YP : Phase × σx = σy × Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma HtimesHid : hadamard × hadamard = I 2. Proof. lma'; Hhelper. Qed.
Lemma H_eq_Hadjoint : hadamard = hadamard†. Proof. lma'. Qed.
Lemma XH_eq_HZ : σx × hadamard = hadamard × σz. Proof. lma'. Qed.





(**************************************)
(* defining Heisenberg representation *)
(**************************************)


Declare Scope heisenberg_scope.
Delimit Scope heisenberg_scope with H.
Open Scope heisenberg_scope.


Definition Eigenstate {n} (U : Square n) (v : Vector n) : Prop :=
  exists λ, Eigenpair U (v, λ). 



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



Definition scale {n : nat} (c : C) (A : vecType n) := 
  List.map (fun a => c .* a) A. 


Definition i {n : nat} (A : vecType n) :=
  scale Ci A.

Definition neg {n : nat} (A : vecType n) :=
  scale (-1) A.

(* tensor similar to mul *)
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
Infix "⊗'" := tensor (at level 51, right associativity) : heisenberg_scope. 
Infix "·" := scale (at level 45, left associativity) : heisenberg_scope. 
Notation "n ⨂' A" := (tensor_n n A) (at level 30, no associativity) : heisenberg_scope.

(*****************************************************)
(* helper lemmas to extract from mult, tensor, scale *)
(*****************************************************)


Lemma in_mult : forall {n} (p : Square n) (A B : vecType n),
  In p (A *' B) -> exists a b, In a A /\ In b B /\ p = a × b.
Proof. intros. induction A as [| h].
       - simpl in H. easy.
       - simpl in H.
         apply in_app_or in H; destruct H as [H | H].
         * apply in_map_iff in H. destruct H.
           exists h, x. split.
           simpl. left. easy. destruct H as [H H']. 
           split. apply H'. rewrite H; reflexivity.
         * apply IHA in H. do 2 (destruct H). 
           exists x, x0. 
           destruct H as [H1 H2].
           split. simpl. right; apply H1.
           apply H2.
Qed.


Lemma in_tensor : forall {n m} (p : Square (n*m)) (A : vecType n) (B : vecType m),
  In p (A ⊗' B) -> exists a b, In a A /\ In b B /\ p = a ⊗ b.
Proof. intros. induction A as [| h].
       - simpl in H. easy.
       - simpl in H.
         apply in_app_or in H; destruct H as [H | H].
         * apply in_map_iff in H. destruct H.
           exists h, x. split.
           simpl. left. easy. destruct H as [H H']. 
           split. apply H'. rewrite H; reflexivity.
         * apply IHA in H. do 2 (destruct H). 
           exists x, x0. 
           destruct H as [H1 H2].
           split. simpl. right; apply H1.
           apply H2.
Qed.


Lemma in_scale : forall {n} (p : Square n) (c : C) (A : vecType n),
  In p (c · A) -> exists a, In a A /\ p = c .* a.
Proof. intros. induction A as [| h].
       - simpl in H. easy.
       - simpl in H.
         destruct H as [H | H].
         * exists h. split.
           left. easy.
           rewrite H. reflexivity.
         * apply IHA in H. do 2 (destruct H). 
           exists x. split.
           right. apply H.
           apply H0. 
Qed.


Lemma in_scale_rev : forall {n} (p : Square n) (c : C) (A : vecType n),
  In p A -> In (c .* p) (c · A).
Proof. intros. induction A as [| h].
       - simpl in H. easy.
       - simpl in H.
         destruct H as [H0 | H0].
         * left. rewrite H0. reflexivity.
         * right. apply IHA. apply H0.
Qed.

(******************)
(* Singleton laws *)
(******************)

Definition X' : vecType 2 := [σx].
Definition Z' : vecType 2 := [σz].
Definition I' : vecType 2 := [I 2].

Definition I_n (n : nat) : vecType n := [I n].


Lemma SI : Singleton I'. Proof. easy. Qed.
Lemma SX : Singleton X'. Proof. easy. Qed.
Lemma SZ : Singleton Z'. Proof. easy. Qed.
Lemma SI_n : forall (n : nat), Singleton (I_n n). Proof. easy. Qed.

Lemma S_neg : forall (n : nat) (A : vecType n), Singleton A -> Singleton (neg A).
Proof. intros n A H. 
       apply singleton_simplify in H.
       destruct H; rewrite H.
       easy.
Qed.

Lemma S_i : forall (n : nat) (A : vecType n), Singleton A -> Singleton (i A).
Proof. intros n A H.
       apply singleton_simplify in H.
       destruct H; rewrite H.
       easy.
Qed.

Lemma S_mul : forall (n : nat) (A B : vecType n), 
  Singleton A -> Singleton B -> Singleton (A *' B).
Proof. intros n A B HA HB.
       apply singleton_simplify in HA;
       apply singleton_simplify in HB;
       destruct HA; destruct HB; rewrite H, H0. 
       easy.
Qed. 

Hint Resolve SI SX SZ SI_n S_neg S_i S_mul : sing_db.

Notation Y' := (i (X' *' Z')).

Lemma SY : Singleton Y'.
Proof. auto with sing_db. Qed.

(****************)
(* Unitary laws *)
(****************)


Definition uni_vecType {n : nat} (vt : vecType n) : Prop :=
  forall A, In A vt -> unitary A.


Lemma univ_I : uni_vecType I'. 
Proof. unfold uni_vecType. intros. 
       apply in_simplify in H; rewrite H. 
       auto with unit_db.
Qed.

Lemma univ_X : uni_vecType X'.
Proof. unfold uni_vecType. intros. 
       apply in_simplify in H; rewrite H. 
       auto with unit_db.
Qed.


Lemma univ_Z : uni_vecType Z'. 
Proof. unfold uni_vecType. intros. 
       apply in_simplify in H; rewrite H. 
       auto with unit_db.
Qed.

Lemma univ_I_n : forall (n : nat), uni_vecType (I_n n). 
Proof. unfold uni_vecType. intros. 
       apply in_simplify in H; rewrite H. 
       auto with unit_db.
Qed.

Lemma univ_neg : forall (n : nat) (A : vecType n), uni_vecType A -> uni_vecType (neg A).
Proof. unfold uni_vecType in *.
       intros n A H a H1. unfold neg in H1.
       apply in_scale in H1. destruct H1 as [x [H1 H2]].
       apply H in H1. rewrite H2. unfold unitary.
       rewrite Mscale_adj.
       distribute_scale. rewrite H1.
       lma. 
Qed.

Lemma univ_i : forall (n : nat) (A : vecType n), uni_vecType A -> uni_vecType (i A).
Proof. unfold uni_vecType in *.
       intros n A H a H1. unfold i in H1.
       apply in_scale in H1. destruct H1 as [x [H1 H2]].
       apply H in H1. rewrite H2. unfold unitary.
       rewrite Mscale_adj.
       distribute_scale. rewrite H1.
       lma. 
Qed.


Lemma univ_mul : forall (n : nat) (A B : vecType n), 
  uni_vecType A -> uni_vecType B -> uni_vecType (A *' B).
Proof. unfold uni_vecType in *.
       intros n A B HA HB ab Hab.
       apply in_mult in Hab.
       destruct Hab as [a [b [Ha [Hb Hab]]]].
       rewrite Hab.
       auto with unit_db.
Qed.


Lemma univ_tensor : forall (n m : nat) (A : vecType n) (B : vecType m),
  uni_vecType A -> uni_vecType B -> uni_vecType (A ⊗' B).
Proof. unfold uni_vecType in *.
       intros n m A B HA HB ab Hab.
       apply in_tensor in Hab.
       destruct Hab as [a [b [Ha [Hb Hab]]]].
       rewrite Hab.
       auto with unit_db.
Qed.

Hint Resolve univ_I univ_X univ_Z univ_I_n univ_neg univ_i univ_mul univ_tensor : univ_db.


Lemma univ_Y : uni_vecType Y'.
Proof. auto with univ_db. Qed.

(***********************)
(* Multiplication laws *)
(***********************)

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

Lemma mul_I_l : forall (A : vecType 2), I' *' A = A.
Proof. intros A. unfold I'. induction A as [| a].
       - reflexivity.
       - rewrite (cons_conc _ a A). 
         rewrite sing_concat_into_mul_r.
         rewrite IHA.
         simpl.
         rewrite Mmult_1_l'.
         reflexivity.
Qed.

Lemma mul_I_r : forall (A : vecType 2), A *' I' = A.
Proof. intros A. unfold I'. induction A as [| a].
       - reflexivity.
       - rewrite cons_into_mul_l.
         rewrite IHA.
         simpl.
         rewrite Mmult_1_r'.
         reflexivity.
Qed.
  
Lemma Xsqr : X' *' X' = I'.
Proof. simpl. unfold I. rewrite XtimesXid. reflexivity.
Qed.

Lemma Zsqr : Z' *' Z' = I'.
Proof. simpl. unfold I. rewrite ZtimesZid. reflexivity.
Qed.

Lemma ZmulX : Z' *' X' = - (X' *' Z').
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
Proof. intros n c A B. 
       unfold scale. 
       rewrite map_app.
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





(***************)
(* Tensor Laws *)
(***************)


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
    ([a] ⊗' [b]) ⊗' C = [a] ⊗' ([b] ⊗' C). 
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
    ([a] ⊗' B) ⊗' C = [a] ⊗' (B ⊗' C). 
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


(********************************)
(* Multiplication & Tensor Laws *)
(********************************)

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
Proof. intros m n A B C D H1 H2. 
       apply singleton_simplify in H1; destruct H1;
       apply singleton_simplify in H2; destruct H2.
       rewrite H, H0. 
       rewrite mul_tensor_dist_sing2.
       reflexivity. 
Qed.


Lemma decompose_tensor : forall (A B : vecType 2),
    Singleton A ->
    Singleton B ->
    A ⊗' B = (A ⊗' I') *' (I' ⊗' B).
Proof.
  intros.
  rewrite mul_tensor_dist;  auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall (A B : vecType 2),
    Singleton A ->
    Singleton B ->
    (A *' B) ⊗' I' = (A ⊗' I') *' (B ⊗' I').
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall (A B : vecType 2),
    I' ⊗' (A *' B) = (I' ⊗' A) *' (I' ⊗' B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.


(**********************)
(* Subset definitions *)
(**********************)

Infix "⊆" := subset_gen (at level 30, no associativity).


(*********************)
(* Intersection Laws *)
(*********************)


Lemma has_type_subset : forall (n : nat) (v : Vector n) (t1s t2s : vecType n),
  (t1s ⊆ t2s) -> v :' t2s -> v :' t1s.
Proof. intros n v t1s t2s.
       unfold subset_gen; unfold vecHasType.
       intros H H0 A H1.
       apply H0; apply H; apply H1.
Qed.

(* 
(* converges of previous statement. Impossible to prove as long as list is multiset *)
Axiom has_type_subset_conv : forall {n} (t1s t2s : vecType n),
  (forall (v : Vector n), v :' t2s -> v :' t1s) -> t1s ⊆ t2s.
*)

Definition eq_vecType {n} (T1 T2 : vecType n) := 
  (forall v, v :' T1 <-> v :' T2).


Infix "≡" := eq_vecType (at level 70, no associativity) : heisenberg_scope.

(* will now show this is an equivalence relation *)
Lemma eq_vecType_refl : forall {n} (A : vecType n), A ≡ A.
Proof. intros n A. 
       unfold eq_vecType. easy.
Qed.

Lemma eq_vecType_sym : forall {n} (A B : vecType n), A ≡ B -> B ≡ A.
Proof. intros n A B H. 
       unfold eq_vecType in *; intros v.
       split. apply H. apply H.
Qed.

Lemma eq_vecType_trans : forall {n} (A B C : vecType n),
    A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros n A B C HAB HBC.
  unfold eq_vecType in *.
  split. 
  - intros. apply HBC; apply HAB; apply H.
  - intros. apply HAB; apply HBC; apply H.
Qed.


Add Parametric Relation n : (vecType n) (@eq_vecType n)
  reflexivity proved by eq_vecType_refl
  symmetry proved by eq_vecType_sym
  transitivity proved by eq_vecType_trans
    as eq_vecType_rel.



(* converse of this is true as well since matrices are unitary? *)
(* probably hard to prove on coq *) 
Lemma eq_types_same_type : forall (n : nat) (T1 T2 : vecType n),
  (T1 ⊆ T2 /\ T2 ⊆ T1) -> T1 ≡ T2.
Proof. intros n T1 T2 [S12 S21]. 
       unfold eq_vecType. 
       intros v; split.
       - apply has_type_subset. apply S21.
       - apply has_type_subset. apply S12. 
Qed.




Lemma cap_idem : forall (n : nat) (A : vecType n), A ∩ A ≡ A.
Proof. intros n A.
       apply eq_types_same_type.
       split. 
       - auto with sub_db.
       - auto with sub_db.
Qed. 

Lemma cap_comm : forall (n : nat) (A B : vecType n), A ∩ B ≡ B ∩ A.
Proof. intros n A B.
       apply eq_types_same_type.
       split.
       - auto with sub_db.
       - auto with sub_db.
Qed.

Lemma cap_assoc_eq : forall (n : nat) (A B C : vecType n), A ∩ (B ∩ C) = (A ∩ B) ∩ C.
Proof. intros n A B C. rewrite app_ass. reflexivity.
Qed.



Lemma cap_I_l : forall {n} (A : vecType n),
  (I_n n) ∩ A ≡ A.
Proof. intros n A.
       unfold eq_vecType.
       intros v; split.
       - apply has_type_subset.
         auto with sub_db.
       - intros H.
         unfold vecHasType; intros A0.
         simpl.
         intros [H1 | H1'].
         + rewrite <- H1.
           unfold singVecType.
           exists C1.
           auto with eig_db.
         + apply H; apply H1'.
Qed.

       
Lemma cap_I_r : forall {n} A,
  A ∩ (I_n n) ≡ A.
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
      try rewrite <- (mul_assoc _ X' Z' _);
      autorewrite with mul_db tensor_db;
      try rewrite mul_assoc).

Lemma Ysqr : Y' *' Y' = I'. Proof. normalize_mul; auto with sing_db. Qed.
Lemma XmulZ : X' *' Z' = - Z' *' X'. Proof. normalize_mul; auto with sing_db. Qed.
Lemma XmulY : X' *' Y' = i Z'. Proof. normalize_mul; auto with sing_db. Qed.
Lemma YmulX : Y' *' X' = -i Z'. Proof. normalize_mul; auto with sing_db. Qed.
Lemma ZmulY : Z' *' Y' = -i X'. Proof. normalize_mul; auto with sing_db. Qed.
Lemma YmulZ : Y' *' Z' = i X'. Proof. normalize_mul; auto with sing_db. Qed.


(* some more lemmas about specific vectors *)


(* note that vecHasType_is_vecHasType' makes this nice since       *)
(* vecHasType' works well with singletons as opposed to vecHasType *)
Ltac solveType := apply vecHasType_is_vecHasType'; 
                  simpl; unfold singVecType; apply kill_true;
                  try (exists C1; auto with eig_db; easy);
                  try (exists (Copp C1); auto with eig_db).

Lemma all_hastype_I : forall (v : Vector 2), v :' I'.
Proof. intros. solveType. 
Qed.
  
Lemma p_hastype_X : ∣+⟩ :' X'. Proof. solveType. Qed. 
Lemma m_hastype_X : ∣-⟩ :' X'. Proof. solveType. Qed.
Lemma O_hastype_Z : ∣0⟩ :' Z'. Proof. solveType. Qed.
Lemma i_hastype_Z : ∣1⟩ :' Z'. Proof. solveType. Qed.

Lemma B_hastype_XX : ∣Φ+⟩ :' X' ⊗' X'. Proof. solveType. Qed.


Hint Resolve all_hastype_I p_hastype_X m_hastype_X O_hastype_Z i_hastype_Z B_hastype_XX : vht_db.

(**************************************************************)
(* Defining pairHasType, which is a helper function for later *)
(**************************************************************)
 
Definition pairHasType {n : nat} (p : Vector n * C) (ts: vecType n) : Prop := 
  forall (A : Square n), In A ts -> Eigenpair A p.


Lemma has_type_subset_pair : forall (n : nat) (p : Vector n * C) (t1s t2s : vecType n),
  (t1s ⊆ t2s) -> pairHasType p t2s -> pairHasType p t1s.
Proof. intros n p t1s t2s.
       unfold subset_gen; unfold pairHasType.
       intros H H0 A H1.
       apply H0; apply H; apply H1.
Qed.


Lemma cap_elim_l_pair : forall {n} (g : Vector n * C) (A B : vecType n),
  pairHasType g (A ∩ B) -> pairHasType g A.
Proof. intros n g A B H. 
       apply (has_type_subset_pair _ _ A (A ∩ B)).
       auto with sub_db.
       apply H.
Qed.

Lemma cap_elim_r_pair : forall {n} (g : Vector n * C) (A B : vecType n),
  pairHasType g (A ∩ B) -> pairHasType g B.
Proof. intros n g A B H. 
       apply (has_type_subset_pair _ _ B (A ∩ B)).
       auto with sub_db. 
       apply H.
Qed.


(***************************)
(* Writing actual programs *)
(***************************)

Notation gateType n := (list (vecType n * vecType n)).



Definition singGateType {n : nat} (U : Square n) (p : vecType n * vecType n) : Prop :=
  forall (A B : Square n), In A (fst p) -> In B (snd p) -> U × A = B × U.

(* alternate, less powerful but more accurate definition *)
(* U : A -> B => U sends eigs of A to eigs of B *)
Definition singGateType' {n : nat} (U : Square n) (p : vecType n * vecType n) : Prop :=
  forall v c, pairHasType (v, c) (fst p) -> pairHasType (U × v, c) (snd p). 

Lemma sgt_implies_sgt' : forall {n} (U : Square n) (g : vecType n * vecType n),
  fst g <> [] -> singGateType U g -> singGateType' U g.
Proof. intros. 
       unfold singGateType in H0. 
       unfold singGateType'. intros v c Ha B Hb.   
       unfold Eigenpair; simpl.
       destruct (fst g) as [| A].
       - easy.
       - assert (H1 : U × A = B × U).
       { apply H0. left. easy. apply Hb. }
       rewrite <- Mmult_assoc.
       rewrite <- H1.
       rewrite Mmult_assoc.
       unfold pairHasType in Ha. 
       unfold Eigenpair in Ha. simpl in Ha.
       assert (H'' : A × v = c .* v).
       { apply Ha. left. easy. }
       rewrite H''.
       rewrite Mscale_mult_dist_r.
       reflexivity.
Qed.


Lemma sgt'_implies_sgt : forall {n} (U : Square n) (g : vecType n * vecType n),
  unitary U -> Singleton (fst g) -> (uni_vecType (fst g) /\ uni_vecType (snd g)) ->
  singGateType' U g -> singGateType U g.
Proof. intros n U g H H0 [Hf Hs] H1. 
       apply singleton_simplify in H0; destruct H0.
       unfold singGateType' in H1. 
       unfold singGateType. intros A B HA HB.  
       unfold uni_vecType in *.
       assert (H': eq_eigs A (U† × B × U)).
       { intros p H2. destruct p.
         apply eig_unit_conv. apply H.
         unfold pairHasType in H1.
         rewrite H0 in *.
         apply (H1 m c). 
         intros. 
         apply in_simplify in H3. 
         apply in_simplify in HA. 
         rewrite H3; rewrite <- HA.
         apply H2.
         apply HB. }
       apply eq_eigs_implies_eq in H'.
       rewrite H'.
       do 2 (rewrite <- Mmult_assoc).
       rewrite H.
       rewrite Mmult_1_l'.
       reflexivity.
       apply Hf. apply HA.
       apply unit_mult. apply unit_mult. 
       apply unit_adjoint. apply H.
       apply Hs. apply HB.
       apply H.
Qed.




(* as before, two defs of gateHasType that are useful in different areas *)
Definition gateHasType {n : nat} (U : Square n) (ts : gateType n) : Prop := 
  forall (A : vecType n * vecType n), In A ts -> singGateType' U A.

Fixpoint gateHasType' {n : nat} (U : Square n) (ts: gateType n) : Prop := 
  match ts with  
  | [] => True
  | (t :: ts') => (singGateType' U t) /\ gateHasType' U ts'
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

(* takes two vecTypes and makes gateType *)
Definition formGateType {n : nat} (A B : vecType n) : gateType n := [(A, B)].

Definition gateApp {n : nat} (U A : Square n) : Square n :=
  U × A × U†.

(* NOTE!! We use the second def, formGateType', here since it works better with singletons *)
Notation "U ::' F" := (gateHasType' U F) (at level 61) : heisenberg_scope.
Notation "A → B" := (formGateType A B) (at level 60, no associativity) : heisenberg_scope. 
Notation "U [ A ]" := (gateApp U A) (at level 0) : heisenberg_scope. 


Lemma type_is_app : forall (n: nat) (U A B : Square n),
  unitary U -> unitary A -> unitary B ->
  (U ::' ([A] → [B])  <-> U[A] = B).
Proof. intros n U A B Hu Ha Hb. split.
       - simpl. intros [H _]. 
         apply sgt'_implies_sgt in H.
         unfold singGateType in H; unfold gateApp. 
         simpl in H. rewrite (H A B). 
         rewrite Mmult_assoc.
         rewrite Hu. apply Mmult_1_r'.
         left. easy. left. easy.
         apply Hu.
         easy.
         unfold uni_vecType.
         simpl. split.
         + intros A' [Ha' | F].
           rewrite <- Ha'; apply Ha. easy.
         + intros B' [Hb' | F].
           rewrite <- Hb'; apply Hb. easy.
       - intros. apply kill_true. 
         apply sgt_implies_sgt'.
         easy.
         unfold singGateType; unfold gateApp in H.
         intros. 
         apply in_simplify in H0. 
         apply in_simplify in H1.
         rewrite H0, H1.
         rewrite <- H.
         rewrite Mmult_assoc.
         apply Minv_flip in Hu.
         rewrite Hu.
         rewrite Mmult_assoc. 
         rewrite Mmult_1_r'; reflexivity. 
Qed.


(* Gate definitions *)

Definition H := hadamard.
Definition S := Phase'.
Definition T := phase_shift (PI / 4).
Definition CNOT :=  cnot.


Definition seq {n : nat} (U1 U2 : Square n) := U2 × U1. 

Infix ";" := seq (at level 52, right associativity).


Lemma singleton_simplify2 : forall {n} (U A B : Square n),
  singGateType U ([A], [B]) <-> U × A = B × U.
Proof. intros. 
       unfold singGateType. split.
       - intros. apply (H0 A B). 
         simpl. left. easy.
         simpl. left. easy. 
       - intros. simpl in *.
         destruct H1 as [H | F].
         destruct H2 as [H' | F'].
         rewrite <- H, <- H'; apply H0.
         easy. easy.
Qed.       


(* lemmas about seq*)
Lemma app_comp : forall (n : nat) (U1 U2 A B C : Square n),
  U1[A] = B -> U2[B] = C -> (U2×U1) [A] = C.
Proof. unfold gateApp. intros n U1 U2 A B C H1 H2. rewrite <- H2. rewrite <- H1.
       rewrite Mmult_adjoint. do 3 rewrite <- Mmult_assoc. reflexivity. 
Qed.

Lemma SeqTypes : forall {n} (g1 g2 : Square n) (A B C : vecType n),
    g1 ::' A → B ->
    g2 ::' B → C ->
    g1 ; g2 ::' A → C.
Proof. intros n g1 g2 A B C. 
       simpl. intros [HAB _] [HBC _].
       apply kill_true.
       unfold singGateType'; simpl; intros.
       unfold seq. rewrite (Mmult_assoc g2 g1 v).
       unfold singGateType' in *; simpl in *.
       apply HBC.
       apply HAB.
       apply H0.
Qed.
       

Lemma seq_assoc : forall {n} (p1 p2 p3 : Square n) (A : gateType n),
    p1 ; (p2 ; p3) ::' A <-> (p1 ; p2) ; p3 ::' A.
Proof. intros n p1 p2 p3 A. unfold seq. split.
       - rewrite Mmult_assoc. easy.
       - rewrite Mmult_assoc. easy.
Qed.


Lemma In_eq_Itensor : forall (n : nat),
  n ⨂' I' = [I (2^n)].
Proof. intros n. assert (H : n ⨂' I' = [n ⨂ I 2]).
       { induction n as [| n']. 
         - reflexivity.
         - simpl. rewrite IHn'. simpl. reflexivity. }
       rewrite H. rewrite kron_n_I.
       reflexivity.
Qed.


Lemma Types_I : forall {n} (p : Square n), p ::' [I n] → [I n].
Proof. intros. 
       apply kill_true.
       apply sgt_implies_sgt'.
       easy.
       unfold singGateType. 
       intros.
       apply in_simplify in H0. 
       apply in_simplify in H1.
       rewrite H0, H1.
       rewrite Mmult_1_r', Mmult_1_l'.
       reflexivity.
Qed.

(* Note that this doesn't restrict # of qubits referenced by p. *)
Lemma TypesI1 : forall (p : Square 2), p ::' I' → I'.
Proof. intros p. unfold I'. 
       apply Types_I.
Qed.


Lemma TypesI2 : forall (p : Square 4), p ::' I' ⊗' I' → I' ⊗' I'.
Proof. intros p.
       assert (H: I' ⊗' I' = [I 4]).
       { simpl. rewrite id_kron. easy. }
       rewrite H.
       apply Types_I.
Qed.


Lemma TypesIn : forall (n : nat) (p : Square (2^n)), p ::' n ⨂' I' → n ⨂' I'.
Proof. intros n p. rewrite In_eq_Itensor. 
       apply (@Types_I (2^n) p).
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
  t1s ⊆ t2s -> g ::' t2s -> g ::' t1s.
Proof. intros n v t1s t2s H H0. 
       apply gateHasType_is_gateHasType'; unfold gateHasType.
       apply gateHasType_is_gateHasType' in H0; unfold gateHasType in H0.
       intros A H2.
       apply H0. 
       apply H; apply H2.
Qed.
       

Definition eq_gateType {n} (T1 T2 : gateType n) := 
  (forall v, v ::' T1 <-> v ::' T2).


Infix "≡≡" := eq_gateType (at level 70, no associativity) : heisenberg_scope.

(* will now show this is an equivalence relation *)
Lemma eq_gateType_refl : forall {n} (A : gateType n), A ≡≡ A.
Proof. intros n A. 
       easy.
Qed.

Lemma eq_gateType_sym : forall {n} (A B : gateType n), A ≡≡ B -> B ≡≡ A.
Proof. intros n A B H. 
       unfold eq_gateType in *; intros v.
       split. apply H. apply H.
Qed.

Lemma eq_gateType_trans : forall {n} (A B C : gateType n),
    A ≡≡ B -> B ≡≡ C -> A ≡≡ C.
Proof.
  intros n A B C HAB HBC.
  unfold eq_gateType in *.
  split. 
  - intros. apply HBC; apply HAB; apply H0.
  - intros. apply HAB; apply HBC; apply H0.
Qed.


Add Parametric Relation n : (gateType n) (@eq_gateType n)
  reflexivity proved by eq_gateType_refl
  symmetry proved by eq_gateType_sym
  transitivity proved by eq_gateType_trans
    as eq_gateType_rel.



 
Lemma eq_types_are_Eq_gate : forall (n : nat) (g : Square n) (T1 T2 : gateType n),
  (T1 ⊆ T2 /\ T2 ⊆ T1) -> T1 ≡≡ T2.
Proof. intros n v T1 T2 [S12 S21].
       unfold eq_gateType. intros. split.
       - apply has_type_subset_gate; apply S21.
       - apply has_type_subset_gate; apply S12. 
Qed.


Lemma cap_elim_l_gate : forall {n} (g : Square n) (A B : gateType n),
  g ::' A ∩ B -> g ::' A.
Proof. intros n g A B H. 
       apply (has_type_subset_gate _ _ A (A ∩ B)).
       auto with sub_db.
       apply H.
Qed.

Lemma cap_elim_r_gate : forall {n} (g : Square n) (A B : gateType n),
  g ::' A ∩ B -> g ::' B.
Proof. intros n g A B H. 
       apply (has_type_subset_gate _ _ B (A ∩ B)).
       auto with sub_db. 
       apply H.
Qed.

Lemma cap_intro : forall {n} (g : Square n) (A B : gateType n),
  g ::' A -> g ::' B -> g ::' A ∩ B.
Proof. intros n g A B. 
       induction A as [| a].
       - simpl; easy. 
       - simpl; intros [Ha Ha'] Hb; split. 
         * apply Ha.
         * apply IHA. 
           apply Ha'. 
           apply Hb.
Qed.

(* Note that both cap_elim_pair and cap_elim_gate are here. Both are necessary *)
Hint Resolve cap_elim_l_gate cap_elim_r_gate cap_elim_l_pair cap_elim_r_pair cap_intro : subtype_db.

Lemma cap_elim : forall {n} (g : Square n) (A B : gateType n),
  g ::' A ∩ B -> g ::' A /\ g ::' B.
Proof. eauto with subtype_db. Qed.


Lemma cap_arrow : forall {n} (g : Square n) (A B C : vecType n),
  g ::' (A → B) ∩ (A → C) ->
  g ::' A → (B ∩ C).
Proof. intros n g A B C [Ha [Hb _]].  
       apply kill_true.
       unfold singGateType' in *; simpl in *.
       intros v c H B' Hb'. 
       apply in_app_or in Hb'; destruct Hb' as [H3 | H3].
       - apply Ha. apply H. apply H3. 
       - apply Hb. apply H. apply H3. 
Qed.
 


Lemma arrow_sub : forall {n} (g : Square n) (A A' B B' : vecType n),
  (forall l, pairHasType l A' -> pairHasType l A) ->
  (forall r, pairHasType r B -> pairHasType r B') ->
  g ::' A → B ->
  g ::' A' → B'.
Proof. intros n g A A' B B' Ha Hb [H _]. simpl in *. 
       apply kill_true. 
       unfold singGateType' in *; simpl in *.
       intros.
       apply Hb.
       apply H.
       apply Ha.
       apply H0.
Qed.


Hint Resolve cap_elim cap_arrow arrow_sub : subtype_db.



(* this is killed by eauto with subtype_db *)
Lemma cap_arrow_distributes : forall {n} (g : Square n) (A A' B B' : vecType n),
  g ::' (A → A') ∩ (B → B') ->
  g ::' (A ∩ B) → (A' ∩ B').
Proof.
  intros; apply cap_arrow.
  apply cap_intro; eauto with subtype_db. 
Qed.

(* "Full explicit proof", as in Programs.v *)
Lemma cap_arrow_distributes'' : forall {n} (g : Square n) (A A' B B' : vecType n),
  g ::' (A → A') ∩ (B → B') ->
  g ::' (A ∩ B) → (A' ∩ B').
Proof.
  intros.
  apply cap_arrow.
  apply cap_intro.
  - eapply arrow_sub; intros.
    + apply cap_elim_l_pair in H1. apply H1.
    + apply H1.
    + eapply cap_elim_l_gate. apply H0.
  - eapply arrow_sub; intros.
    + eapply cap_elim_r_pair. apply H1.
    + apply H1.
    + eapply cap_elim_r_gate. apply H0.
Qed.

(***************)
(* Arrow rules *)
(***************)



Lemma arrow_mul : forall {n} (p : Square n) (A A' B B' : vecType n),
    Singleton A -> Singleton B ->
    unitary p ->
    uni_vecType A -> uni_vecType A' ->
    uni_vecType B -> uni_vecType B' ->
    p ::' A → A' ->
    p ::' B → B' ->
    p ::' A *' B → A' *' B'.
Proof. intros n p A A' B B' Hsa Hsb Hup Hua Hua' Hub Hub' [Ha _] [Hb _].
       assert (Hsa' : Singleton A). { apply Hsa. }
       assert (Hsb' : Singleton B). { apply Hsb. }
       apply singleton_simplify in Hsa; destruct Hsa;
       apply singleton_simplify in Hsb; destruct Hsb;
       apply kill_true.
       apply sgt_implies_sgt'.
       rewrite H0, H1. simpl. easy.
       apply sgt'_implies_sgt in Ha.
       apply sgt'_implies_sgt in Hb.
       unfold singGateType in *.
       intros AB A'B' H2 H3. simpl in *.
       apply in_mult in H2.
       apply in_mult in H3.
       do 2 (destruct H2); destruct H2 as [H2 H2']; destruct H2' as [H2' H2''].
       do 2 (destruct H3); destruct H3 as [H3 H3']; destruct H3' as [H3' H3''].
       rewrite H2'', H3''.
       rewrite <- Mmult_assoc. 
       assert (H4: p × x1 = x3 × p).
       { apply Ha. apply H2. apply H3. }
       assert (H5: p × x2 = x4 × p).
       { apply Hb. apply H2'. apply H3'. }
       rewrite H4. rewrite Mmult_assoc. 
       rewrite H5. rewrite <- Mmult_assoc.
       reflexivity.
       apply Hup. apply Hsb'. 
       split. apply Hub. apply Hub'.
       apply Hup. apply Hsa'.
       split. apply Hua. apply Hua'.
Qed.




Lemma arrow_scale : forall {n} (p : Square n) (A A' : vecType n) (c : C),
    c <> C0 -> p ::' A → A' -> p ::' c · A → c · A'.
Proof. intros n p A A' c H0 [H _]. 
       apply kill_true.
       unfold singGateType' in *.
       intros v x H1. simpl in *.
       intros A0 H2.
       unfold pairHasType in *.
       apply in_scale in H2.
       destruct H2 as [a' [H2 H2']].
       assert (H' : Eigenpair a' (p × v, x / c)). 
       { apply H. intros A1 H3. 
         apply (eigen_scale_div _ _ _ c).
         apply H0.
         assert (H' : c * (x / c) = x). 
         { C_field_simplify. reflexivity. apply H0. }
         rewrite H'. apply H1.
         apply in_scale_rev. apply H3.
         apply H2. }
       rewrite H2'.
       assert (H'' : x = (x / c) * c). 
       { C_field_simplify. reflexivity. apply H0. }
       rewrite H''.
       apply eigen_scale.
       apply H'.
Qed.           


Lemma arrow_i : forall {n} (p : Square n) (A A' : vecType n),
    p ::' A → A' ->
    p ::' i A → i A'.
Proof. unfold i. intros. 
       apply arrow_scale. 
       apply C0_snd_neq. simpl. easy. 
       apply H0.
Qed.

Lemma arrow_neg : forall {n} (p : Square n) (A A' : vecType n),
    p ::' A → A' ->
    p ::' -A → -A'.
Proof. unfold neg. intros.
       apply arrow_scale.
       rewrite <- Cexp_PI.
       apply Cexp_nonzero.
       apply H0.
Qed.



Lemma eq_arrow_r : forall {n} (g : Square n) (A B B' : vecType n),
    g ::' A → B ->
    B = B' ->
    g ::' A → B'.
Proof. intros; subst; easy. Qed.


(*****************************)
(** Typing Rules for Tensors *)
(*****************************)

Notation s := Datatypes.S.

Local Open Scope nat_scope.

(* where can I find tactics to deal with this??? *)
Lemma easy_sub : forall (n : nat), 1 + n - n = 1. Proof. nia. Qed. 
Lemma easy_sub2 : forall (n k : nat), k - (1 + n) - 1 = k - n - 2. Proof. nia. Qed.
Lemma easy_sub3 : forall (n k : nat), n <> 0 -> n + k - 0 - 1 = n - 0 - 1 + k. 
Proof. intros. 
       destruct n as [| n].
       - easy.
       - simpl. nia. 
Qed.

Lemma easy_leb : forall (n : nat), n <? 1 + n = true. 
Proof. induction n as [| n']. easy.
       simpl. unfold Nat.ltb. simpl. unfold Nat.ltb in IHn'.
       simpl in IHn'. easy.
Qed.
Lemma easy_pow : forall (a n m : nat), a^(n + m) = a^n * a^m.
Proof. intros. induction n as [| n'].
       - simpl. nia.
       - simpl. rewrite IHn'. nia.
Qed.
Lemma easy_pow2 : forall (a p : nat), p <> 0 -> a^p = a * a ^ (p - 0 - 1). 
Proof. intros. destruct p as [| p']. easy. simpl. 
       rewrite Nat.sub_0_r.  easy.
Qed.


(* defining program application *)
Definition prog_simple_app (prg_len : nat) (U : Square 2) (bit : nat) : Square (2^prg_len) :=
  I (2^bit) ⊗ U ⊗ I (2^(prg_len - bit - 1)).


Definition prog_ctrl_app (prg_len : nat) (U : Square 2) (ctrl targ : nat) : Square (2^prg_len) :=
  match (ctrl <? targ) with
  | true => I (2^ctrl) ⊗
             (∣0⟩⟨0∣ ⊗ I (2^(targ - ctrl)) .+ 
              ∣1⟩⟨1∣ ⊗ I (2^(targ - ctrl - 1)) ⊗ U) ⊗ I (2^(prg_len - targ - 1))
  | false => I (2^targ) ⊗
             (I (2^(ctrl - targ)) ⊗ ∣0⟩⟨0∣ .+ 
              U ⊗ I (2^(ctrl - targ - 1)) ⊗ ∣1⟩⟨1∣) ⊗ I (2^(prg_len - ctrl - 1))
  end.


Lemma tensor_base : forall (prg_len new_len : nat) (g : Square 2) 
                           (A A' : vecType (2^prg_len)) (E : vecType (2^new_len)),
    prg_len <> 0 -> unitary g -> 
    uni_vecType A -> uni_vecType A' ->
    WF_Matrix g -> Singleton A -> Singleton E ->
    (prog_simple_app prg_len g 0) ::' (A → A') ->
    (prog_simple_app (prg_len + new_len) g 0) ::'  A ⊗' E → A' ⊗' E.
Proof. unfold prog_simple_app in *.
       intros prg_len new_len g A A' E Hp0 Hug Hua Hua' Hwfg Hsa Hse [H _].
       apply sgt'_implies_sgt in H.
       apply kill_true.
       apply singleton_simplify in Hsa.
       destruct Hsa as [a Ha]. 
       apply singleton_simplify in Hse.
       destruct Hse as [e He]. 
       rewrite Ha, He.
       apply sgt_implies_sgt'.
       easy.
       unfold singGateType in *; simpl in *.
       intros.
       apply in_tensor in H1.
       destruct H1 as [a' [e1 [Ha1 [Ha2 Ha3]]]].
       apply in_simplify in Ha2. rewrite Ha2 in *.
       destruct H0 as [H0 | F].
       - rewrite <- H0, Ha3.
         rewrite kron_1_l in *. 
         rewrite easy_sub3. 
         rewrite (easy_pow 2 (prg_len - 0 - 1) new_len).
         rewrite <- id_kron.
         rewrite <- kron_assoc.
         restore_dims; 
         rewrite (kron_mixed_product (g ⊗ I (2 ^ (prg_len - 0 - 1))) _ a e).
         restore_dims;
         rewrite (kron_mixed_product a' e (g ⊗ I (2 ^ (prg_len - 0 - 1))) 
                                     (I (2 ^ new_len))).
         assert (Ha' : In a A). 
         { rewrite Ha. left. easy. }
         apply (H a a') in Ha'.
         repeat (rewrite <- easy_pow2 in *).
         rewrite Ha'.
         rewrite Mmult_1_l'; rewrite Mmult_1_r'.
         reflexivity.
         apply Hp0.
         apply Ha1.
         apply Hp0.
         apply Hwfg. apply Hwfg.
       - easy.
       - simpl. rewrite kron_1_l.
         rewrite easy_pow2.
         apply unit_kron.
         apply Hug. 
         apply unit_I.
         apply Hp0.
         apply Hwfg.
       - apply Hsa.
       - split. apply Hua. apply Hua'.
Qed.


Lemma tensor_inc : forall (prg_len bit : nat) (g : Square 2) 
                          (E : vecType 2) (A A' : vecType (2^prg_len)),
    prg_len <> 0 -> bit < prg_len -> unitary g ->
    uni_vecType A -> uni_vecType A' ->
    WF_Matrix g -> Singleton E -> Singleton A ->
    (prog_simple_app prg_len g bit) ::' (A → A') ->
    (prog_simple_app (prg_len + 1) g (s bit)) ::'  E ⊗' A → E ⊗' A'.
Proof. Admitted.


Lemma adj_ctrlX_is_cnot : forall (prg_len ctrl : nat),
  prog_ctrl_app prg_len σx ctrl (1 + ctrl) = 
  Matrix.I (2^ctrl) ⊗ cnot ⊗ Matrix.I (2^(prg_len - ctrl - 2)).
Proof. intros; unfold prog_ctrl_app.
       rewrite easy_leb. rewrite easy_sub. 
       assert (H : (∣0⟩⟨0∣ ⊗ Matrix.I (2 ^ 1) .+ ∣1⟩⟨1∣ ⊗ Matrix.I (2 ^ (1 - 1)) ⊗ σx) = cnot).
       { lma'. }
       rewrite H. rewrite easy_sub2. 
       reflexivity.
Qed.


Lemma adj_ctrlX_is_cnot1 : prog_ctrl_app 2 σx 0 1 = cnot.
Proof. assert (H : cnot = Matrix.I (2^0) ⊗ cnot ⊗ Matrix.I (2^0)).
       { lma'. } 
       rewrite H.
       rewrite adj_ctrlX_is_cnot.
       assert (H' : (2 - 0 - 2) = 0).
       { nia. }
       rewrite H'. reflexivity.
Qed.


Lemma ctrlX_is_notc1 : prog_ctrl_app 2 σx 1 0 = notc.
Proof. lma'. unfold prog_ctrl_app. simpl.
       apply WF_kron. reflexivity. reflexivity.
       apply WF_kron. reflexivity. reflexivity.
       auto with wf_db.
       apply WF_plus; auto with wf_db.
       auto with wf_db.
Qed.



Ltac solve_gate_type :=
  repeat match goal with
         | |- singGateType' ?U ?g /\ _ => split
         | |- ?g <> [] => easy
         | |- singGateType' ?U ?g => apply sgt_implies_sgt' 
         | |- singGateType ?U ?g => simpl; apply singleton_simplify2; lma'
         | |- _ => try easy
         end.


Lemma HTypes : (prog_simple_app 1 H 0) ::' (Z' → X') ∩ (X' → Z').
Proof. simpl. unfold Z', X', prog_simple_app. 
       solve_gate_type. 
Qed.
       

Lemma STypes : (prog_simple_app 1 S 0) ::' (X' → Y') ∩ (Z' → Z').
Proof. simpl. unfold Z', X', prog_simple_app. 
       solve_gate_type. 
Qed.

Lemma CNOTTypes : (prog_ctrl_app 2 σx 0 1) ::' (X' ⊗' I' → X' ⊗' X') ∩ (I' ⊗' X' → I' ⊗' X') ∩
                          (Z' ⊗' I' → Z' ⊗' I') ∩ (I' ⊗' Z' → Z' ⊗' Z').
Proof. rewrite adj_ctrlX_is_cnot1.
       simpl. unfold X', I', Z'. 
       solve_gate_type.
Qed.
      

(* T only takes Z → Z *)
Lemma TTypes : T ::' (Z' → Z').
Proof. simpl. unfold T, Z'. 
       solve_gate_type. 
Qed.

Hint Resolve HTypes STypes TTypes CNOTTypes : base_types_db.
Hint Resolve cap_elim_l_gate cap_elim_r_gate : base_types_db.

Hint Resolve HTypes STypes TTypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve SeqTypes : typing_db.



Definition bell00 : Square 16 := (prog_simple_app 4 H 2); (prog_ctrl_app 4 σx 2 3).

Definition encode : Square 16 := (prog_ctrl_app 4 σz 0 2); (prog_ctrl_app 4 σx 1 2).

Definition decode : Square 16 := (prog_ctrl_app 4 σx 2 3); (prog_simple_app 4 H 2).

Definition superdense := bell00 ; encode; decode.


Ltac type_check_base :=
  repeat apply cap_intro;
  repeat eapply SeqTypes; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Singleton _       => auto 50 with sing_db
         | |- ?g :: ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :: - ?A → ?B    => apply arrow_neg
         | |- ?g :: i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :: ?A * ?B → _ => apply arrow_mul
         | |- ?g :: (?A * ?B) ⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :: I ⊗ (?A * ?B) → _ => rewrite decompose_tensor_mult_r
         | |- prog_simple_app (S ?n) ?g (S ?m) :: ?T => eapply (tensor_inc ?n ?m _ _ _ _) 
         | |- prog_simple_app (S ?n) ?g 0 :: ?T => eapply (tensor_base n 1 _ _ _ _)
         | |- ?g :: ?A ⊗ ?B → _  => rewrite (decompose_tensor A B) by (auto 50 with sing_db)
         | |- ?g :: ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?B = ?B'          => tryif has_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         | |- ?n <> ?m => nia
         | |- ?n < ?m => nia
         end.



Ltac type_check_base' :=
         match goal with
         | |- (prog_simple_app (S ?n) ?g _) ::' _ => eapply (tensor_inc ?n _ _ _ _ _) 
         | |- (prog_simple_app (S ?n) ?g 0) ::' _ => eapply (tensor_base ?n 1 _ _ _ _)
         | |- ?n <> ?m => nia
         | |- ?n < ?m => nia
         end.


Lemma superdenseTypesQPL : superdense ::' (Z' ⊗' Z' ⊗' Z' ⊗' Z' → I' ⊗' I' ⊗' Z' ⊗' Z').
Proof. unfold superdense.
       repeat (eapply SeqTypes).
       type_check_base'.

       eapply (tensor_inc 3 _ _ _ _ _). 
       9: { eapply (tensor_inc 2 _ _ _ _ _). 
            9: { eapply (tensor_base 1 1 _ _ _ _). 
                 8: { solve [eauto with base_types_db]. }
                 nia. apply H_unitary.
                 auto with univ_db.
                 auto with univ_db.
                 auto with wf_db.
                 auto with sing_db.
                 auto with sing_db. }
            nia. nia. auto with unit_db.
            apply univ_tensor.            
            auto with univ_db.
            auto with univ_db.
            apply univ_tensor.    
            auto with univ_db.
            auto with univ_db.
            auto with wf_db.
            auto with sing_db.
            auto with sing_db. }
       nia. nia. 
       auto with unit_db.
       apply univ_tensor.
       auto with univ_db.
       apply univ_tensor.
       auto with univ_db.
       auto with univ_db.
       apply univ_tensor.
       auto with univ_db.
       apply univ_tensor.
       auto with univ_db.
       auto with univ_db.
       auto with wf_db.
       auto with sing_db.
       auto with sing_db.
       


            5: { auto with sing_db.
            
            auto with univ_db. simpl.
            auto with univ_db.
                 
Focus 9.
       
       nia. nia. apply H_unitary.
       simpl. unfold uni_vecType. intros.
       apply in_simplify in H0. rewrite H0.
       assert (H : 8 = 2 * 4). { nia. }
       rewrite H. apply unit_kron.
       apply Z_unitary.
       assert (H' : 4 = 2 * 2). { nia. }
       rewrite H'. apply unit_kron.
       apply Z_unitary. apply Z_unitary.



Lemma tensor_base : forall (prg_len new_len : nat) (g : Square 2) 
                           (A A' : vecType (2^prg_len)) (E : vecType (2^new_len)),
    prg_len <> 0 -> unitary g -> 
    uni_vecType A -> uni_vecType A' ->
    WF_Matrix g -> Singleton A -> Singleton E ->
    (prog_simple_app prg_len g 0) ::' (A → A') ->
    (prog_simple_app (prg_len + new_len) g 0) ::'  A ⊗' E → A' ⊗' E.

Lemma tensor_inc : forall (prg_len bit : nat) (g : Square 2) 
                          (E : vecType 2) (A A' : vecType (2^prg_len)),
    prg_len <> 0 -> bit < prg_len -> unitary g ->
    uni_vecType A -> uni_vecType A' ->
    WF_Matrix g -> Singleton E -> Singleton A ->
    (prog_simple_app prg_len g bit) ::' (A → A') ->
    (prog_simple_app (s prg_len) g (s bit)) ::'  E ⊗' A → E ⊗' A'.
Proof. Admitted.


simpl. apply kill_true. 
       unfold singGateType. simpl.
       intros A B [H | F] [H1 | F'].
       rewrite <- H, <- H1.
       lma'.






Lemma tensor_base : forall {n m} (g : Square 2) (A A' : vecType (2 * n)) (E : vecType m),
    Singleton A -> Singleton A' -> Singleton E ->
    (g ⊗ Matrix.I n) ::' (A → A') ->
    (g ⊗ Matrix.I (n * m)) ::'  A ⊗' E → A' ⊗' E.
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
    U ::' [A] → [B] -> v :' [A] -> (U × v) :' [B].
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
