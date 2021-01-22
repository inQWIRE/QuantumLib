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
Lemma ZX_eq_negXZ : σz × σx = -1 .* (σx × σz). Proof. lma'. Qed.
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


Definition singVecType' := (list (Square 2)).
Definition singVecType (n : nat) := (list (Square 2)).

Definition WF_svt {n : nat} (m : singVecType n) := length m = n.

Fixpoint sing_mul {n : nat} (m1 m2 : singVecType n) : singVecType n :=
  match m1 with
  | [] => m2
  | (h1 :: t1) => 
    match m2 with 
    | [] => m1
    | (h2 :: t2) => (h1 × h2 :: @sing_mul n t1 t2)
    end
  end.

Definition sing_tensor {n m : nat} (m1 : singVecType n) (m2 : singVecType m)
  : singVecType (n + m) := m1 ++ m2.


Definition sing_scale (c : C) {n : nat} (m : singVecType n) : singVecType n :=
  match m with
  | [] => []
  | (h :: t) => (c .* h :: t)
  end.


Definition vecHasSingType {n: nat} (v : Vector (2^n)) (U : singVecType n) : Prop :=
  Eigenpair (⨂ U) (v, C1) \/ Eigenpair (⨂ U) (v, -C1).


Infix "*'" := sing_mul (at level 40, left associativity) : heisenberg_scope. 
Infix "⊗'" := sing_tensor (at level 51, right associativity) : heisenberg_scope. 
Infix "·" := sing_scale (at level 45, left associativity) : heisenberg_scope. 


(*****************)
(* WF_svt lemmas *)
(*****************)


Lemma WF_svt_mul_helper : forall (n m : nat) (A B : singVecType'),
  length A = m -> length B = m -> length (@sing_mul n A B) = m.
Proof. induction m as [| m'].
       - intros. 
         destruct A. easy. 
         destruct B. easy. 
         easy.
       - intros. 
         destruct A. easy.
         destruct B. easy.
         simpl in *. 
         rewrite IHm'.
         reflexivity.
         injection H. easy.
         injection H0. easy. 
Qed.

Lemma WF_svt_mul : forall {n} (A B : singVecType n),
    WF_svt A -> WF_svt B -> WF_svt (A *' B).
Proof. intros. 
       unfold WF_svt in *.
       apply WF_svt_mul_helper. 
       apply H. apply H0.
Qed.


Lemma WF_svt_tensor : forall {n m} (A : singVecType n) (B : singVecType m),
    WF_svt A -> WF_svt B -> WF_svt (A ⊗' B).
Proof. intros. 
       unfold WF_svt, sing_tensor in *.
       rewrite app_length. 
       rewrite H, H0.
       reflexivity.
Qed.


(*****************************)
(* Basic vectType operations *)
(*****************************)

Local Open Scope nat_scope.


Definition I_n (n : nat) : singVecType' := repeat (I 2) n.



Theorem sing_mul_assoc : forall {n : nat} (A B C : singVecType n), A *' (B *' C) = A *' B *' C.
Proof. induction A as [| a].
       - simpl. reflexivity. 
       - destruct B. 
         + reflexivity.
         + destruct C. 
           * reflexivity.
           * simpl. 
             rewrite IHA.
             rewrite Mmult_assoc.
             reflexivity.
Qed.

Lemma duh : 1 + 1 = 2. Proof. nia. Qed. 

Lemma mul_I_l_helper : forall (A : singVecType') (n m : nat), 
  n <= length A ->  @sing_mul m (I_n n) A = A.
Proof. intros A. induction A as [| a].
       - intros. 
         apply le_n_0_eq in H. 
         rewrite <- H. 
         reflexivity.
       - intros. destruct n as [| n']. 
         + reflexivity.
         + simpl in H.
           apply le_S_n in H.
           simpl.
           rewrite IHA.
           rewrite Mmult_1_l'. 
           reflexivity.
           assumption.
Qed.

Lemma mul_I_l : forall {n} (A : singVecType n), 
  WF_svt A -> (I_n n) *' A = A.
Proof. intros.
       apply mul_I_l_helper.
       unfold WF_svt in H.
       rewrite H.
       nia. 
Qed.


Lemma mul_I_r_helper : forall (A : singVecType') (n m : nat), 
  n <= length A ->  @sing_mul m A (I_n n) = A.
Proof. intros A. induction A as [| a].
       - intros. 
         apply le_n_0_eq in H. 
         rewrite <- H. 
         reflexivity.
       - intros. destruct n as [| n']. 
         + reflexivity.
         + simpl in H.
           apply le_S_n in H.
           simpl.
           rewrite IHA.
           rewrite Mmult_1_r'. 
           reflexivity.
           assumption.
Qed.


Lemma mul_I_r : forall {n} (A : singVecType n), 
  WF_svt A -> A *' (I_n n) = A.
Proof. intros.
       apply mul_I_r_helper.
       unfold WF_svt in H.
       rewrite H.
       nia. 
Qed.


Local Close Scope nat_scope.


Lemma scale_1_l : forall {n} (A : singVecType n), C1 · A = A.
Proof. intros n A. destruct A as [|a].
       - easy.
       - simpl. 
         rewrite Mscale_1_l.
         reflexivity. 
Qed.


Lemma scale_assoc : forall {n} (a b : C) (A : singVecType n),
    a · (b · A) = (a * b) · A.
Proof. intros n a b A. destruct A as [| h].
       - simpl. 
         reflexivity.
       - simpl. 
         rewrite Mscale_assoc.
         reflexivity.
Qed.
         


Lemma scale_dist_l : forall {n} (c : C) (A B : singVecType n), 
    WF_svt A -> WF_svt B -> (c · A) *' B = c · (A *' B).
Proof. intros n c A B Ha Hb. destruct A as [|a].
       - unfold WF_svt in *; simpl in Ha.
         rewrite <- Ha in Hb.
         destruct B.
         + easy.
         + easy.
       - destruct B as [| b]. 
         + reflexivity.
         + simpl. 
           rewrite Mscale_mult_dist_l.
           reflexivity.
Qed.



Lemma scale_dist_r : forall {n} (c : C) (A B : singVecType n), 
    WF_svt A -> WF_svt B -> A *' (c · B) = c · (A *' B).
Proof. intros n c A B Ha Hb. destruct A as [|a].
       - unfold WF_svt in *; simpl in Ha.
         rewrite <- Ha in Hb.
         destruct B.
         + easy.
         + easy.
       - destruct B as [| b]. 
         + unfold WF_svt in *; simpl in *.
           rewrite <- Hb in Ha.
           easy. 
         + simpl. 
           rewrite Mscale_mult_dist_r.
           reflexivity.
Qed.



Theorem tensor_assoc : forall {n m o} (A : singVecType n) (B : singVecType m)
  (C : singVecType o),  
  A ⊗' (B ⊗' C) = (A ⊗' B) ⊗' C. 
Proof. intros n m o A B C. unfold sing_tensor. 
       rewrite app_ass. 
       reflexivity.
Qed. 


Lemma scale_tensor_dist_l : forall {n} (c : C) (A B : singVecType n),
    WF_svt A -> WF_svt B -> (c · A) ⊗' B = c · (A ⊗' B).
Proof. intros n c A B Ha Hb. destruct A as [|a].
       - unfold WF_svt in *; simpl in *.
         rewrite <- Ha in Hb.
         destruct B.
         easy. easy. 
       - reflexivity. 
Qed.




(*
Ltac solveType := intros; 
                  try (left; simpl; rewrite kron_1_r; auto with eig_db; easy);
                  try (right; simpl; rewrite kron_1_r; auto with eig_db).


Lemma all_hastype_I : forall (v : Vector 2), v :' I'.
Proof. solveType.
Qed.
  
Lemma p_hastype_X : ∣+⟩ :' X'. Proof. solveType. Qed. 
Lemma m_hastype_X : ∣-⟩ :' X'. Proof. solveType. Qed.
Lemma O_hastype_Z : ∣0⟩ :' Z'. Proof. solveType. Qed.
Lemma i_hastype_Z : ∣1⟩ :' Z'. Proof. solveType. Qed.

Lemma B_hastype_XX : ∣Φ+⟩ :' X' ⊗' X'. Proof. solveType. Qed.


Hint Resolve all_hastype_I p_hastype_X m_hastype_X O_hastype_Z i_hastype_Z B_hastype_XX : vht_db.
*)


(*

(***************************)
(* Writing actual programs *)
(***************************)

Local Open Scope nat_scope. 


Inductive sing_prog :=
| Smpl (A : Square 2) (bit : nat)
| Ctrl (A : Square 2) (ctrl targ : nat).

Notation prog := (list sing_prog).


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


Definition prog_to_sqr (prg_len : nat) (prg : sing_prog) : Square (2^prg_len) :=
  match prg with
  | Smpl A bit => prog_simple_app prg_len A bit
  | Ctrl A ctrl targ => prog_ctrl_app prg_len A ctrl targ
  end.


Notation gateType := (singVecType * singVecType). *)

