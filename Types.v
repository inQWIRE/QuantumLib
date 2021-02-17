Require Import Psatz.
Require Import Reals.


Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.
Require Export Heisenberg. 



Fixpoint zip {X : Type} (f : X -> X -> X) (As Bs : list X) : list X :=
  match As with
  | [] => Bs
  | (a :: As') => 
    match Bs with 
    | [] => As
    | (b :: Bs') => (f a b :: zip f As' Bs')
    end
  end.


Lemma zip_len_pres : forall {X : Type} (f : X -> X -> X) (n : nat) (As Bs : list X),
  length As = n -> length Bs = n -> length (zip f As Bs) = n.
Proof. induction n as [| n'].
       - intros. 
         destruct As. easy. easy.
       - intros. 
         destruct As. easy.
         destruct Bs. easy.
         simpl in *. 
         rewrite IHn'.
         reflexivity. 
         nia. nia.
Qed.


(**********************)
(* Defining the types *)
(**********************)


Inductive GType :=
| gI
| gX
| gZ
| gIm : GType -> GType
| gNeg : GType -> GType
| gMul : GType -> GType -> GType.


Fixpoint translate_gt (g : GType) : vecType 2 :=
  match g with
  | gI => I'
  | gX => X'
  | gZ => Z'
  | gIm g => Ci · (translate_gt g)
  | gNeg g => (Copp C1) · (translate_gt g)
  | gMul g1 g2 => (translate_gt g1) *' (translate_gt g2)
  end. 


Definition GTypeT (len : nat) := (C * (list GType))%type. 


Definition gMulT {n} (A B : GTypeT n) : GTypeT n :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => (c1 * c2, zip gMul g1 g2)
    end
  end.

Definition gTensorT {n m} (A : GTypeT n) (B : GTypeT m) : GTypeT (n + m) :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => (c1 * c2, g1 ++ g2)
    end
  end.

Definition gScaleT {n} (c : C) (A : GTypeT n) : GTypeT n :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.


Definition translate {n} (A : GTypeT n) : vecTypeT n := 
  match (snd A) with
  | [] => []
  | (a :: As) => (fst A) · (translate_gt a) :: (map translate_gt As)
  end.


Notation gateTypeResize n := (list (vecType (2^n) * vecType (2^n))).


Definition formGTypeT {len : nat} (A B : GTypeT len) : gateTypeResize len := 
  formGateTypeT (translate A) (translate B).



Definition i {n} (A : GTypeT n) := gScaleT Ci A.
Notation "- A" := (gScaleT (Copp C1) A).
Infix ".*" := gMulT (at level 40, left associativity).
Infix ".⊗" := gTensorT (at level 51, right associativity).
Infix "→" := formGTypeT (at level 60, no associativity).

 
Definition I : GTypeT 1 := (C1, [gI]).
Definition X : GTypeT 1 := (C1, [gX]).
Definition Z : GTypeT 1 := (C1, [gZ]).

Notation Y := (i (X .* Z)).


(**************************)
(* Well Formedness Lemmas *)
(**************************)


Definition WF_GTypeT {len : nat} (gtt : GTypeT len) := length (snd gtt) = len.


Lemma WF_I : WF_GTypeT I. Proof. easy. Qed.
Lemma WF_X : WF_GTypeT X. Proof. easy. Qed.
Lemma WF_Z : WF_GTypeT Z. Proof. easy. Qed.


Lemma WF_gMulT : forall {n} (A B : GTypeT n),
  WF_GTypeT A -> WF_GTypeT B -> WF_GTypeT (A .* B). 
Proof. intros. 
       unfold WF_GTypeT in *.
       destruct A.
       destruct B.
       simpl in *. 
       apply zip_len_pres.
       assumption.
       assumption. 
Qed.

Lemma WF_gTensorT : forall {n m} (A : GTypeT n) (B : GTypeT m),
  WF_GTypeT A -> WF_GTypeT B -> WF_GTypeT (A .⊗ B). 
Proof. intros. 
       unfold WF_GTypeT in *.
       destruct A.
       destruct B.
       simpl in *. 
       rewrite app_length.
       nia. 
Qed.

Lemma WF_neg : forall {n} (A : GTypeT n),
  WF_GTypeT A ->  WF_GTypeT (- A). 
Proof. intros. 
       unfold WF_GTypeT in *.
       destruct A. 
       easy. 
Qed.
   
Lemma WF_i : forall {n} (A : GTypeT n),
  WF_GTypeT A ->  WF_GTypeT (i A). 
Proof. intros. 
       unfold WF_GTypeT in *.
       destruct A. 
       easy. 
Qed.


Hint Resolve WF_I WF_X WF_Z WF_gMulT WF_gTensorT WF_neg WF_i : wfgt_db.


Lemma WF_Y : WF_GTypeT Y.
Proof. auto with wfgt_db. Qed.


(*********************)
(* defining programs *)
(*********************)

Inductive prog :=
| H' (n : nat)
| S' (n : nat)
| T' (n : nat)
| CNOT (n1 n2 : nat)
| seq (p1 p2 : prog).

Infix ";;" := seq (at level 51, right associativity).


Fixpoint translate_prog (prg_len : nat) (p : prog) : Square (2^prg_len) :=
  match p with 
  | H' n => (prog_smpl_app prg_len hadamard n)
  | S' n => (prog_smpl_app prg_len Phase' n)
  | T' n => (prog_smpl_app prg_len (phase_shift (PI / 4)) n)
  | CNOT n1 n2 => (prog_ctrl_app prg_len σx n1 n2)
  | seq p1 p2 => (translate_prog prg_len p1) ; (translate_prog prg_len p2)
  end.




Definition progHasType {prg_len : nat} (p : prog) (T : gateTypeResize prg_len) :=
  (translate_prog prg_len p) ::' T.


Notation "p :' T" := (progHasType p T).


(********************)
(* Base type lemmas *)
(********************)


Lemma Hsimp : prog_smpl_app 1 hadamard 0 = hadamard.
Proof. unfold prog_smpl_app. 
       rewrite kron_1_r.
       rewrite kron_1_l.
       reflexivity. 
       auto with wf_db.
Qed.

Lemma Ssimp : prog_smpl_app 1 Phase' 0 = Phase'.
Proof. unfold prog_smpl_app. 
       rewrite kron_1_r.
       rewrite kron_1_l.
       reflexivity. 
       auto with wf_db.
Qed.


Lemma HTypes : H' 0 :' (X → Z) ∩ (Z → X).
Proof. unfold progHasType, formGTypeT.
       simpl. split. 
       apply sgt_implies_sgt'.
       easy.
       apply singleton_simplify2.
       rewrite Hsimp.
       lma'. split. 
       apply sgt_implies_sgt'.
       easy.
       apply singleton_simplify2.
       rewrite Hsimp.
       lma'. easy.
Qed.



Lemma STypes : S' 0 :' (X → Y) ∩ (Z → Z).
Proof. unfold progHasType, formGTypeT.
       simpl. split. 
       apply sgt_implies_sgt'.
       easy.
       apply singleton_simplify2.
       rewrite Ssimp.
       lma'. split. 
       apply sgt_implies_sgt'.
       easy.
       apply singleton_simplify2.
       rewrite Ssimp.
       lma'. easy.
Qed.

Lemma CNOTTypes : CNOT 0 1 :' (X .⊗ I → X .⊗ X) ∩ (I .⊗ X → I .⊗ X) ∩
                             (Z .⊗ I → Z .⊗ I) ∩ (I .⊗ Z → Z .⊗ Z).
Proof. unfold progHasType, formGTypeT.
       simpl. rewrite adj_ctrlX_is_cnot1.
       split. apply sgt_implies_sgt'. easy.
       apply singleton_simplify2.
       lma'. split. apply sgt_implies_sgt'. easy.
       apply singleton_simplify2.
       lma'. split. apply sgt_implies_sgt'. easy.
       apply singleton_simplify2.
       lma'. split. apply sgt_implies_sgt'. easy.
       apply singleton_simplify2.
       lma'. easy. 
Qed.


(*************************)
(* Proving typing lemmas *)
(*************************)

(* we need this for now. should eventually rewrite defs to make proofs easier *)
Lemma fgt_conv : forall (n : nat) (A B : vecType n), [(A, B)] = formGateType A B.
Proof. easy. Qed.



Lemma SeqTypes : forall {n} (g1 g2 : prog) (A B C : GTypeT n),
  g1 :' A → B ->
  g2 :' B → C ->
  (g1 ;; g2) :' A → C.
Proof. intros.  
       unfold progHasType, formGTypeT, formGateTypeT in *.
       simpl translate_prog. 
       rewrite (fgt_conv (2^n) _ _). 
       apply (Heisenberg.SeqTypes (translate_prog n g1) _  _ (⨂' translate B) _).
       rewrite <- (fgt_conv (2^n) _ _); apply H.
       rewrite <- (fgt_conv (2^n) _ _); apply H0.
Qed.


Lemma seq_assoc : forall {n} (g1 g2 g3 : prog) (T : gateTypeResize n),
    g1 ;; (g2 ;; g3) :' T <-> (g1 ;; g2) ;; g3 :' T.
Proof. intros. 
       unfold progHasType.
       simpl. 
       apply Heisenberg.seq_assoc.
Qed.




(* Note that this doesn't restrict # of qubits referenced by p. *)
Lemma TypesI : forall (p : prog), p :' I → I.
Proof. intros. 
       unfold progHasType, formGTypeT, formGateTypeT.
       Admitted.
      

Lemma TypesI2 : forall p, p :' I .⊗ I → I .⊗ I.
Proof. Admitted.

Hint Resolve TypesI TypesI2 : base_types_db.

(** Structural rules *)

(* Subtyping rules *)
Axiom cap_elim_l : forall g A B, g :: A ∩ B -> g :: A.
Axiom cap_elim_r : forall g A B, g :: A ∩ B -> g :: B.
Axiom cap_intro : forall g A B, g :: A -> g :: B -> g :: A ∩ B.
Axiom cap_arrow : forall g A B C,
  g :: (A → B) ∩ (A → C) ->
  g :: A → (B ∩ C).


      

Definition progHasType {prg_len : nat} (p : prog) (T : gateTypeResize prg_len) :=
  (translate_prog prg_len p) ::' T.


Fixpoint gateHasType' {n : nat} (U : Square n) (ts: gateType n) : Prop := 
  match ts with  
  | [] => True
  | (t :: ts') => (singGateType' U t) /\ gateHasType' U ts'
  end.


Definition H' := hadamard.
Definition S' := Phase'.
Definition T' := phase_shift (PI / 4).
Definition CNOT :=  cnot.



Definition bell00 : Square 16 := (prog_smpl_app 4 H' 2); (prog_ctrl_app 4 σx 2 3).

Definition encode : Square 16 := (prog_ctrl_app 4 σz 0 2); (prog_ctrl_app 4 σx 1 2).

Definition decode : Square 16 := (prog_ctrl_app 4 σx 2 3); (prog_smpl_app 4 H' 2).

Definition superdense := bell00 ; encode; decode.



Ltac is_I A :=
  match A with


Definition vecTypeT (len : nat) := (list (vecType 2)).

| tensor : GType -> GType -> GType
| cap : GType -> GType -> GType
| arrow : GType -> GType -> GType. 

Notation "- T" := (neg T).
Infix ".*" := mul (at level 40, left associativity).
Infix ".⊗" := tensor (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X .* Z)).


Fixpoint singGType (g : GType) := 
  match g with
  | I => 
  | X => 
  | Z => 
  | i g => 
  | neg g => 
  | mul g1 g2 => 
  | tensor g1 g2 =>
  | 



Fixpoint translate (g : GType) :=
  match g with
  | gI => I''
  | gX => X''
  | gZ => Z''
  | gmul g1 g2 => mulT' (translate g1) (translate g2)
  | gtensor g1 g2 => tensorT (translate g1) (translate g2)
  | gi g => scaleT Ci (translate g)
  | gneg g => scaleT (Copp C1) (translate g)
  | _ => I''
  end. 



Parameter GType : Type.
Parameter I : GType.
Parameter X : GType.
Parameter Z : GType.
Parameter i : GType -> GType.
Parameter neg : GType -> GType.
Parameter mul : GType -> GType -> GType.
Parameter tensor : GType -> GType -> GType.
Parameter cap : GType -> GType -> GType.
Parameter arrow : GType -> GType -> GType.


(*
Parameter toGType : Matrix 2 2 -> GType.
Axiom ItoG : toGType (Matrix.I 2) = I.
Axiom XtoG : toGType σx  = X.
Axiom ZtoG : toGType σz  = Z.
*)


Notation "- T" := (neg T).
Infix "*" := mul (at level 40, left associativity).
Infix "⊗" := tensor (at level 51, right associativity).
Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

Notation Y := (i (X * Z)).

(* Singleton Types *)
(* Could probably safely make this inductive. Can't do inversion on GTypes anyhow. *)

Parameter Singleton : GType -> Prop.
Axiom SI: Singleton I.
Axiom SX : Singleton X.
Axiom SZ : Singleton Z.
Axiom S_neg : forall A, Singleton A -> Singleton (neg A).
Axiom S_i : forall A, Singleton A -> Singleton (i A).
Axiom S_mul : forall A B, Singleton A -> Singleton B -> Singleton (A * B).

Hint Resolve SI SX SZ S_neg S_i S_mul : sing_db.

Lemma SY : Singleton Y.
Proof. auto with sing_db. Qed.

(* Multiplication laws *)

Axiom mul_assoc : forall A B C, A * (B * C) = A * B * C.
Axiom mul_I_l : forall A, I * A = A.
Axiom mul_I_r : forall A, A * I = A.
Axiom Xsqr : X * X = I.
Axiom Zsqr : Z * Z = I.
Axiom ZmulX : Z * X = - (X * Z).

Axiom neg_inv : forall A, - - A = A.
Axiom neg_dist_l : forall A B, -A * B = - (A * B).
Axiom neg_dist_r : forall A B, A * -B = - (A * B).

Axiom i_sqr : forall A, i (i A) = -A.
Axiom i_dist_l : forall A B, i A * B = i (A * B).
Axiom i_dist_r : forall A B, A * i B = i (A * B).

Axiom i_neg_comm : forall A, i (-A) = -i A.

Hint Rewrite mul_I_l mul_I_r Xsqr Zsqr ZmulX neg_inv neg_dist_l neg_dist_r i_sqr i_dist_l i_dist_r i_neg_comm : mul_db.

(** ** Tensor Laws *)

Axiom tensor_assoc : forall A B C, A ⊗ (B ⊗ C) = (A ⊗ B) ⊗ C.  

Axiom neg_tensor_dist_l : forall A B, -A ⊗ B = - (A ⊗ B).
Axiom neg_tensor_dist_r : forall A B, A ⊗ -B = - (A ⊗ B).
Axiom i_tensor_dist_l : forall A B, i A ⊗ B = i (A ⊗ B).
Axiom i_tensor_dist_r : forall A B, A ⊗ i B = i (A ⊗ B).

(** ** Multiplication & Tensor Laws *)

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Axiom mul_tensor_dist : forall A B C D,
    Singleton A ->
    Singleton C ->
    (A ⊗ B) * (C ⊗ D) = (A * C) ⊗ (B * D).

Lemma decompose_tensor : forall A B,
    Singleton A ->
    Singleton B ->
    A ⊗ B = (A ⊗ I) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l, mul_I_r. 
  easy.
Qed.

Lemma decompose_tensor_mult_l : forall A B,
    Singleton A ->
    Singleton B ->
    (A * B) ⊗ I = (A ⊗ I) * (B ⊗ I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.

Lemma decompose_tensor_mult_r : forall A B,
    I ⊗ (A * B) = (I ⊗ A) * (I ⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with sing_db.
  rewrite mul_I_l.
  easy.
Qed.
  
Hint Rewrite neg_tensor_dist_l neg_tensor_dist_r i_tensor_dist_l i_tensor_dist_r : tensor_db.

(** ** Intersection Laws *)

Axiom cap_idem : forall A, A ∩ A = A.

Axiom cap_comm : forall A B, A ∩ B = B ∩ A.

Axiom cap_assoc : forall A B C, A ∩ (B ∩ C) = (A ∩ B) ∩ C.

Axiom cap_I_l : forall A,
  Singleton A ->
  I ∩ A = A.

Lemma cap_I_r : forall A,
  Singleton A ->
  A ∩ I = A.
Proof. intros; rewrite cap_comm, cap_I_l; easy. Qed.


(* Note: I haven't proven that this works or terminates.
   An anticommutative monoidal solver would be ideal here. *)
Ltac normalize_mul :=
  repeat match goal with
  | |- context[(?A ⊗ ?B) ⊗ ?C] => rewrite <- (tensor_assoc A B C)
  end;
  repeat (rewrite mul_tensor_dist by auto with sing_db);
  repeat rewrite mul_assoc;
  repeat (
      try rewrite <- (mul_assoc X Z _);
      autorewrite with mul_db tensor_db;
      try rewrite mul_assoc ).



Lemma Ysqr : Y * Y = I. Proof. 
autorewrite with mul_db.
try rewrite mul_assoc.
try rewrite <- (mul_assoc X Z _).
autorewrite with mul_db.
try rewrite mul_assoc.
try rewrite <- (mul_assoc X Z _).
autorewrite with mul_db.

  reflexivity. Qed.
Lemma XmulZ : X * Z = - Z * X. Proof. normalize_mul. reflexivity. Qed.
Lemma XmulY : X * Y = i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulX : Y * X = -i Z. Proof. normalize_mul. reflexivity. Qed.
Lemma ZmulY : Z * Y = -i X. Proof. normalize_mul. reflexivity. Qed.
Lemma YmulZ : Y * Z = i X. Proof. normalize_mul. reflexivity. Qed.
