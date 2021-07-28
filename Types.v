Require Import Psatz.
Require Import Reals.


Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.
Require Export Heisenberg. 
Require Import Setoid.


(************************)
(* Defining coeficients *)
(************************)


Inductive Coef :=
| p_1
| p_i
| n_1
| n_i.

Definition cNeg (c : Coef) : Coef :=
  match c with
  | p_1 => n_1
  | n_1 => p_1
  | p_i => n_i
  | n_i => p_i
  end.

Lemma cNeg_inv : forall (c : Coef), cNeg (cNeg c) = c.
Proof. destruct c; easy.
Qed.


Definition cMul (c1 c2 : Coef) : Coef :=
  match (c1, c2) with
  | (p_1, _) => c2
  | (_, p_1) => c1
  | (n_1, _) => cNeg c2
  | (_, n_1) => cNeg c1
  | (p_i, p_i) => n_1
  | (n_i, n_i) => n_1
  | (p_i, n_i) => p_1
  | (n_i, p_i) => p_1
  end.

Fixpoint cBigMul (cs : list Coef) : Coef := 
  match cs with
  | nil => p_1 
  | c :: cs' => cMul c (cBigMul cs')
  end. 


 
Infix "*" := cMul (at level 40, left associativity).


Lemma cMul_comm : forall (c1 c2 : Coef), c1 * c2 = c2 * c1.
Proof. intros. 
       destruct c1;
       destruct c2;
       easy. 
Qed.

Lemma cMul_assoc : forall (c1 c2 c3 : Coef), (c1 * c2) * c3 = c1 * (c2 * c3).
Proof. intros. 
       destruct c1;
       destruct c2;
       destruct c3;
       easy. 
Qed.


Lemma cBigMul_app : forall (l1 l2 : list Coef),
  (cBigMul l1) * (cBigMul l2) = cBigMul (l1 ++ l2).
Proof. induction l1 as [| h]; try easy.
       intros. simpl. 
       rewrite cMul_assoc, IHl1; easy.
Qed.



Definition translate_coef (c : Coef) : C :=
  match c with
  | p_1 => C1
  | p_i => Ci
  | n_1 => -C1
  | n_i => -Ci
  end. 

Lemma translate_coef_cMul : forall (c1 c2 : Coef), 
    translate_coef (cMul c1 c2) = ((translate_coef c1) * (translate_coef c2))%C. 
Proof. intros.
       destruct c1; 
       destruct c2;
       unfold translate_coef;
       unfold cMul;
       unfold cNeg;
       try lca. 
Qed.

Lemma translate_coef_nonzero : forall (c : Coef), translate_coef c <> C0.
Proof. destruct c; simpl; 
         try (apply C0_fst_neq; simpl; lra);
         try (apply C0_snd_neq; simpl; lra).
Qed.

(**********************)
(* Defining the types *)
(**********************)

(* this is the lowest level, only Pauli gates are defined *)
Inductive Pauli :=
| gI
| gX
| gY
| gZ.

Definition translate_P (g : Pauli) : Square 2 :=
  match g with
  | gI => I 2
  | gX => σx
  | gY => σy
  | gZ => σz
  end. 


Lemma WF_Matrix_Pauli : forall (g : Pauli), WF_Matrix (translate_P g).
Proof. intros. 
       destruct g; simpl; auto with wf_db.
Qed.


(* scaling, multiplication, and tensoring done at this level *)
Definition TType (len : nat) := (Coef * (list Pauli))%type. 

(* we define an error TType for when things go wrong *)
Definition ErrT : TType 0 := (p_1, []).


(*
(* we first define a multiplication for Paulis *)
Definition gMul (p : Pauli * Pauli) : (Coef * Pauli) :=
  match p with 
  | (g1, g2) =>
    match g1, g2 with
    | gI, _ => (p_1, g2)
    | _, gI => (p_1, g1)
    | gX, gX => (p_1, gI)
    | gY, gY => (p_1, gI)
    | gZ, gZ => (p_1, gI)
    | gX, gY => (p_i, gZ)
    | gY, gX => (n_i, gZ)
    | gX, gZ => (n_i, gY)
    | gZ, gX => (p_i, gY)
    | gY, gZ => (p_i, gX)
    | gZ, gY => (n_i, gX)
    end
  end.
*)


(* Here we define a gMul to give Coef followed by a gMul to give the actual type *)
(* this allows for an easy zip in gMulT *)

Definition gMul_Coef (g1 g2 : Pauli) : Coef :=
  match g1, g2 with
  | gI, _ => p_1
  | _, gI => p_1
  | gX, gX => p_1
  | gY, gY => p_1
  | gZ, gZ => p_1
  | gX, gY => p_i
  | gY, gX => n_i
  | gX, gZ => n_i
  | gZ, gX => p_i
  | gY, gZ => p_i
  | gZ, gY => n_i
  end.

Definition gMul_base (g1 g2 : Pauli) : Pauli :=
  match g1, g2 with
  | gI, _ => g2
  | _, gI => g1
  | gX, gX => gI
  | gY, gY => gI
  | gZ, gZ => gI
  | gX, gY => gZ
  | gY, gX => gZ
  | gX, gZ => gY
  | gZ, gX => gY
  | gY, gZ => gX
  | gZ, gY => gX
  end.


(*
Definition gMulT {n} (A B : TType n) : TType n :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => if length g1 =? length g2 
                 then (c1 * c2 * (cBigMul (fst (List.split (map gMul (combine g1 g2))))), 
                       snd (List.split (map gMul (combine g1 g2))))
                 else ErrT
    end
  end.
*)

(* the idea here is that we cannot have any coeficients in the Pauli list 
   Thus, we need to extract the coeficients we get when multiplying paulis,
   bringing them to the front. This allows for easy equality verification since we
   just compare one Coef *) 
Definition gMulT {n} (A B : TType n) : TType n :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => if length g1 =? length g2 
                 then (c1 * c2 * (cBigMul (zipWith gMul_Coef g1 g2)), 
                       zipWith gMul_base g1 g2)
                 else ErrT
    end
  end.


Definition gTensorT {n m} (A : TType n) (B : TType m) : TType (n + m) :=
  match A with
  | (c1, g1) =>
    match B with
    | (c2, g2) => if (length g1 =? n) && (length g2 =? m) 
                 then (c1 * c2, g1 ++ g2)
                 else ErrT
    end
  end.

Definition gScaleT {n} (c : Coef) (A : TType n) : TType n :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.


Definition translate {n} (A : TType n) : Square (2^n) := 
  (translate_coef (fst A)) .* ⨂ (map translate_P (snd A)).
  


Inductive vType (n : nat) : Type :=
  | G : TType n -> vType n
  | Cap : vType n -> vType n -> vType n
  | Arrow : vType n -> vType n -> vType n
  | Err : vType n.


(* you cannot multiply intersection or arrow types (for now) 
   so any of these options returns Err *)
Definition mul {n} (A B : vType n) : vType n :=
  match A with
  | G _ a =>
    match B with
    | G _ b => G n (gMulT a b)
    | _ => Err n
    end
  | _ => Err n
  end.
                                       
Definition tensor {n m} (A : vType n) (B : vType m) : vType (n + m) :=
  match A with
  | G _ a =>
    match B with
    | G _ b => G (n + m) (gTensorT a b)
    | _ => Err (n + m)
    end
  | _ => Err (n + m)
  end.

(* since scaling intersections makes sense, we allow this *)
Fixpoint scale {n} (c : Coef) (A : vType n) : vType n :=
  match A with
  | G _ a => G n (gScaleT c a)
  | Cap _ g1 g2 => Cap n (scale c g1) (scale c g2)
  | _ => Err n
  end.


Definition i {n} (A : vType n) := scale p_i A.
Notation "- A" := (scale n_1 A).
Infix ".*" := mul (at level 40, left associativity).
Infix ".⊗" := tensor (at level 51, right associativity).

Definition cap {n} (A B : vType n) : vType n := Cap n A B.
Definition arrow {n} (A B : vType n) : vType n := Arrow n A B.

Infix "→" := arrow (at level 60, no associativity).
Infix "∩" := cap (at level 60, no associativity).

(******************************************************************************)
(* Defining different types of vTypes to ensure WF and Singleton translations *)
(******************************************************************************)


Definition Sing_vt {n} (A : vType n) : Prop :=
  match A with
  | G _ _ => True
  | _ => False
  end.

Fixpoint Cap_vt {n} (A : vType n) : Prop :=
  match A with
  | G _ _ => True
  | Cap _ v1 v2 => Cap_vt v1 /\ Cap_vt v2
  | _ => False
  end.

(* we also use a bool version of Cap_vt for matching *)
Fixpoint Cap_vt_bool {n} (A : vType n) : bool :=
  match A with
  | G _ _ => true
  | Cap _ v1 v2 => Cap_vt_bool v1 && Cap_vt_bool v2
  | _ => false
  end.

Lemma Cap_vt_conv : forall {n} (A : vType n),
  Cap_vt A <-> Cap_vt_bool A = true.
Proof. intros. split. 
       + induction A as [| | |]; try easy.
         - intros. 
           destruct H.
           simpl. 
           rewrite IHA1, IHA2;
           easy.
       + induction A as [| | |]; try easy.
         - intros.
           simpl in *. 
           apply andb_true_iff in H.
           destruct H.
           split;
           try (apply IHA1); 
           try (apply IHA2); 
           assumption.
Qed.         


Definition Sing_gt {n} (A : vType n) : Prop :=
  match A with
  | Arrow _ v1 v2 => Cap_vt v1 /\ Cap_vt v2
  | _ => False
  end.


Fixpoint Cap_gt {n} (A : vType n) : Prop :=
  match A with
  | Arrow _ v1 v2 => Cap_vt v1 /\ Cap_vt v2
  | Cap _ v1 v2 => Cap_gt v1 /\ Cap_gt v2
  | _ => False
  end.



Fixpoint translate_vecType {n} (A : vType n) := 
  match Cap_vt_bool A with
  | false => []
  | true => 
    match A with
    | G _ g => [translate g]
    | Cap _ v1 v2 => translate_vecType v1 ++ translate_vecType v2
    | _ => []
    end
  end.


Lemma singleton_sing_vt : forall {n m} (A : vType n),
  Sing_vt A -> @Singleton m (translate_vecType A).
Proof. intros. destruct A; easy. 
Qed.


Lemma sing_vt_simplify : forall {n} (A : vType n),
  Sing_vt A -> (exists a, A = G n a).
Proof. intros. destruct A; try easy.
       - exists t. reflexivity. 
Qed. 


Definition I : vType 1 := G 1 (p_1, [gI]).
Definition X : vType 1 := G 1 (p_1, [gX]).
Definition Y : vType 1 := G 1 (p_1, [gY]).
Definition Z : vType 1 := G 1 (p_1, [gZ]).

Lemma Itrans : translate_vecType I = I'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r. 
       reflexivity. 
Qed.

Lemma Xtrans : translate_vecType X = X'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r. 
       reflexivity. 
Qed.

Lemma Ytrans : translate_vecType Y = Y'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r, Y_eq_iXZ.
       distribute_scale.
       reflexivity. 
Qed.

Lemma Ztrans : translate_vecType Z = Z'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l, kron_1_r. 
       reflexivity. 
Qed.

Lemma Y_eq_iXZ : Y = (i (X .* Z)).
Proof. easy. Qed.


(***************)
(* Sing Lemmas *)
(***************)

Lemma SI : Sing_vt I. Proof. easy. Qed.
Lemma SX : Sing_vt X. Proof. easy. Qed.
Lemma SZ : Sing_vt Z. Proof. easy. Qed.

Lemma S_scale : forall {n} (A : vType n) (c : Coef), Sing_vt A -> (Sing_vt (scale c A)).  
Proof. intros. destruct A; easy. Qed. 

Lemma S_neg : forall {n} (A : vType n), Sing_vt A -> Sing_vt (- A).
Proof. intros. destruct A; easy. Qed. 
 
Lemma S_i : forall {n} (A : vType n), Sing_vt A -> Sing_vt (i A).
Proof. intros. destruct A; easy. Qed. 

Lemma S_mul : forall {n} (A B : vType n), Sing_vt A -> Sing_vt B -> Sing_vt (A .* B).
Proof. intros.
       destruct A; destruct B; easy.
Qed.

Lemma S_tensor : forall {n m} (A : vType n) (B : vType m), Sing_vt A -> Sing_vt B -> Sing_vt (A .⊗ B).
Proof. intros.
       destruct A; destruct B; easy.
Qed.

Hint Resolve SI SX SZ S_scale S_neg S_i S_mul S_tensor : svt_db.

Lemma SY : Sing_vt Y.
Proof. auto with svt_db. Qed.




(**************************)
(* Well Formedness Lemmas *)
(**************************)

 
Definition WF_TType {len : nat} (tt : TType len) := length (snd tt) = len.

Fixpoint WF_vType {n} (A : vType n) : Prop :=
  match A with
  | G _ a => WF_TType a
  | Cap _ a1 a2 => WF_vType a1 /\ WF_vType a2
  | Arrow _ a1 a2 => WF_vType a1 /\ WF_vType a2
  | _ => False
  end.

Lemma WF_I : WF_vType I. Proof. easy. Qed.
Lemma WF_X : WF_vType X. Proof. easy. Qed.
Lemma WF_Z : WF_vType Z. Proof. easy. Qed.

Lemma WF_scale : forall {n} (A : vType n) (c : Coef), 
  Sing_vt A -> WF_vType A ->
  (WF_vType (scale c A)).  
Proof. intros. 
       destruct A; try easy.
       destruct t; easy.
Qed.

Lemma WF_mul : forall {n} (A B : vType n),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B ->
  WF_vType (A .* B). 
Proof. intros. 
       destruct A;
       destruct B; try easy.
       destruct t;
       destruct t0. simpl;  
       rewrite H1, H2, Nat.eqb_refl. 
       unfold WF_TType; simpl. 
       rewrite (zipWith_len_pres _ n); easy.
Qed.


Lemma WF_tensor : forall {n m} (A : vType n) (B : vType m),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B ->
  WF_vType (A .⊗ B). 
Proof. intros. 
       destruct A;
       destruct B; try easy.
       destruct t;
       destruct t0.
       simpl in *. 
       unfold WF_TType in *.
       simpl in *.
       bdestruct_all; simpl. 
       rewrite app_length;
       lia. 
Qed.


Lemma WF_neg : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (- A). 
Proof. intros. 
       destruct A; try easy.
       destruct t; easy.
Qed.
   
Lemma WF_i : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (i A). 
Proof. intros. 
       destruct A; try easy.
       destruct t; easy.
Qed.


Hint Resolve SI SX SZ WF_I WF_X WF_Z WF_mul WF_scale WF_tensor WF_neg WF_i : wfvt_db.


Lemma WF_Y : WF_vType Y.
Proof. auto with wfvt_db. Qed.


Lemma WF_Matrix_TType : forall {n} (A : TType n), WF_TType A -> WF_Matrix (translate A). 
Proof. intros. destruct A.
       destruct l as [| h].
       - unfold translate; simpl.
         rewrite <- H.
         auto with wf_db.          
        - unfold translate; simpl. 
          assert (H' : forall n, (2^n + (2^n +0) = 2^ (S n))%nat). { simpl. nia. }
          rewrite H'.      
          rewrite map_length.
          unfold WF_TType in H; simpl in H. 
          rewrite H.
          apply Matrix.WF_scale.
          apply WF_kron;
          try (rewrite <- H);
          try simpl; try nia. 
          apply WF_Matrix_Pauli.
          rewrite <- (map_length translate_P _).
          apply (WF_big_kron _ _ (map translate_P l) (translate_P gI)).
          intros. 
          rewrite map_nth.
          apply WF_Matrix_Pauli. 
Qed.

(*************)
(* WFS types *)
(*************)

Definition WFS_vType {n} (T : vType n) : Prop :=
  Sing_vt T /\ WF_vType T.


Lemma WFS_I : WFS_vType I. Proof. easy. Qed.
Lemma WFS_X : WFS_vType X. Proof. easy. Qed.
Lemma WFS_Z : WFS_vType Z. Proof. easy. Qed.


Lemma WFS_mul : forall {n} (A B : vType n),
  WFS_vType A -> WFS_vType B -> 
  WFS_vType (A .* B). 
Proof. intros n A B [H H0] [H1 H2]. 
       split; auto with svt_db.
       apply WF_mul; easy.
Qed.


Lemma WFS_tensor : forall {n m} (A : vType n) (B : vType m),
  WFS_vType A -> WFS_vType B ->
  WFS_vType (A .⊗ B). 
Proof. intros n m A B [H H0] [H1 H2]. 
       split; auto with svt_db.
       apply WF_tensor; easy.
Qed.


Lemma WFS_scale : forall {n} (A : vType n) (c : Coef),
  WFS_vType A ->  WFS_vType (scale c A). 
Proof. intros n A c [H H0]. 
       split; auto with svt_db.
       auto with wfvt_db.
Qed.

Lemma WFS_neg : forall {n} (A : vType n),
  WFS_vType A ->  WFS_vType (- A). 
Proof. intros n A [H H0]. 
       split; auto with svt_db.
       apply WF_neg; easy.
Qed.
   
Lemma WFS_i : forall {n} (A : vType n),
  WFS_vType A ->  WFS_vType (i A). 
Proof. intros n A [H H0]. 
       split; auto with svt_db.
       apply WF_i; easy.
Qed.

Hint Resolve WFS_I WFS_X WFS_Z WFS_scale WFS_mul WFS_tensor WFS_neg WFS_i : wfvt_db.

(******************)
(* unitary lemmas *)
(******************)


Lemma unit_Pauli : forall (p : Pauli), WF_Unitary (translate_P p).
Proof. intros. 
       destruct p; simpl; auto with unit_db.
Qed.


Lemma unit_TType : forall {n} (A : TType n), WF_TType A -> WF_Unitary (translate A). 
Proof. intros. destruct A.
       destruct l as [| h].
       - unfold translate; simpl. 
         unfold WF_TType in H; simpl in H.
         rewrite <- H.
         apply unit_scale. 
         auto with unit_db.
         destruct c; lca.          
        - unfold translate; simpl. 
          assert (H' : forall n, (2^n + (2^n +0) = 2^ (S n))%nat). { simpl. nia. }
          rewrite H'.      
          rewrite map_length.
          unfold WF_TType in H; simpl in H.
          rewrite <- H.
          apply unit_scale.
          apply kron_unitary. 
          apply unit_Pauli. 
          rewrite <- (map_length translate_P _).
          apply (unit_big_kron 2 (map translate_P l)).
          intros. 
          apply in_map_iff in H0.
          do 2 (destruct H0).
          rewrite <- H0.
          apply unit_Pauli.
          destruct c; lca.      
Qed.


Lemma unit_vType : forall {n} (A : vType n), 
    WF_vType A -> uni_vecType (translate_vecType A).
Proof. intros. 
       induction A as [| | |]; try easy. 
       - simpl; unfold uni_vecType. 
         intros A [H0 | F]; try easy. 
         rewrite <- H0, <- H.   
         apply unit_TType.
         simpl in H.
         easy.
       - simpl.
         destruct (Cap_vt_bool A1 && Cap_vt_bool A2).
         + simpl in H.
           destruct H as [H1 H2].
           apply IHA1 in H1;
           apply IHA2 in H2.
           unfold uni_vecType in *.
           intros.
           apply in_app_or in H.
           destruct H as [H | H].
           apply H1; apply H.
           apply H2; apply H.
         + easy. 
Qed.


(******************************************************)
(* Showing translations preserves relevent properties *)
(******************************************************)

(* we actually use this to prove translate_mult, so we prove it first *)
Lemma translate_kron : forall {n m} (g1 : TType n) (g2 : TType m),
    length (snd g1) = n -> length (snd g2) = m ->
    translate (gTensorT g1 g2) = (translate g1) ⊗ (translate g2).
Proof. intros. unfold translate.
         destruct g1; destruct g2.
         simpl in *.
         do 3 (rewrite map_length). 
         unfold WF_TType in *.
         rewrite H, H0 in *.
         rewrite Mscale_kron_dist_r.
         rewrite Mscale_kron_dist_l.
         rewrite Mscale_assoc.
         bdestruct_all; simpl. 
         rewrite translate_coef_cMul.
         rewrite Cmult_comm.
         rewrite map_app. 
         assert (H3 : forall (l : list Pauli) (i0 : nat), WF_Matrix (nth i0 (map translate_P l) Zero)).
         { intros. 
           bdestruct (i0 <? length (map translate_P l1)).
           + apply (nth_In _ (@Zero 2 2)) in H3.
             apply in_map_iff in H3.
             destruct H3 as [x [H3 H4]].
             rewrite <- H3; apply WF_Matrix_Pauli.
           + rewrite nth_overflow; try lia. 
             auto with wf_db. }
         rewrite big_kron_app; auto.
         do 2 (rewrite map_length).
         rewrite app_length.
         rewrite H, H0 in *.
         reflexivity.
Qed.


Lemma gMulT_reduce : forall (n : nat) (c1 c2 : Coef) (p1 p2 : Pauli) (l1 l2 : list Pauli),
  length l1 = n -> length l2 = n ->
  gMulT (c1, p1 :: l1) (c2, p2 :: l2) = 
  @gTensorT 1 n (gMul_Coef p1 p2, [gMul_base p1 p2]) (gMulT (c1, l1) (c2, l2)).
Proof. intros. simpl.
       rewrite H, H0.
       bdestruct (n =? n); try lia. 
       rewrite (zipWith_len_pres _ n); try easy.
       bdestruct (n =? n); try lia. 
       rewrite zipWith_cons.
       apply injective_projections; try easy.
       simpl.
       unfold zipWith. 
       rewrite <- (cMul_assoc (c1 * c2)), (cMul_comm (c1 * c2)). 
       replace (uncurry gMul_Coef (p1, p2)) with (gMul_Coef p1 p2) by easy.
       rewrite cMul_assoc; easy. 
Qed.

Lemma translate_reduce : forall (n : nat) (c : Coef) (p : Pauli) (l : list Pauli),
  length l = n -> 
  @translate (S n) (c, p :: l) = (translate_P p) ⊗ @translate n (c, l).
Proof. intros. 
       unfold translate. 
       simpl. 
       rewrite map_length.
       replace (2^(length l) + (2^(length l) + 0))%nat with (2 * 2^(length l))%nat by lia. 
       rewrite <- Mscale_kron_dist_r.
       rewrite H; easy. 
Qed.


Lemma translate_Mmult : forall {n} (g1 g2 : TType n),
    length (snd g1) = n -> length (snd g2) = n ->
    translate (gMulT g1 g2) = (translate g1) × (translate g2).
Proof. intros. induction n as [| n'].
       - destruct g1; destruct g2. 
         destruct l; destruct l0; try easy. 
         unfold translate. simpl. 
         distribute_scale.
         rewrite Mmult_1_r; auto with wf_db.
         rewrite <- translate_coef_cMul.
         destruct c; destruct c0; try easy.
       - destruct g1; destruct g2.
         destruct l; destruct l0; try easy. 
         simpl in H; simpl in H0.
         apply Nat.succ_inj in H.
         apply Nat.succ_inj in H0.
         rewrite gMulT_reduce; try easy.
         replace (S n') with (1 + n')%nat by lia.
         rewrite translate_kron; try easy.
         rewrite IHn'; try easy.
         rewrite (translate_reduce _ c), (translate_reduce _ c0); try easy.
         restore_dims.
         rewrite kron_mixed_product.
         assert (H' : @translate 1 (gMul_Coef p p0, [gMul_base p p0]) = 
                      translate_P p × translate_P p0).
         { destruct p; destruct p0; simpl. 
           all : unfold translate; simpl. 
           all : lma'. }
         rewrite H'; easy. 
         simpl. 
         rewrite H, H0; bdestruct_all.
         simpl. 
         apply zipWith_len_pres; easy.
Qed.


Lemma translate_vecType_mMult : forall {n} (A B : vType n),
  WFS_vType A -> WFS_vType B -> 
  translate_vecType (A .* B) = (translate_vecType A) *' (translate_vecType B).
Proof. intros n A B [H H0] [H1 H2]. 
       destruct A; destruct B; try easy.
       simpl.
       rewrite translate_Mmult; easy.
Qed.


Lemma translate_scale : forall {n} (A : TType n) (c : Coef),
  translate (gScaleT c A) = Matrix.scale (translate_coef c) (translate A).
Proof. intros. 
       unfold translate. 
       destruct A. simpl. 
       rewrite translate_coef_cMul.
       rewrite <- Mscale_assoc.     
       reflexivity. 
Qed.



Lemma Cap_vt_scale : forall {n} (A : vType n) (c : Coef), 
    Cap_vt_bool (scale c A) = Cap_vt_bool A.
Proof. intros. induction A as [| | |]; try easy.
       simpl. rewrite IHA1, IHA2.
       reflexivity.
Qed.       

Lemma translate_vecType_scale : forall {n} (A : vType n) (c : Coef),
  translate_vecType (scale c A) = (translate_coef c) · (translate_vecType A).
Proof. intros. induction A; try easy.
       - simpl. rewrite translate_scale.
         reflexivity. 
       - simpl translate_vecType.
         do 2 (rewrite Cap_vt_scale).
         destruct (Cap_vt_bool A1 && Cap_vt_bool A2); try easy.
         rewrite IHA1, IHA2.
         rewrite concat_into_scale.
         reflexivity.
Qed.





(**************************)
(* Defining vector typing *)
(**************************)


(* we need this for now. should eventually rewrite defs to make proofs easier *)
Lemma fgt_conv : forall {n m} (A B : vecType n), [(A, B)] = @formGateType m A B.
Proof. easy. Qed.

Lemma ite_conv : forall {X : Type} (x1 x2 : X), (if true && true then x1 else x2) = x1.
Proof. easy. Qed.


Definition vecPair (prg_len : nat) := (Vector (2^prg_len) * C)%type.

Definition vecHasType {prg_len : nat} (p : vecPair prg_len) (T : vType prg_len) :=
  match (Cap_vt_bool T) with 
  | false => False
  | true => pairHasType p (translate_vecType T)
  end. 

  

Notation "p ;' T" := (vecHasType p T) (at level 61, no associativity).



Lemma cap_elim_l_vec : forall {n} (v : vecPair n) (A B : vType n), v ;' A ∩ B -> v ;' A.
Proof. intros. 
       unfold vecHasType in *.
       simpl Cap_vt_bool in H.
       simpl translate_vecType in *.
       destruct (Cap_vt_bool A).
       destruct (Cap_vt_bool B).
       do 2 (rewrite ite_conv in H).
       apply (Heisenberg.cap_elim_l_pair _ _ (translate_vecType B)).
       assumption.
       rewrite andb_false_r in H; easy.
       easy. 
Qed.       


Lemma cap_elim_r_vec : forall {n} (v : vecPair n) (A B : vType n), v ;' A ∩ B -> v ;' B.
Proof. intros. 
       unfold vecHasType in *.
       simpl Cap_vt_bool in H.
       simpl translate_vecType in *.
       destruct (Cap_vt_bool A).
       destruct (Cap_vt_bool B).
       do 2 (rewrite ite_conv in H).
       apply (Heisenberg.cap_elim_r_pair _ (translate_vecType A) _).
       assumption.
       rewrite andb_false_r in H; easy.
       easy. 
Qed.      




(***************************************************************************)
(* proving some preliminary lemmas on the TType level before we prove their 
                    counterparts on the vType level *)
(***************************************************************************)


Lemma gMulT_gTensorT_dist : forall {n m : nat} (t1 t2 : TType n) (t3 t4 : TType m),
  WF_TType t1 -> WF_TType t2 -> WF_TType t3 -> WF_TType t4 ->
  gMulT (gTensorT t1 t3) (gTensorT t2 t4) = gTensorT (gMulT t1 t2) (gMulT t3 t4).
Proof. intros. 
       destruct t1; destruct t2; destruct t3; destruct t4. 
       simpl gTensorT.
       rewrite H, H0, H1, H2.
       bdestruct_all. simpl. 
       rewrite (zipWith_len_pres _ n), (zipWith_len_pres _ m); try easy.
       do 2 rewrite app_length. 
       rewrite H, H0, H1, H2.
       bdestruct_all. simpl. 
       apply injective_projections; simpl. 
       - rewrite (cMul_assoc (c * c0)). 
         rewrite (cMul_comm (cBigMul (zipWith gMul_Coef l l0))).
         rewrite (cMul_assoc (c1 * c2)). 
         rewrite (cMul_comm (cBigMul (zipWith gMul_Coef l1 l2))).
         rewrite cBigMul_app.
         rewrite (zipWith_app_product _ n); try easy.
         rewrite (cMul_assoc c), <- (cMul_assoc c1), (cMul_comm c1 c0).
         repeat rewrite cMul_assoc; easy.
       - rewrite (zipWith_app_product _ n); easy.
Qed.


Lemma gMulT_assoc : forall (n : nat) (t1 t2 t3 : TType n),
  WF_TType t1 -> WF_TType t2 -> WF_TType t3 ->
  gMulT (gMulT t1 t2) t3 = gMulT t1 (gMulT t2 t3).
Proof. induction n as [| n']. 
       - intros. 
         destruct t1; destruct t2; destruct t3.
         destruct l; destruct l0; destruct l1; try easy.
         destruct c; destruct c0; destruct c1; easy.
       - intros. 
         destruct t1; destruct t2; destruct t3.
         destruct l; destruct l0; destruct l1; try easy.
         unfold WF_TType in *.
         simpl in H; simpl in H0; simpl in H1.
         apply Nat.succ_inj in H;
         apply Nat.succ_inj in H0;
         apply Nat.succ_inj in H1.
         repeat rewrite gMulT_reduce; try easy.
         assert (H2 : (c1, p1 :: l1) = @gTensorT 1 n' (p_1, [p1]) (c1, l1)).
         { simpl. bdestruct_all. easy. }
         assert (H3 : (c, p :: l) = @gTensorT 1 n' (p_1, [p]) (c, l)).
         { simpl. bdestruct_all. easy. }
         rewrite H2, H3. 
         do 2 replace (S n') with (1 + n')%nat by lia.
         rewrite gMulT_gTensorT_dist, gMulT_gTensorT_dist; try easy. 
         rewrite IHn'; try easy.
         assert (H4 : (@gMulT 1 (gMul_Coef p p0, [gMul_base p p0]) (p_1, [p1])) = 
                      (@gMulT 1 (p_1, [p]) (gMul_Coef p0 p1, [gMul_base p0 p1]))).
         { destruct p; destruct p0; destruct p1; easy. }
         rewrite H4; easy. 
         all : simpl; bdestruct_all; unfold WF_TType; simpl. 
         all : rewrite (zipWith_len_pres _ n'); easy.
Qed.


(* Multiplication laws *)

Lemma mul_assoc : forall {n} (A B C : vType n), 
  WFS_vType A -> WFS_vType B -> WFS_vType C -> 
  A .* (B .* C) = A .* B .* C. 
Proof. intros. 
       destruct A; destruct B; destruct C; try easy.
       unfold mul.
       destruct H; destruct H0; destruct H1.       
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite gMulT_assoc; easy. 
Qed.


Lemma mul_I_l : forall (A : vType 1), WFS_vType A -> I .* A = A.
Proof. intros A [H H0].
       destruct A; try easy.
       destruct t.
       do 2 (destruct l; try easy).
       simpl. 
       destruct c; easy.
Qed.

Lemma mul_I_r : forall (A : vType 1), WFS_vType A -> A .* I = A.
Proof. intros A [H H0].
       destruct A; try easy.
       destruct t.
       do 2 (destruct l; try easy).
       destruct p; destruct c; easy.
Qed.

Lemma Xsqr : X .* X = I.
Proof. easy. Qed.       

Lemma Zsqr : Z .* Z = I.
Proof. easy. Qed.

Lemma ZmulX : Z .* X = - (X .* Z).
Proof. easy. Qed.


Lemma neg_inv : forall (n : nat) (A : vType n), WFS_vType A -> - - A = A.
Proof. intros n A [H H0]. 
       destruct A; try easy.
       simpl. 
       unfold gScaleT. 
       destruct t; destruct c; easy.  
Qed.


Lemma neg_dist_l : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  -A .* B = - (A .* B).
Proof. intros. 
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all; try easy.
       unfold gScaleT.
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma neg_dist_r : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  A .* (-B) = - (A .* B).
Proof. intros.  
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all; try easy.
       unfold gScaleT.
       rewrite <- cMul_assoc, (cMul_comm c).
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma i_sqr : forall (n : nat) (A : vType n), i (i A) = -A.
Proof. intros. 
       induction A; try easy. 
       - destruct t. simpl. 
         unfold translate; simpl. 
         destruct c; easy.
       - simpl. unfold i in *.
         simpl. 
         rewrite IHA1, IHA2.
         reflexivity. 
Qed.

Lemma i_dist_l : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  i A .* B = i (A .* B).
Proof. intros. 
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all; try easy.
       unfold gScaleT.
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma i_dist_r : forall (n : nat) (A B : vType n), 
  WFS_vType A -> WFS_vType B -> 
  A .* i B = i (A .* B).
Proof. intros.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all; try easy.
       unfold gScaleT.
       rewrite <- cMul_assoc, (cMul_comm c).
       repeat rewrite cMul_assoc.
       easy.
Qed.


Lemma i_neg_comm : forall (n : nat) (A : vType n), i (-A) = -i A.
Proof. intros.
       induction A; try easy. 
       - destruct t. simpl. 
         unfold translate; simpl. 
         destruct c; easy.
       - simpl. unfold i in *.
         simpl. 
         rewrite IHA1, IHA2.
         reflexivity. 
Qed.


(** ** Tensor Laws *)

(*
Lemma tensor_assoc : forall {n m o : nat} (A : vType n) (B : vType m) (C : vType o), 
  eq_vType' (A .⊗ (B .⊗ C)) ((A .⊗ B) .⊗ C).  
Proof. intros. unfold eq_vType'.
       destruct A; destruct B; destruct C; try easy.
       destruct t; destruct t0; destruct t1; simpl.
       rewrite app_ass.
       rewrite cMul_assoc. 
       reflexivity. 
Qed.       
*)


Lemma neg_tensor_dist_l : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  -A .⊗ B = - (A .⊗ B).
Proof. intros.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold translate; simpl.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all. simpl. 
       destruct c; destruct c0; easy. 
Qed.


Lemma neg_tensor_dist_r : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  A .⊗ (-B) = - (A .⊗ B).
Proof. intros.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold translate; simpl.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all. simpl. 
       destruct c; destruct c0; easy. 
Qed.


Lemma i_tensor_dist_l : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  i A .⊗ B = i (A .⊗ B).
Proof. intros.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold translate; simpl.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all. simpl. 
       destruct c; destruct c0; easy. 
Qed.


Lemma i_tensor_dist_r : forall {n m} (A : vType n) (B : vType m), 
  WFS_vType A -> WFS_vType B -> 
  A .⊗ i B = i (A .⊗ B).
Proof. intros.
       destruct A; destruct B; try easy. 
       destruct t; destruct t0; simpl. 
       destruct H; destruct H0.
       unfold translate; simpl.
       unfold WF_vType, WF_TType in *; simpl in *.
       rewrite H1, H2.
       bdestruct_all. simpl. 
       destruct c; destruct c0; easy. 
Qed.



(** ** Multiplication & Tensor Laws *)

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Lemma mul_tensor_dist : forall {n m} (A C : vType n) (B D : vType m),
  WFS_vType A -> WFS_vType B -> WFS_vType C -> WFS_vType D ->
  (A .⊗ B) .* (C .⊗ D) = (A .* C) .⊗ (B .* D).
Proof. intros.
       destruct A; destruct B; destruct C; destruct D; try easy.
       unfold mul, tensor. 
       destruct H; destruct H0; destruct H1; destruct H2.
       unfold WF_vType in *.
       rewrite gMulT_gTensorT_dist; easy. 
Qed.



Lemma decompose_tensor : forall (A B : vType 1),
  WFS_vType A -> WFS_vType B ->
  A .⊗ B = (A .⊗ I) .* (I .⊗ B).
Proof.
  intros A B H H0.  
  rewrite mul_tensor_dist; auto with wfvt_db.
  rewrite mul_I_r, mul_I_l; easy.
Qed.


Lemma decompose_tensor_mult_l : forall (A B : vType 1),
  WFS_vType A -> WFS_vType B ->
  (A .* B) .⊗ I = (A .⊗ I) .* (B .⊗ I).
Proof.
  intros. 
  rewrite mul_tensor_dist; auto with wfvt_db.
Qed.


Lemma decompose_tensor_mult_r : forall (A B : vType 1),
  WFS_vType A -> WFS_vType B ->
  I .⊗ (A .* B) = (I .⊗ A) .* (I .⊗ B).
Proof.
  intros. 
  rewrite mul_tensor_dist; auto with wfvt_db.
Qed.
  

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
  | S' n => (prog_smpl_app prg_len Phase n)
  | T' n => (prog_smpl_app prg_len (phase_shift (PI / 4)) n)
  | CNOT n1 n2 => (prog_ctrl_app prg_len σx n1 n2)
  | seq p1 p2 => (translate_prog prg_len p1) ; (translate_prog prg_len p2)
  end.


Lemma unit_prog : forall (prg_len : nat) (p : prog), 
  WF_Unitary (translate_prog prg_len p).
Proof. intros. induction p as [| | | |];
       try (apply unit_prog_smpl_app; auto with unit_db);
       try (apply unit_prog_ctrl_app; auto with unit_db).
       simpl. apply Mmult_unitary; easy. 
Qed.      





Definition progHasSingType {prg_len : nat} (p : prog) (T1 T2 : vType prg_len) :=
  match (Cap_vt_bool T1) && (Cap_vt_bool T2) with 
  | false => False
  | true => (translate_prog prg_len p) ::' [(translate_vecType T1, translate_vecType T2)]
  end. 


Fixpoint progHasType {prg_len : nat} (p : prog) (T : vType prg_len) :=
  match T with 
  | Arrow _ v1 v2 => progHasSingType p v1 v2
  | Cap _ v1 v2 => progHasType p v1 /\ progHasType p v2
  | _ => False
  end. 

  

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

Lemma Ssimp : prog_smpl_app 1 Phase 0 = Phase.
Proof. unfold prog_smpl_app. 
       rewrite kron_1_r.
       rewrite kron_1_l.
       reflexivity. 
       auto with wf_db.
Qed.


Lemma Isimp : @translate 1 (p_1, [gI]) = Matrix.I 2. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Xsimp : @translate 1 (p_1, [gX]) = σx. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Zsimp : @translate 1 (p_1, [gZ]) = σz. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Ysimp : @translate 1 (p_1, [gY]) = σy. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.


Lemma kron_simp : forall (g1 g2 : Pauli), 
    @translate 2 (p_1 * p_1, g1 :: [g2]) = (translate_P g1) ⊗ (translate_P g2).  
Proof. intros. 
       unfold translate; simpl. 
       autorewrite with C_db.
       rewrite Mscale_1_l. 
       rewrite kron_1_r. 
       reflexivity. 
Qed.


Hint Rewrite Ssimp Hsimp Isimp Xsimp Zsimp Ysimp adj_ctrlX_is_cnot1 kron_simp : simp_db.


Ltac solve_ground_type := simpl; unfold progHasSingType; simpl;
                          autorewrite with simp_db;
                          repeat split;
                          repeat (apply sgt_implies_sgt'; try easy; 
                                  apply singleton_simplify2;
                                  unfold translate; simpl; auto with id_db).
                          

Lemma HTypes : H' 0 :' (X → Z) ∩ (Z → X).
Proof. solve_ground_type. Qed.


Lemma HTypes_not : ~ (H' 0 :' (X → X)).
Proof. solve_ground_type. unfold not. 
       intros. destruct H.
       apply sgt'_implies_sgt in H.
       unfold singGateType in H.
       assert (H' : hadamard × σx = σx × hadamard). 
       { apply H. left; easy. left; easy. }
       assert (H'' : forall (m1 m2 : Square 2), m1 = m2 -> m1 1%nat 0%nat = m2 1%nat 0%nat). 
       { intros. rewrite H1. reflexivity. }
       apply H'' in H'. 
       unfold Mmult in H'. simpl in H'.
       assert (H1 : C0 + C1 * (C1 / √ 2) + C0 * (C1 / √ 2) = (C1 / √ 2)). { lca. }
       assert (H2 : C0 + C1 / √ 2 * C0 + Copp (C1 / √ 2) * C1 =  Copp (C1 / √ 2)). { lca. }
       rewrite H1, H2 in H'.
       unfold Cdiv in H'.
       rewrite Copp_mult_distr_l in H'.
       assert (H3 : forall c1 c2 , (c1 = c2 -> c1 * √ 2 = c2 * √ 2)%C). 
       { intros. rewrite H3. easy. }
       apply H3 in H'.
       do 2 (rewrite <- Cmult_assoc in H').
       rewrite (Cinv_l (√ 2)) in H'.
       do 2 (rewrite Cmult_1_r in H').
       assert (H4: forall {X} (p1 p2 : X * X), p1 = p2 -> fst p1 = fst p2). 
       { intros. rewrite H4. easy. }
       apply H4 in H'. simpl in H'.
       lra. 
       apply C0_fst_neq. simpl. 
       apply sqrt_neq_0_compat. 
       lra. 
       auto with unit_db.
       auto with sing_db.
       auto with univ_db.
Qed.

Lemma STypes : S' 0 :' (X → Y) ∩ (Z → Z).
Proof. solve_ground_type. 
Qed.


Lemma CNOTTypes : CNOT 0 1 :' (X .⊗ I → X .⊗ X) ∩ (I .⊗ X → I .⊗ X) ∩
                             (Z .⊗ I → Z .⊗ I) ∩ (I .⊗ Z → Z .⊗ Z).
Proof. solve_ground_type. Qed.



Notation CZ m n := (H' n ;; CNOT m n ;; H' n).




(*************************)
(* Proving typing lemmas *)
(*************************)

Lemma SeqTypes : forall {n} (g1 g2 : prog) (A B C : vType n),
  g1 :' A → B ->
  g2 :' B → C ->
  (g1 ;; g2) :' A → C.
Proof. intros.  
       simpl in *. 
       unfold progHasSingType in *.
       destruct (Cap_vt_bool A).
       destruct (Cap_vt_bool B).
       destruct (Cap_vt_bool C).
       rewrite ite_conv in *.
       simpl translate_prog. 
       rewrite (@fgt_conv (2^n) _ _ _). 
       apply (Heisenberg.SeqTypes (translate_prog n g1) _  _ (translate_vecType B) _).
       rewrite <- (@fgt_conv (2^n) _ _ _); apply H.
       rewrite <- (@fgt_conv (2^n) _ _ _); apply H0.
       rewrite andb_false_r in H0; easy.
       easy. easy.       
Qed.


Lemma seq_assoc : forall {n} (g1 g2 g3 : prog) (T : vType n),
    g1 ;; (g2 ;; g3) :' T <-> (g1 ;; g2) ;; g3 :' T.
Proof. induction T as [| | |]; try easy. 
       - simpl. split. 
         intros [H1 H2].
         split. 
         apply IHT1; apply H1.
         apply IHT2; apply H2.
         intros [H1 H2].
         split. 
         apply IHT1; apply H1.
         apply IHT2; apply H2.
       - simpl. unfold progHasSingType. 
         destruct (Cap_vt_bool T1 && Cap_vt_bool T2).
         simpl translate_prog.
         apply Heisenberg.seq_assoc.
         easy.  
Qed.


(* Note that this doesn't restrict # of qubits referenced by p. *)
Lemma TypesI : forall (p : prog), p :' I → I.
Proof. intros. simpl. 
       unfold progHasSingType. 
       rewrite ite_conv.
       rewrite Itrans.
       rewrite fgt_conv.
       apply Heisenberg.TypesI1.
       apply (unit_prog 1 p).
Qed.

  

Lemma TypesI2 : forall (p : prog), p :' I .⊗ I → I .⊗ I.
Proof. intros. simpl. 
       unfold progHasSingType. 
       rewrite ite_conv.
       unfold translate_vecType. 
       rewrite ite_conv. 
       autorewrite with simp_db. 
       simpl translate_P.
       rewrite fgt_conv.
       apply Heisenberg.TypesI2.
       apply (unit_prog 2 p).
Qed.


Hint Resolve TypesI TypesI2 : base_types_db.


(** Structural rules *)

(* Subtyping rules *)
Lemma cap_elim_l : forall {n} (g : prog) (A B : vType n), g :' A ∩ B -> g :' A.
Proof. intros. simpl in H.
       easy. 
Qed.

Lemma cap_elim_r : forall {n} (g : prog) (A B : vType n), g :' A ∩ B -> g :' B.
Proof. intros. simpl in H.
       easy. 
Qed.

Lemma cap_intro : forall {n} (g : prog) (A B : vType n), g :' A -> g :' B -> g :' A ∩ B.
Proof. intros. simpl. 
       easy. 
Qed.

Lemma cap_arrow : forall {n} (g : prog) (A B C : vType n),
  g :' (A → B) ∩ (A → C) ->
  g :' A → (B ∩ C).
Proof. intros. simpl in *. 
       unfold progHasSingType in *.
       destruct (Cap_vt_bool A).
       simpl Cap_vt_bool.
       destruct (Cap_vt_bool B) eqn:E1.
       destruct (Cap_vt_bool C) eqn:E2.
       destruct H as [H1 H2].       
       rewrite ite_conv.
       rewrite fgt_conv.
       assert (H' : translate_vecType (cap B C) = 
                    (translate_vecType B) ++ (translate_vecType C)). 
       { simpl. rewrite E1, E2. easy. }
       rewrite H'.
       apply Heisenberg.cap_arrow.
       simpl in *. split.
       destruct H1. apply H.
       split. destruct H2. apply H.
       easy. 
       rewrite andb_false_r in H; easy. 
       rewrite andb_false_r in H; easy. 
       easy. 
Qed.



Lemma arrow_sub : forall {n} g (A A' B B' : vType n),
  Cap_vt A' -> Cap_vt B' ->
  (forall l, l ;' A' -> l ;' A) ->
  (forall r, r ;' B -> r ;' B') ->
  g :' A → B ->
  g :' A' → B'.
Proof. intros. simpl in *.
       unfold progHasSingType in *.
       unfold vecHasType in *.
       apply Cap_vt_conv in H.
       apply Cap_vt_conv in H0.
       destruct (Cap_vt_bool A);
       destruct (Cap_vt_bool B);
       destruct (Cap_vt_bool A');
       destruct (Cap_vt_bool B');
       try easy. 
       rewrite ite_conv in *.
       rewrite fgt_conv in *.
       apply (Heisenberg.arrow_sub _ (translate_vecType A) _ (translate_vecType B) _).
       apply H1.
       apply H2.
       apply H3.
Qed.



Hint Resolve cap_elim_l cap_elim_r cap_intro cap_arrow arrow_sub : subtype_db.

Lemma cap_elim : forall {n} g (A B : vType n), g :' A ∩ B -> g :' A /\ g :' B.
Proof. eauto with subtype_db. Qed.


(* Full explicit proof (due to changes to arrow_sub) *)
Lemma cap_arrow_distributes'' : forall {n} g (A A' B B' : vType n),
  g :' (A → A') ∩ (B → B') ->
  g :' (A ∩ B) → (A' ∩ B').
Proof.
  intros. simpl in H.
  unfold progHasSingType in H.
  destruct (Cap_vt_bool A) eqn:E1;
  destruct (Cap_vt_bool B) eqn:E2;
  destruct (Cap_vt_bool A') eqn:E3;
  destruct (Cap_vt_bool B') eqn:E4;
  try easy.
  destruct H as [H H0].
  rewrite ite_conv in H;
  rewrite ite_conv in H0.
  apply cap_arrow.
  apply cap_intro.
  - eapply arrow_sub; intros;
    repeat(try split; 
           try (apply Cap_vt_conv); 
           try assumption).
    + eapply cap_elim_l_vec. apply H1.
    + apply H1.
    + simpl; unfold progHasSingType. 
      rewrite E1, E3.
      rewrite ite_conv.
      assumption.
  - eapply arrow_sub; intros;
    repeat(try split; 
           try (apply Cap_vt_conv); 
           try assumption).
    + eapply cap_elim_r_vec. apply H1.
    + apply H1.
    + simpl; unfold progHasSingType. 
      rewrite E2, E4.
      rewrite ite_conv.
      assumption.
Qed.






(***************************************************)
(* Prelim lemmas for tensoring in the next section *)
(***************************************************)


Local Open Scope nat_scope. 

Notation s := Datatypes.S.


Definition smpl_prog_H (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = H' n).
Definition smpl_prog_S (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = S' n).

Definition smpl_prog_T (p : nat -> prog) : Prop := 
  (forall (n : nat), p n = T' n).
        
Definition smpl_prog (p : nat -> prog) : Prop := 
  smpl_prog_H p \/ smpl_prog_S p \/ smpl_prog_T p.


Definition ctrl_prog (p : prog) : Prop :=
  match p with 
  | CNOT _ _ => True 
  | _ => False
  end.


Lemma smpl_prog_H_ver : smpl_prog H'. Proof. left. easy. Qed.
Lemma smpl_prog_S_ver : smpl_prog S'. Proof. right. left. easy. Qed.
Lemma smpl_prog_T_ver : smpl_prog T'. Proof. right. right. easy. Qed.


Hint Resolve smpl_prog_H_ver smpl_prog_S_ver smpl_prog_T_ver : wfvt_db.




Lemma tensor_smpl_base : forall (prg_len : nat) (p : nat -> prog)
                           (a b : vType 1) (A : vType prg_len),
  WFS_vType a -> WFS_vType b -> 
  WFS_vType A -> 
  smpl_prog p -> 
  (p 0) :' a → b ->
  (p 0) :' a .⊗ A → b .⊗ A. 
Proof. intros. 
       destruct H; destruct H0; destruct H1.
       destruct a; destruct b; destruct A; try easy.
       simpl in *.
       unfold progHasSingType in *. 
       rewrite ite_conv in *.
       rewrite fgt_conv in *. 
       simpl translate_vecType in *.
       replace (s prg_len) with (1 + prg_len) by lia. 
       rewrite translate_kron, translate_kron; try easy. 
       destruct H2.
       - rewrite H2 in *.
         unfold translate_prog in *.
         simpl in *. 
         apply kill_true; destruct H3.
         apply sgt'_implies_sgt in H3; auto. 
         apply sgt_implies_sgt'; try easy. 
         unfold singGateType in *.
         intros. simpl in H3.
         simpl in H8; simpl in H9.
         destruct H8; destruct H9; try easy.
         unfold prog_smpl_app in *. 
         bdestruct_all.
         bdestruct (0 <? 1); try lia. 
         replace (1 - 0 - 1) with 0 in * by lia. 
         replace (2 ^ 0) with 1 in * by easy.
         replace (s prg_len - 0 - 1) with prg_len by lia. 
         rewrite kron_1_l, kron_1_r in *; auto with wf_db.
         rewrite <- H8, <- H9.
         restore_dims. 
         do 2 rewrite kron_mixed_product.
         replace (2^1) with 2 by easy. 
         rewrite (H3 (translate t) (translate t0)); auto. 
         rewrite Mmult_1_r, Mmult_1_l; try easy. 
         all : try (apply unit_TType; easy). 
         apply (unit_prog_smpl_app 1 _ 0); auto with unit_db. 
         split; simpl. 
         all : unfold uni_vecType; intros. 
         all : unfold In in H8; destruct H8; try easy; rewrite <- H8.
         apply unit_TType in H4; easy.
         apply unit_TType in H5; easy.
       - destruct H2. 
         + rewrite H2 in *.
         unfold translate_prog in *.
         simpl in *. 
         apply kill_true; destruct H3.
         apply sgt'_implies_sgt in H3; auto. 
         apply sgt_implies_sgt'; try easy. 
         unfold singGateType in *.
         intros. simpl in H3.
         simpl in H8; simpl in H9.
         destruct H8; destruct H9; try easy.
         unfold prog_smpl_app in *. 
         bdestruct_all.
         bdestruct (0 <? 1); try lia. 
         replace (1 - 0 - 1) with 0 in * by lia. 
         replace (2 ^ 0) with 1 in * by easy.
         replace (s prg_len - 0 - 1) with prg_len by lia. 
         rewrite kron_1_l, kron_1_r in *; auto with wf_db.
         rewrite <- H8, <- H9.
         restore_dims. 
         do 2 rewrite kron_mixed_product.
         replace (2^1) with 2 by easy. 
         rewrite (H3 (translate t) (translate t0)); auto. 
         rewrite Mmult_1_r, Mmult_1_l; try easy. 
         all : try (apply unit_TType; easy). 
         apply (unit_prog_smpl_app 1 _ 0); auto with unit_db. 
         split; simpl. 
         all : unfold uni_vecType; intros. 
         all : unfold In in H8; destruct H8; try easy; rewrite <- H8.
         apply unit_TType in H4; easy.
         apply unit_TType in H5; easy.
       + rewrite H2 in *.
         unfold translate_prog in *.
         simpl in *. 
         apply kill_true; destruct H3.
         apply sgt'_implies_sgt in H3; auto. 
         apply sgt_implies_sgt'; try easy. 
         unfold singGateType in *.
         intros. simpl in H3.
         simpl in H8; simpl in H9.
         destruct H8; destruct H9; try easy.
         unfold prog_smpl_app in *. 
         bdestruct_all.
         bdestruct (0 <? 1); try lia. 
         replace (1 - 0 - 1) with 0 in * by lia. 
         replace (2 ^ 0) with 1 in * by easy.
         replace (s prg_len - 0 - 1) with prg_len by lia. 
         rewrite kron_1_l, kron_1_r in *; auto with wf_db.
         rewrite <- H8, <- H9.
         restore_dims. 
         do 2 rewrite kron_mixed_product.
         replace (2^1) with 2 by easy. 
         rewrite (H3 (translate t) (translate t0)); auto. 
         rewrite Mmult_1_r, Mmult_1_l; try easy. 
         all : try (apply unit_TType; easy). 
         apply (unit_prog_smpl_app 1 _ 0); auto with unit_db. 
         split; simpl. 
         all : unfold uni_vecType; intros. 
         all : unfold In in H8; destruct H8; try easy; rewrite <- H8.
         apply unit_TType in H4; easy.
         apply unit_TType in H5; easy.
Qed.



Lemma tensor_smpl_inc : forall (prg_len bit : nat) (p : nat -> prog)
                          (a : vType 1) (A A' : vType prg_len),
  WFS_vType a ->
  WFS_vType A -> WFS_vType A' -> 
  smpl_prog p -> 
  (p bit) :' A → A' ->
  (p (s bit)) :' a .⊗ A → a .⊗ A'.
Proof. Admitted. 



Lemma tensor_ctrl_base : forall (prg_len : nat) 
                           (a b a' b' : vType 1) (A : vType prg_len),
  WFS_vType a -> WFS_vType a' -> WFS_vType b -> WFS_vType b' ->
  WFS_vType A ->
  CNOT 0 1 :' (a .⊗ b → a' .⊗ b') ->
  CNOT 0 1 :' (a .⊗ b .⊗ A → a' .⊗ b' .⊗ A).
Proof. Admitted. 


Lemma tensor_ctrl_base_inv :  forall (prg_len : nat)
                                (a b a' b' : vType 1) (A : vType prg_len),
  WFS_vType a -> WFS_vType a' -> WFS_vType b -> WFS_vType b' ->
  WFS_vType A ->
  CNOT 0 1 :' (b .⊗ a → b' .⊗ a') ->
  CNOT 1 0 :' (a .⊗ b .⊗ A → a' .⊗ b' .⊗ A).
Proof. Admitted. 

Lemma tensor_ctrl_inc : forall (prg_len ctrl targ : nat) 
                          (a : vType 1) (A A' : vType prg_len),
  WFS_vType a -> 
  WFS_vType A -> WFS_vType A' ->
  CNOT ctrl targ :' (A → A') ->
  CNOT (s ctrl) (s targ) :' a .⊗ A → a .⊗ A'.
Proof. Admitted.


Lemma tensor_ctrl_inc_l : forall (prg_len ctrl : nat) 
                            (a a' b : vType 1) (A A' : vType prg_len),
  WFS_vType a -> WFS_vType a' -> WFS_vType b ->  
  WFS_vType A -> WFS_vType A' ->
  CNOT ctrl 0 :' (a .⊗ A → a' .⊗ A') ->
  CNOT (s ctrl) 0 :' a .⊗ b .⊗ A → a' .⊗ b .⊗ A'.
Proof. Admitted.


Lemma tensor_ctrl_inc_r : forall (prg_len targ : nat) 
                            (a a' b : vType 1) (A A' : vType prg_len),
  WFS_vType a -> WFS_vType a' -> WFS_vType b ->  
  WFS_vType A -> WFS_vType A' ->
  CNOT 0 targ :' (a .⊗ A → a' .⊗ A') ->
  CNOT 0 (s targ) :' a .⊗ b .⊗ A → a' .⊗ b .⊗ A'.
Proof. Admitted.


(* For flipping CNOTs. *)
Lemma tensor_ctrl_comm : forall (a b a' b' : vType 1),
  WFS_vType a -> WFS_vType a' -> WFS_vType b -> WFS_vType b' ->
  CNOT 0 1 :' a .⊗ b → a' .⊗ b' ->
  CNOT 1 0 :' b .⊗ a → b' .⊗ a'.
Proof. Admitted.

(***************)
(* Arrow rules *)
(***************)


Lemma arrow_mul : forall {n} g (A A' B B' : vType n),
    WFS_vType A -> WFS_vType A' ->
    WFS_vType B -> WFS_vType B' ->
    g :' A → A' ->
    g :' B → B' ->
    g :' A .* B → A' .* B'.
Proof. intros; simpl in *.
       assert (H' : Sing_vt A). { apply H. }
       assert (H0' : Sing_vt B). { apply H1. }
       assert (H1' : Sing_vt A'). { apply H0. }
       assert (H2' : Sing_vt B'). { apply H2. } 
       apply sing_vt_simplify in H'; destruct H';
       apply sing_vt_simplify in H0'; destruct H0';
       apply sing_vt_simplify in H1'; destruct H1';
       apply sing_vt_simplify in H2'; destruct H2'; try easy.
       unfold progHasSingType in *. 
       rewrite H5, H6, H7, H8 in *.
       simpl Cap_vt_bool in *. 
       rewrite ite_conv in *.
       rewrite translate_vecType_mMult; try easy.
       rewrite translate_vecType_mMult; try easy.
       rewrite fgt_conv.
       apply Heisenberg.arrow_mul; 
       try (apply unit_prog);
       try (apply unit_vType); try easy.
       apply H. apply H0. apply H1. apply H2.
Qed. 
  

Lemma mul_simp : forall (a b : Pauli),
  G 1 (gMul_Coef a b, [gMul_base a b]) = G 1 (p_1, [a]) .* G 1 (p_1, [b]). 
Proof. intros. 
       simpl. 
       destruct a; destruct b; try easy. 
Qed.


Lemma arrow_mul_1 : forall g (a a' b b' : Pauli),
    g :' G 1 (p_1, [a]) → G 1 (p_1, [a']) ->
    g :' G 1 (p_1, [b]) → G 1 (p_1, [b']) ->
    g :' G 1 (gMul_Coef a b, [gMul_base a b]) → G 1 (gMul_Coef a' b', [gMul_base a' b']).
Proof. intros. 
       do 2 rewrite mul_simp. 
       apply arrow_mul; easy.
Qed.



Lemma arrow_scale : forall {n} (p : prog) (A A' : vType n) (c : Coef),
  p :' A → A' -> p :' (scale c A) → (scale c A').
Proof. intros. simpl in *. 
       unfold progHasSingType in *.
       do 2 (rewrite Cap_vt_scale).
       destruct (Cap_vt_bool A && Cap_vt_bool A'); try easy.
       rewrite fgt_conv in *.
       do 2 (rewrite translate_vecType_scale).
       apply Heisenberg.arrow_scale.
       destruct c; try simpl; try nonzero.
       apply C0_fst_neq. unfold Copp. 
       simpl. lra. 
       apply C0_snd_neq. unfold Copp.
       simpl. lra. apply H.
Qed.


Lemma arrow_i : forall {n} (p : prog) (A A' : vType n),
  p :' A → A' ->
  p :' i A → i A'.
Proof. intros;
       apply arrow_scale;
       assumption.
Qed.


Lemma arrow_neg : forall {n} (p : prog) (A A' : vType n),
  p :' A → A' ->
  p :' -A → -A'.
Proof. intros;
       apply arrow_scale;
       assumption.
Qed.



Hint Resolve HTypes STypes TTypes CNOTTypes : base_types_db.
Hint Resolve cap_elim_l cap_elim_r : base_types_db.

Hint Resolve HTypes STypes TTypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve SeqTypes : typing_db.



(* basically just eq_type_conv_output but with different order hypotheses *)
Lemma eq_arrow_r : forall {n} (g : prog) (A B B' : vType n),
    g :' A → B ->
    B = B' ->
    g :' A → B'.
Proof. intros. subst; easy. Qed.

(* Tactics *)


Ltac is_I A :=
  match A with
  | I => idtac 
  end.

Ltac is_prog1 A :=
 match A with 
  | H' _ => idtac
  | S' _ => idtac
  | T' _ => idtac
  end.
              
Ltac is_prog2 A :=
  match A with
  | CNOT _ _ => idtac
  end.



Ltac expand_prog := match goal with
                    | |- ?p1 ;; ?p2 :' ?T => eapply SeqTypes
                    end.

(* Reduces to sequence of H, S and CNOT *)
Ltac type_check_base :=
  repeat apply cap_intro;
  repeat expand_prog; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end; auto with wfvt_db; try easy.



Lemma CZTypes : CZ 0 1 :' (X .⊗ I → X .⊗ Z) ∩ (I .⊗ X → Z .⊗ X) ∩
                          (Z .⊗ I → Z .⊗ I) ∩ (I .⊗ Z → I .⊗ Z).
Proof. type_check_base.   
Qed.




Notation bell00 := ((H' 2);; (CNOT 2 3)).

Notation encode := ((CZ 0 2);; (CNOT 1 2)).

Notation decode := ((CNOT 2 3);; (H' 2)).

Notation superdense := (bell00;; encode;; decode).


Check Heisenberg.S'.




Lemma superdenseTypesQPL : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog.
       type_check_base.
       type_check_base.
       type_check_base.
       rewrite mul_tensor_dist; auto with wfvt_db.
       type_check_base.
       type_check_base.
       type_check_base.
       type_check_base.
       type_check_base.
Qed.


       rewrite mul_tensor_dist; auto with wfvt_db.



match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.
6 : match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.


6 : match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => tryif is_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.
       type_check_base. easy. 
       6 : {  rewrite mul_tensor_dist; auto with wfvt_db.
               rewrite mul_tensor_dist; auto with wfvt_db.
match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => try easy
         end.

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => idtac 4
                                           end.


rewrite decompose_tensor_mult_r.
             apply arrow_mul; type_check_base.
       3 : {


match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) -> _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => try easy
         end.

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- WFS_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A .⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => rewrite decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) -> _ => rewrite decompose_tensor_mult_r
         | |- CNOT (s _) (s _) :' ?T => apply tensor_ctrl_inc
         | |- CNOT 0 (s (s _)) :' ?T => apply tensor_ctrl_inc_r
         | |- CNOT (s (s _)) 0 :' ?T => apply tensor_ctrl_inc_l
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_base_inv
         | |- CNOT 0 1 :' ?T       => apply tensor_ctrl_base
         | |- CNOT 1 0 :' ?T       => apply tensor_ctrl_comm
         | |- H' (s _) :' ?T     => apply tensor_smpl_inc
         | |- H' 0 :' ?T         => apply tensor_smpl_base
         | |- S' (s _) :' ?T     => apply tensor_smpl_inc
         | |- S' 0 :' ?T         => apply tensor_smpl_base
         | |- T' (s _) :' ?T     => apply tensor_smpl_inc
         | |- T' 0 :' ?T         => apply tensor_smpl_base
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         | |- ?g :' ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?A = ?B => try easy
         end.

       3 : {

         match goal with
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with wfvt_db)
         end; auto with wfvt_db; try easy.


       type_check_base'.       
       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.
       kill_switch2.


       repeat (repeat (rewrite switch_vType_inc; auto with gt_db); 
         try rewrite switch_vType_base; try rewrite switch_vType_base_one;
           auto with gt_db).





       
       kill_

       
       type_check_base'.
       type_check_base'.
       


apply evSuper_ev; auto 50 with wfvt_db.
       unfold eq_vType; simpl.
       apply hd_inj; unfold uncurry; simpl. 
       apply TType_compare; auto; simpl.
       repeat (split; try lma').
       unfold translate






       

Check hd_inj.

       repeat (apply wfs_switch_vType'; auto 50 with wfvt_db).
       apply wfs_switch_vType'; auto 50 with wfvt_db.
       apply wfs_switch_vType'; auto with wfvt_db.


3 : {
         unfold eq_vType. simpl. 
         unfold translate. simpl. 
         unfold translate_vecType


       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.      
       type_check_base'.
       type_check_base'.
       type_check_base'.

rewrite mul_tensor_dist; auto with wfvt_db.
             easy. 

type_check_base'.
       type_check_base'.
       3 : { rewrite mul_compat.
              try rewrite mul_tensor_dist;
              try easy; auto with wfvt_db.


pushA. 
       all : auto with gt_db.
       type_check_base'.
       type_check_base'.
       all : try pushA. 
       all : try pushA. 
       
        3 :  { pushA. 
               3 : pushA.
               all : auto with wfvt_db. }
        all : auto with gt_db.
        type_check_base'.
        3 : { pushA rewrite mul_compat;
             try rewrite mul_tensor_dist;
             try easy; auto with wfvt_db. 
              3 : { rewrite mul_compat;
                    try rewrite mul_tensor_dist;
                    try easy; auto with wfvt_db. 
                    3 : rewrite mul_compat;
                      try rewrite mul_tensor_dist;
                      try easy; auto with wfvt_db. 
                    all : auto with wfvt_db. }
              all : auto with wfvt_db. }
        all : auto with gt_db.
        type_check_base'.
        unfold eq_vType.
        simpl switch_vType'.
        unfold translate. simpl.
        apply hd_inj.
        crunch_matrix.
try easy.

       type_check_base'.

       2 : { simp_switch.


rewrite nth_vswitch_hit. try easy; try lia; auto with gt_db).
  repeat (rewrite nth_vswitch_miss; try easy; try lia; auto with gt_db). 

match goal with
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?n) → _ => 
                rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db 
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?m) → _ => 
                rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db
end.
match goal with
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?n) → _ => 
                rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db 
         | |- ?g :' nth_vType ?n (switch_vType' _ _ ?m) → _ => 
                rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db
end.



nth_vType bit (switch_vType' A a bit) = a.


       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗



       econstructor; reflexivity.


       rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db.
       rewrite nth_vswitch_hit; [| nia | | |]. try easy; try nia; auto with gt_db. 
       


rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db. 


       simpl nth_vType.
       apply arrow_mul_1.
       solve [eauto with base_types_db].  
       solve [eauto with base_types_db].
       eapply tensor_ctrl. 
       simpl nth_vType. 
       type_check_base'.

       2 : { simp_switch.


solve [eauto with base_types_db].  type_check_base'. }
       all : try type_check_base'
 try rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db; 
         try rewrite nth_vswitch_hit; try easy; try nia; auto with gt_db. 
       2 : { type_check_base'. }
       type_check_base'.

       type_check_base'.


       3 : {  rewrite mul_tensor_dist. easy. 


       type_check_base.

       simpl nth_vType. 
       assert (H : G 1 (p_1, [gMul gX gZ]) = X .* Z). 
       { easy. }
       rewrite H.
       type_check_base.
       eapply tensor_ctrl.
       apply prog_decompose_tensor; auto with wfvt_db.
       eapply eq_arrow_r.
       apply arrow_mul; auto with wfvt_db; try solve [eauto with base_types_db].
       5 : { simpl nth_vType.

       type_check_base.

repeat match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end; auto with wfvt_db.





       match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.
match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.



match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end; auto with wfvt_db.
 

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end;

try match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end; 

match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.  easy.
 

match goal with
         | |- Sing_vt _       => tryif is_evar A then fail else auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl
         | |- H' (S ?n) :' ?T => eapply tensor_smpl; auto with wfvt_db
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.

        type_check_base.


Lemma superdenseTypesQPL' : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog.
       type_check_base'.
       
       eapply tensor_ctrl'; try (apply prog_decompose_tensor); try easy;
         try (eapply eq_arrow_r; apply arrow_mul; try (solve [eauto with base_types_db])).
       
       3: { eapply eq_arrow_r. apply arrow_mul; try (solve [eauto with base_types_db]);
                                 try (auto with wfvt_db).
         rewrite mul_tensor_dist; 
         auto with wfvt_db; easy. }
         auto with gt_db.
       auto with gt_db.
         
         eapply tensor_smpl.
         simpl. easy.
         auto with wfvt_db.
         rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db. 
         rewrite nth_vswitch_hit; try easy; try nia; auto with gt_db. 
         eapply eq_arrow_r.
         apply arrow_mul; try (solve [eauto with base_types_db]); try (auto with wfvt_db).
         easy. 
         solve [eauto with base_types_db].
         9: { solve [eauto with base_types_db]. }

Lemma superdenseTypesQPL' : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog.
       type_check_base'.
       
       eapply tensor_ctrl'; try (apply prog_decompose_tensor); try easy;
         try (eapply eq_arrow_r; apply arrow_mul; try (solve [eauto with base_types_db])).
       
       3: { eapply eq_arrow_r. apply arrow_mul; try (solve [eauto with base_types_db]);
                                 try (auto with wfvt_db).
         rewrite mul_tensor_dist; 
         auto with wfvt_db; easy. }
         auto with gt_db.
       auto with gt_db.
         
         eapply tensor_smpl.
         simpl. easy.
         auto with wfvt_db.
         rewrite nth_vswitch_miss; try easy; try nia; auto with gt_db. 
         rewrite nth_vswitch_hit; try easy; try nia; auto with gt_db. 
         eapply eq_arrow_r.
         apply arrow_mul; try (solve [eauto with base_types_db]); try (auto with wfvt_db).
         easy. 
         solve [eauto with base_types_db].
         9: { solve [eauto with base_types_db]. }


       
  repeat expand_prog.
  repeat match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply (tensor_ctrl (S n) m _ _ _) 
         | |- ?g (S ?n) :' ?T => eapply (tensor_smpl (S n) _ _ _)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.
  eapply (tensor_ctrl 2 3 _ _ _). 
 match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply (tensor_ctrl (S n) m _ _ _) 
         | |- ?g (S ?n) :' ?T => idtac 4
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.








repeat apply cap_intro;
  repeat expand_prog; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Sing_vt _       => auto 50 with svt_db
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r
         | |- ?g :' - ?A → ?B    => apply arrow_neg
         | |- ?g :' i ?A → ?B    => apply arrow_i
         | |- context[?A ⊗ ?B]  => progress (autorewrite with tensor_db)
         | |- ?g :' ?A → ?B      => tryif is_evar B then fail else eapply eq_arrow_r 
         | |- ?g 0 1 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI2)); 
             solve [eauto with base_types_db]
         | |- ?g 0 :' ?A → ?B => tryif is_evar A then fail else
             (try (eapply TypesI)); 
             solve [eauto with base_types_db]
         | |- ?g (S ?n) ?m :' ?T => eapply (tensor_ctrl (S n) m _ _ _) 
         | |- ?g (S ?n) :' ?T => eapply (tensor_smpl (S n) _ _ _)
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try easy
         end.


repeat match goal with
              | |- ?p1 ;; ?p2 :' ?T => eapply SeqTypes
              end.
       eapply (tensor_smpl 2 _ _ _).
       solve [eauto with base_types_db]. 
       eapply (tensor_ctrl 4 2 3 _ _ _).
       simpl nth_vType.
       apply prog_decompose_tensor; try easy.
       eapply eq_arrow_r.
       apply arrow_mul; 
         try (solve [eauto with base_types_db]);
         try easy.
       rewrite mul_tensor_dist; try easy.
       eapply (tensor_ctrl 2 _ _ _).
       simpl. 
       solve [eauto with base_types_db]. 



reflexivity. 
try easy.
       5: { solve [eauto with base_types_db]. }
       5: { solve [eauto with base_types_db]. }
       



    auto with univ_db.
       auto with univ_db.
       nia. 
       easy. 
       eapply (tensor_ctrl 4 2 3 _ _ _).
       rewrite CX_is_CNOT.
       rewrite decompose_tensor.
       eapply eq_arrow_r.
       apply arrow_mul.
       auto with sing_db.
       auto with sing_db.
       auto with unit_db.
       auto with univ_db.
       4: { solve [eauto with base_types_db]. }
       auto with univ_db.
       auto with univ_db.



emma prog_decompose_tensor : forall (p : prog) (A B : vType 1) (T : vType 2),
  Sing_vt A -> WF_vType A ->
  Sing_vt B -> WF_vType B ->
  p :' ((A .⊗ I) .* (I .⊗ B)) → T -> p :' (A .⊗ B) → T.
Proof. intros. 
       apply (eq_type_conv_input p ((A .⊗ I) .* (I .⊗ B)) (A .⊗ B) T); try easy.
       rewrite <- decompose_tensor; easy.
Qed.


       
       rewrite decompose_tensor.
       eapply eq_arrow_r.
       apply arrow_mul.
       auto with sing_db.
       auto with sing_db.
       auto with unit_db.
       auto with univ_db.



       assert (H : G 1 (p_1, [gX]) = X). { easy. }
       assert (H' : G 1 (p_1, [gZ]) = Z). { easy. }
       rewrite H, H'.
                                         

solve [eauto with base_types_db]. }
       auto with univ_db.
       auto with univ_db.
       2: { solve [eauto with base_types_db]. }
       auto with univ_db.
       rewrite mul_tensor_dist.
       reflexivity.
       auto with sing_db.
       auto with sing_db.
       auto with sing_db.
       auto with sing_db.
       eapply (tensor_ctrl 4 0 2 _ _ _).
       rewrite decompose_tensor.
       eapply eq_arrow_r.


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



Fixpoint zipWith {X : Type} (f : X -> X -> X) (As Bs : list X) : list X :=
  match As with 
  | [] => Bs
  | a :: As' => 
    match Bs with
    | [] => As
    | b :: Bs' => f a b :: zipWith f As' Bs'
    end
  end.  


Lemma zipWith_len_pres : forall {X : Type} (f : X -> X -> X) (n : nat) 
                                (As : list X) (Bs : list X),
  length As = n -> length Bs = n -> length (zipWith f As Bs) = n.
Proof. induction n as [| n'].
       - intros. 
         destruct As; destruct Bs; easy. 
       - intros. 
         destruct As; destruct Bs; try easy.
         simpl in *.
         apply Nat.succ_inj in H; apply Nat.succ_inj in H0.
         rewrite IHn'; easy. 
Qed.


Lemma zipWith_app_product : forall {X : Type} (f : X -> X -> X) (n : nat) 
                               (l0s l2s : list X) (l1s l3s : list X),
  length l0s = n -> length l1s = n -> 
  (zipWith f l0s l1s) ++ (zipWith f l2s l3s) = zipWith f (l0s ++ l2s) (l1s ++ l3s).
Proof. induction n as [| n'].
       - intros. destruct l0s; destruct l1s; easy. 
       - intros. destruct l0s; destruct l1s; try easy.
         unfold zipWith in *.
         simpl in *. 
         rewrite <- IHn'; try nia. 
         reflexivity. 
Qed.
