Require Import Psatz.
Require Import Reals.


Require Export Complex.
Require Export Matrix.
Require Export Quantum.
Require Export Eigenvectors.
Require Export Heisenberg. 



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


Inductive GType :=
| gI
| gX
| gZ
| gIm : GType -> GType
| gNeg : GType -> GType
| gMul : GType -> GType -> GType.


Fixpoint translate_gt (g : GType) : Square 2 :=
  match g with
  | gI => I 2
  | gX => σx
  | gZ => σz
  | gIm g => Ci .* (translate_gt g)
  | gNeg g => (Copp C1) .* (translate_gt g)
  | gMul g1 g2 => (translate_gt g1) × (translate_gt g2)
  end. 


Lemma WF_Matrix_GType : forall (g : GType), WF_Matrix (translate_gt g).
Proof. intros. induction g as [| | | | |];  
       simpl; auto with wf_db.
Qed.


Definition GTypeT (len : nat) := (Coef * (list GType))%type. 


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

Definition gScaleT {n} (c : Coef) (A : GTypeT n) : GTypeT n :=
  match A with
  | (c1, g1) => (c * c1, g1)
  end.


Definition translate {n} (A : GTypeT n) : Square (2^n) := 
  (translate_coef (fst A)) .* ⨂ (map translate_gt (snd A)).
  


Inductive vType (n : nat) : Type :=
  | G : GTypeT n -> vType n
  | Cap : vType n -> vType n -> vType n
  | Arrow : vType n -> vType n -> vType n
  | Err : vType n.



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
       - exists g. reflexivity. 
Qed. 


Definition I : vType 1 := G 1 (p_1, [gI]).
Definition X : vType 1 := G 1 (p_1, [gX]).
Definition Z : vType 1 := G 1 (p_1, [gZ]).

Lemma Itrans : translate_vecType I = I'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l. 
       rewrite kron_1_r. 
       reflexivity. 
Qed.

Lemma Xtrans : translate_vecType X = X'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l. 
       rewrite kron_1_r. 
       reflexivity. 
Qed.

Lemma Ztrans : translate_vecType Z = Z'.
Proof. simpl. 
       unfold translate; simpl. 
       rewrite Mscale_1_l. 
       rewrite kron_1_r. 
       reflexivity. 
Qed.

Notation Y := (i (X .* Z)).



(***************)
(* Sing Lemmas *)
(***************)

Lemma SI : Sing_vt I. Proof. easy. Qed.
Lemma SX : Sing_vt X. Proof. easy. Qed.
Lemma SZ : Sing_vt Z. Proof. easy. Qed.

Lemma S_neg : forall {n} (A : vType n), Sing_vt A -> Sing_vt (- A).
Proof. intros. destruct A; easy. Qed. 
 
Lemma S_i : forall {n} (A : vType n), Sing_vt A -> Sing_vt (i A).
Proof. intros. destruct A; easy. Qed. 

Lemma S_mul : forall {n} (A B : vType n), Sing_vt A -> Sing_vt B -> Sing_vt (A .* B).
Proof. intros.
       destruct A; destruct B; easy.
Qed.


Hint Resolve SI SX SZ S_neg S_i S_mul : svt_db.

Lemma SY : Sing_vt Y.
Proof. auto with svt_db. Qed.




(**************************)
(* Well Formedness Lemmas *)
(**************************)


Definition WF_GTypeT {len : nat} (gtt : GTypeT len) := length (snd gtt) = len.

Fixpoint WF_vType {n} (A : vType n) : Prop :=
  match A with
  | G _ a => WF_GTypeT a
  | Cap _ a1 a2 => WF_vType a1 /\ WF_vType a2
  | Arrow _ a1 a2 => WF_vType a1 /\ WF_vType a2
  | _ => False
  end.

Lemma WF_I : WF_vType I. Proof. easy. Qed.
Lemma WF_X : WF_vType X. Proof. easy. Qed.
Lemma WF_Z : WF_vType Z. Proof. easy. Qed.


Lemma WF_mul : forall {n} (A B : vType n),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B -> 
  WF_vType (A .* B). 
Proof. intros. 
       destruct A;
       destruct B; try easy.
       destruct g;
       destruct g0.
       apply zip_len_pres;
       assumption.
Qed.


Lemma WF_tensor : forall {n m} (A : vType n) (B : vType m),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B ->
  WF_vType (A .⊗ B). 
Proof. intros. 
       destruct A;
       destruct B; try easy.
       destruct g;
       destruct g0.
       simpl in *. 
       unfold WF_GTypeT in *.
       simpl in *.
       rewrite app_length;
       nia. 
Qed.


Lemma WF_neg : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (- A). 
Proof. intros. 
       destruct A; try easy.
       destruct g; easy.
Qed.
   
Lemma WF_i : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (i A). 
Proof. intros. 
       destruct A; try easy.
       destruct g; easy.
Qed.


Hint Resolve SI SX SZ WF_I WF_X WF_Z WF_mul WF_tensor WF_neg WF_i : wfvt_db.


Lemma WF_Y : WF_vType Y.
Proof. auto with wfvt_db. Qed.


Lemma WF_Matrix_GTypeT : forall {n} (A : GTypeT n), WF_GTypeT A -> WF_Matrix (translate A). 
Proof. intros. destruct A.
       destruct l as [| h].
       - unfold translate; simpl.
         rewrite <- H.
         auto with wf_db.          
        - unfold translate; simpl. 
          assert (H' : forall n, (2^n + (2^n +0) = 2^ (S n))%nat). { simpl. nia. }
          rewrite H'.      
          rewrite map_length.
          unfold WF_GTypeT in H; simpl in H. 
          rewrite H.
          apply WF_scale.
          apply WF_kron;
          try (rewrite <- H);
          try simpl; try nia. 
          apply WF_Matrix_GType.
          rewrite <- (map_length translate_gt _).
          apply (WF_big_kron _ _ (map translate_gt l) (translate_gt gI)).
          intros. 
          rewrite map_nth.
          apply WF_Matrix_GType. 
Qed.

(******************)
(* unitary lemmas *)
(******************)

Lemma unit_GType : forall (g : GType), unitary (translate_gt g).
Proof. intros. induction g as [| | | | |]; 
       simpl; auto with unit_db;
       repeat 
       (try (apply unit_scale);
        try (apply IHg);
        try lca).
Qed.


Lemma unit_GTypeT : forall {n} (A : GTypeT n), WF_GTypeT A -> unitary (translate A). 
Proof. intros. destruct A.
       destruct l as [| h].
       - unfold translate; simpl. 
         unfold WF_GTypeT in H; simpl in H.
         rewrite <- H.
         apply unit_scale. 
         auto with unit_db.
         destruct c; lca.          
        - unfold translate; simpl. 
          assert (H' : forall n, (2^n + (2^n +0) = 2^ (S n))%nat). { simpl. nia. }
          rewrite H'.      
          rewrite map_length.
          unfold WF_GTypeT in H; simpl in H.
          rewrite <- H.
          apply unit_scale.
          apply unit_kron. 
          apply unit_GType. 
          rewrite <- (map_length translate_gt _).
          apply (unit_big_kron 2 (map translate_gt l)).
          intros. 
          apply in_map_iff in H0.
          do 2 (destruct H0).
          rewrite <- H0.
          apply unit_GType.
          destruct c; lca.      
Qed.


Lemma unit_vType : forall {n} (A : vType n), 
    WF_vType A -> uni_vecType (translate_vecType A).
Proof. intros. 
       induction A as [| | |]; try easy. 
       - simpl; unfold uni_vecType. 
         intros A [H0 | F]; try easy. 
         rewrite <- H0, <- H.   
         apply unit_GTypeT.
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



Lemma translate_gt_Mmult : forall {n} (l1 l2 : list GType),
  length l1 = n -> length l2 = n ->
  ⨂ map translate_gt (zip gMul l1 l2) = 
  @Mmult (2^n) (2^n) (2^n) (⨂ map translate_gt l1) (⨂ map translate_gt l2). 
Proof. induction n as [| n'].
       - intros.
         destruct l1; destruct l2; try easy.
         simpl. lma'.
       - intros. 
         destruct l1; destruct l2; try easy.
         simpl in *.
         assert (H' : forall n m, S n = S m -> n = m). { nia. }
         apply H' in H; apply H' in H0.
         rewrite map_length.
         rewrite (zip_len_pres _ n' _ _).
         assert (H'' : forall n, (2^n + (2^n + 0) = 2*2^n)%nat). { nia. }
         rewrite H''.
         do 2 (rewrite map_length).
         rewrite H, H0 in *.
         rewrite kron_mixed_product.
         rewrite IHn'; try easy. 
         easy. easy.
Qed.


Lemma translate_Mmult : forall {n} (g1 g2 : GTypeT n),
    length (snd g1) = n -> length (snd g2) = n ->
    translate (gMulT g1 g2) = (translate g1) × (translate g2).
Proof. intros. unfold translate.
         destruct g1; destruct g2.
         simpl in *.
         do 3 (rewrite map_length). 
         unfold WF_GTypeT in *.
         rewrite H, H0 in *.
         rewrite (zip_len_pres _ n _ _); try easy.
         distribute_scale.
         rewrite translate_gt_Mmult.
         rewrite translate_coef_cMul.
         distribute_scale.
         rewrite Cmult_comm.
         rewrite <- Mscale_assoc.
         rewrite Mscale_mult_dist_l.
         rewrite map_length. 
         rewrite (zip_len_pres _ n _ _); try easy.
         rewrite map_length.
         rewrite (zip_len_pres _ n _ _); try (rewrite H1); try easy.
         rewrite map_length.
         rewrite (zip_len_pres _ n _ _); try (rewrite H1); try easy.
Qed.



Lemma translate_vecType_mMult : forall {n} (A B : vType n),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B -> 
  translate_vecType (A .* B) = (translate_vecType A) *' (translate_vecType B).
Proof. intros. 
       destruct A; try easy.
       destruct B; try easy.
       simpl.
       rewrite translate_Mmult.
       reflexivity. 
       unfold WF_vType in *; unfold WF_GTypeT in *.
       destruct g; destruct g0;
       simpl in *. easy. easy.
Qed.



Lemma translate_kron : forall {n m} (g1 : GTypeT n) (g2 : GTypeT m),
    length (snd g1) = n -> length (snd g2) = m ->
    translate (gTensorT g1 g2) = (translate g1) ⊗ (translate g2).
Proof. intros. unfold translate.
         destruct g1; destruct g2.
         simpl in *.
         do 3 (rewrite map_length). 
         unfold WF_GTypeT in *.
         rewrite H, H0 in *.
         rewrite Mscale_kron_dist_r.
         rewrite Mscale_kron_dist_l.
         rewrite Mscale_assoc.
         rewrite translate_coef_cMul.
         rewrite Cmult_comm.
         rewrite map_app.
         rewrite big_kron_app.
         do 2 (rewrite map_length).
         rewrite app_length.
         rewrite H, H0 in *.
         reflexivity.
Qed.



Lemma translate_scale : forall {n} (A : GTypeT n) (c : Coef),
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

Local Open Scope nat_scope. 

Lemma translate_gt_mul_assoc : forall (n : nat) (A B C : list GType),
  length A < n -> length B < n -> length C < n ->
  map translate_gt (zip gMul A (zip gMul B C)) =
  map translate_gt (zip gMul (zip gMul A B) C).
Proof. induction n as [| n']. 
       - easy.
       - intros. 
         destruct A; destruct B; destruct C; try easy.
         simpl in *.
         rewrite Mmult_assoc, IHn'; try nia; try easy.
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



(********************************************************************************************)
(* Defining looser notion of vType equality which will allow us to prove mult, tensor props *)
(********************************************************************************************)


Definition eq_vType {n} (T1 T2 : vType n) := 
  translate_vecType T1 = translate_vecType T2.

(* looser def for when dims do not align *) 
Definition eq_vType' {n m} (T1 : vType n) (T2 : vType m) := 
  translate_vecType T1 = translate_vecType T2.


Infix "≡" := eq_vType (at level 70, no associativity).

(* will now show this is an equivalence relation *)
Lemma eq_vType_refl : forall {n} (A : vType n), A ≡ A.
Proof. intros n A. easy.
Qed.

Lemma eq_vType_sym : forall {n} (A B : vType n), A ≡ B -> B ≡ A.
Proof. intros n A B H. easy. 
Qed.

Lemma eq_vType_trans : forall {n} (A B C : vType n),
    A ≡ B -> B ≡ C -> A ≡ C.
Proof.
  intros n A B C HAB HBC.
  unfold eq_vType in *.
  rewrite HAB; assumption. 
Qed.


Add Parametric Relation n : (vType n) (@eq_vType n)
  reflexivity proved by eq_vType_refl
  symmetry proved by eq_vType_sym
  transitivity proved by eq_vType_trans
    as eq_vType_rel.



Lemma hd_inj : forall (X : Type) (a b : X), [a] = [b] <-> a = b.
Proof. split. intros. 
       assert (H' : forall (X : Type) (a : X), [] ++ [a] = [a]). { easy. }  
       rewrite <- H' in H.
       rewrite <- (H' _ b) in H.
       apply app_inj_tail in H.
       easy.
       intros. 
       rewrite H; easy.
Qed.




Lemma mul_compat : forall {n} (A A' B B' : vType n),
    Sing_vt A -> Sing_vt A' ->
    Sing_vt B -> Sing_vt B' ->
    WF_vType A -> WF_vType A' ->
    WF_vType B -> WF_vType B' ->  
    A ≡ A' -> B ≡ B' -> A .* B ≡ A' .* B'.
Proof.
  intros. unfold eq_vType in *.
  destruct A; destruct A'; destruct B; destruct B'; try easy.
  simpl in *. unfold WF_GTypeT in *.
  rewrite translate_Mmult; try easy.
  rewrite translate_Mmult; try easy.
  apply -> hd_inj in H7.
  apply -> hd_inj in H8.
  rewrite H7, H8.
  reflexivity.
Qed.


Lemma kron_compat : forall (n m : nat) (A A' : vType n) (B B' : vType m),
    Sing_vt A -> Sing_vt A' ->
    Sing_vt B -> Sing_vt B' ->
    WF_vType A -> WF_vType A' ->
    WF_vType B -> WF_vType B' ->  
    A ≡ A' -> B ≡ B' -> A .⊗ B ≡ A' .⊗ B'.
Proof.
  intros. unfold eq_vType in *.
  destruct A; destruct A'; destruct B; destruct B'; try easy.
  simpl in *. unfold WF_GTypeT in *.
  rewrite translate_kron; try easy.
  rewrite translate_kron; try easy.
  apply -> hd_inj in H7.
  apply -> hd_inj in H8.
  rewrite H7, H8.
  reflexivity.
Qed.



Lemma Cap_vt_bool_nempty : forall {n} (A : vType n),
  Cap_vt_bool A = true <-> translate_vecType A <> [].
Proof. split. 
       - induction A as [| | |]; try easy.
         intros; simpl in *.
         destruct (Cap_vt_bool A1);
         destruct (Cap_vt_bool A2);
         try easy. simpl in *.
         destruct (translate_vecType A1);
         destruct (translate_vecType A2);
         try easy. 
         apply IHA1 in H; easy.
       - destruct (Cap_vt_bool A) eqn:E; try easy.
         destruct A; try easy.
         simpl in *. rewrite E.
         easy. 
Qed.


Lemma eq_vType_cap_vt_bool : forall {n} (A A' : vType n),
  A ≡ A' -> Cap_vt_bool A = Cap_vt_bool A'.
Proof. destruct A;
       destruct A'; 
       try easy; 
       intros; unfold eq_vType in H; simpl in *.  
       - destruct (Cap_vt_bool A'1);
         destruct (Cap_vt_bool A'2);
         try easy.
       - destruct (Cap_vt_bool A1);
         destruct (Cap_vt_bool A2);
         try easy.
       - destruct (Cap_vt_bool A1) eqn:E1;
         destruct (Cap_vt_bool A2) eqn:E2; 
         destruct (Cap_vt_bool A'1) eqn:E3;
         destruct (Cap_vt_bool A'2) eqn:E4;
         try easy; 
         try (simpl in *;
              apply Cap_vt_bool_nempty in E1;
              destruct (translate_vecType A1); easy); 
         try (simpl in *;
              apply Cap_vt_bool_nempty in E3;
              destruct (translate_vecType A'1); easy).
       - destruct (Cap_vt_bool A1) eqn:E;
         destruct (Cap_vt_bool A2);
         try easy.
         simpl in *.
         apply Cap_vt_bool_nempty in E;
         destruct (translate_vecType A1); try easy.
       - destruct (Cap_vt_bool A1) eqn:E;
         destruct (Cap_vt_bool A2);
         try easy.
         simpl in *.
         apply Cap_vt_bool_nempty in E;
         destruct (translate_vecType A1); try easy. 
       - destruct (Cap_vt_bool A'1) eqn:E;
         destruct (Cap_vt_bool A'2);
         try easy.
         simpl in *.
         apply Cap_vt_bool_nempty in E;
         destruct (translate_vecType A'1); try easy. 
       - destruct (Cap_vt_bool A'1) eqn:E;
         destruct (Cap_vt_bool A'2);
         try easy.
         simpl in *.
         apply Cap_vt_bool_nempty in E;
         destruct (translate_vecType A'1); try easy. 
Qed.



(* Multiplication laws *)

Lemma mul_assoc : forall {n} (A B C : vType n), A .* (B .* C) ≡ A .* B .* C.
Proof. intros. unfold eq_vType.
       destruct A; destruct B; destruct C; try easy.
       destruct g; destruct g0; destruct g1; simpl.
       unfold translate; simpl. 
       rewrite cMul_assoc. 
       rewrite (translate_gt_mul_assoc (length l + length l0 + length l1 + 1) _ _ _); try nia.
       reflexivity. 
Qed.

Lemma mul_I_l : forall (A : vType 1), WF_vType A -> Sing_vt A -> I .* A ≡ A.
Proof. intros. unfold eq_vType.
       destruct A; try easy.
       destruct g.
       do 2 (destruct l; try easy).
       simpl. 
       unfold translate. simpl. 
       rewrite Mmult_1_l; try (apply WF_Matrix_GType).
       destruct c; easy.
Qed.

Lemma mul_I_r : forall (A : vType 1), WF_vType A -> Sing_vt A -> A .* I ≡ A.
Proof. intros. unfold eq_vType.
       destruct A; try easy.
       destruct g.
       do 2 (destruct l; try easy).
       simpl. 
       unfold translate. simpl. 
       rewrite Mmult_1_r; try (apply WF_Matrix_GType).
       destruct c; easy.
Qed.


Lemma Xsqr : X .* X ≡ I.
Proof. intros. unfold eq_vType.
       simpl. unfold translate. simpl.
       rewrite XtimesXid.
       reflexivity. 
Qed.       


Lemma Zsqr : Z .* Z ≡ I.
Proof. intros. unfold eq_vType.
       simpl. unfold translate. simpl.
       rewrite ZtimesZid.
       reflexivity. 
Qed.       


Lemma ZmulX : Z .* X ≡ - (X .* Z).
Proof. intros. unfold eq_vType.
       simpl. unfold translate. simpl.
       do 2 (rewrite kron_1_r).
       assert (H : (C1 .* (σz × σx) = ((Copp C1) .* (σx × σz)))%M). 
       { lma'. } rewrite H. reflexivity.       
Qed.


Lemma neg_inv : forall (n : nat) (A : vType n), - - A ≡ A.
Proof. intros. unfold eq_vType.
       induction A; try easy. 
       - destruct g. simpl. 
         unfold translate; simpl. 
         destruct c; easy.
       - simpl. rewrite IHA1, IHA2.
         do 4 (rewrite Cap_vt_scale). 
         reflexivity. 
Qed.

Lemma neg_dist_l : forall (n : nat) (A B : vType n), -A .* B ≡ - (A .* B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy. 
       destruct g; destruct g0; simpl. 
       unfold translate; simpl.
       destruct c; destruct c0; easy. 
Qed.


Lemma neg_dist_r : forall (n : nat) (A B : vType n), A .* (-B) ≡ - (A .* B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy. 
       destruct g; destruct g0; simpl. 
       unfold translate; simpl.
       destruct c; destruct c0; easy. 
Qed.


Lemma i_sqr : forall (n : nat) (A : vType n), i (i A) ≡ -A.
Proof. intros. unfold eq_vType.
       induction A; try easy. 
       - destruct g. simpl. 
         unfold translate; simpl. 
         destruct c; easy.
       - simpl. unfold i in *.
         rewrite IHA1, IHA2.
         do 6 (rewrite Cap_vt_scale). 
         reflexivity. 
Qed.


Lemma i_dist_l : forall (n : nat) (A B : vType n), i A .* B ≡ i (A .* B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy. 
       destruct g; destruct g0; simpl. 
       unfold translate; simpl.
       destruct c; destruct c0; easy. 
Qed.


Lemma i_dist_r : forall (n : nat) (A B : vType n), A .* i B ≡ i (A .* B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy. 
       destruct g; destruct g0; simpl. 
       unfold translate; simpl.
       destruct c; destruct c0; easy. 
Qed.


Lemma i_neg_comm : forall (n : nat) (A : vType n), i (-A) ≡ -i A.
Proof. intros. unfold eq_vType.
       induction A; try easy. 
       - destruct g. simpl. 
         unfold translate; simpl. 
         destruct c; easy.
       - simpl. unfold i in *.
         rewrite IHA1, IHA2.
         do 8 (rewrite Cap_vt_scale). 
         reflexivity. 
Qed.


(** ** Tensor Laws *)


Lemma tensor_assoc : forall {n m o : nat} (A : vType n) (B : vType m) (C : vType o), 
  eq_vType' (A .⊗ (B .⊗ C)) ((A .⊗ B) .⊗ C).  
Proof. intros. unfold eq_vType'.
       destruct A; destruct B; destruct C; try easy.
       destruct g; destruct g0; destruct g1; simpl.
       rewrite app_ass.
       rewrite cMul_assoc. 
       reflexivity. 
Qed.       



Lemma neg_tensor_dist_l : forall {n m} (A : vType n) (B : vType m), -A .⊗ B ≡ - (A .⊗ B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy.
       destruct g; destruct g0; simpl.
       rewrite cMul_assoc. 
       reflexivity. 
Qed.


Lemma neg_tensor_dist_r : forall {n m} (A : vType n) (B : vType m), A .⊗ (-B) ≡ - (A .⊗ B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy.
       destruct g; destruct g0; simpl.
       rewrite <- cMul_assoc. 
       rewrite (cMul_comm c n_1).
       rewrite cMul_assoc.
       reflexivity. 
Qed.

Lemma i_tensor_dist_l : forall {n m} (A : vType n) (B : vType m), i A .⊗ B ≡ i (A .⊗ B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy.
       destruct g; destruct g0; simpl.
       rewrite cMul_assoc. 
       reflexivity. 
Qed.


Lemma i_tensor_dist_r : forall {n m} (A : vType n) (B : vType m), A .⊗ i B ≡ i (A .⊗ B).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; try easy.
       destruct g; destruct g0; simpl.
       rewrite <- cMul_assoc. 
       rewrite (cMul_comm c p_i).
       rewrite cMul_assoc.
       reflexivity. 
Qed.



(** ** Multiplication & Tensor Laws *)

(* Appropriate restriction is that size A = size C and size B = size D,
   but axiomatization doesn't allow for that calculation. *)
(* This should be generalizable to the other, assuming we're multiplying
   valid types. *)
Lemma mul_tensor_dist : forall {n m} (A C : vType n) (B D : vType m),
    WF_vType A -> WF_vType C ->
    (A .⊗ B) .* (C .⊗ D) ≡ (A .* C) .⊗ (B .* D).
Proof. intros. unfold eq_vType.
       destruct A; destruct B; destruct C; destruct D; try easy.
       destruct g; destruct g0; destruct g1; destruct g2; simpl.
       simpl in *.
       unfold WF_GTypeT in *; simpl in *.
       rewrite (zip_app_product _ n _ _ _ _); try nia.  
       rewrite <- cMul_assoc. 
       rewrite (cMul_assoc c c0 c1).
       rewrite (cMul_comm c0 c1).
       rewrite <- cMul_assoc.  
       rewrite cMul_assoc. 
       reflexivity. 
Qed.



Lemma decompose_tensor : forall (A B : vType 1),
    Sing_vt A -> WF_vType A ->
    Sing_vt B -> WF_vType B ->
    A .⊗ B ≡ (A .⊗ I) .* (I .⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with wfvt_db.
  destruct A; destruct B; try easy.
  apply kron_compat; try easy; try auto with wfvt_db.
  rewrite mul_I_r; try easy.
  rewrite mul_I_l; try easy.
Qed.


Lemma decompose_tensor_mult_l : forall (A B : vType 1),
    Sing_vt A -> WF_vType A -> 
    Sing_vt B -> WF_vType B ->
    (A .* B) .⊗ I ≡ (A .⊗ I) .* (B .⊗ I).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with wfvt_db.
  destruct A; destruct B; try easy.
  apply kron_compat; try easy; try auto with wfvt_db.
  rewrite mul_I_l; try auto with wfvt_db.
  easy.
Qed.


Lemma decompose_tensor_mult_r : forall (A B : vType 1),
    Sing_vt A -> WF_vType A -> 
    Sing_vt B -> WF_vType B ->
    I .⊗ (A .* B) ≡ (I .⊗ A) .* (I .⊗ B).
Proof.
  intros.
  rewrite mul_tensor_dist; auto with wfvt_db.
  destruct A; destruct B; try easy.
  apply kron_compat; try easy; try auto with wfvt_db.
  rewrite mul_I_r; try auto with wfvt_db.
  easy.
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
  unitary (translate_prog prg_len p).
Proof. intros. induction p as [| | | |];
       try (apply unit_prog_smpl_app; auto with unit_db);
       try (apply unit_prog_ctrl_app; auto with unit_db).
       simpl. apply unit_mult; easy. 
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



Local Close Scope nat_scope.

(*******************************************************)
(* establishing support for eq_vType in program typing *)
(*******************************************************)

Lemma eq_type_conv_input : forall {n} (p : prog) (A A' B : vType n),
  A ≡ A' -> p :' A → B -> p :' A' → B.
Proof. intros. 
       simpl in *. 
       unfold progHasSingType in *.
       rewrite <- H.
       apply eq_vType_cap_vt_bool in H.
       rewrite <- H.
       assumption. 
Qed.

(*
Lemma eq_type_conv_input' : forall {n m} (p : prog) (A' : vType m) (A B : vType n),
  eq_vType' A A' -> n = m -> p :' A → B -> p :' A' → B.
Proof. intros. 
       simpl in *. 
       unfold progHasSingType in *.
       rewrite <- H.
       apply eq_vType_cap_vt_bool in H.
       rewrite <- H.
       assumption. 
Qed. *)

Lemma eq_type_conv_output : forall {n} (p : prog) (A B B' : vType n),
  B ≡ B' -> p :' A → B -> p :' A → B'.
Proof. intros. 
       simpl in *. 
       unfold progHasSingType in *.
       rewrite <- H.
       apply eq_vType_cap_vt_bool in H.
       rewrite <- H.
       assumption. 
Qed.


Lemma eq_type_conv : forall {n} (p : prog) (A A' B B' : vType n),
  A ≡ A' -> B ≡ B' -> (p :' A → B <-> p :' A' → B').
Proof. intros. split. 
       - intros. simpl in *. 
         unfold progHasSingType in *.
         rewrite <- H, <- H0.
         apply eq_vType_cap_vt_bool in H;
         apply eq_vType_cap_vt_bool in H0.
         rewrite <- H, <- H0.
         easy.
       - intros. simpl in *. 
         unfold progHasSingType in *.
         rewrite H, H0.
         apply eq_vType_cap_vt_bool in H;
         apply eq_vType_cap_vt_bool in H0.
         rewrite H, H0.
         easy.
Qed.


Lemma prog_decompose_tensor_mult_l : forall (p : prog) (A B : vType 1) (T : vType 2),
  Sing_vt A -> WF_vType A ->
  Sing_vt B -> WF_vType B ->
  p :' ((A .⊗ I) .* (B .⊗ I)) → T -> p :' ((A .* B) .⊗ I) → T.
Proof. intros. 
       apply (eq_type_conv_input p ((A .⊗ I) .* (B .⊗ I)) ((A .* B) .⊗ I) T); try easy.
       rewrite decompose_tensor_mult_l; easy.
Qed.


Lemma prog_decompose_tensor_mult_r : forall (p : prog) (A B : vType 1) (T : vType 2),
  Sing_vt A -> WF_vType A ->
  Sing_vt B -> WF_vType B ->
  p :' ((I .⊗ A) .* (I .⊗ B)) → T -> p :' (I .⊗ (A .* B)) → T.
Proof. intros. 
       apply (eq_type_conv_input p ((I .⊗ A) .* (I .⊗ B)) (I .⊗ (A .* B)) T); try easy.
       rewrite decompose_tensor_mult_r; easy.
Qed.


Lemma prog_decompose_tensor : forall (p : prog) (A B : vType 1) (T : vType 2),
  Sing_vt A -> WF_vType A ->
  Sing_vt B -> WF_vType B ->
  p :' ((A .⊗ I) .* (I .⊗ B)) → T -> p :' (A .⊗ B) → T.
Proof. intros. 
       apply (eq_type_conv_input p ((A .⊗ I) .* (I .⊗ B)) (A .⊗ B) T); try easy.
       rewrite <- decompose_tensor; easy.
Qed.



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

Lemma Ysimp : @translate 1 (p_i * (p_1 * p_1), [gMul gX gZ]) = σy. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.


Lemma kron_simp : forall (g1 g2 : GType), 
    @translate 2 (p_1 * p_1, g1 :: [g2]) = (translate_gt g1) ⊗ (translate_gt g2).  
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
Proof. solve_ground_type. Qed.


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
Qed.

  

Lemma TypesI2 : forall (p : prog), p :' I .⊗ I → I .⊗ I.
Proof. intros. simpl. 
       unfold progHasSingType. 
       rewrite ite_conv.
       unfold translate_vecType. 
       rewrite ite_conv. 
       autorewrite with simp_db. 
       simpl translate_gt.
       rewrite fgt_conv.
       apply Heisenberg.TypesI2.
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





(* Defining a "ground" vType to be used for switching *)

Definition ground_type {n} (A : vType n) : Prop :=
  exists a, (G n (p_1, [a])) = A.

Lemma ground_I : ground_type I. Proof. exists gI. easy. Qed.
Lemma ground_X : ground_type X. Proof. exists gX. easy. Qed.
Lemma ground_Z : ground_type Z. Proof. exists gZ. easy. Qed.

Lemma ground_mul : forall {n} (A B : vType n),
    ground_type A -> ground_type B -> ground_type (A .* B).
Proof. intros. 
       destruct H; destruct H0.
       exists (gMul x x0).
       rewrite <- H, <- H0.
       easy. 
Qed.


Hint Resolve ground_I ground_X ground_Z ground_mul : gt_db.




Definition nth_vType {n} (bit : nat) (A : vType n) : vType 1 :=
  match A with 
  | G _ g => G 1 (p_1, [nth bit (snd g) gI])         
  | _ => Err 1
  end. 


Definition switch_vType {n} (A : vType n) (a : GType) (bit : nat) : vType n :=
  match A with 
  | G _ g => G n (fst g, switch (snd g) a bit)         
  | _ => Err n
  end.

Definition switch_vType' {n} (A : vType n) (a : vType 1) (bit : nat) : vType n :=
  match A with 
  | G _ g =>
    match a with
    | G _ g0 => G n (fst g, switch (snd g) (hd gI (snd g0))  bit)
    | _ => Err n
    end
  | _ => Err n
  end.


Lemma switch_eq : forall {n} (A : vType n) (x : GType) (bit : nat),
    switch_vType' A (G 1 (p_1, [x])) bit = switch_vType A x bit.
Proof. easy. Qed.



Lemma nth_vswitch_miss : forall {n} (A : vType n) (a : vType 1) (bit sbit : nat),
    bit <> sbit -> ground_type a ->
    nth_vType bit (switch_vType' A a sbit) = nth_vType bit A.
Proof. intros. 
       destruct H0; rewrite <- H0.
       destruct A; try easy.
       simpl. 
       rewrite nth_switch_miss;
       easy. 
Qed.


Lemma nth_vswitch_hit : forall {n} (A : vType n) (a : vType 1) (bit : nat),
    bit < n -> Sing_vt A -> WF_vType A -> ground_type a ->
    nth_vType bit (switch_vType' A a bit) = a.
Proof. intros. 
       destruct H2; rewrite <- H2.
       destruct A; try easy.
       simpl. 
       rewrite nth_switch_hit; try easy. 
       unfold WF_vType in *.
       unfold WF_GTypeT in *.
       rewrite H1; easy.
Qed.


Definition box {X : Type} (x : X) : list X := [x].

Lemma box_simplify : forall {X} (x : X), box x = [x]. Proof. easy. Qed.

Lemma Mscale_to_VTscale : forall {n} (A : Square n) (c : C), [(c .* A)%M] = c · [A].
Proof. easy. Qed.


Lemma big_tensor_cons : forall {n} (A : vecType n) (As : list (vecType n)),
   ⨂' (A :: As) = A ⊗' (⨂' As).
Proof. intros. easy. Qed.


Lemma big_kron_to_big_tensor : forall {n} (As : list (Square n)),
    [⨂ As] = ⨂' (map box As).
Proof. induction As as [| h]. 
       - easy. 
       - simpl map. 
         simpl big_kron.
         rewrite big_tensor_cons.
         rewrite <- IHAs. 
         rewrite map_length. easy.
Qed.


Lemma switch_out_of_bounds : forall {X : Type} (n : nat) (ls : list X) (x : X),
  length ls <= n -> switch ls x n = ls.
Proof. induction n as [| n'].
       - destruct ls; easy. 
       - destruct ls. easy. 
         intros; simpl; rewrite IHn'. 
         reflexivity. 
         simpl in H; nia. 
Qed.




(****************)
(* tensor rules *)
(****************)



Lemma tensor_smpl : forall (prg_len bit : nat) (p : nat -> prog)
                           (A : vType prg_len) (a : GType),
    WF_vType A -> smpl_prog p -> 
    (p 0) :' (nth_vType bit A) → (G 1 (p_1, [a])) ->
    (p bit) :'  A → (switch_vType A a bit).
Proof. intros. destruct A; try easy.
       destruct g. simpl in *.
       unfold progHasSingType in *. 
       rewrite ite_conv in *.
       rewrite fgt_conv in *. 
       simpl translate_vecType in *. 
       unfold translate in *.
       simpl fst in *; simpl snd in *; simpl in H1; destruct H1.       
       do 2 (rewrite kron_1_r in H1; rewrite Mscale_1_l in H1; rewrite map_length);
       rewrite switch_len; 
       unfold WF_GTypeT in *; simpl in H.
       rewrite <- H. 
       do 2 (rewrite (@Mscale_to_VTscale (2^(length l)) _)).
       apply arrow_scale.
       apply translate_coef_nonzero.
       rewrite switch_map.
       simpl; apply kill_true.
       destruct H0.
       rewrite H0 in *.
       simpl translate_prog in *.
       unfold prog_smpl_app. 
       destruct (bit <? length l) eqn:E.
       - apply Nat.ltb_lt in E.
         rewrite <- (map_length translate_gt _).
         rewrite big_kron_to_big_tensor.
         rewrite <- (switch_len bit _ (translate_gt a)).               
         rewrite big_kron_to_big_tensor.
         rewrite switch_map.
         rewrite (switch_tensor_inc bit prg_len _ _).
         rewrite (nth_tensor_inc bit prg_len _).
         rewrite switch_len.
         rewrite map_length.
         rewrite (easy_pow3 (length l) bit).
         rewrite firstn_length_le. 
         rewrite skipn_length.
         do 2 (rewrite map_length).
         assert (H' : length l - s bit = length l - bit - 1). { nia. }
         rewrite H'.
         apply sgt'_reduce_smpl; try easy.
         apply (S_tensor_subset _ (map box (map translate_gt l)) _).
         apply S_big_tensor. intros. 
         apply in_map_iff in H3; do 2 (destruct H3).
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3.
         rewrite <- H3. easy. 
         apply firstn_subset.
         apply (S_tensor_subset _ (map box (map translate_gt l)) _).
         apply S_big_tensor. intros. 
         apply in_map_iff in H3; do 2 (destruct H3).
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3.
         rewrite <- H3. easy. 
         apply skipn_subset.
         destruct (nth_in_or_default bit (map box (map translate_gt l)) I').
         apply in_map_iff in i0; destruct i0; destruct H3.
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3; rewrite <- H3; easy.
         rewrite e; easy.
         auto with unit_db. 
         destruct (nth_in_or_default bit (map box (map translate_gt l)) I').
         apply in_map_iff in i0; destruct i0; destruct H3.
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3; rewrite <- H3. 
         unfold uni_vecType. intros. 
         rewrite box_simplify in H6. simpl in H6.
         destruct H6. rewrite <- H6. 
         apply unit_GType. easy. 
         rewrite e. 
         auto with univ_db.
         rewrite box_simplify. unfold uni_vecType. 
         intros; simpl in H3; destruct H3.
         rewrite <- H3. 
         apply unit_GType. easy. 
         unfold prog_smpl_app in H1; simpl in *.
         rewrite box_simplify. 
         rewrite kron_1_l in H1; rewrite kron_1_r in H1.
         unfold I'. rewrite <- (box_simplify (Matrix.I 2)).
         rewrite map_nth. 
         assert (H'' : Matrix.I 2 = translate_gt gI). { easy. }
         rewrite H''. rewrite map_nth. 
         rewrite box_simplify. 
         apply H1. auto with wf_db.
         do 2 (rewrite map_length).
         nia. nia. nia. 
         unfold WF_vtt. 
         do 2 (rewrite map_length); easy. nia.
         unfold WF_vtt. 
         do 2 (rewrite map_length); easy. 
       - rewrite switch_out_of_bounds.
         unfold singGateType'; intros. 
         simpl in *. rewrite Mmult_1_l'; easy.
         rewrite map_length.
         unfold Nat.ltb in E. 
         apply leb_iff_conv in E.
         nia.
       - destruct H0.
         rewrite H0 in *.
         simpl translate_prog in *.
         unfold prog_smpl_app. 
         destruct (bit <? length l) eqn:E.
         apply Nat.ltb_lt in E.
         rewrite <- (map_length translate_gt _).
         rewrite big_kron_to_big_tensor.
         rewrite <- (switch_len bit _ (translate_gt a)).               
         rewrite big_kron_to_big_tensor.
         rewrite switch_map.
         rewrite (switch_tensor_inc bit prg_len _ _).
         rewrite (nth_tensor_inc bit prg_len _).
         rewrite switch_len.
         rewrite map_length.
         rewrite (easy_pow3 (length l) bit).
         rewrite firstn_length_le. 
         rewrite skipn_length.
         do 2 (rewrite map_length).
         assert (H' : length l - s bit = length l - bit - 1). { nia. }
         rewrite H'.
         apply sgt'_reduce_smpl; try easy.
         apply (S_tensor_subset _ (map box (map translate_gt l)) _).
         apply S_big_tensor. intros. 
         apply in_map_iff in H3; do 2 (destruct H3).
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3.
         rewrite <- H3. easy. 
         apply firstn_subset.
         apply (S_tensor_subset _ (map box (map translate_gt l)) _).
         apply S_big_tensor. intros. 
         apply in_map_iff in H3; do 2 (destruct H3).
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3.
         rewrite <- H3. easy. 
         apply skipn_subset.
         destruct (nth_in_or_default bit (map box (map translate_gt l)) I').
         apply in_map_iff in i0; destruct i0; destruct H3.
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3; rewrite <- H3; easy.
         rewrite e; easy.
         auto with unit_db. 
         destruct (nth_in_or_default bit (map box (map translate_gt l)) I').
         apply in_map_iff in i0; destruct i0; destruct H3.
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3; rewrite <- H3. 
         unfold uni_vecType. intros. 
         rewrite box_simplify in H6. simpl in H6.
         destruct H6. rewrite <- H6. 
         apply unit_GType. easy. 
         rewrite e. 
         auto with univ_db.
         rewrite box_simplify. unfold uni_vecType. 
         intros; simpl in H3; destruct H3.
         rewrite <- H3. 
         apply unit_GType. easy. 
         unfold prog_smpl_app in H1; simpl in *.
         rewrite box_simplify. 
         rewrite kron_1_l in H1; rewrite kron_1_r in H1.
         unfold I'. rewrite <- (box_simplify (Matrix.I 2)).
         rewrite map_nth. 
         assert (H'' : Matrix.I 2 = translate_gt gI). { easy. }
         rewrite H''. rewrite map_nth. 
         rewrite box_simplify. 
         apply H1. auto with wf_db.
         do 2 (rewrite map_length).
         nia. nia. nia. 
         unfold WF_vtt. 
         do 2 (rewrite map_length); easy. nia.
         unfold WF_vtt. 
         do 2 (rewrite map_length); easy. 
         rewrite switch_out_of_bounds.
         unfold singGateType'; intros. 
         simpl in *. rewrite Mmult_1_l'; easy.
         rewrite map_length.
         unfold Nat.ltb in E. 
         apply leb_iff_conv in E.
         nia.
         rewrite H0 in *.
         simpl translate_prog in *.
         unfold prog_smpl_app. 
         destruct (bit <? length l) eqn:E.
         apply Nat.ltb_lt in E.
         rewrite <- (map_length translate_gt _).
         rewrite big_kron_to_big_tensor.
         rewrite <- (switch_len bit _ (translate_gt a)).               
         rewrite big_kron_to_big_tensor.
         rewrite switch_map.
         rewrite (switch_tensor_inc bit prg_len _ _).
         rewrite (nth_tensor_inc bit prg_len _).
         rewrite switch_len.
         rewrite map_length.
         rewrite (easy_pow3 (length l) bit).
         rewrite firstn_length_le. 
         rewrite skipn_length.
         do 2 (rewrite map_length).
         assert (H' : length l - s bit = length l - bit - 1). { nia. }
         rewrite H'.
         apply sgt'_reduce_smpl; try easy.
         apply (S_tensor_subset _ (map box (map translate_gt l)) _).
         apply S_big_tensor. intros. 
         apply in_map_iff in H3; do 2 (destruct H3).
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3.
         rewrite <- H3. easy. 
         apply firstn_subset.
         apply (S_tensor_subset _ (map box (map translate_gt l)) _).
         apply S_big_tensor. intros. 
         apply in_map_iff in H3; do 2 (destruct H3).
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3.
         rewrite <- H3. easy. 
         apply skipn_subset.
         destruct (nth_in_or_default bit (map box (map translate_gt l)) I').
         apply in_map_iff in i0; destruct i0; destruct H3.
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3; rewrite <- H3; easy.
         rewrite e; easy.
         auto with unit_db. 
         destruct (nth_in_or_default bit (map box (map translate_gt l)) I').
         apply in_map_iff in i0; destruct i0; destruct H3.
         apply in_map_iff in H4; do 2 (destruct H4).
         rewrite <- H4 in H3; rewrite <- H3. 
         unfold uni_vecType. intros. 
         rewrite box_simplify in H6. simpl in H6.
         destruct H6. rewrite <- H6. 
         apply unit_GType. easy. 
         rewrite e. 
         auto with univ_db.
         rewrite box_simplify. unfold uni_vecType. 
         intros; simpl in H3; destruct H3.
         rewrite <- H3. 
         apply unit_GType. easy. 
         unfold prog_smpl_app in H1; simpl in *.
         rewrite box_simplify. 
         rewrite kron_1_l in H1; rewrite kron_1_r in H1.
         unfold I'. rewrite <- (box_simplify (Matrix.I 2)).
         rewrite map_nth. 
         assert (H'' : Matrix.I 2 = translate_gt gI). { easy. }
         rewrite H''. rewrite map_nth. 
         rewrite box_simplify. 
         apply H1. auto with wf_db.
         do 2 (rewrite map_length).
         nia. nia. nia. 
         unfold WF_vtt. 
         do 2 (rewrite map_length); easy. nia.
         unfold WF_vtt. 
         do 2 (rewrite map_length); easy. 
         rewrite switch_out_of_bounds.
         unfold singGateType'; intros. 
         simpl in *. rewrite Mmult_1_l'; easy.
         rewrite map_length.
         unfold Nat.ltb in E. 
         apply leb_iff_conv in E.
         nia.
Qed.



Lemma tensor_smpl' : forall (prg_len bit : nat) (p : nat -> prog)
                           (A : vType prg_len) (a : vType 1),
    WF_vType A -> smpl_prog p -> ground_type a ->
    (p 0) :' (nth_vType bit A) → a ->
    (p bit) :'  A → (switch_vType' A a bit).
Proof. intros.
       destruct H1.
       rewrite <- H1 in *.
       rewrite switch_eq.
       apply tensor_smpl; easy. 
Qed.


Lemma tensor_ctrl : forall (prg_len ctrl targ : nat)   
                           (A : vType prg_len) (a b : GType),
  (CNOT 0 1) :' (nth_vType ctrl A) .⊗ (nth_vType targ A) → (G 1 (p_1, [a])) .⊗ (G 1 (p_1, [b])) ->
  (CNOT ctrl targ) :'  A → switch_vType (switch_vType A a ctrl) b targ.
Proof. Admitted. 


Lemma tensor_ctrl' : forall (prg_len ctrl targ : nat)   
                           (A : vType prg_len) (a b : vType 1),
  ground_type a -> ground_type b -> 
  (CNOT 0 1) :' (nth_vType ctrl A) .⊗ (nth_vType targ A) → a .⊗ b ->
  (CNOT ctrl targ) :'  A → switch_vType' (switch_vType' A a ctrl) b targ.
Proof. intros. 
       destruct H; destruct H0.
       rewrite <- H, <- H0 in *.
       do 2 (rewrite switch_eq).
       apply tensor_ctrl; easy. 
Qed.

(***************)
(* Arrow rules *)
(***************)


Lemma mul_simp : forall (a b : GType),
  G 1 (p_1, [gMul a b]) = G 1 (p_1, [a]) .* G 1 (p_1, [b]). 
Proof. easy. Qed.


Lemma arrow_mul : forall {n} g (A A' B B' : vType n),
    Sing_vt A -> Sing_vt B ->
    Sing_vt A' -> Sing_vt B' ->
    WF_vType A -> WF_vType A' ->
    WF_vType B -> WF_vType B' ->
    g :' A → A' ->
    g :' B → B' ->
    g :' A .* B → A' .* B'.
Proof. intros; simpl in *.
       assert (H' : Sing_vt A). { apply H. }
       assert (H0' : Sing_vt B). { apply H0. }
       assert (H1' : Sing_vt A'). { apply H1. }
       assert (H2' : Sing_vt B'). { apply H2. } 
       apply sing_vt_simplify in H; destruct H;
       apply sing_vt_simplify in H0; destruct H0;
       apply sing_vt_simplify in H1; destruct H1;
       apply sing_vt_simplify in H2; destruct H2; try easy.
       unfold progHasSingType in *. 
       rewrite H, H0, H1, H2 in *.
       simpl Cap_vt_bool in *. 
       rewrite ite_conv in *.
       rewrite translate_vecType_mMult; try easy.
       rewrite translate_vecType_mMult; try easy.
       rewrite fgt_conv.
       apply Heisenberg.arrow_mul; 
       try (apply unit_prog);
       try (apply unit_vType); try easy.
Qed. 
  


Lemma arrow_mul_1 : forall g (a a' b b' : GType),
    g :' G 1 (p_1, [a]) → G 1 (p_1, [a']) ->
    g :' G 1 (p_1, [b]) → G 1 (p_1, [b']) ->
    g :' G 1 (p_1, [gMul a b]) → G 1 (p_1, [gMul a' b']).
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
    B ≡ B' ->
    g :' A → B'.
Proof. intros. apply (eq_type_conv_output g A B B'); easy. Qed.

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


Ltac simp_switch :=  
  repeat (
      try (rewrite nth_vswitch_hit; try easy; try lia; auto with gt_db);
      try (rewrite nth_vswitch_miss; try easy; try lia; auto with gt_db)). 
  


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
         end; auto with wfvt_db; try easy.


Ltac type_check_base' :=
  repeat apply cap_intro;
  repeat expand_prog; (* will automatically unfold compound progs *)
  repeat match goal with
         | |- Sing_vt ?A       => tryif is_evar A then fail else auto 50 with svt_db
         | |- WF_vType ?A       => tryif is_evar A then fail else auto with wfvt_db
         | |- ground_type ?A => tryif is_evar A then fail else auto with gt_db
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
         | |- ?g (S ?n) ?m :' ?T => eapply tensor_ctrl'; simp_switch
         | |- ?g 0 (S (S ?m)) :' ?T => eapply tensor_ctrl'; simp_switch
         | |- H' (S ?n) :' ?T => eapply tensor_smpl'; auto with wfvt_db; simp_switch
         | |- ?g :' nth_vType _ _ → _ => simp_switch 
         | |- ?g :' ?A .* ?B → _ => apply arrow_mul
         | |- ?g :' (?A .* ?B) .⊗ I → _ => apply prog_decompose_tensor_mult_l
         | |- ?g :' I .⊗ (?A .* ?B) → _ => apply prog_decompose_tensor_mult_r
         | |- ?g :' ?A .⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             apply prog_decompose_tensor
         | |- ?A ≡ ?B => try rewrite mul_tensor_dist; try easy
         end;
  auto with gt_db; auto with wfvt_db; try easy.



Lemma CZTypes : CZ 0 1 :' (X .⊗ I → X .⊗ Z) ∩ (I .⊗ X → Z .⊗ X) ∩
                          (Z .⊗ I → Z .⊗ I) ∩ (I .⊗ Z → I .⊗ Z).
Proof. type_check_base'.   
Qed.




Notation bell00 := ((H' 2);; (CNOT 2 3)).

Notation encode := ((CZ 0 2);; (CNOT 1 2)).

Notation decode := ((CNOT 2 3);; (H' 2)).

Notation superdense := (bell00;; encode;; decode).


Check Heisenberg.S'.


Lemma superdenseTypesQPL : superdense :' (Z .⊗ Z .⊗ Z .⊗ Z → I .⊗ I .⊗ Z .⊗ Z).
Proof. repeat expand_prog. 
       type_check_base'.
       type_check_base'.
       type_check_base'.
       type_check_base'.
       3 : { rewrite mul_compat;
             try rewrite mul_tensor_dist;
             try easy; auto with wfvt_db. }
       all : auto with gt_db.
       type_check_base'.
       type_check_base'.
        3 : { rewrite mul_compat;
             try rewrite mul_tensor_dist;
             try easy; auto with wfvt_db. 
              4 : { rewrite mul_compat;
                    try rewrite mul_tensor_dist;
                    try easy; auto with wfvt_db. }
              all : auto with wfvt_db. }
        all : auto with gt_db.
        type_check_base'.
        3 : { rewrite mul_compat;
             try rewrite mul_tensor_dist;
             try easy; auto with wfvt_db. 
              4 : { rewrite mul_compat;
                    try rewrite mul_tensor_dist;
                    try easy; auto with wfvt_db. 
                    4 : rewrite mul_compat;
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
