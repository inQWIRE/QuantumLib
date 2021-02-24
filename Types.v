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


Fixpoint translate_gt (g : GType) : Square 2 :=
  match g with
  | gI => I 2
  | gX => σx
  | gZ => σz
  | gIm g => Ci .* (translate_gt g)
  | gNeg g => (Copp C1) .* (translate_gt g)
  | gMul g1 g2 => (translate_gt g1) × (translate_gt g2)
  end. 


(*
Inductive Coef :=
| c1
| ci
| neg_c1
| neg_ci.


Definition translate_coef (c : Coef) : C :=
  match c with
  | c1 => C1
  | ci => Ci
  | neg_c1 => -C1
  | neg_ci => -Ci
  end. 
*)


Lemma WF_Matrix_GType : forall (g : GType), WF_Matrix (translate_gt g).
Proof. intros. induction g as [| | | | |].  
       - simpl. auto with wf_db.
       - simpl. auto with wf_db.
       - simpl. auto with wf_db.
       - simpl. auto with wf_db.
       - simpl. auto with wf_db.
       - simpl. auto with wf_db.
Qed.

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


Definition translate {n} (A : GTypeT n) : Square (2^n) := 
  match (snd A) with
  | [] => I 1
  | (a :: As) => (fst A) .* ⨂ (map translate_gt (snd A))
  end.


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

Definition scale {n} (c : C) (A : vType n) : vType n :=
  match A with
  | G _ a => G n (gScaleT c a)
  | _ => Err n
  end.


Definition i {n} (A : vType n) := scale Ci A.
Notation "- A" := (scale (Copp C1) A).
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
       + induction A as [| | |].
         - easy.
         - intros. 
           destruct H.
           simpl. 
           rewrite IHA1, IHA2.
           easy. assumption. assumption.
         - easy.
         - easy.
       + induction A as [| | |].
         - easy.
         - intros.
           simpl in *. 
           apply andb_true_iff in H.
           destruct H.
           split. 
           apply IHA1.
           assumption.
           apply IHA2.
           assumption. 
         - easy.
         - easy.
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


Lemma singleton_sing_vt : forall {n} (A : vType n),
  Sing_vt A -> Singleton (translate_vecType A).
Proof. intros. destruct A.
       + easy. 
       + easy. 
       + easy. 
       + easy. 
Qed.


Lemma sing_vt_simplify : forall {n} (A : vType n),
  Sing_vt A -> (exists a, A = G n a).
Proof. intros. destruct A.
       - exists g. reflexivity. 
       - easy. 
       - easy. 
       - easy. 
Qed.


Definition I : vType 1 := G 1 (C1, [gI]).
Definition X : vType 1 := G 1 (C1, [gX]).
Definition Z : vType 1 := G 1 (C1, [gZ]).

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


(**************************)
(* Well Formedness Lemmas *)
(**************************)


Definition WF_GTypeT {len : nat} (gtt : GTypeT len) := length (snd gtt) = len.

Fixpoint WF_vType {n} (A : vType n) : Prop :=
  match A with
  | G _ a => WF_GTypeT a
  | Cap _ a1 a2 => WF_vType a1 /\ WF_vType a1
  | Arrow _ a1 a2 => WF_vType a1 /\ WF_vType a1
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
       destruct A.
       destruct B.
       destruct g.
       destruct g0.
       apply zip_len_pres.
       assumption.
       assumption.
       easy. easy. easy.
       easy. easy. easy. 
Qed.


Lemma WF_tensor : forall {n m} (A : vType n) (B : vType m),
  Sing_vt A -> Sing_vt B ->
  WF_vType A -> WF_vType B ->
  WF_vType (A .⊗ B). 
Proof. intros. 
       destruct A.
       destruct B.
       destruct g.
       destruct g0.
       simpl in *. 
       unfold WF_GTypeT in *.
       simpl in *.
       rewrite app_length.
       nia. 
       easy. easy. easy.
       easy. easy. easy. 
Qed.


Lemma WF_neg : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (- A). 
Proof. intros. 
       destruct A. 
       destruct g.
       easy. easy.
       easy. easy.
Qed.
   
Lemma WF_i : forall {n} (A : vType n),
  Sing_vt A -> WF_vType A ->  WF_vType (i A). 
Proof. intros. 
       destruct A. 
       destruct g.
       easy. easy.
       easy. easy.
Qed.


Hint Resolve WF_I WF_X WF_Z WF_mul WF_tensor WF_neg WF_i : wfvt_db.


Lemma WF_Y : WF_vType Y.
Proof. auto with wfvt_db. Qed.


Lemma WF_Matrix_GTypeT : forall {n} (A : GTypeT n), WF_GTypeT A -> WF_Matrix (translate A). 
Proof. intros. destruct A.
       destruct l as [| h].
       - unfold translate; simpl. 
         unfold WF_GTypeT in H; simpl in H.
         rewrite <- H; simpl.
         auto with wf_db.          
        - unfold translate; simpl. 
          unfold WF_GTypeT in H; simpl in H.
          rewrite <- H.
          assert (H' : forall n, (2^n + (2^n +0) = 2^ (S n))%nat). { simpl. nia. }
          rewrite H'.      
          rewrite map_length.
          apply WF_scale. 
          apply WF_kron.
          simpl. nia. 
          simpl. nia. 
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
Proof. intros. induction g as [| | | | |].  
       - simpl. auto with unit_db.
       - simpl. auto with unit_db.
       - simpl. auto with unit_db.
       - simpl. unfold unitary. 
         distribute_adjoint.
         distribute_scale.
         rewrite IHg. lma'. 
       - simpl. unfold unitary. 
         distribute_adjoint.
         distribute_scale.
         rewrite IHg. lma'. 
       - simpl. auto with unit_db.
Qed.


Definition uni_vType {n} (A : vType n) := uni_vecType (translate_vecType A).



(**************************)
(* defining vector typing *)
(**************************)


(* we need this for now. should eventually rewrite defs to make proofs easier *)
Lemma fgt_conv : forall (n : nat) (A B : vecType n), [(A, B)] = formGateType A B.
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


Lemma Isimp : @translate 1 (C1, [gI]) = Matrix.I 2. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Xsimp : @translate 1 (C1, [gX]) = σx. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Zsimp : @translate 1 (C1, [gZ]) = σz. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.

Lemma Ysimp : @translate 1 (Ci * (C1 * C1), [gMul gX gZ]) = σy. 
Proof. unfold translate; simpl. 
       lma'. 
Qed.


Lemma kron_simp : forall (g1 g2 : GType), 
    @translate 2 (C1 * C1, g1 :: [g2]) = (translate_gt g1) ⊗ (translate_gt g2).  
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
       assert (H3 : forall c1 c2 , c1 = c2 -> c1 * √ 2 = c2 * √ 2). 
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
       rewrite (fgt_conv (2^n) _ _). 
       apply (Heisenberg.SeqTypes (translate_prog n g1) _  _ (translate_vecType B) _).
       rewrite <- (fgt_conv (2^n) _ _); apply H.
       rewrite <- (fgt_conv (2^n) _ _); apply H0.
       rewrite andb_false_r in H0; easy.
       easy. easy.       
Qed.


Lemma seq_assoc : forall {n} (g1 g2 g3 : prog) (T : vType n),
    g1 ;; (g2 ;; g3) :' T <-> (g1 ;; g2) ;; g3 :' T.
Proof. induction T as [| | |].
       - easy. 
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
       - easy. 
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
       destruct (Cap_vt_bool A).
       destruct (Cap_vt_bool B).
       destruct (Cap_vt_bool A').
       destruct (Cap_vt_bool B').
       rewrite ite_conv in *.
       rewrite fgt_conv in *.
       apply (Heisenberg.arrow_sub _ (translate_vecType A) _ (translate_vecType B) _).
       apply H1.
       apply H2.
       apply H3.
       easy. easy.
       rewrite andb_false_r in H3; easy. 
       easy.
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
  destruct (Cap_vt_bool A) eqn:E1.
  destruct (Cap_vt_bool B) eqn:E2.
  destruct (Cap_vt_bool A') eqn:E3.
  destruct (Cap_vt_bool B') eqn:E4.
  destruct H as [H H0].
  rewrite ite_conv in H.
  rewrite ite_conv in H0.
  apply cap_arrow.
  apply cap_intro.
  - eapply arrow_sub; intros.
    + simpl. split. 
      * apply Cap_vt_conv.
        assumption.
      * apply Cap_vt_conv.
        assumption.
    + apply Cap_vt_conv.
        assumption.
    + eapply cap_elim_l_vec. apply H1.
    + apply H1.
    + simpl; unfold progHasSingType. 
      rewrite E1, E3.
      rewrite ite_conv.
      assumption.
  - eapply arrow_sub; intros.
    + simpl. split. 
      * apply Cap_vt_conv.
        assumption.
      * apply Cap_vt_conv.
        assumption.
    + apply Cap_vt_conv.
        assumption.
    + eapply cap_elim_r_vec. apply H1.
    + apply H1.
    + simpl; unfold progHasSingType. 
      rewrite E2, E4.
      rewrite ite_conv.
      assumption.
  - rewrite andb_false_r in H; easy. 
  - rewrite andb_false_r in H; easy.
  - easy. 
  - easy.
Qed.




(** Typing Rules for Tensors *)

Local Open Scope nat_scope.

Notation s := Datatypes.S.


Definition nth_vType {n} (bit : nat) (A : vType n) : vType 1 :=
  match A with 
  | G _ g => G 1 (C1, [nth bit (snd g) gI])         
  | _ => Err 1
  end. 


Definition switch_vType {n} (A : vType n) (a : GType) (bit : nat) : vType n :=
  match A with 
  | G _ g => G n (fst g, switch (snd g) a bit)         
  | _ => Err n
  end. 



Lemma tensor_smpl : forall (prg_len bit : nat) p  
                           (A : vType prg_len) (a : GType),
    (p 0) :' (nth_vType bit A) → (G 1 (C1, [a])) ->
    (p bit) :'  A → (switch_vType A a bit).
Proof. Admitted. 


Lemma tensor_ctrl : forall (prg_len ctrl targ : nat) p  
                           (A : vType prg_len) (a b : GType),
    (p 0 1) :' (nth_vType ctrl A) .⊗ (nth_vType targ A) → (G 1 (C1, [a])) .⊗ (G 1 (C1, [b])) ->
    (p ctrl targ) :'  A → switch_vType (switch_vType A a ctrl) b targ.
Proof. Admitted. 

                 

(** Arrow rules *)

(* Does this need restrictions? 
   If we had g :: X → iX then we could get 
   g :: I → -I which makes negation meaningless 
   (and leads to a contradiction if I ∩ -I = ⊥.    
*)


Lemma helper : forall {n} (A B : vType n),
  translate_vecType (A .* B) = (translate_vecType A) *' (translate_vecType B).
Proof. intros. 
       destruct A.
       destruct B.
       simpl.
       destruct g. destruct g0.
       simpl. 
       unfold translate. 
       simpl. 



(translate_vecType (G n x .* G n x0)

Lemma arrow_mul : forall {n} g (A A' B B' : vType n),
    Sing_vt A -> Sing_vt B ->
    Sing_vt A' -> Sing_vt B' ->
    uni_vType A -> uni_vType A' ->
    uni_vType B -> uni_vType B' ->
    g :' A → A' ->
    g :' B → B' ->
    g :' A .* B → A' .* B'.
Proof. intros; simpl in *.
       assert (H' : Sing_vt A). { apply H. }
       assert (H0' : Sing_vt B). { apply H0. }
       apply sing_vt_simplify in H; destruct H;
       apply sing_vt_simplify in H0; destruct H0;
       apply sing_vt_simplify in H1; destruct H1;
       apply sing_vt_simplify in H2; destruct H2.
       unfold progHasSingType in *. 
       rewrite H, H0, H1, H2 in *.
       simpl Cap_vt_bool in *. 
       rewrite ite_conv in *.
       simpl translate_vecType in *. 
       unfold translate. 
       simpl. 
Lemma arrow_mul : forall {n} (p : Square n) (A A' B B' : vecType n),
    Singleton A -> Singleton B ->
    unitary p ->
    uni_vecType A -> uni_vecType A' ->
    uni_vecType B -> uni_vecType B' ->
    p ::' A → A' ->
    p ::' B → B' ->
    p ::' A *' B → A' *' B'.


Axiom arrow_i : forall p A A',
    p :: A → A' ->
    p :: i A → i A'.

Axiom arrow_neg : forall p A A',
    p :: A → A' ->
    p :: -A → -A'.

Hint Resolve HTypes STypes TTypes CNOTTypes : base_types_db.
Hint Resolve cap_elim_l cap_elim_r : base_types_db.

Hint Resolve HTypes STypes TTypes CNOTTypes : typing_db.
Hint Resolve cap_intro cap_elim_l cap_elim_r : typing_db.
Hint Resolve SeqTypes : typing_db.

Lemma eq_arrow_r : forall g A B B',
    g :: A → B ->
    B = B' ->
    g :: A → B'.
Proof. intros; subst; easy. Qed.


(* Tactics *)

Ltac is_I A :=
  match A with
  | I => idtac
  end.

Ltac is_prog1 A :=
  match A with
  | H' => idtac
  | S' => idtac
  | T' => idtac
  end. 
              
Ltac is_prog2 A :=
  match A with
  | CNOT => idtac
  end.

(* Reduces to sequence of H, S and CNOT *)
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
         | |- ?g (S _) (S _) :: ?T => apply tensor_inc2
         | |- ?g 0 (S (S _)) :: ?T => apply tensor_inc_r
         | |- ?g (S (S _)) 0 :: ?T => apply tensor_inc_l
         | |- ?g 1 0 :: ?T       => apply tensor_base2_inv
         | |- ?g 0 1 :: ?T       => apply tensor_base2
         | |- ?g 1 0 :: ?T       => apply tensor2_comm
         | |- ?g (S _) :: ?T     => is_prog1 g; apply tensor_inc
         | |- ?g 0 :: ?T         => is_prog1 g; apply tensor_base
         | |- ?g :: ?A ⊗ ?B → _  => tryif (is_I A + is_I B) then fail else
             rewrite (decompose_tensor A B) by (auto 50 with sing_db)
         | |- ?g :: ?A → ?B      => tryif is_evar A then fail else
             solve [eauto with base_types_db]
         | |- ?B = ?B'          => tryif has_evar B then fail else
            (repeat rewrite mul_tensor_dist);
            (repeat normalize_mul);
            (repeat rewrite <- i_tensor_dist_l);
            (repeat rewrite <- neg_tensor_dist_l);
            autorewrite with mul_db;
            try reflexivity
         end.








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
