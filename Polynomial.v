Require Import Psatz.
Require Import String.
Require Export Complex.
Require Export VecSet.
Require Import List.
Require Import Setoid.

(*
Require Export CoRN.fta.FTA. 
Require Export CoRN.coq_reals.Rreals_iso.
*)


Declare Scope poly_scope.
Delimit Scope poly_scope with P.
Open Scope poly_scope.



(* polynomial represented by a list of coeficients and a degree*)
Definition Polynomial := list C.

Definition Peval (p : Polynomial) (x : Complex.C):=
  Csum (fun i => (nth i p C0)* x^i) (length p).

Definition Peq (p1 p2 : Polynomial) :=
  Peval p1 = Peval p2. 

Fixpoint Pplus (p1 p2 : Polynomial) : Polynomial := 
  match p1 with 
  | [] => p2
  | (a1 :: p1') =>
    match p2 with
    | [] => p1
    | (a2 :: p2') => (a1 + a2) :: (Pplus p1' p2')
    end
  end. 

Fixpoint Pmult (p1 p2 : Polynomial) : Polynomial := 
  match p1 with 
  | [] => []
  | (a1 :: p1') => Pplus (map (Cmult a1) p2) (C0 :: (Pmult p1' p2))
  end. 

Fixpoint Psum (f : nat -> Polynomial) (n : nat) : Polynomial := 
  match n with
  | 0 => [C0]
  | S n' => (Pplus (Psum f n') (f n'))
  end.

Infix "≅" := Peq (at level 70) : poly_scope. 
Infix "+," := Pplus (at level 50, left associativity) : poly_scope. 
Infix "*," := Pmult (at level 40, left associativity) : poly_scope.
Notation "P [[ x ]]" := (Peval P x) (at level 0) : poly_scope.  

(* some useful lemmas about Peval *)
Lemma cons_eval : forall (p1 : Polynomial) (a c : C),
  (a :: p1)[[c]] = a + c * (p1[[c]]).
Proof. intros. 
       unfold Peval.
       simpl length. 
       rewrite <- Csum_extend_l.
       repeat apply f_equal_gen; try easy; try lca. 
       rewrite Csum_mult_l; apply Csum_eq_bounded.
       intros. 
       lca. 
Qed.

Lemma Pplus_eval : forall (p1 p2 : Polynomial) (c : C),
  (p1 +, p2)[[c]] = p1[[c]] + p2[[c]].
Proof. induction p1 as [| a1]. 
       - intros. 
         unfold Peval; lca. 
       - intros. 
         destruct p2. 
         + unfold Peval; lca. 
         + simpl in *. 
           do 3 rewrite cons_eval. 
           rewrite IHp1; lca. 
Qed.

Lemma Pmult_eval : forall (p1 p2 : Polynomial) (c : C),
  (p1 *, p2)[[c]] = p1[[c]] * p2[[c]].
Proof. induction p1 as [| a1].
       - intros; lca. 
       - intros; simpl. 
         rewrite Pplus_eval.
         do 2 rewrite cons_eval.
         rewrite IHp1, Cmult_plus_distr_r.
         apply f_equal_gen; try lca. 
         apply f_equal_gen; try easy. 
         unfold Peval.
         rewrite map_length, Csum_mult_l.
         apply Csum_eq_bounded; intros. 
         replace C0 with (Cmult a1 C0) by lca. 
         rewrite map_nth, Cmult_0_r.
         lca. 
Qed.

Lemma Psum_eval : forall (f : nat -> Polynomial) (n : nat) (c : C),
  (Psum f n)[[c]] = Csum (fun i => (f i)[[c]]) n.
Proof. induction n as [| n'].
       - intros. unfold Peval; lca. 
       - intros; simpl.  
         rewrite Pplus_eval.
         repeat apply f_equal_gen; try easy; try lca. 
Qed.


(* Now we show that Peq is an equivalence relation, and we prove compatability lemmas *)


Lemma Peq_refl : forall (p : Polynomial), p ≅ p.
Proof. easy. Qed.

Lemma Peq_symm : forall (p1 p2 : Polynomial), p1 ≅ p2 -> p2 ≅ p1.
Proof. easy. Qed. 

Lemma Peq_trans : forall (p1 p2 p3 : Polynomial), 
  p1 ≅ p2 -> p2 ≅ p3 -> p1 ≅ p3.
Proof. intros. 
       unfold Peq in *; rewrite H; easy. 
Qed.

Lemma Pplus_eq_compat : forall (p1 p1' p2 p2' : Polynomial),
  p1 ≅ p1' -> p2 ≅ p2' -> p1 +, p2 ≅ p1' +, p2'.
Proof. intros.
       unfold Peq in *.
       apply functional_extensionality; intros. 
       do 2 rewrite Pplus_eval. 
       rewrite H, H0; easy. 
Qed.

Lemma Pmult_eq_compat : forall (p1 p1' p2 p2' : Polynomial),
  p1 ≅ p1' -> p2 ≅ p2' -> p1 *, p2 ≅ p1' *, p2'.
Proof. intros.
       unfold Peq in *.
       apply functional_extensionality; intros. 
       do 2 rewrite Pmult_eval. 
       rewrite H, H0; easy. 
Qed.

Add Parametric Relation : Polynomial Peq
  reflexivity proved by Peq_refl
  symmetry proved by Peq_symm
  transitivity proved by Peq_trans
  as Peq_equiv_rel.
  

Add Parametric Morphism : Pplus
  with signature Peq ==> Peq ==> Peq as Pplus_mor.
Proof. intros p1 p2 H p1' p2' H0; apply Pplus_eq_compat; easy. Qed.

Add Parametric Morphism : Pmult
  with signature Peq ==> Peq ==> Peq as Pmult_mor.
Proof. intros p1 p2 H p1' p2' H0; apply Pmult_eq_compat; easy. Qed.

Add Parametric Morphism : cons
  with signature eq ==> Peq ==> Peq as cons_mor.
Proof. intros c p1 p2 H. 
       unfold Peq in *.
       apply functional_extensionality; intros. 
       do 2 rewrite cons_eval.
       rewrite H; easy. 
Qed. 



(* now we prove some basic lemmas *)

Lemma Pplus_comm : forall (p1 p2 : Polynomial),
  p1 +, p2 = p2 +, p1. 
Proof. induction p1 as [| h];
         intros; destruct p2; try easy; simpl.  
       rewrite IHp1, Cplus_comm; easy. 
Qed.


Lemma Pplus_assoc : forall (p1 p2 p3 : Polynomial),
  (p1 +, p2) +, p3 = p1 +, (p2 +, p3).
Proof. induction p1 as [| h]; try easy.    
       intros. 
       destruct p2; destruct p3; try easy; simpl. 
       rewrite IHp1, Cplus_assoc; easy.
Qed.

Lemma Pplus_0_r : forall (p : Polynomial),
  p +, [] = p.
Proof. intros. 
       destruct p; easy. 
Qed.


Lemma C0_Peq_nil : [C0] ≅ [].
Proof. apply functional_extensionality; intros; lca. Qed.


Lemma Pmult_0_r : forall (p : Polynomial),
  p *, [] ≅ [].
Proof. induction p as [| a]; try easy.
       simpl. 
       rewrite IHp.
       apply C0_Peq_nil.
Qed.

Lemma Pmult_comm_helper : forall (n : nat) (p1 p2 : Polynomial),
  (length p1 + length p2 <= n)%nat -> 
  p1 *, p2 ≅ p2 *, p1. 
Proof. induction n as [| n'].
       - intros. 
         destruct p1; destruct p2; try easy.          
       - intros.
         destruct p1; destruct p2; try (rewrite Pmult_0_r; easy). 
         simpl in *. 
         rewrite (IHn' p1 (c0 :: p2)), (IHn' p2 (c :: p1)); simpl; try lia. 
         rewrite (IHn' p1 p2); try lia. 
         do 2 rewrite <- Pplus_assoc.
         rewrite (Pplus_comm _ (map (Cmult c0) p1)), Cmult_comm; easy. 
Qed.         

Lemma Pmult_comm : forall (p1 p2 : Polynomial),
  p1 *, p2 ≅ p2 *, p1. 
Proof. intros. 
       apply (Pmult_comm_helper (length p1 + length p2)).
       easy. 
Qed.


Lemma map_comm_distr_l : forall (p1 p2 : Polynomial) (c : C),
  map (Cmult c) (p1 +, p2) = map (Cmult c) p1 +, map (Cmult c) p2.
Proof. induction p1 as [| a1]; try easy. 
       intros. 
       destruct p2; try easy; simpl. 
       rewrite IHp1.
       repeat (apply f_equal_gen; try lca); easy.
Qed.


Lemma Pmult_plus_distr_l : forall (p1 p2 p3 : Polynomial),
  p1 *, (p2 +, p3) ≅ p1 *, p2 +, p1 *, p3.
Proof. induction p1 as [| a1]; try easy. 
       intros. 
       simpl. rewrite IHp1.
       rewrite map_comm_distr_l.
       unfold Peq; apply functional_extensionality; intros. 
       repeat (rewrite Pplus_eval).
       repeat (rewrite <- Cplus_assoc).
       apply f_equal_gen; try easy.
       repeat rewrite cons_eval.
       rewrite Pplus_eval.
       lca. 
Qed.

Lemma Pmult_plus_distr_r : forall (p1 p2 p3 : Polynomial),
  (p2 +, p3) *, p1 ≅ p2 *, p1 +, p3 *, p1.
Proof. intros. 
       rewrite Pmult_comm, Pmult_plus_distr_l. 
       rewrite Pmult_comm, (Pmult_comm _ p3). 
       easy. 
Qed.

Lemma cons_simplify : forall (p : Polynomial) (a : C),
  (a :: p) = [a] +, (C0 :: p).
Proof. intros. 
       unfold Pplus. 
       rewrite Cplus_0_r; easy. 
Qed.

Lemma cons_0_mult : forall (p1 p2 : Polynomial),
  (C0 :: p1) *, p2 ≅ C0 :: (p1 *, p2).
Proof. intros; simpl. 
       assert (H' : (map (Cmult C0) p2) ≅ ([C0] *, p2)).
       { simpl. rewrite C0_Peq_nil, Pplus_comm; easy. }
       rewrite H', C0_Peq_nil. 
       easy. 
Qed.

Lemma cons_singleton_mult : forall (p : Polynomial) (a : C),
  [a] *, p ≅ map (Cmult a) p.
Proof. intros; simpl. 
       rewrite C0_Peq_nil, Pplus_comm; easy.
Qed.

Lemma Pmult_assoc_singleton : forall  (a1 : C) (p2 p3 : Polynomial),
  ([a1] *, p2) *, p3 ≅ [a1] *, (p2 *, p3).
Proof. induction p2 as [| a2].
       - intros. 
         rewrite Pmult_0_r; simpl. 
         rewrite C0_Peq_nil; easy. 
       - intros.
         rewrite (cons_simplify p2 a2), Pmult_plus_distr_l, 
                 Pmult_plus_distr_r, (Pmult_comm _ (C0 :: p2)).
         do 2 rewrite cons_0_mult. 
         rewrite (Pmult_comm p2), IHp2, Pmult_plus_distr_r, Pmult_plus_distr_l, cons_0_mult.
         rewrite (Pmult_comm _ (C0 :: p2 *, p3)), cons_0_mult, 
                 (Pmult_comm _ [a1]), cons_singleton_mult; simpl map.  
         rewrite cons_singleton_mult, (cons_singleton_mult _ a2), 
                 (cons_singleton_mult (map (Cmult a2) p3)), map_map.
         repeat (apply f_equal_gen; try easy).
         apply functional_extensionality; intros. 
         lca.
Qed. 

Lemma Pmult_assoc : forall (p1 p2 p3 : Polynomial),
  (p1 *, p2) *, p3 ≅ p1 *, (p2 *, p3).
Proof. induction p1 as [| a1]; try easy. 
       intros. 
       rewrite cons_simplify.
       do 3 rewrite Pmult_plus_distr_r, cons_0_mult.
       rewrite Pmult_assoc_singleton, IHp1.
       easy. 
Qed.

(* We now need to show that if two polynomials are equal at infinite values, 
   then they are infinite everywhere *)

Lemma Peq_head_eq : forall (p1 p2 : Polynomial) (a1 a2 : C),
  (a1 :: p1) ≅ (a2 :: p2) -> a1 = a2.
Proof. intros. 
       unfold Peq, Peval in H.
       apply (f_equal_inv C0) in H.
       simpl length in H.
       rewrite (Csum_unique a1), (Csum_unique a2) in H; auto. 
       all : exists O; split; try lia; split; try lca.  
       all : intros; destruct x'; try easy; lca. 
Qed.


Lemma Peq_tail_eq : forall (p1 p2 : Polynomial) (a1 a2 : C),
  (a1 :: p1) ≅ (a2 :: p2) -> p1 ≅ p2.
Proof. intros. 
       unfold Peq, Peval in *.
       simpl length in H.
       apply functional_extensionality; intros. 
       destruct (Ceq_dec x C0).
       - Admitted. 


Lemma Peq_length_eq_helper : forall (n : nat) (p1 p2 : Polynomial),
  p1 ≅ p2 -> 
  length p1 = n -> length p2 = n ->
  p1 = p2. 
Proof. induction n as [| n']. 
       - intros. 
         destruct p1; destruct p2; try easy. 
       - intros. 
         destruct p1; destruct p2; try easy. 
         simpl in *.
         apply Nat.succ_inj in H0.
         apply Nat.succ_inj in H1.
         repeat apply f_equal_gen; try easy. 
         apply (Peq_head_eq p1 p2); easy. 
         apply IHn'; try easy.
         apply (Peq_tail_eq _ _ c c0); easy.
Qed.

(* now we define the degree of a polynomial *) 

Local Open Scope nat_scope.

Fixpoint prune (p : Polynomial) : Polynomial :=
  match p with 
  | [] => []
  | (a :: p') => 
    match (Ceq_dec a C0) with
    | left _ => prune p'
    | right _ => p
    end
  end. 

Definition compactify (p : Polynomial) : Polynomial :=
  rev (prune (rev p)).

Lemma prune_prune : forall (p : Polynomial),
  prune (prune p) = prune p.
Proof. induction p as [| a]; try easy; simpl.
       destruct (Ceq_dec a C0); try easy; simpl.
       destruct (Ceq_dec a C0); easy. 
Qed.       

Lemma prune_length : forall (p : Polynomial),
  length (prune p) <= length p.
Proof. induction p as [| a]; try easy; simpl. 
       destruct (Ceq_dec a C0); try easy; simpl.
       lia. 
Qed. 

Lemma compactify_length : forall (p : Polynomial),
  length (compactify p) <= length p.
Proof. intros. 
       unfold compactify.
       rewrite rev_length, <- (rev_length p).
       apply prune_length.
Qed.

Lemma compactify_compactify : forall (p : Polynomial),
  compactify (compactify p) = compactify p.
Proof. intros. 
       unfold compactify.
       rewrite rev_involutive, prune_prune; easy.
Qed.

Lemma prune_0_reduce : forall (p : Polynomial),
  prune p = [] -> prune (p ++ [C0]) = [].
Proof. induction p as [| a]. 
       - intros; simpl. 
         destruct (Ceq_dec C0 C0); try easy. 
       - intros. 
         simpl in *.
         destruct (Ceq_dec a C0); try easy. 
         apply IHp; easy. 
Qed.

Lemma Peq_0_prune_0 : forall (p : Polynomial),
  p ≅ [] -> prune p = []. 
Proof. induction p; try easy.
       intros; simpl. 
       destruct (Ceq_dec a C0).
       - apply IHp. 
         rewrite <- C0_Peq_nil in H.
         apply (Peq_tail_eq _ _ a C0); easy. 
       - rewrite <- C0_Peq_nil in H.
         apply (Peq_head_eq _ _ a C0) in H; easy. 
Qed.

Lemma Peq_0_compactify_0 : forall (n : nat) (p : Polynomial),
  length p = n -> p ≅ [] -> compactify p = []. 
Proof. induction n as [| n']. 
       - intros. destruct p; try easy. 
       - intros. 
         destruct (rev p) eqn:E.
         + unfold compactify.
           rewrite E; easy.
         + Admitted.

Lemma Peq_compactify_eq : forall (n : nat) (p1 p2 : Polynomial),
  length p1 <= n -> 
  p1 ≅ p2 -> compactify p1 = compactify p2.
Proof. induction n as [| n'].
       - intros. 
         destruct p1; try easy. 
         rewrite (Peq_0_compactify_0 (length p2) p2); easy. 
       - intros. 
         unfold compactify in *.
         destruct (rev p1) eqn:E.
         + replace (rev (prune (rev p2))) with (compactify p2) by easy. 
           rewrite (Peq_0_compactify_0 (length p2)); try easy. 
           rewrite <- H0, <- (rev_involutive p1), E; easy. 
         + simpl. 



induction p2; try easy.  
         intros. 


Lemma p_Peq_pruned_p_helper : forall (n : nat) (p : Polynomial),
  (length p = n) -> p ≅ compactify p.
Proof. induction n as [| n']. 
       - intros. destruct p; easy. 
       - intros. 
         unfold compactify.
         destruct (rev p) eqn:E.
         + simpl.  
           rewrite <- (rev_involutive p), E.
           easy. 
         + simpl. 
           destruct (Ceq_dec c C0).
           * rewrite <- (rev_involutive l).
             unfold compactify in IHn'.
             rewrite <- IHn', <- (rev_involutive p), E. 
             apply functional_extensionality; intros. 
             unfold Peval.
             do 2 rewrite rev_length. simpl length. 
             rewrite <- Cplus_0_r, <- Csum_extend_r.
             apply Cplus_simplify.
             apply Csum_eq_bounded; intros; simpl. 
             rewrite app_nth1; auto. 
             rewrite rev_length; easy.
             rewrite <- (plus_0_r (length l)); simpl.
             rewrite <- rev_length, (app_nth2_plus (rev l) [c]), e.
             lca. 
             rewrite <- rev_length, E in H.
             simpl in H.
             apply Nat.succ_inj in H.
             rewrite rev_length; easy.
           * rewrite <- E, rev_involutive; easy. 
Qed.

Lemma p_Peq_pruned_p : forall (p : Polynomial),
  p ≅ compactify p.
Proof. intros. 
       apply (p_Peq_pruned_p_helper (length p)); easy. 
Qed.


Lemma Pplus_length : forall (p1 p2 : Polynomial),
  length (p1 +, p2) = max (length p1) (length p2).
Proof. induction p1 as [| a1]; try easy. 
       intros. 
       destruct p2; try easy. 
       simpl. 
       rewrite IHp1; easy. 
Qed.

Lemma Pmult_length_le : forall (p1 p2 : Polynomial),
  p2 <> [] ->
  length p1 <= length (p2 *, p1).
Proof. induction p1 as [| a1].
       - intros; destruct p2; try easy; simpl; lia.
       - intros. destruct p2; try easy; simpl.
         rewrite Pplus_length, map_length.
         destruct p2; try lia.  
Qed.         

Lemma Pmult_length_helper : forall (n : nat) (a1 a2 : C) (p1 p2 : Polynomial),
  length p1 <= n ->
  length ((a1 :: p1) *, (a2 :: p2)) = (length (a1 :: p1)) + (length (a2 :: p2)) - 1.
Proof. induction n as [| n'].
       - intros.
         destruct p1; try easy; simpl. 
         rewrite Pplus_0_r, map_length.
         easy. 
       - intros; simpl.  
         rewrite Pplus_length, map_length; simpl. 
         destruct p1.
         + simpl; lia. 
         + rewrite max_r, IHn'.
           simpl; lia. 
           simpl in H; apply le_S_n; easy.
           assert (H0 : length (a2 :: p2) <= length ((c :: p1) *, (a2 :: p2))).
           { apply Pmult_length_le; easy. }
           simpl in *. 
           lia. 
Qed. 

Lemma Pmult_length : forall (n : nat) (a1 a2 : C) (p1 p2 : Polynomial),
  p1 <> [] -> p2 <> [] ->
  length (p1 *, p2) = length p1 + length p2 - 1.          
Proof. intros. 
       destruct p1; destruct p2; try easy. 
       apply (Pmult_length_helper (length (c :: p1))).
       simpl; lia. 
Qed.


Definition degree (p : Polynomial) : nat :=
  length (compactify p) - 1. 


Add Parametric Morphism : degree
  with signature Peq ==> eq as degree_mor.
Proof. intros p1 p2 H. 
       unfold degree. 


 
Qed. 



Axiom Pplus_degree1 : forall (p1 p2 : Polynomial),
  degree (p1 +, p2) <= max (degree p1) (degree p2).

Axiom Pplus_degree2 : forall (p1 p2 : Polynomial),
  degree p1 < degree p2 -> 
  degree (p1 +, p2) = degree p2. 

Axiom Pmult_degree : forall (p1 p2 : Polynomial),
  degree (p1 *, p2) = (degree p1) + (degree p2).


       


(*****************************************************)
(* First, we show that our C is the same as ccorns C *)
(*****************************************************)



(*

Definition CtoCC (c : Complex.C) : CC_set := Build_CC_set (RasIR (fst c)) (RasIR (snd c)). 
Definition CCtoC (c : CC_set) : Complex.C := (IRasR (Re c), IRasR (Im c)).


Lemma CasCCasC_id : forall (x : Complex.C), (CCtoC (CtoCC x) = x).
Proof. intros.
       unfold CtoCC, CCtoC.
       simpl.
       do 2 rewrite RasIRasR_id.
       rewrite surjective_pairing.
       easy. 
Qed.


(*
Lemma CCasCasCC_id : forall (x : CC_set), (CtoCC (CCtoC x) = x).
Proof. intros.
       unfold CtoCC, CCtoC.
       simpl.
       do 2 rewrite RasIRasR_id.
       rewrite surjective_pairing.
       easy. 
Qed. *)

*)
       

Theorem Fundamental_Theorem_Algebra : forall (p : Polynomial),
  (exists c : C, p[[c]] = C0).
Proof. Admitted.

