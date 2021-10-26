Require Import Psatz.
Require Import String.
Require Export Complex.
Require Export VecSet.
Require Import List.
Require Import Setoid.

Declare Scope poly_scope.
Delimit Scope poly_scope with P.
Open Scope poly_scope.

(* some prelim lemmas that should be moved *)

Lemma diff_pow_n : forall (n : nat) (a b : C),
  (a^(S n) - b^(S n)) = (a - b) * (Csum (fun i => a^i * b^(n - i)) (S n)).
Proof. intros.
       unfold Cminus. 
       rewrite Cmult_plus_distr_r, Csum_mult_l, Csum_mult_l.
       rewrite <- Csum_extend_r, <- Csum_extend_l, Nat.sub_diag, Nat.sub_0_r.      
       replace (a * (a ^ n * b ^ 0)) with (a^ (S n)) by lca. 
       replace (- b * (a ^ 0 * b ^ n)) with (- b^(S n)) by lca. 
       rewrite (Cplus_comm _ (a ^ _)), <- Cplus_assoc. 
       apply Cplus_simplify; try easy. 
       rewrite Cplus_assoc, (Cplus_comm _ (- b ^ _)), <- (Cplus_0_r (- b ^ _)). 
       do 2 rewrite <- Cplus_assoc. 
       apply Cplus_simplify; try easy. 
       rewrite <- Csum_plus, Cplus_0_l.
       rewrite Csum_0_bounded; auto.  
       intros.
       replace (n - x)%nat with (S (n - S x))%nat by lia. 
       lca. 
Qed.

Lemma destruct_from_last : forall {X} (n : nat) (d : X) (l : list X),
  length l = S n -> l = (firstn n l) ++ [nth n l d].
Proof. induction n as [| n'].
       - intros. 
         repeat (destruct l; try easy).
       - intros. 
         destruct l; try easy.
         simpl in *. 
         apply Nat.succ_inj in H.
         rewrite <- IHn'; easy.
Qed.     


Lemma ind_from_end_helper : forall {X} (p : list X -> Prop) (n : nat),
  p [] -> 
  (forall (x : X) (l : list X), p l -> p (l ++ [x])) -> 
  forall l, length l = n -> p l. 
Proof. intros X p n H H0.
       induction n as [| n'].
       - intros. 
         destruct l; try easy.
       - intros. destruct l; try easy. 
         rewrite (destruct_from_last n' x); auto. 
         apply H0.
         apply IHn'.
         rewrite firstn_length, H1.
         rewrite min_l; lia.
Qed.
       
Lemma ind_from_end : forall {X} (p : list X -> Prop),
  p [] -> 
  (forall (x : X) (l : list X), p l -> p (l ++ [x])) -> 
  forall l, p l. 
Proof. intros. 
       apply (ind_from_end_helper _ (length l)); easy. 
Qed.


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

Definition Popp (p : Polynomial) : Polynomial :=
  Pmult [-C1] p.

Fixpoint Psum (f : nat -> Polynomial) (n : nat) : Polynomial := 
  match n with
  | 0 => [C0]
  | S n' => (Pplus (Psum f n') (f n'))
  end.

Infix "≅" := Peq (at level 70) : poly_scope. 
Infix "+," := Pplus (at level 50, left associativity) : poly_scope. 
Infix "*," := Pmult (at level 40, left associativity) : poly_scope.
Notation "-, P" := (Popp P) (at level 30) : poly_scope. 
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

Lemma app_eval : forall (f g : Polynomial),
  Peval (f ++ g) = (fun c => f [[ c ]] + ((repeat C0 (length f)) ++ g) [[ c ]]). 
Proof. intros. 
       apply functional_extensionality; intros.  
       unfold Peval.
       rewrite app_length, Csum_sum. 
       apply Cplus_simplify.
       apply Csum_eq_bounded; intros. 
       rewrite app_nth1; easy.
       rewrite app_length, Csum_sum.
       rewrite repeat_length.  
       assert (Csum (fun i : nat => nth i (repeat C0 (Datatypes.length f) ++ g) C0 * x ^ i) 
                    (length f) = C0).
       { apply Csum_0_bounded; intros. 
         rewrite app_nth1.
         destruct (nth_in_or_default x0 (repeat C0 (Datatypes.length f)) C0).
         - apply repeat_spec in i.
           rewrite i; lca. 
         - rewrite e; lca.
         - rewrite repeat_length; easy. }
       rewrite H, Cplus_0_l.
       apply Csum_eq_bounded; intros. 
       rewrite app_nth2_plus, app_nth2, repeat_length.
       replace (Datatypes.length f + x0 - Datatypes.length f)%nat with x0 by lia. 
       easy. 
       rewrite repeat_length; lia. 
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

Lemma Pscale_comm_nempty : forall (a : C) (p : Polynomial),
  p <> [] -> [a] *, p = p *, [a].
Proof. induction p as [| h]; try easy.
       intros; simpl. 
       destruct p.
       + simpl; rewrite Cmult_comm; easy. 
       + rewrite <- IHp; try easy.
         apply f_equal_gen; try (apply f_equal_gen; try lca; easy).
         simpl. 
         rewrite Pplus_0_r, Cplus_0_r.
         reflexivity.
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

Lemma map_1_id : forall (p : Polynomial),
  map (Cmult C1) p = p. 
Proof. induction p; try easy. 
       simpl. 
       rewrite IHp, Cmult_1_l.
       easy. 
Qed.

Lemma Pmult_1_l : forall (p : Polynomial),
  [C1] *, p ≅ p.
Proof. intros. 
       simpl. 
       rewrite map_1_id, C0_Peq_nil, Pplus_0_r.
       easy. 
Qed.

Lemma Pmult_1_r : forall (p : Polynomial),
  p *, [C1] ≅ p.
Proof. intros. 
       rewrite Pmult_comm. 
       apply Pmult_1_l.
Qed.

Lemma Pplus_opp_r : forall (p : Polynomial),
  p +, -,p ≅ [].
Proof. induction p as [| a]. 
       - unfold Popp; simpl.  
         rewrite C0_Peq_nil; easy. 
       - simpl.
         assert (H' : (map (Cmult (- C1)) p +, []) ≅ -, p).
         { unfold Popp, Pmult; 
           rewrite C0_Peq_nil; easy. }
         rewrite H', IHp. 
         replace (a + (- C1 * a + C0)) with C0 by lca. 
         rewrite C0_Peq_nil; easy. 
Qed.

Lemma Pplus_opp_l : forall (p : Polynomial),
  -,p +, p ≅ [].
Proof. intros. 
       rewrite Pplus_comm. 
       apply Pplus_opp_r.
Qed.

Lemma head_0_Pmult_x : forall (p : Polynomial),
  (C0 :: p) ≅ [C0; C1] *, p.
Proof. intros. 
       rewrite cons_0_mult, Pmult_1_l.
       easy. 
Qed.

(* We now need to show that if two polynomials are equal at infinite values, 
   then they are infinite everywhere *)

    
(* we start by defining limits *) 

Definition limit_at_point (f : C -> C) (a L : C) : Prop :=
  forall ϵ : R, ϵ > 0 -> exists δ, (δ > 0 /\ forall x, x <> a -> Cmod (x - a) < δ -> Cmod (f(x) - L) < ϵ).

Definition continuous_at (f : C -> C) (a : C) : Prop :=
  limit_at_point f a (f a).

Lemma limit_unique : forall (f : C -> C) (a L1 L2 : C),
  limit_at_point f a L1 -> limit_at_point f a L2 ->
  L1 = L2.
Proof. intros. 
       destruct (Ceq_dec (L1 - L2) C0).
       - rewrite <- Cplus_0_r, <- e.
         lca. 
       - unfold limit_at_point in *.
         destruct (H ((Cmod (L1 - L2)) / 2)%R) as [δ1 [H1 H2] ];
         destruct (H0 ((Cmod (L1 - L2)) / 2)%R) as [δ2 [H3 H4] ];
         try (unfold Rdiv; apply Rmult_gt_0_compat; try lra; apply Cmod_gt_0; easy).
         assert (H5 : exists b, b <> a /\ Cmod (b - a) < (Rmin δ1 δ2)).
         { exists (a + ((Rmin δ1 δ2) / 2, 0)%R)%C.
           split. 
           + unfold not; intros. 
             apply (f_equal (Cplus (-a))) in H5.
             rewrite Cplus_assoc, Cplus_opp_l, Cplus_0_l in H5.
             apply (f_equal fst) in H5; simpl in H5.
             apply (f_equal (Rmult 2)) in H5.
             rewrite Rmult_0_r in H5.
             replace (2 * (Rmin δ1 δ2 / 2))%R with (Rmin δ1 δ2) in H5 by lra. 
             apply (Rmin_pos δ1 δ2) in H1; auto.
             lra. 
           + unfold Cplus, Cminus, Copp, Cmod; simpl.
             replace (snd a + 0 + - snd a)%R with 0 by lra. 
             replace (fst a + Rmin δ1 δ2 / 2 + - fst a)%R with (Rmin δ1 δ2 / 2)%R by lra. 
             rewrite Rmult_0_l, Rplus_0_r, Rmult_1_r, sqrt_square. 
             apply Rlt_eps2_eps.
             apply (Rmin_pos δ1 δ2); auto.
             unfold Rdiv.
             apply Rmult_le_pos; try lra. 
             left; apply (Rmin_pos δ1 δ2); auto. }
         destruct H5 as [b [H5 H6] ].
         assert (H7 : Cmod (f b - L1) + Cmod (f b - L2) < Cmod (L1 - L2)).
         rewrite (double_var (Cmod (L1 - L2))).
         apply Rplus_lt_compat.
         apply H2; auto. 
         assert (H' := (Rmin_l δ1 δ2)). lra. 
         apply H4; auto. 
         assert (H' := (Rmin_r δ1 δ2)). lra. 
         assert (H8 :  Cmod (L1 - (f b) + (f b - L2)) <= Cmod (L1 - f b) + Cmod (f b - L2)).
         { apply Cmod_triangle. }
         replace (L1 - f b + (f b - L2)) with (L1 - L2) in H8 by lca. 
         replace (L1 - f b) with (- (f b - L1)) in H8 by lca. 
         rewrite Cmod_opp in H8. lra. 
Qed.

Lemma limit_const : forall (a x : C),
  limit_at_point (fun c => a) x a.
Proof. unfold limit_at_point; intros. 
       exists 1. split; try lra. 
       intros. 
       replace (a - a) with C0 by lca. 
       rewrite Cmod_0.
       easy. 
Qed.

Lemma limit_const_poly : forall (a x : C),
  limit_at_point (Peval [a]) x a. 
Proof. unfold limit_at_point.
       intros. 
       exists 1; split. 
       lra. 
       intros. 
       unfold Peval; simpl. 
       replace (C0 + a * C1 - a) with C0 by lca. 
       rewrite Cmod_0.
       easy. 
Qed.

Lemma limit_linear_poly : forall (a x : C),
  limit_at_point (Peval [C0;a]) x (a * x). 
Proof. unfold limit_at_point; intros. 
       destruct (Ceq_dec a C0); subst.
       - exists 1.
         split; try lra. 
         intros. 
         replace (([C0; C0]) [[x0]] - C0 * x) with C0 by lca. 
         rewrite Cmod_0.
         easy.
       - exists (ϵ / (Cmod a))%R.
         split. 
         unfold Rdiv.  
         apply Rmult_gt_0_compat; auto.
         apply Rinv_0_lt_compat.
         apply Cmod_gt_0; easy. 
         intros. 
         replace (([C0; a]) [[x0]]) with (a * x0) by lca. 
         unfold Cminus. 
         rewrite Copp_mult_distr_r, <- Cmult_plus_distr_l, Cmod_mult.
         assert (H2 : Cmod (x0 - x) * Cmod a < ϵ / Cmod a * Cmod a).
         { apply Rmult_lt_compat_r; auto. 
           apply Cmod_gt_0; easy. }
         unfold Rdiv, Cminus in H2.
         rewrite Rmult_assoc, Rinv_l in H2.
         lra.
         unfold not; intros. 
         apply n. 
         apply Cmod_eq_0; easy.
Qed.

Lemma limit_scale : forall (f : C -> C) (a c L : C),
  limit_at_point f a L ->
  limit_at_point (fun x => c * f x) a (c * L).
Proof. intros. 
       unfold limit_at_point in *.
       intros. 
       destruct (Ceq_dec c 0); subst.
       - exists 1. 
         split; try lra. 
         intros. 
         replace (C0 * f x - C0 * L) with C0 by lca. 
         rewrite Cmod_0; easy.
       - destruct (H (ϵ / Cmod c)%R).
         unfold Rdiv.
         apply Rmult_lt_0_compat; auto. 
         apply Rinv_0_lt_compat.
         apply Cmod_gt_0; auto. 
         exists (x)%R.
         destruct H1.
         split. auto. 
         intros. 
         unfold Cminus.
         rewrite Copp_mult_distr_r, <- Cmult_plus_distr_l, Cmod_mult.
         apply H2 in H3; auto. 
         apply (Rmult_lt_compat_l (Cmod c)) in H3.
         unfold Rdiv in H3.
         rewrite (Rmult_comm ϵ), <- Rmult_assoc, Rinv_r, Rmult_1_l in H3; auto.
         unfold not; intros; apply n.
         apply Cmod_eq_0; auto. 
         apply Cmod_gt_0; auto.
Qed.

Lemma limit_plus : forall (f1 f2 : C -> C) (a L1 L2 : C),
  limit_at_point f1 a L1 -> limit_at_point f2 a L2 ->
  limit_at_point (fun c => f1 c + f2 c) a (L1 + L2).
Proof. unfold limit_at_point. 
       intros. 
       assert (H2 : ϵ / 2 > 0).
       { lra. }
       assert (H3 := H2).
       apply H in H2.
       apply H0 in H3.
       destruct H2 as [δ1 [H2 H4] ]; destruct H3 as [δ2 [H3 H5] ]. 
       exists (Rmin δ1 δ2); split. 
       apply Rmin_Rgt; auto.
       intros. 
       assert (H8 : Cmod (f1 x - L1) < ϵ / 2).
       { apply H4; auto.
         assert (H' := (Rmin_l δ1 δ2)); lra. }
       assert (H9 : Cmod (f2 x - L2) < ϵ / 2).
       { apply H5; auto.
         assert (H' := (Rmin_r δ1 δ2)); lra. }
       apply (Rplus_lt_compat (Cmod (f1 x - L1)) (ϵ / 2) (Cmod (f2 x - L2)) (ϵ / 2)) in H8; auto.
       replace (ϵ / 2 + ϵ / 2)%R with ϵ in H8 by lra.   
       replace (f1 x + f2 x - (L1 + L2))%C with ((f1 x - L1) + (f2 x - L2))%C by lca. 
       assert (H10 :  Cmod (f1 x - L1 + (f2 x - L2)) <= Cmod (f1 x - L1) + Cmod (f2 x - L2)).
       { apply Cmod_triangle. }
       lra. 
Qed.

Lemma limit_mult_0 : forall (f1 f2 : C -> C) (a : C),
  limit_at_point f1 a C0 -> limit_at_point f2 a C0 ->
  limit_at_point (fun c => f1 c * f2 c) a C0.
Proof. intros. 
       unfold limit_at_point in *.
       intros. 
       destruct (H (√ ϵ)); try apply sqrt_lt_R0; auto. 
       destruct (H0 (√ ϵ)); try apply sqrt_lt_R0; auto. 
       destruct H2; destruct H3.
       exists (Rmin x x0).       
       split. 
       apply Rmin_pos; auto.
       intros. 
       unfold Cminus in *.
       rewrite Copp_0, Cplus_0_r in *.
       rewrite Cmod_mult, <- (sqrt_def ϵ); try lra.
       apply Rmult_le_0_lt_compat; try apply Cmod_ge_0.
       all : rewrite <- (Cplus_0_r (_ x1)).
       apply H4; auto.  
       assert (H8 := Rmin_l x x0). lra. 
       apply H5; auto.  
       assert (H8 := Rmin_r x x0). lra. 
Qed.

Lemma limit_mult : forall (f1 f2 : C -> C) (a L1 L2 : C),
  limit_at_point f1 a L1 -> limit_at_point f2 a L2 ->
  limit_at_point (fun c => f1 c * f2 c) a (L1 * L2).
Proof. intros. 
       assert (H' : (fun c => f1 c * f2 c) = 
                    (fun c => ((f1 c - L1) * (f2 c - L2)) + (L1 * f2 c) + (L2 * f1 c) - (L1 * L2))).
       { apply functional_extensionality. 
         intros. lca. }
       replace (L1 * L2) with (C0 + L1 * L2 + L2 * L1 - L1 * L2) by lca. 
       rewrite H'. 
       repeat apply limit_plus.
       unfold Cminus.
       apply limit_mult_0. 
       replace C0 with (L1 + - L1) by lca. 
       apply limit_plus; auto. 
       apply limit_const.
       replace C0 with (L2 + - L2) by lca. 
       apply limit_plus; auto. 
       apply limit_const.
       all : try apply limit_scale; auto.
       apply limit_const.
Qed.

Lemma continuous_plus : forall (f1 f2 : C -> C) (a : C),
  continuous_at f1 a -> continuous_at f2 a -> 
  continuous_at (fun c => f1 c + f2 c)  a.
Proof. intros. 
       unfold continuous_at in *.
       apply (limit_plus f1 f2 a (f1 a) (f2 a)); easy.
Qed.

Lemma continuous_mult : forall (f1 f2 : C -> C) (a : C),
  continuous_at f1 a -> continuous_at f2 a -> 
  continuous_at (fun c => f1 c * f2 c)  a.
Proof. intros. 
       unfold continuous_at in *.
       apply (limit_mult f1 f2 a (f1 a) (f2 a)); easy.
Qed.

Lemma constant_continuous_poly : forall (c a : C),
  continuous_at (Peval [c]) a.
Proof. intros. 
       unfold continuous_at.
       replace (([c]) [[a]]) with c by lca. 
       apply limit_const_poly.
Qed.

Lemma linear_continuous_poly : forall (c a : C),
  continuous_at (Peval [C0; c]) a.
Proof. intros. 
       unfold continuous_at.
       replace (([C0; c]) [[a]]) with (c * a) by lca. 
       apply limit_linear_poly.
Qed.

Lemma power_x_eval : forall (n : nat) (a x : C),
  (repeat C0 n ++ [a]) [[x]] = a * x^n.
Proof. intros.
       unfold Peval. 
       rewrite app_length; simpl. 
       rewrite Nat.add_1_r, <- Csum_extend_r, <- (Nat.add_0_r (length (repeat C0 n))), 
       app_nth2_plus, Nat.add_0_r, repeat_length; simpl. 
       rewrite <- Cplus_0_l.
       apply Cplus_simplify; auto. 
       apply Csum_0_bounded; intros.
       rewrite app_nth1.
       destruct (nth_in_or_default x0 (repeat C0 n) C0).
       - apply repeat_spec in i.
         rewrite i; lca. 
       - rewrite e; lca. 
       - rewrite repeat_length; easy. 
Qed.

Lemma power_x_mul_x : forall (n : nat) (a : C),
  (repeat C0 (S n) ++ [a]) ≅ [C0; C1] *, (repeat C0 n ++ [a]).
Proof. intros. 
       simpl repeat. 
       rewrite <- app_comm_cons.
       apply head_0_Pmult_x. 
Qed.

Lemma continuous_power_x : forall (n : nat) (a b : C), 
  continuous_at (Peval ((repeat C0 n) ++ [b])) a.
Proof. induction n as [| n'].
       - intros. 
         apply constant_continuous_poly.
       - intros.
         rewrite power_x_mul_x. 
         assert (H' : forall p q : Polynomial, Peval (p *, q) = fun c => p[[c]] * q[[c]]).
         { intros. 
           apply functional_extensionality. 
           intros. 
           apply Pmult_eval. }
         rewrite H'.
         apply continuous_mult.
         apply linear_continuous_poly.
         apply IHn'.
Qed.

Lemma polynomial_continuous : forall (p : Polynomial) (a : C),
  (fun p => continuous_at (Peval p) a) p.
Proof. intros.       
       apply (@ind_from_end C).
       - rewrite <- C0_Peq_nil.
         apply constant_continuous_poly. 
       - intros. 
         rewrite app_eval. 
         apply continuous_plus.
         apply H.
         apply continuous_power_x.
Qed.

Lemma constant_ae_continuous : forall (f : C -> C) (a c : C),
  continuous_at f c -> (forall x, x <> c -> f x = a) -> 
  f c = a. 
Proof. intros.
       unfold continuous_at in H.
       assert (H1 : limit_at_point f c a).
       { unfold limit_at_point.
         intros.  
         exists 1.
         split; try lra. 
         intros. 
         rewrite H0; auto.
         unfold Cminus. 
         rewrite Cplus_opp_r, Cmod_0.
         lra. }
       apply (limit_unique f c); easy.
Qed.

Lemma almost_0_implies_0 : forall (p : Polynomial),
  (forall c, c <> C0 -> p[[c]] = C0) -> p ≅ [].
Proof. intros. 
       unfold Peq.
       apply functional_extensionality; intros. 
       destruct (Ceq_dec x C0).
       - replace (([]) [[x]]) with C0 by easy. 
         apply constant_ae_continuous.
         apply polynomial_continuous.
         intros. 
         apply H; subst; easy. 
       - apply H; easy. 
Qed.

Lemma almost_Peq_implies_Peq : forall (p1 p2 : Polynomial),
  (forall c, c <> C0 -> p1[[c]] = p2[[c]]) -> p1 ≅ p2. 
Proof. intros. 
       assert (H' : p1 +, -, p2 ≅ []).
       { apply almost_0_implies_0.
         intros. 
         unfold Popp.
         rewrite Pplus_eval, Pmult_eval, H; auto. 
         replace (([- C1]) [[c]]) with (-C1) by lca. 
         lca. }
       replace p2 with ([] +, p2) by easy. 
       rewrite <- H', Pplus_assoc, Pplus_opp_l, Pplus_0_r. 
       easy. 
Qed.

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


Lemma Peq_tail_Peq_helper : forall (p1 p2 : Polynomial),
  (C0 :: p1) ≅ (C0 :: p2) -> p1 ≅ p2.
Proof. intros. 
       apply almost_Peq_implies_Peq; intros. 
       apply (f_equal_inv c) in H.
       unfold Peval in *.
       simpl length in *. 
       do 2 rewrite <- Csum_extend_l in H.
       simpl in H. 
       rewrite Cmult_0_l, Cplus_0_l, Cplus_0_l in H. 
       rewrite <- Cmult_1_l, <- (Cinv_l c), <- Cmult_assoc, Csum_mult_l; auto. 
       assert (H' : (fun x : nat => nth x p2 C0 * (c * c ^ x)) = 
                    (fun x : nat => c * (nth x p2 C0 * c ^ x))).
       { apply functional_extensionality; intros. 
         lca. }
       rewrite <- H', <- H. 
       assert (H'' : (fun x : nat => nth x p1 C0 * (c * c ^ x)) = 
                    (fun x : nat => c * (nth x p1 C0 * c ^ x))).
       { apply functional_extensionality; intros. 
         lca. }
       rewrite H''. 
       rewrite <- Csum_mult_l, Cmult_assoc, Cinv_l; auto; lca. 
Qed.


Lemma Peq_tail_Peq : forall (p1 p2 : Polynomial) (a1 a2 : C),
  (a1 :: p1) ≅ (a2 :: p2) -> p1 ≅ p2.
Proof. intros. 
       assert (H' : a1 = a2).
       { apply Peq_head_eq in H; easy. } 
       rewrite cons_simplify, (cons_simplify p2) in H; subst.
       assert (H'' : [-a2] +, [a2] +, (C0 :: p1) ≅ [-a2] +, [a2] +, (C0 :: p2)).
       { rewrite Pplus_assoc, H, <- Pplus_assoc. 
         easy. }
       simpl in H''. 
       replace (- a2 + a2 + C0) with C0 in H'' by lca. 
       apply Peq_tail_Peq_helper in H''. 
       easy. 
Qed.

Lemma Peq_app_Peq : forall (p p1 p2 : Polynomial),
  (p ++ p1) ≅ (p ++ p2) -> p1 ≅ p2.
Proof. induction p as [| a]; try easy.
       intros; simpl in H.
       apply Peq_tail_Peq in H.
       apply IHp; easy. 
Qed. 

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
         apply (Peq_tail_Peq _ _ c c0); easy.
Qed.

Lemma Peq_length_eq : forall (n : nat) (p1 p2 : Polynomial),
  p1 ≅ p2 -> length p1 = length p2 ->
  p1 = p2. 
Proof. intros. 
       apply (Peq_length_eq_helper (length p1)); easy. 
Qed.

Lemma Peq_nil_reduce : forall (p : Polynomial) (a : C),
  (a :: p) ≅ [] -> a = C0 /\ p ≅ [].
Proof. intros. 
       rewrite <- C0_Peq_nil in H.
       split. 
       - apply Peq_head_eq in H; easy. 
       - apply Peq_tail_Peq in H; easy. 
Qed.

Lemma Peq_nil_contains_C0 : forall (p : Polynomial),
  p ≅ [] -> (forall c, In c p -> c = C0).
Proof. induction p; try easy.  
       intros. 
       apply Peq_nil_reduce in H. 
       destruct H0; try (subst; easy). 
       apply IHp; easy. 
Qed.

Lemma same_elem_same_rev : forall (p : Polynomial),
  (forall c, In c p -> c = C0) -> p = repeat C0 (length p).
Proof. induction p as [| a]; try easy.
       intros; simpl. 
       rewrite (H a), IHp, repeat_length; try easy. 
       intros. 
       apply H; right; easy. 
       left; easy. 
Qed.

Lemma Peq_nil_rev_Peq_nil : forall (p : Polynomial),
  p ≅ [] -> rev p = p. 
Proof. intros.
       rewrite same_elem_same_rev, <- rev_repeat, <- same_elem_same_rev; try easy.
       all : apply Peq_nil_contains_C0; easy. 
Qed.

Lemma last_C0_Peq_front : forall (p : Polynomial),
  p ++ [C0] ≅ p.
Proof. intros. 
       unfold Peq, Peval. 
       apply functional_extensionality; intros. 
       rewrite app_length; simpl.
       rewrite Nat.add_1_r, <- Csum_extend_r.
       rewrite app_nth2, Nat.sub_diag; auto; simpl.
       rewrite Cmult_0_l, Cplus_0_r.
       apply Csum_eq_bounded; intros.
       rewrite app_nth1; easy. 
Qed.

Lemma repeat_C0_Peq_front : forall (n : nat) (p : Polynomial),
  p ++ (repeat C0 n) ≅ p.
Proof. induction n as [| n'].
       - intros; simpl. 
         rewrite app_nil_r.
         easy.
       - intros.
         simpl. 
         replace (p ++ C0 :: repeat C0 n') with (p ++ [C0] ++ repeat C0 n') by easy.
         rewrite app_assoc.
         rewrite (IHn' (p ++ [C0])), last_C0_Peq_front.
         easy.
Qed.

Lemma Peq_firstn_eq : forall (p1 p2 : Polynomial), 
  p1 ≅ p2 -> (length p1 <= length p2)%nat -> 
  p1 = firstn (length p1) p2.
Proof. induction p1 as [| a]; try easy.
       intros. 
       destruct p2; try easy. 
       simpl. 
       rewrite <- IHp1; try (simpl in *; lia).
       repeat apply f_equal_gen; try easy. 
       apply Peq_head_eq in H; easy.  
       apply Peq_tail_Peq in H; easy.  
Qed.

Lemma Peq_skipn_Peq_nil : forall (p1 p2 : Polynomial), 
  p1 ≅ p2 -> (length p1 <= length p2)%nat -> 
  skipn (length p1) p2 ≅ [].
Proof. intros. 
       apply Peq_firstn_eq in H0; auto.
       rewrite (app_nil_end p1) in H.
       rewrite H0, <- (firstn_skipn (length p1)) in H. 
       apply Peq_app_Peq in H.
       easy. 
Qed.

(* now we define prune/compactify which removes the uneccesary 0s at the end of a polynomial *) 

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

Lemma prune_idempotent : forall (p : Polynomial),
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

Lemma compactify_idempotent : forall (p : Polynomial),
  compactify (compactify p) = compactify p.
Proof. intros. 
       unfold compactify.
       rewrite rev_involutive, prune_idempotent; easy.
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
         apply (Peq_tail_Peq _ _ a C0); easy. 
       - rewrite <- C0_Peq_nil in H.
         apply (Peq_head_eq _ _ a C0) in H; easy. 
Qed.

Lemma Peq_0_compactify_0 : forall (p : Polynomial),
  p ≅ [] -> compactify p = []. 
Proof. intros. 
       unfold compactify. 
       rewrite (Peq_nil_rev_Peq_nil p); auto. 
       rewrite Peq_0_prune_0; easy.
Qed.

Lemma app_C0_compactify_reduce : forall (n : nat) (p : Polynomial),
  compactify (p ++ (repeat C0 n)) = compactify p. 
Proof. induction n as [| n'].
       - intros; simpl. 
         rewrite app_nil_r; easy. 
       - intros. 
         unfold compactify in *.
         rewrite rev_app_distr.
         rewrite rev_repeat.
         simpl.
         destruct (Ceq_dec C0 C0); try easy. 
         rewrite <- rev_repeat, <- rev_app_distr. 
         easy.
Qed.

Lemma app_C0_compactify_reduce_1 : forall (p : Polynomial),
  compactify (p ++ [C0]) = compactify p. 
Proof. intros. 
       replace [C0] with (repeat C0 1) by easy.
       apply app_C0_compactify_reduce.
Qed.

Lemma app_nonzero_compactify_reduce : forall (p : Polynomial) (a : C),
  a <> C0 -> compactify (p ++ [a]) = p ++ [a].
Proof. intros. 
       unfold compactify.
       rewrite rev_unit; simpl. 
       destruct (Ceq_dec a C0); try easy. 
       rewrite <- rev_unit, rev_involutive.
       easy. 
Qed.

Lemma Peq_compactify_eq_helper : forall (p1 p2 : Polynomial),
  length p1 <= length p2 -> 
  p1 ≅ p2 -> compactify p1 = compactify p2.
Proof. intros. 
       rewrite <- (firstn_skipn (length p1) p2),
         (same_elem_same_rev (skipn (Datatypes.length p1) p2)), app_C0_compactify_reduce.
       rewrite <- (Peq_firstn_eq); auto.
       apply Peq_nil_contains_C0.
       apply Peq_skipn_Peq_nil; auto.
Qed.

Lemma Peq_compactify_eq : forall (p1 p2 : Polynomial),
  p1 ≅ p2 -> compactify p1 = compactify p2.
Proof. intros. 
       bdestruct (length p1 <? length p2).
       - apply Peq_compactify_eq_helper; auto; try lia. 
       - rewrite (Peq_compactify_eq_helper p2 p1); try lia; easy. 
Qed.

Add Parametric Morphism : compactify
  with signature Peq ==> eq as compactify_mor.
Proof. intros p1 p2 H. 
       apply Peq_compactify_eq; easy. 
Qed.

Lemma p_Peq_compactify_p : forall (p : Polynomial),
  (fun p0 => p0 ≅ compactify p0) p.
Proof. apply ind_from_end; try easy.
       intros.
       unfold compactify.
       rewrite rev_unit; simpl. 
       destruct (Ceq_dec x C0); subst. 
       - rewrite <- H.
         apply last_C0_Peq_front.
       - rewrite <- rev_unit, rev_involutive.
         easy.
Qed.

Lemma compactify_eq_Peq : forall (p1 p2 : Polynomial),
  compactify p1 = compactify p2 -> p1 ≅ p2.
Proof. intros. 
       rewrite p_Peq_compactify_p, (p_Peq_compactify_p p2), H.
       easy.
Qed.


(* We can now show that ≅ is decidable *)
Lemma Peq_0_dec : forall (p : Polynomial),
  { p ≅ [] } + { ~( p ≅ [] ) }.
Proof. intros.
       destruct (compactify p) eqn:E.
       - left. 
         rewrite <- E.
         apply p_Peq_compactify_p.
       - right. 
         unfold not; intros. 
         rewrite Peq_0_compactify_0 in E; auto. 
         easy. 
Qed.


Lemma Peq_dec : forall (p1 p2 : Polynomial),
  { p1 ≅ p2 } + { ~(p1 ≅ p2) }.
Proof. intros. 
       destruct (Peq_0_dec (p1 +, (-, p2))).
       - left. 
         assert (H' : (p1 +, -, p2) +, p2 ≅ [] +, p2).
         { rewrite p; easy. }
         rewrite Pplus_assoc, Pplus_opp_l, Pplus_0_r in H'.
         easy. 
       - right. 
         unfold not in *; intros. 
         apply n. 
         rewrite H, Pplus_opp_r.
         easy.
Qed.

(* now we start proving stuff about lengths/degree *)

Lemma Pplus_length1 : forall (p1 p2 : Polynomial),
  length (p1 +, p2) = max (length p1) (length p2).
Proof. induction p1 as [| a1]; try easy. 
       intros. 
       destruct p2; try easy. 
       simpl. 
       rewrite IHp1; easy. 
Qed.

Lemma Pplus_length2 : forall (p1 p2 : Polynomial),
  length p1 <= length p2 ->
  length (p1 +, p2) = length p2.
Proof. induction p1 as [| a1]; try easy. 
       intros. 
       destruct p2; try easy. 
       simpl in *.
       apply le_S_n in H.
       rewrite IHp1; easy.
Qed.

Lemma Pplus_lt_app : forall (a : C) (p1 p2 : Polynomial), 
  length p1 <= length p2 -> 
  p1 +, (p2 ++ [a]) = (p1 +, p2) ++ [a].
Proof. induction p1 as [| h]; try easy.
       intros. 
       destruct p2; try easy. 
       simpl in *. 
       rewrite IHp1; try easy.
       lia. 
Qed.

Lemma Pmult_leading_terms : forall (a1 a2 : C) (p1 p2 : Polynomial),
  exists p : Polynomial, (p1 ++ [a1]) *, (p2 ++ [a2]) = p ++ [(a1 * a2)%C] /\ 
                    length p2 <= length p. 
Proof. induction p1 as [| h].
       - intros.
         destruct p2.
         + do 2 rewrite app_nil_l.
           exists [].
           simpl. 
           rewrite Cplus_0_r; easy. 
         + exists ([a1] *, (c :: p2)).
           rewrite app_nil_l.
           simpl. 
           do 2 rewrite Pplus_0_r.
           rewrite map_app.
           split; try easy. 
           rewrite map_length; easy.
       - intros. 
         simpl.  
         destruct (IHp1 p2) as [p [H1 H2] ].     
         exists (map (Cmult h) (p2 ++ [a2]) +, (C0 :: p)).
         split. 
         rewrite H1, app_comm_cons. 
         apply Pplus_lt_app.
         rewrite map_length, app_length; simpl; lia. 
         rewrite Pplus_length1, map_length, app_length; simpl.
         lia. 
Qed.

Lemma Pmult_length_le : forall (p1 p2 : Polynomial),
  p2 <> [] ->
  length p1 <= length (p2 *, p1).
Proof. induction p1 as [| a1].
       - intros; destruct p2; try easy; simpl; lia.
       - intros. destruct p2; try easy; simpl.
         rewrite Pplus_length1, map_length.
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
         rewrite Pplus_length1, map_length; simpl. 
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

Lemma Pmult_length : forall (p1 p2 : Polynomial),
  p1 <> [] -> p2 <> [] ->
  length (p1 *, p2) = length p1 + length p2 - 1.          
Proof. intros. 
       destruct p1; destruct p2; try easy. 
       apply (Pmult_length_helper (length (c :: p1))).
       simpl; lia. 
Qed.

Lemma compactify_neq_nil : forall (a : C) (p : Polynomial),
  a <> C0 -> (fun p0 => compactify (a :: p0) <> []) p.
Proof. intros a p H.
       apply ind_from_end.
       - unfold compactify, prune; simpl.
         destruct (Ceq_dec a C0); try easy. 
       - intros. 
         rewrite app_comm_cons. 
         destruct (Ceq_dec x C0); subst.
         + rewrite app_C0_compactify_reduce_1; easy. 
         + rewrite app_nonzero_compactify_reduce; easy.
Qed.

Lemma compactify_Pscale : forall (a b : C) (p : Polynomial),
  a <> C0 -> b <> C0 -> (fun p0 => [a] *, compactify (b :: p0) = compactify ([a] *, (b :: p0))) p.
Proof. intros. 
       apply ind_from_end. 
       - unfold compactify; simpl. 
         rewrite Cplus_0_r.
         apply (Cmult_neq_0 a b) in H; auto.
         destruct (Ceq_dec b C0); destruct (Ceq_dec (a * b) C0); try easy.
         simpl; rewrite Cplus_0_r; easy.
       - intros.
         destruct (Ceq_dec x C0); subst.
         + rewrite app_comm_cons, app_C0_compactify_reduce_1, H1; simpl. 
           rewrite Pplus_0_r, Pplus_0_r, map_last, Cmult_0_r.
           rewrite app_comm_cons, app_C0_compactify_reduce_1; easy.
         + rewrite app_comm_cons, app_nonzero_compactify_reduce; auto; simpl. 
           rewrite Pplus_0_r, map_last, app_comm_cons, app_nonzero_compactify_reduce; auto.
           apply Cmult_neq_0; auto.
Qed.   

Lemma compactify_Pmult_helper : forall (a1 a2 : C) (p1 p2 : Polynomial),
  a1 <> C0 -> a2 <> C0 ->  
  compactify (p1 ++ [a1]) *, compactify (p2 ++ [a2]) = compactify ((p1 ++ [a1]) *, (p2 ++ [a2])).
Proof. intros. 
       destruct (Pmult_leading_terms a1 a2 p1 p2) as [p [H1 H2] ].
       rewrite H1.
       do 3 (rewrite app_nonzero_compactify_reduce; auto).
       apply Cmult_neq_0; easy. 
Qed.

Lemma C0_end_breakdown : forall (p : Polynomial),
  (fun p0 => Peval p0 <> Peval [] -> 
  (exists n a p', a <> C0 /\ p0 = (p' ++ [a]) ++ (repeat C0 n))) p.
Proof. apply ind_from_end; try easy.
       intros. 
       destruct (Ceq_dec x C0); subst.
       - rewrite last_C0_Peq_front in H0.
         apply H in H0.
         destruct H0 as [n [a [p' [H1 H2] ] ] ].
         exists (S n), a, p'.
         split; auto. 
         rewrite H2, app_assoc_reverse.
         apply f_equal_gen; try easy.
         simpl. 
         rewrite repeat_cons.
         easy. 
       - exists 0, x, l.
         split; auto.         
         apply app_nil_end.
Qed.

Lemma compactify_Pmult : forall (p1 p2 : Polynomial),
  Peval p1 <> Peval [] -> Peval p2 <> Peval [] ->
  compactify p1 *, compactify p2 = compactify (p1 *, p2).
Proof. intros. 
       apply C0_end_breakdown in H; apply C0_end_breakdown in H0.
       destruct H as [n1 [a1 [p1' [H1 H2] ] ] ];
       destruct H0 as [n2 [a2 [p2' [H3 H4] ] ] ]; subst. 
       do 2 rewrite repeat_C0_Peq_front.
       apply compactify_Pmult_helper; easy.
Qed.

Definition degree (p : Polynomial) : nat :=
  length (compactify p) - 1. 

Add Parametric Morphism : degree
  with signature Peq ==> eq as degree_mor.
Proof. intros p1 p2 H. 
       unfold degree. 
       rewrite H; easy.
Qed.

Lemma length_compactify1 : forall (p1 p2 : Polynomial),
  length (compactify (p1 +, p2)) <= length (compactify p1 +, compactify p2).
Proof. intros. 
       assert (H' : compactify (p1 +, p2) = compactify (compactify p1 +, compactify p2)).
       { rewrite <- (p_Peq_compactify_p p1).
         rewrite <- (p_Peq_compactify_p p2).
         easy. }
       rewrite H'.
       apply compactify_length.
Qed.

Lemma length_compactify2 : forall (p1 p2 : Polynomial),
  (fun p =>
  length (compactify p1) < length (compactify p) -> 
  length (compactify (p1 +, p)) = length (compactify p)) p2.
Proof. intros. 
       apply ind_from_end; try easy.
       intros. 
       destruct (Ceq_dec x C0); subst.
       + rewrite app_C0_compactify_reduce_1 in *.
         rewrite <- H; auto. 
         apply f_equal_gen; auto.
         rewrite last_C0_Peq_front; easy.
       + rewrite app_nonzero_compactify_reduce, app_length in *; auto.
         rewrite (p_Peq_compactify_p p1), Pplus_lt_app.
         rewrite app_nonzero_compactify_reduce, app_length; auto.
         do 2 (apply f_equal_gen; auto).
         rewrite Pplus_length2; auto.
         all : simpl in *; lia. 
Qed.

Lemma Pplus_degree1 : forall (p1 p2 : Polynomial),
  degree (p1 +, p2) <= max (degree p1) (degree p2).
Proof. intros. 
       unfold degree.
       rewrite Nat.sub_max_distr_r.
       apply Nat.sub_le_mono_r.
       bdestruct (Datatypes.length (compactify p1) <? Datatypes.length (compactify p2)).
       - rewrite Max.max_r, length_compactify2; try lia. 
       - bdestruct (Datatypes.length (compactify p2) <? Datatypes.length (compactify p1)).
         + rewrite Max.max_l, Pplus_comm, length_compactify2; try lia. 
         + apply Nat.le_antisymm in H; auto.
           rewrite <- Pplus_length1.
           apply length_compactify1.
Qed.

Lemma Pplus_degree2 : forall (p1 p2 : Polynomial),
  degree p1 < degree p2 -> 
  degree (p1 +, p2) = degree p2. 
Proof. intros. 
       unfold degree in *.
       rewrite length_compactify2; try easy. 
       lia. 
Qed.

Lemma Pmult_degree : forall (p1 p2 : Polynomial),
  Peval p1 <> Peval [] -> Peval p2 <> Peval [] ->
  degree (p1 *, p2) = (degree p1) + (degree p2).
Proof. intros.
       assert (H' : forall p, Peval p <> Peval [] -> compactify p <> []).
       { intros. 
         unfold not; intros; apply H1.
         apply compactify_eq_Peq.
         rewrite H2; easy. }
       unfold degree.
       rewrite <- compactify_Pmult; auto.
       apply H' in H; apply H' in H0.
       rewrite Pmult_length; auto.
       destruct (compactify p1); destruct (compactify p2); try easy.
       simpl; lia. 
Qed.


Lemma Psum_degree : forall (f : nat -> Polynomial) (n deg : nat), 
  (forall i, degree (f i) <= deg) -> degree (Psum f n) <= deg.
Proof. induction n as [| n'].
       - intros; simpl.  
         unfold degree, compactify; simpl.
         destruct (Ceq_dec C0 C0); try easy; simpl; lia. 
       - intros; simpl. 
         apply (Nat.le_trans _ (max (degree (Psum f n')) (degree (f n')))).
         apply Pplus_degree1.
         apply Max.max_lub; auto. 
Qed.


(*****************************************************)
(* First, we show that our C is the same as ccorns C *)
(*****************************************************)

Require Import CoRN.fta.FTA. 
Require Import CoRN.coq_reals.Rreals_iso. 
Require Import CoRN.coq_reals.Rreals.
Require Import CoRN.reals.iso_CReals.

Definition CtoCC (c : Complex.C) : CC := cc_set_CC (RasIR (fst c)) (RasIR (snd c)). 
Definition CCtoC (c : CC_set) : Complex.C := (IRasR (Re c), IRasR (Im c)).

Lemma CtoCCtoC_id : forall (x : Complex.C), CCtoC (CtoCC x) = x.
Proof. intros.
       unfold CtoCC, CCtoC.
       simpl.
       do 2 rewrite RasIRasR_id.
       rewrite surjective_pairing.
       easy. 
Qed.

Lemma CCtoCtoCC_id : forall (x : CC), CtoCC (CCtoC x) [=] x.
Proof. intros.
       split; simpl; rewrite IRasRasIR_id;
       easy. 
Qed. 

Lemma C_eq_to_CC : forall x y, (x = y -> CtoCC x [=] CtoCC y).
Proof. intros. 
       split; simpl; subst; easy. 
Qed.

Lemma CC_eq_to_C : forall x y : CC, (x [=] y -> CCtoC x = CCtoC y).
Proof. intros.
       unfold CCtoC; simpl.
       destruct H.
       rewrite <- IRasRasIR_id, <- (IRasRasIR_id (Re y)) in H.
       rewrite <- IRasRasIR_id, <- (IRasRasIR_id (Im y)) in H0.
       apply R_eq_as_IR_back in H; apply R_eq_as_IR_back in H0.
       rewrite H, H0.
       easy. 
Qed.     

Lemma CC_ap_as_C : forall x y, (x <> y -> CtoCC x [#] CtoCC y).
Proof. intros. 
       destruct x as [x1 x2], y as [y1 y2].
       destruct (Req_EM_T x1 y1); subst.
       - destruct (Req_EM_T x2 y2); subst; try easy.
         right; simpl. 
         apply R_ap_as_IR_back; auto. 
       - left; simpl. 
         apply R_ap_as_IR_back; auto. 
Qed.   

Lemma C_zero_to_CC : CtoCC C0 [=] [0].
Proof. split; simpl; apply R_Zero_as_IR. 
Qed.

Lemma CC_zero_to_C : CCtoC cc_zero = C0.
Proof. unfold CCtoC, cc_zero.
       simpl. 
       rewrite IR_Zero_as_R.
       easy.
Qed.       

Lemma C_plus_to_CC : forall x y, (CtoCC (x+y) [=] CtoCC x [+] CtoCC y).
Proof. intros. 
       split; simpl; 
       apply R_plus_as_IR.
Qed.

Lemma CC_plus_to_C : forall x y : CC, (CCtoC (x [+] y) = (CCtoC x + CCtoC y)%C).
Proof. intros; simpl. 
       unfold Cplus, cc_plus, CCtoC; simpl. 
       do 2 rewrite <- IR_plus_as_R.
       easy. 
Qed.

Lemma C_mult_to_CC : forall x y, (CtoCC (x*y) [=] CtoCC x [*] CtoCC y).
Proof. intros. 
       split; simpl. 
       rewrite R_minus_as_IR, R_mult_as_IR, R_mult_as_IR; easy. 
       rewrite R_plus_as_IR, R_mult_as_IR, R_mult_as_IR; easy. 
Qed.

(* these should be added to ccorn *)
Lemma IR_mult_as_R : forall x y, (IRasR (x[*]y) = IRasR x * IRasR y).
Proof.
 apply: map_pres_mult_unfolded.
Qed.

Lemma IR_minus_as_R : forall x y, (IRasR (x[-]y) = IRasR x - IRasR y).
Proof. intros x y.
       unfold cg_minus, Rminus.
       rewrite IR_plus_as_R.
       apply f_equal_gen; try easy.
       apply : map_pres_minus_unfolded.
Qed.

Lemma CC_mult_to_C : forall x y : CC, (CCtoC (x [*] y) = (CCtoC x * CCtoC y)%C).
Proof. intros.
       unfold cc_mult, CCtoC, Cmult; simpl. 
       rewrite IR_minus_as_R, IR_plus_as_R.
       do 4 rewrite IR_mult_as_R; easy. 
Qed.


Fixpoint PolytoCCX (p : Polynomial) : CCX :=
  match p with 
  | [] => (cpoly_zero CC)
  | a :: p' => (cpoly_linear CC) (CtoCC a) (PolytoCCX p')
  end.

Fixpoint CCXtoPoly (f : CCX) : Polynomial := 
  match f with 
  | (cpoly_zero _) => [] 
  | (cpoly_linear _ a f') => (CCtoC a) :: (CCXtoPoly f')
  end.

Lemma PolytoCCXtoPoly : forall (p : Polynomial), CCXtoPoly (PolytoCCX p) = p.
Proof. induction p as [| p']; try easy.
       simpl. 
       rewrite CtoCCtoC_id, IHp; easy. 
Qed.

Lemma CCXtoPolytoCCX : forall (f : CCX), PolytoCCX (CCXtoPoly f) [=] f.
Proof. induction f as [| a]; try easy.
       split. 
       apply CCtoCtoCC_id.
       apply IHf.
Qed.

Lemma Poly_eval_iso : forall (p : Polynomial) (c : CC),
  p [[CCtoC c]] = CCtoC ((PolytoCCX p) ! c).
Proof. induction p as [| a]. 
       - intros. simpl. 
         rewrite CC_zero_to_C.
         easy. 
       - intros. 
         simpl. 
         rewrite cons_eval, IHp.
         rewrite CC_plus_to_C, CC_mult_to_C, CtoCCtoC_id.
         easy. 
Qed.

Lemma nth_poly_translate : forall (p : Polynomial) (n : nat),
  nth_coeff n (PolytoCCX p) [=] CtoCC (nth n p C0). 
Proof. induction p as [| a]. 
       - intros.
         replace (nth n [] C0) with C0. 
         2 : destruct n; easy. 
         rewrite C_zero_to_CC.
         easy.
       - intros. 
         destruct n; try easy.         
         apply IHp.
Qed.

Lemma ap_wdl_unfolded_CC : forall (a b c : CC), 
  a [=] b -> a [#] c -> b [#] c.
Proof. intros. eapply ap_wdl; eauto.
Qed.

Lemma ap_wdr_unfolded_CC : forall (a b c : CC), 
  b [=] a -> a [#] c -> c [#] b.
Proof. intros. 
       apply ap_symmetric_unfolded.
       eapply ap_wdl; eauto.
       easy.
Qed. 

Lemma nth_compactify_nonzero : forall (p : Polynomial),
  (fun p0 => (Polynomial.degree p0 > 0)%nat -> 
  C0 <> nth (Datatypes.length (compactify p0) - 1) p0 C0) p.
Proof. intros.
       apply ind_from_end; try easy.
       intros. 
       unfold Polynomial.degree in *.
       destruct (Ceq_dec x C0); subst.
       - rewrite app_C0_compactify_reduce_1, app_nth1 in *.
         apply H; easy.
         assert (H' : (Datatypes.length (compactify l) - 1 < Datatypes.length (compactify l))%nat).
         { lia. }
         assert (H'' := (compactify_length l)).
         lia. 
       - rewrite app_nonzero_compactify_reduce; auto.
         rewrite app_length, Nat.add_sub; simpl. 
         rewrite nth_middle. 
         unfold not; intros; apply n; easy.
Qed.

Lemma degree_gt_1_nonConst : forall (p : Polynomial),
  ((Polynomial.degree p) > 0)%nat -> nonConst _ (PolytoCCX p).
Proof. intros. 
       unfold nonConst.
       unfold Polynomial.degree in H.
       exists (Datatypes.length (compactify p) - 1)%nat; auto.
       apply (ap_wdl_unfolded_CC (CtoCC (nth (Datatypes.length (compactify p) - 1) p C0))).
       rewrite nth_poly_translate; easy.
       apply (ap_wdr_unfolded_CC (CtoCC (CCtoC cc_zero))).
       rewrite CCtoCtoCC_id; easy.
       apply CC_ap_as_C.
       rewrite CC_zero_to_C.
       apply nth_compactify_nonzero.
       easy.
Qed.       

Theorem Fundamental_Theorem_Algebra : forall (p : Polynomial),
  (Polynomial.degree p > 0)%nat -> (exists c : Complex.C, p[[c]] = C0).
Proof. intros.  
       destruct (FTA (PolytoCCX p)).
       apply degree_gt_1_nonConst; auto.
       exists (CCtoC x). 
       rewrite Poly_eval_iso, <- CC_zero_to_C.
       apply CC_eq_to_C; easy. 
Qed.

