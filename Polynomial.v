Require Import Psatz.
Require Import String.
Require Export Complex. 
Require Import List. 
Require Import Setoid.
 
Declare Scope poly_scope.
Delimit Scope poly_scope with P.
Open Scope poly_scope.

(* some prelim lemmas that should be moved *)

Lemma diff_pow_n : forall (n : nat) (a b : C),
  (a^(S n) - b^(S n)) = (a - b) * (big_sum (fun i => a^i * b^(n - i)) (S n)).
Proof. intros.
       unfold Cminus. 
       rewrite Cmult_plus_distr_r.
       do 2 rewrite (@big_sum_mult_l C _ _ _ C_is_ring). 
       rewrite <- big_sum_extend_r, <- big_sum_extend_l, Nat.sub_diag, Nat.sub_0_r.
       simpl. 
       replace (a * (a ^ n * C1)) with (a^ (S n)) by lca. 
       replace (- b * (C1 * b ^ n)) with (- b^(S n)) by lca. 
       rewrite (Cplus_comm _ (a ^ _)), <- Cplus_assoc. 
       apply Cplus_simplify; try easy. 
       rewrite Cplus_assoc, (Cplus_comm _ (- b ^ _)), <- (Cplus_0_r (- b ^ _)). 
       do 2 rewrite <- Cplus_assoc.
       rewrite <- (Cplus_0_r (- (b * b ^ n))).
       apply Cplus_simplify; try easy. 
       rewrite <- (@big_sum_plus C _ _ C_is_comm_group), Cplus_0_l.
       rewrite big_sum_0_bounded; auto.  
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
  big_sum (fun i => (nth i p C0)* x^i) (length p).

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

Global Program Instance P_is_monoid : Monoid Polynomial := 
  { Gzero := []
  ; Gplus := Pplus
  }.
Solve All Obligations with program_simpl; try lca.
Next Obligation. induction g as [| g']; easy. Qed.
Next Obligation. 
assert (H' : forall p1 p2 p3, Pplus (Pplus p1 p2) p3 = Pplus p1 (Pplus p2 p3)).
induction p1 as [| a]; try easy.    
intros. 
destruct p2; destruct p3; try easy; simpl. 
rewrite IHp1, Cplus_assoc; easy. 
rewrite H'; easy.
Qed.

(*
Fixpoint Psum (f : nat -> Polynomial) (n : nat) : Polynomial := 
  match n with
  | 0 => [C0]
  | S n' => (Pplus (Psum f n') (f n'))
  end.
*)

Infix "≅" := Peq (at level 70) : poly_scope. 
Infix "+," := Pplus (at level 50, left associativity) : poly_scope. 
Infix "*," := Pmult (at level 40, left associativity) : poly_scope.
Notation "-, P" := (Popp P) (at level 35) : poly_scope. 
Notation "P [[ x ]]" := (Peval P x) (at level 0) : poly_scope.  

(* some useful lemmas about Peval *)
Lemma cons_eval : forall (p1 : Polynomial) (a c : C),
  (a :: p1)[[c]] = a + c * (p1[[c]]).
Proof. intros. 
       unfold Peval.
       simpl length. 
       rewrite <- big_sum_extend_l.
       repeat apply f_equal_gen; try easy; try lca. 
       rewrite (@big_sum_mult_l C _ _ _ C_is_ring); apply big_sum_eq_bounded.
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
         rewrite map_length, (@big_sum_mult_l C _ _ _ C_is_ring).
         apply big_sum_eq_bounded; intros. 
         replace C0 with (Cmult a1 C0) by lca. 
         rewrite map_nth, Cmult_0_r.
         lca. 
Qed.

Lemma Psum_eval : forall (f : nat -> Polynomial) (n : nat) (c : C),
  (big_sum f n)[[c]] = big_sum (fun i => (f i)[[c]]) n.
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
       rewrite app_length, big_sum_sum. 
       apply Cplus_simplify.
       apply big_sum_eq_bounded; intros. 
       rewrite app_nth1; easy.
       rewrite app_length, big_sum_sum.
       rewrite repeat_length.  
       assert (big_sum (fun i : nat => nth i (repeat C0 (Datatypes.length f) ++ g) C0 * x ^ i) 
                    (length f) = C0).
       { apply (@big_sum_0_bounded C C_is_monoid); intros. 
         rewrite app_nth1.
         destruct (nth_in_or_default x0 (repeat C0 (Datatypes.length f)) C0).
         - apply repeat_spec in i.
           rewrite i; lca. 
         - rewrite e; lca.
         - rewrite repeat_length; easy. }
       rewrite H, Cplus_0_l.
       apply big_sum_eq_bounded; intros. 
       rewrite app_nth2_plus, app_nth2, repeat_length.
       replace (Datatypes.length f + x0 - Datatypes.length f)%nat with x0 by lia. 
       easy. 
       rewrite repeat_length; lia. 
Qed.

Lemma nth_repeat : forall {X} (x : X) (i n : nat),
  (nth i (repeat x n) x) = x.
Proof. induction i as [| i'].
       - destruct n; easy.
       - destruct n; try easy.
         simpl in *. 
         apply IHi'.
Qed.

Lemma mul_by_x_to_n : forall (f : Polynomial) (n : nat) (c : C),
  ((repeat C0 n) ++ f)[[c]] = f[[c]] * c^n.
Proof. intros.   
       unfold Peval.
       rewrite app_length, big_sum_sum, <- Cplus_0_l.
       apply Cplus_simplify.
       apply (@big_sum_0_bounded C C_is_monoid); intros. 
       rewrite app_nth1, nth_repeat; auto; lca.
       rewrite (@big_sum_mult_r C _ _ _ C_is_ring).
       apply big_sum_eq_bounded; intros. 
       rewrite app_nth2_plus, repeat_length, Cpow_add_r; lca.
Qed.

Lemma app_eval_to_mul : forall (f g : Polynomial) (c : C),
  (f ++ g)[[c]] = f[[c]] + c^(length f) * g[[c]].
Proof. intros. 
       rewrite Cmult_comm, app_eval, mul_by_x_to_n; easy.
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
       rewrite Nat.add_1_r, <- big_sum_extend_r, <- (Nat.add_0_r (length (repeat C0 n))), 
       app_nth2_plus, Nat.add_0_r, repeat_length; simpl. 
       rewrite <- Cplus_0_l.
       apply Cplus_simplify; auto. 
       apply (@big_sum_0_bounded C C_is_monoid); intros.
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
       rewrite (big_sum_unique a1), (big_sum_unique a2) in H; auto. 
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
       do 2 rewrite <- big_sum_extend_l in H.
       simpl in H. 
       rewrite Cmult_0_l, Cplus_0_l, Cplus_0_l in H. 
       rewrite <- Cmult_1_l, <- (Cinv_l c), <- Cmult_assoc, (@big_sum_mult_l C _ _ _ C_is_ring); auto. 
       assert (H' : (fun x : nat => nth x p2 C0 * (c * c ^ x)) = 
                    (fun x : nat => c * (nth x p2 C0 * c ^ x))).
       { apply functional_extensionality; intros. 
         lca. }
       simpl in *.
       rewrite <- H', <- H. 
       assert (H'' : (fun x : nat => nth x p1 C0 * (c * c ^ x)) = 
                    (fun x : nat => c * (nth x p1 C0 * c ^ x))).
       { apply functional_extensionality; intros. 
         lca. }
       rewrite H''. 
       rewrite <- (@big_sum_mult_l C _ _ _ C_is_ring), Cmult_assoc, Cinv_l; auto; lca. 
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

Lemma Peq_0_eq_repeat_0 : forall (p : Polynomial),
  p ≅ [] -> p = repeat C0 (length p).
Proof. intros.  
       apply same_elem_same_rev.
       apply Peq_nil_contains_C0; easy. 
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
       rewrite Nat.add_1_r, <- big_sum_extend_r.
       rewrite app_nth2, Nat.sub_diag; auto; simpl.
       rewrite Cmult_0_l, Cplus_0_r.
       apply big_sum_eq_bounded; intros.
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

Lemma compactify_breakdown : forall (p : Polynomial),
  Peval p <> Peval [] ->
  (exists a p', a <> C0 /\ compactify p = (p' ++ [a])).
Proof. intros. 
       apply C0_end_breakdown in H.
       destruct H as [n [a [p' [H H0] ] ] ].
       exists a, p'; split; auto.
       rewrite H0, app_C0_compactify_reduce, app_nonzero_compactify_reduce; easy.
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
       - rewrite Nat.max_r, length_compactify2; try lia. 
       - bdestruct (Datatypes.length (compactify p2) <? Datatypes.length (compactify p1)).
         + rewrite Nat.max_l, Pplus_comm, length_compactify2; try lia. 
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
  (forall i, i < n -> degree (f i) <= deg) -> degree (big_sum f n) <= deg.
Proof. induction n as [| n'].
       - intros; simpl.  
         unfold degree, compactify; simpl.
         destruct (Ceq_dec C0 C0); try easy; simpl; lia. 
       - intros; simpl. 
         apply (Nat.le_trans _ (max (degree (big_sum f n')) (degree (f n')))).
         apply Pplus_degree1.
         apply Nat.max_lub; auto. 
Qed.

(* we can now prove the zero product property for polynomials *)
Lemma Pmult_neq_0 : forall (p1 p2 : Polynomial),
  Peval p1 <> Peval [] -> Peval p2 <> Peval [] ->
  Peval (p1 *, p2) <> Peval []. 
Proof. intros. 
       destruct (length (compactify p1)) as [| n] eqn:E1. 
       - destruct (compactify p1) eqn:E; try easy.
         unfold not; intros; apply H.
         rewrite p_Peq_compactify_p, E; easy.
       - destruct n as [| n].
         + destruct (compactify p1) eqn:E; try easy.
           destruct p; try easy.
           assert (H' : c <> C0).
           { unfold not; intros; apply H.
             rewrite (p_Peq_compactify_p p1), E, H1.
             apply C0_Peq_nil. }
           unfold not; intros; apply H0.
           assert (H2 : (p1 *, p2) ≅ []). easy.
           rewrite (p_Peq_compactify_p p1), E in H2.
           apply functional_extensionality; intros. 
           assert (H3 : ([c] *, p2)[[x]] = [] [[x]]). 
           rewrite H2; easy. 
           rewrite Pmult_eval in H3.
           replace (([]) [[x]]) with C0 in * by easy.            
           replace (([c]) [[x]]) with c in * by lca. 
           destruct (Ceq_dec ((p2) [[x]]) C0); try easy. 
           apply (Cmult_neq_0 c) in n; easy.
         + apply (Pmult_degree p1 p2) in H; auto.
           assert (H' : degree (p1 *, p2) > 0).
           { rewrite H.
             unfold degree.
             rewrite E1; lia. }
           destruct (Peq_0_dec (p1 *, p2)); try easy. 
           rewrite p in H'.
           easy.
Qed.


(*****************)
(* Defining Ppow *)
(*****************)

Fixpoint Ppow (p : Polynomial) (n : nat) :=
  match n with
  | 0 => [C1]
  | S n' => (Ppow p n') *, p
  end.

Add Parametric Morphism : Ppow
  with signature Peq ==> eq ==> Peq as Ppow_mor.
Proof. intros p1 p2 H n. 
       induction n as [| n']; try easy.
       simpl. 
       rewrite IHn', H; easy.
Qed.

Lemma Ppow_eval : forall (p : Polynomial) (n : nat) (a : C),
  (Ppow p n)[[a]] = ((p[[a]])^n)%C.
Proof. induction n as [| n'].
       - intros; unfold Peval; simpl; lca. 
       - intros; simpl. 
         rewrite Pmult_eval.
         rewrite IHn'; lca.
Qed.

Lemma Ppow_neq_0 : forall (p : Polynomial) (n : nat),
  Peval p <> Peval [] ->
  Peval (Ppow p n) <> Peval [].
Proof. induction n as [| n'].
       - intros; simpl. 
         unfold not; intros; apply C1_neq_C0.
         apply (f_equal_gen _ _ C1 C1) in H0; try easy.
         unfold Peval in H0; simpl in H0.
         rewrite <- H0; lca.
       - intros; simpl.
         apply Pmult_neq_0; try apply IHn'; easy.
Qed.

Lemma Ppow_degree : forall (p : Polynomial) (n : nat),
  degree (Ppow p n) = n * (degree p).
Proof. induction n as [| n'].
       - unfold degree, compactify, prune; simpl. 
         destruct (Ceq_dec C1 C0); easy.
       - destruct (Peq_0_dec p); simpl. 
         + rewrite p0, Pmult_0_r.
           unfold degree; simpl; lia.
         + rewrite Pmult_degree, IHn'; try apply Ppow_neq_0; try easy.
           lia. 
Qed.

(********************************************)
(* Defining poly_shift, to shift polynomial *)
(********************************************)

Definition poly_shift (p : Polynomial) (m : C) : Polynomial :=
  big_sum (fun i => [nth i p C0] *, (Ppow [-m;  C1] i)) (length p).

Lemma poly_shift_ver : forall (p : Polynomial) (m c : C),
  p[[c - m]] = (poly_shift p m)[[c]].
Proof. intros. 
       unfold poly_shift. 
       rewrite Psum_eval.
       apply big_sum_eq_bounded; intros. 
       rewrite Pmult_eval, Ppow_eval. 
       unfold Peval; simpl. 
       replace (0%R + - m * C1 + C1 * (c * C1))%C with (c - m)%C by lca.
       lca. 
Qed.

Add Parametric Morphism : poly_shift
  with signature Peq ==> eq ==> Peq as polyshift_mor.
Proof. intros p1 p2 H m. 
       unfold Peq; apply functional_extensionality; intros. 
       do 2 rewrite <- poly_shift_ver.
       rewrite H; easy.
Qed.

Lemma poly_shift_const : forall (a m : C),
  [a] ≅ (poly_shift [a] m).
Proof. unfold Peq, Peval; intros. 
       apply functional_extensionality; simpl. 
       intros; lca.
Qed.
 
(* this proof got really long somehow *)
Lemma poly_shift_degree : forall (p : Polynomial) (m : C),
  degree p = degree (poly_shift p m).
Proof. intros.
       rewrite p_Peq_compactify_p.
       destruct (length (compactify p)) as [| n] eqn:E.
       - destruct (compactify p); try easy.
       - destruct (Peq_0_dec p).
         + rewrite Peq_0_compactify_0 in E; easy.
         + apply compactify_breakdown in n0.
           destruct n0 as [a [p' [H H0] ] ]. 
           destruct (length p') as [| n'] eqn:E1.
           destruct p'; try easy.
           rewrite H0; simpl. 
           rewrite <- poly_shift_const; easy.
           unfold poly_shift.  
           rewrite H0, app_length, Nat.add_1_r; simpl.  
            assert (H1 : degree (p' ++ [a]) =
                          degree
                            (map (Cmult (nth (Datatypes.length p') (p' ++ [a]) C0))
                                 (Ppow [- m; C1] (Datatypes.length p')) +, [C0])).
           { rewrite nth_middle.
             replace (map (Cmult a) (Ppow [- m; C1] (Datatypes.length p')) +, [C0]) with
               ([a] *, (Ppow [- m; C1] (Datatypes.length p'))) by easy.
             rewrite Pmult_degree, Ppow_degree. 
             unfold degree.
             rewrite <- H0, compactify_idempotent, H0, app_length; simpl.
             unfold compactify, prune; simpl.
             destruct (Ceq_dec a C0); try easy.
             assert (H' := C1_neq_C0).
             destruct (Ceq_dec C1 C0); try easy; simpl; lia.
             unfold not; intros. 
             apply (f_equal_gen _ _ C1 C1) in H1; auto.
             unfold Peval in H1; simpl in H1.
             apply H; rewrite <- H1; lca.
             apply Ppow_neq_0.
             unfold not; intros; apply C1_neq_C0.
             apply (f_equal_gen _ _ (m + C1)%C (m + C1)%C) in H1; auto.
             unfold Peval in H1; simpl in H1; rewrite <- H1; lca. }
           rewrite Pplus_degree2; try easy.
           rewrite <- H1.
           replace (degree (p' ++ [a])) with (length p') by 
           (unfold degree; rewrite <- H0, compactify_idempotent, H0, app_length; simpl; lia). 
           rewrite E1. 
           apply Nat.lt_succ_r; apply Psum_degree; intros. 
           replace (map (Cmult (nth i (p' ++ [a]) C0)) (Ppow [- m; C1] i) +, [C0]) with
             ([(nth i (p' ++ [a]) C0)] *, (Ppow [- m; C1] i)) by easy.
           destruct (Peq_0_dec [nth i (p' ++ [a]) 0%R]).
           rewrite p0; unfold degree, compactify, prune; simpl; lia.
           rewrite Pmult_degree, Ppow_degree; try easy.
           unfold degree, compactify, prune; simpl.
           destruct (Ceq_dec C1 C0); try (apply C1_neq_C0 in e; easy).
           destruct (Ceq_dec (nth i (p' ++ [a]) C0)); simpl; lia.
           apply Ppow_neq_0.
           unfold not; intros; apply C1_neq_C0.
           apply (f_equal_gen _ _ (m + C1)%C (m + C1)%C) in H3; auto.
           unfold Peval in H3; simpl in H3; rewrite <- H3; lca.
Qed.




(* proving results specific to quadratics *)

Local Close Scope nat_scope.


Lemma discriminant_pos_Peval_pos : forall (a b c : R),
  a > 0 ->
  (forall t, 0 <= fst (Peval [(c,0); (b,0); (a,0)] (t, 0))) <-> 0 <= 4*a*c - b^2.
Proof. split; intros. 
       - assert (H1 := H0 (-b/(2*a))%R).
         replace (fst ([(c, 0); (b, 0); (a, 0)]) [[((-b/(2*a))%R, 0)]])
           with (c + b*(-b/(2*a)) + a*(-b/(2*a))^2)%R in H1 by (unfold Peval; simpl; lra).
         unfold Rdiv in *.
         unfold pow in *.
         apply (Rmult_le_pos a) in H1; try lra.
         rewrite Rmult_plus_distr_l, Rinv_mult_distr, Rmult_plus_distr_l in H1; try lra.
         replace (a * (b * (- b * (/ 2 * / a))))%R 
           with (- b * b * (a * / a) * / 2)%R in H1 by lra. 
         replace (a * (a * (- b * (/ 2 * / a) * (- b * (/ 2 * / a) * 1))))%R
           with (b * b * (a * /a) * (a * /a) * /2 * /2)%R in H1 by lra. 
         rewrite Rinv_r, Rmult_1_r, Rmult_1_r, Rmult_1_r, Rplus_assoc in H1; try lra.         
       - replace (fst ([(c, 0); (b, 0); (a, 0)]) [[(t, 0)]])
           with (c + b*t + a*t^2)%R by (unfold Peval; simpl; lra).
         rewrite <- (Rmult_1_l c), <- (Rmult_1_l b), <- (Rinv_r a); try lra.
         replace (a * / a * c + a * / a * b * t + a * t ^ 2)%R
           with (a * (c/a + b/a * t + t^2))%R by lra.
         assert (H1 : ((t + b/(2*a))^2 + ((a * c)* /a^2 - b^2/4 * /a^2) = 
                        (c / a + b / a * t + t ^ 2))%R).
         { unfold pow; repeat rewrite Rmult_1_r.
           unfold Rdiv; repeat rewrite Rinv_mult; try lra.
           replace ((t + b * (/ 2 * / a)) * (t + b * (/ 2 * / a)))%R 
             with (t * t + t * b * / a + (b * b * /a * /a * /4))%R by lra.
           replace (a * c * (/ a * / a))%R with (c * / a)%R; [ | shelve ].
           R_field_simplify.
           easy.
           lra.
           Unshelve.
           rewrite (Rmult_comm a c).
           rewrite Rmult_assoc.
           rewrite <- (Rmult_assoc a (/ a)).
           rewrite Rinv_r.
           all: lra.
         }
         rewrite <- H1.
         apply Rmult_le_pos; try lra.
         apply Rplus_le_le_0_compat.
         apply pow2_ge_0.
         replace (a * c * / a ^ 2 - b ^ 2 / 4 * / a ^ 2)%R
           with ((a * c - b ^ 2 / 4) * / a ^ 2)%R by lra.
         apply Rmult_le_pos.
         lra.
         assert (H' : 0 < / a ^ 2).
         apply Rinv_0_lt_compat; unfold pow; rewrite Rmult_1_r.
         apply Rmult_lt_0_compat; auto.
         lra. 
Qed.




       



(*****)
