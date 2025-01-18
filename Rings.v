
Require Import List.       
Require Export Complex.

(*
Require Export Quantum. 
Require Import FTA.
*)


 

(* how should I do this? *)
(*
Lemma Submonoid_theorem : forall (R : Set) `{Monoid R} (S : Set) 
                            (S0 : S) (Splus : S -> S -> S) (StoR : S -> R),
 (forall s1 s2, StoR (Splus s1 s2) = ((StoR s1) + (StoR s2))%G) -> 
  Monoid S.
Proof. intros. 
       split. 


Lemma Subring_theorem : forall (R : Set) `{Comm_Ring R} (S : Set) (S0 S1 : S) (Splus : S -> S -> S) 
                          (Sopp : S -> S) (Smult : S -> S -> S) (StoR : S -> R),
 (forall s1 s2, StoR (Splus s1 s2) = ((StoR s1) + (StoR s2))%G) -> 
 (forall s, StoR (Sopp s) = (- (StoR s))%G) ->
  Monoid S.
Proof. intros. 
*)







Open Scope C_scope.

(* exponentiation by positives *)
Fixpoint Cpow_pos (c : C) (p : positive) : C :=
  match p with 
  | xH => c
  | xO p' => (Cpow_pos c p') * (Cpow_pos c p')
  | xI p' => c * (Cpow_pos c p') * (Cpow_pos c p')
  end.             




Lemma Cpow_pos_to_nat : forall (c : C) (p : positive),
  Cpow_pos c p = c ^ (Pos.to_nat p).
Proof. intros. 
       induction p.
       - rewrite Pos2Nat.inj_xI, Nat.mul_comm; simpl. 
         rewrite Cpow_mult, IHp. 
         lca.
       - rewrite Pos2Nat.inj_xO, Nat.mul_comm; simpl. 
         rewrite Cpow_mult, IHp. 
         lca.
       - lca.
Qed.

Lemma Cpow_pos_0 : forall (p : positive), Cpow_pos C0 p = C0. 
Proof.
  intros p.
  rewrite Cpow_pos_to_nat.
  apply Cpow_0_l.
  lia.
Qed.

Lemma Cpow_pos_nonzero : forall (c : C) (p : positive), c <> C0 -> Cpow_pos c p <> C0. 
Proof. intros.
       rewrite Cpow_pos_to_nat.
       apply Cpow_nonzero.  
       easy.
Qed.


Lemma Cpow_pos_add_r : forall (c : C) (p1 p2 : positive), 
  Cpow_pos c (p1 + p2) = (Cpow_pos c p1) * (Cpow_pos c p2).
Proof. intros.
       do 3 rewrite Cpow_pos_to_nat.
       rewrite Pos2Nat.inj_add, Cpow_add.
       easy.
Qed.


Lemma Cpow_pos_mult_r : forall (c : C) (p1 p2 : positive), 
  Cpow_pos c (p1 * p2) = Cpow_pos (Cpow_pos c p1) p2.
Proof. intros. 
       do 3 rewrite Cpow_pos_to_nat.
       rewrite Pos2Nat.inj_mul, Cpow_mult.
       easy.
Qed.

Lemma Cpow_pos_mult_l : forall (c1 c2 : C) (p : positive), 
  Cpow_pos (c1 * c2) p = (Cpow_pos c1 p) * (Cpow_pos c2 p). 
Proof. intros. 
       do 3 rewrite Cpow_pos_to_nat.
       rewrite Cpow_mul_l.
       easy.
Qed.

Lemma Cpow_pos_succ : forall (c : C) (p : positive), 
  Cpow_pos c (Pos.succ p) = c * Cpow_pos c p.
Proof. intros.
       induction p; simpl; auto.
       - rewrite IHp; lca.
       - lca.
Qed.

Lemma Cpow_pos_pred_double : forall (c : C) (p : positive), 
  Cpow_pos c (Pos.pred_double p) = (/ c) * (Cpow_pos c p * Cpow_pos c p).
Proof. 
  intros c p.
  destruct (Ceq_dec c 0); [subst; rewrite Cpow_pos_0; lca|].
  induction p; simpl; auto.
  - repeat rewrite Cmult_assoc.
    rewrite Cinv_l; try lca; auto.
  - rewrite IHp.
    repeat rewrite Cmult_assoc.
    rewrite Cinv_r; try lca; auto.
  - rewrite Cmult_assoc, Cinv_l; try lca; auto.
Qed.

Lemma Cpow_pos_inv : forall (c : C) (p : positive),
  Cpow_pos (/ c) p = / (Cpow_pos c p).
Proof. 
  intros c p. 
  destruct (Ceq_dec c 0); [subst; rewrite Cinv_0, Cpow_pos_0; lca|].
  induction p; simpl.
  - rewrite IHp.
    repeat rewrite Cinv_mult_distr; auto.
  - rewrite IHp.
    rewrite Cinv_mult_distr; try apply Cpow_pos_nonzero; auto.
  - easy.
Qed.

Lemma Cpow_pos_real : forall (c : C) (p : positive), 
  snd c = 0 -> snd (Cpow_pos c p) = 0.
Proof. intros.
       induction p; simpl.
       - rewrite IHp, H; lra.
       - rewrite IHp; lra.
       - easy.
Qed.


Lemma Cpow_pos_1 : forall (p : positive),
  Cpow_pos C1 p = C1.
Proof. intros.
       induction p; simpl.
       - rewrite IHp; lca.
       - rewrite IHp; lca.
       - lca.
Qed.


(* exponentiation by integers *)
Definition Cpow_int (c : C) (z : Z) : C :=  
  match z with
    | Z0 => C1
    | Zpos p => Cpow_pos c p
    | Zneg p => / Cpow_pos c p
  end.


Infix "^^" := Cpow_int (at level 10) : C_scope.



Lemma Cpow_int_nonzero : forall (c : C) (z : Z), c <> C0 -> c ^^ z <> C0. 
Proof. intros.
       destruct z.
       - apply C1_neq_C0.
       - apply Cpow_pos_nonzero; easy.
       - apply nonzero_div_nonzero.
         apply Cpow_pos_nonzero; easy.
Qed.

Lemma Cpow_int_0_l : forall (z : Z), z <> 0%Z -> C0 ^^ z = C0.
Proof.
  intros z Hz.
  destruct z; [easy|..];
  simpl.
  - apply Cpow_pos_0.
  - rewrite Cpow_pos_0, Cinv_0.
    reflexivity.
Qed.

Lemma Cpow_int_add_1 : forall (c : C) (z : Z), 
  c <> C0 -> c ^^ (1 + z) = c * c^^z.
Proof. 
  intros.
  destruct z; try lca.
  - destruct p; simpl; try lca. 
    rewrite Cpow_pos_succ; lca.
  - destruct p; simpl.
    + rewrite <- Cmult_assoc, (Cinv_mult_distr c); auto.
      destruct (Ceq_dec c 0);
      [subst; now rewrite Cpow_pos_0, !Cmult_0_l, Cinv_0|].
      rewrite Cmult_assoc, Cinv_r; try lca; auto.
    + rewrite Cpow_pos_pred_double, Cinv_mult_distr, Cinv_inv; auto.
    + rewrite Cinv_r; easy.
Qed.

Lemma Cpow_int_minus_1 : forall (c : C) (z : Z), 
  c <> C0 -> c ^^ (-1 + z) = / c * c^^z.
Proof. intros.
       destruct z; try lca.
       - destruct p; simpl; try lca. 
         + repeat rewrite Cmult_assoc.
           rewrite Cinv_l; auto; lca.
         + rewrite Cpow_pos_pred_double; auto.
         + rewrite Cinv_l; easy.
       - destruct p; simpl; try lca. 
         + rewrite Cpow_pos_succ, <- Cinv_mult_distr; auto.
           apply f_equal; lca.
         + rewrite <- Cmult_assoc, Cinv_mult_distr; auto.
         + rewrite Cinv_mult_distr; easy.
Qed.

Lemma Cpow_int_add_nat : forall (c : C) (n : nat) (z : Z), 
  c <> C0 -> c ^^ (Z.of_nat n + z) = c^^(Z.of_nat n) * c^^z.
Proof. intros.
       induction n; try lca.
       replace (S n + z)%Z with (1 + (n + z))%Z by lia.
       replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.       
       repeat rewrite Cpow_int_add_1; auto.
       rewrite IHn; lca.
Qed.

Lemma Cpow_int_minus_nat : forall (c : C) (n : nat) (z : Z), 
  c <> C0 -> c ^^ (- Z.of_nat n + z) = c^^(- Z.of_nat n) * c^^z.
Proof. intros. 
       induction n; try lca.
       replace (- S n + z)%Z with (- 1 + (- n + z))%Z by lia.
       replace (- (S n))%Z with (- 1 + - n)%Z by lia.       
       repeat rewrite Cpow_int_minus_1; auto.
       rewrite IHn; lca.
Qed.

Theorem Cpow_int_add_r : forall (c : C) (z1 z2 : Z), 
  c <> C0 -> c ^^ (z1 + z2) = c^^z1 * c^^z2.
Proof. intros.
       destruct (Z_plusminus_nat z1) as [n [H0 | H0]].
       - rewrite H0, Cpow_int_add_nat; easy.
       - rewrite H0, Cpow_int_minus_nat; easy.
Qed.

Lemma Cpow_int_mult_r : forall (c : C) (z1 z2 : Z), 
  c <> C0 -> c ^^ (z1 * z2) = (c ^^ z1) ^^ z2.
Proof. intros. 
       destruct z1; destruct z2; try lca; simpl.
       all : try (rewrite Cpow_pos_1; lca).
       all : rewrite Cpow_pos_mult_r; try lca. 
       all : rewrite Cpow_pos_inv; try apply Cpow_pos_nonzero; auto.
       rewrite Cinv_inv; auto.
Qed.

Lemma Cpow_int_mult_l : forall (c1 c2 : C) (z : Z), 
  c1 <> C0 -> c2 <> C0 -> (c1 * c2) ^^ z = (c1 ^^ z) * (c2 ^^ z).
Proof. intros. 
       destruct z; try lca; simpl. 
       rewrite Cpow_pos_mult_l; easy.
       rewrite Cpow_pos_mult_l, Cinv_mult_distr; auto; 
       apply Cpow_pos_nonzero; easy.
Qed.


Lemma Cpow_inv1 : forall (c : C) (z : Z), c <> C0 -> c^^(-z) = / (c^^z).
Proof. intros.
       replace (-z)%Z with (z * -1)%Z by lia.
       rewrite Cpow_int_mult_r; easy.
Qed.

Lemma Cpow_inv2 : forall (c : C) (z : Z), c <> C0 -> (/ c)^^z = / (c^^z).
Proof. intros.
       replace z with (-1 * -z)%Z by lia.
       rewrite Cpow_int_mult_r. 
       replace ((/ c) ^^ (-1)) with (/ / c) by easy.
       replace (-1 * - z)%Z with z by lia.
       rewrite Cinv_inv, Cpow_inv1; auto.
       apply nonzero_div_nonzero; auto.
Qed.


(* checking that Cpow_int is consistent with Cpow on nats *)
Lemma Cpow_int_cons : forall (c : C) (n : nat),
  c^n = c ^^ n.
Proof. intros. 
       destruct n; try lca.
       unfold Cpow_int.
       destruct (Z.of_nat (S n)) eqn:E; try easy.
       rewrite Cpow_pos_to_nat.
       apply f_equal_gen; try apply f_equal; auto.
       apply Pos2Z.inj_pos in E.
       rewrite <- E, SuccNat2Pos.id_succ.
       easy.
Qed.


Lemma Cpow_int_real : forall (c : C) (z : Z), 
  c <> 0 -> snd c = 0 -> snd (c ^^ z) = 0.
Proof. intros.
       destruct z; auto.
       - simpl; apply Cpow_pos_real; auto.
       - replace (Z.neg p) with (- Z.pos p)%Z by lia.
         rewrite Cpow_inv1; auto.
         apply div_real.
         apply Cpow_pos_real; auto.
Qed.



(* foreboding: translating between Cpow_int and Zpow *)
Lemma ZtoC_pow_nat : forall (z : Z) (n : nat), 
  RtoC (IZR (z^n)%Z) = (RtoC (IZR z))^^n.
Proof. intros. 
       induction n; try easy.
       rewrite <- Cpow_int_cons in *.
       replace (S n) with (1 + n)%nat by lia.
       rewrite Nat2Z.inj_add, Z.pow_add_r, Cpow_add_r; try lia.
       rewrite mult_IZR, <- IHn, RtoC_mult, RtoC_pow, pow_IZR.
       apply f_equal_gen; auto.
Qed.



(* foreboding: translating between Cpow_int and Zpow *)
Lemma ZtoC_pow : forall (z n : Z), 
  (n >= 0)%Z ->
  RtoC (IZR (z^n)%Z) = (RtoC (IZR z))^^n.
Proof. intros.
       destruct (Z_plusminus_nat n) as [x [H0 | H0]]; subst.
       - rewrite ZtoC_pow_nat; easy.
       - destruct x; try lia.
         replace (-O)%Z with (Z.of_nat O) by lia.
         rewrite ZtoC_pow_nat; easy.
Qed.



#[global] Hint Rewrite plus_IZR minus_IZR opp_IZR mult_IZR ZtoC_pow : ZtoR_db.

(* NB: use plus_IZR, mult_IZR, RtoC_plus, RtoC_mult to move between types: *)
(* quick helper tactic. TODO: centralize these *)
Ltac fastZtoC := repeat (autorewrite with ZtoR_db; autorewrite with RtoC_db; try lia).





   
(*
 *
 *
 *)







(* fst d is the 2-adic value of d, snd d is (odd leftover part / 2) *)

(* should this be type or Set ?*)
(* TODO: could make Dpos Dneg, like Z, but this makes for a lot of cases *)
Inductive Dyadic : Set :=
  | D0 : Dyadic
  | Dn : Z -> Z -> Dyadic. (* fst arg = 2-adic value, snd arg = (odd_part / 2) *)


Definition D1 : Dyadic := Dn 0 0.
Definition D2 : Dyadic := Dn 1 0.
Definition Dhalf : Dyadic := Dn (Z.opp 1) 0.


Declare Scope D_scope.
Delimit Scope D_scope with D.
 
Open Scope D_scope.
Bind Scope D_scope with Dyadic.


Open Scope Z_scope. 

Coercion IZR : Z >-> R.




Definition DtoC (x : Dyadic) : C := 
  match x with
  | D0 => C0
  | Dn n x => (C2^^n * (C2 * x + 1))
  end.


Coercion DtoC : Dyadic >-> C.
(* Coercions make things soo nice! *)




Lemma DtoC_D0 : DtoC D0 = C0.
Proof. easy. Qed.

Lemma DtoC_D1 : DtoC D1 = C1.
Proof. lca. Qed.

Lemma DtoC_D2 : DtoC D2 = C2.
Proof. lca. Qed.

Lemma DtoC_Dhalf : DtoC Dhalf = / C2.
Proof. unfold DtoC, Dhalf.
       rewrite Cpow_inv1. 
       lca.
       apply RtoC_neq.
       lra.
Qed.
     

Lemma DtoC_neq_0 : forall (z z0 : Z),
  (C2 ^^ z * (C2 * z0 + C1))%C <> C0.
Proof. intros.
       apply Cmult_neq_0.
       apply Cpow_int_nonzero. 
       apply RtoC_neq; lra.
       replace (C2 * z0 + C1)%C with (RtoC (IZR (2 * z0 + 1)%Z)).
       unfold not; intros.        
       apply RtoC_inj in H.
       apply eq_IZR in H. 
       lia.
       fastZtoC.
       easy.
Qed.


Lemma move_power_2 : forall (z1 z2 : Z) (c1 c2 : C),
  (C2 ^^ z1 * c1 = C2 ^^ z2 * c2)%C -> (c1 = C2 ^^ (z2 - z1) * c2)%C.
Proof. intros.
       apply (Cmult_simplify (C2 ^^ (-z1)) (C2 ^^ (-z1))) in H; auto.
       do 2 rewrite Cmult_assoc, <- Cpow_int_add_r in H.
       replace (- z1 + z1) with 0 in H by lia; simpl in H.
       rewrite Cmult_1_l in H; subst.
       replace (- z1 + z2) with (z2 - z1) by lia.
       easy.
       all : apply RtoC_neq; lra.
Qed.


(* TODO: move these next two lemmas somewhere else, they are never used here *)
Lemma log2_inj_0 : forall (n : nat),
  (C2 ^ n)%C = C1 -> n = O.
Proof. intros. 
       destruct n; try easy; simpl in *.
       assert (H' : forall n, (C2 ^ n)%C = RtoC (IZR ((2 ^ n)%Z))).
       { induction n0; auto.
         replace (C2 ^ S n0)%C with (C2 * (C2 ^ n0))%C by easy.
         rewrite IHn0.
         autorewrite with ZtoR_db; try lia.
         replace (Z.of_nat (S n0)) with (1 + n0)%Z by lia.
         rewrite Cpow_int_add_r; try easy.
         apply RtoC_neq; lra. }
       rewrite H' in H. 
       simpl in H.
       rewrite <- RtoC_mult in H.
       apply RtoC_inj in H.
       rewrite <- mult_IZR in H.
       apply eq_IZR in H. 
       lia.
Qed.


Lemma log2_inj : forall (n1 n2 : nat), 
  Cpow C2 n1 = Cpow C2 n2 -> n1 = n2.
Proof. induction n1.
       - intros. 
         replace (C2 ^ 0)%C with C1 in H by easy. 
         symmetry in H.
         apply log2_inj_0 in H; easy.
       - intros.
         destruct n2.
         replace (C2 ^ 0)%C with C1 in H by easy. 
         apply log2_inj_0 in H; easy.
         simpl in H.
         rewrite (IHn1 n2); auto.
         apply Cmult_cancel_l in H; auto.
         apply RtoC_neq; lra.
Qed.


Lemma DtoC_inj_uneq_case : forall z z0 z1 z2 : Z, 
  z < z1 -> 
  (C2 ^^ z * (C2 * z0 + C1))%C = (C2 ^^ z1 * (C2 * z2 + C1))%C ->
  False.
Proof. intros. 
       apply move_power_2 in H0.
       assert (H' : 0 < z1 - z). lia.
       destruct (Z_plusminus_nat (z1 - z)) as [x [H1 | H1]]; try lia.
       rewrite H1 in *.
       destruct x; try easy.
       rewrite <- ZtoC_pow_nat in H0.
       repeat rewrite <- RtoC_mult, <- mult_IZR in H0.
       repeat rewrite <- RtoC_plus, <- plus_IZR in H0.
       repeat rewrite <- RtoC_mult, <- mult_IZR in H0.
       apply RtoC_inj in H0.
       apply eq_IZR in H0. 
       replace (Z.of_nat (S x)) with (1 + x)%Z in H0 by lia.
       rewrite Z.pow_add_r in H0; try lia.
Qed.


(* idea: WLOG v(x) <= v(y), equality case is easy, then reflect back to Z *)
Lemma DtoC_inj : forall (x y : Dyadic),
  DtoC x = DtoC y -> x = y.
Proof.
  intros. 
  unfold DtoC in *.
  destruct x; destruct y; try easy.
  - assert (H' := DtoC_neq_0 z z0).
    rewrite H in H'; easy.
  - assert (H' := DtoC_neq_0 z z0).
    rewrite H in H'; easy.
  - destruct (Ztrichotomy_inf z z1) as [[H0 | H0] | H0].
    + apply DtoC_inj_uneq_case in H; lia. 
    + subst.
      apply move_power_2 in H.
      replace (z1 - z1)%Z with 0%Z in H by lia.
      rewrite Cmult_1_l in H.
      apply (Cplus_simplify _ _ (-C1) (-C1)) in H; auto.
      replace (C2 * z0 + C1 + - C1)%C with (C2 * z0)%C in H by lca.
      replace (C2 * z2 + C1 + - C1)%C with (C2 * z2)%C in H by lca.
      apply Cmult_cancel_l in H. 
      apply RtoC_inj in H.
      apply eq_IZR in H; subst; easy.
      apply RtoC_neq; lra.
    + symmetry in H.
      apply DtoC_inj_uneq_case in H; lia. 
Qed.
      



(* this is actually overkill because Z is decible, but shows usefulness of DtoC_inj *)
Lemma Deq_dec (d1 d2 : Dyadic) : { d1 = d2 } + { ~ (d1 = d2) }.
Proof.
  destruct (Ceq_dec (DtoC d1) (DtoC d2)).
  - apply DtoC_inj in e.
    left; easy.
  - right. 
    unfold not; intros; apply n. 
    rewrite H; easy. 
Qed.
    


(* TODO: create 'lda', which is like lca but for dyadics *)

(*  
(* lca, a great tactic for solving computations or basic equality checking *)
Lemma c_proj_eq : forall (c1 c2 : C), fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.  
Proof. intros c1 c2 H1 H2. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

(* essentially, we just bootsrap coq's lra *)
Ltac lca := eapply c_proj_eq; simpl; lra.
*)



(** *** Arithmetic operations *)


(* this one will be terrible... but just need to prove DtoC_plus! *)
Definition Dplus (x y : Dyadic) : Dyadic :=
  match (x, y) with 
  | (D0, _) => y
  | (_, D0) => x
  | (Dn n x', Dn m y') => 
      match Ztrichotomy_inf n m with
      | inleft (left _) =>                      (* x has lower power of 2 *)
          Dn n (2^(m-n-1) * (2*y'+1) + x')      
      | inleft (right _) =>                     (* equal power of 2 *)
          match odd_part ((2*x'+1) + (2*y'+1)) with
          | Z0 => D0
          | _ => Dn (n + two_val ((2*x'+1) + (2*y'+1))) 
                   (((odd_part ((2*x'+1) + (2*y'+1))) - 1) / 2)
          end                                  (* y has lower power of 2 *)
      | inright _ => Dn m (2^(n-m-1) * (2*x'+1) + y')            
      end
  end.


Definition Dopp (x : Dyadic) : Dyadic := 
  match x with 
  | D0 => D0
  | Dn n x => Dn n (-x-1)
  end.

Definition Dminus (x y : Dyadic) : Dyadic := Dplus x (Dopp y).

(* this one is much easier! *)
Definition Dmult (x y : Dyadic) : Dyadic :=
  match (x, y) with 
  | (D0, _) => D0
  | (_, D0) => D0
  | (Dn n x, Dn m y) => Dn (n + m) (2*x*y + x + y)
  end.


Fixpoint Dpow (d : Dyadic) (n : nat) : Dyadic :=  
  match n with
  | 0%nat => D1
  | S n' => Dmult d (Dpow d n')
  end.

 


Infix "+," := Dplus (at level 50, left associativity) : D_scope. 
Infix "*," := Dmult (at level 40, left associativity) : D_scope. 
Notation "-, d" := (Dopp d) (at level 35) : D_scope.  
Infix "-," := Dminus (at level 50, left associativity) : D_scope.
Infix "^," := Dpow (at level 30) : D_scope.

(* showing compatability *)


(* could make this shorter, but it was also expected that this would be the hardest part,
   so its messiness is warrented *)
Lemma DtoC_plus : forall d1 d2, DtoC (d1 +, d2) = (DtoC d1 + DtoC d2)%C.
Proof. intros.
       destruct d1; destruct d2; simpl; try lca.
       unfold Dplus; destruct (Ztrichotomy_inf z z1); try destruct s. 
       - unfold Dplus, DtoC. 
         fastZtoC. 
         rewrite (Cmult_plus_distr_l _ _ z0), (Cmult_assoc C2).
         replace (C2 * C2 ^^ (z1 - z - 1))%C with (C2 ^^ (z1 - z)).
         rewrite <- Cplus_assoc, (Cmult_plus_distr_l _ _ (C2 * z0 + C1)), Cmult_assoc.
         replace (C2 ^^ z * C2 ^^ (z1 - z))%C with (C2 ^^ z1).
         lca.
         rewrite <- Cpow_int_add_r.
         apply f_equal; lia.
         apply RtoC_neq; lra.
         replace (Cmult C2) with (Cmult (C2 ^^ 1)) by (apply f_equal; easy).
         rewrite <- Cpow_int_add_r.
         apply f_equal; lia.
         apply RtoC_neq; lra.
       - subst.
         replace (2 * z0 + 1 + (2 * z2 + 1))%Z with (2 * (z0 + z2 + 1))%Z by lia.
         rewrite odd_part_reduce.
         destruct (Z.eq_dec (z0 + z2 + 1) Z0).
         rewrite e. simpl.
         replace (C2 ^^ z1 * (C2 * z0 + C1) + C2 ^^ z1 * (C2 * z2 + C1))%C with
           (C2 ^^ z1 * C2 * (z0 + z2 + C1))%C by lca.
         do 2 rewrite <- RtoC_plus, <- plus_IZR.
         rewrite e.
         lca.
         assert (H' : odd_part (z0 + z2 + 1) <> 0). 
         unfold not; intros; apply n.
         apply odd_part_0; auto.
         destruct (odd_part (z0 + z2 + 1)) eqn:E; try easy.
         all : unfold DtoC; 
           repeat (repeat rewrite <- RtoC_plus, <- plus_IZR;
                   repeat rewrite <- RtoC_mult, <- mult_IZR).
         all : rewrite <- E, odd_part_odd, Cpow_int_add_r, <- Cmult_plus_distr_l, 
           <- Cmult_assoc; auto; try apply f_equal.
         all : try (apply RtoC_neq; lra).
         all : rewrite <- ZtoC_pow, <- odd_part_reduce; try apply two_val_ge_0.
         all : rewrite <- RtoC_mult, <- mult_IZR, <- RtoC_plus, <- plus_IZR.
         all : rewrite <- twoadic_breakdown; try lia.
         all : fastZtoC; lca.
       - unfold Dplus, DtoC. 
         fastZtoC. 
         rewrite (Cmult_plus_distr_l _ _ z2), (Cmult_assoc C2).
         replace (C2 * C2 ^^ (z - z1 - 1))%C with (C2 ^^ (z - z1)).
         rewrite <- Cplus_assoc, (Cmult_plus_distr_l _ _ (C2 * z2 + C1)), Cmult_assoc.
         replace (C2 ^^ z1 * C2 ^^ (z - z1))%C with (C2 ^^ z).
         lca.
         rewrite <- Cpow_int_add_r.
         apply f_equal; lia.
         apply RtoC_neq; lra.
         replace (Cmult C2) with (Cmult (C2 ^^ 1)) by (apply f_equal; easy).
         rewrite <- Cpow_int_add_r.
         apply f_equal; lia.
         apply RtoC_neq; lra.       
Qed.
 

         


Lemma DtoC_opp : forall d, DtoC (-, d) = (- (DtoC d))%C. 
Proof. intros.
       destruct d; try lca. 
       unfold Dopp, DtoC, Zminus.
       fastZtoC.
       rewrite Copp_mult_distr_r. 
       lca.
Qed.       


Lemma DtoC_minus : forall d1 d2, DtoC (d1 -, d2) = ((DtoC d1) - (DtoC d2))%C. 
Proof. intros.
       unfold Cminus, Dminus.
       rewrite DtoC_plus, DtoC_opp.
       easy.
Qed.     


(* this is surprisingly easy! *)
Lemma DtoC_mult : forall d1 d2,  DtoC (d1 *, d2) = (DtoC d1 * DtoC d2)%C.
Proof. intros.
       destruct d1; destruct d2; try lca.
       unfold Dmult, DtoC.
       fastZtoC.
       rewrite Cpow_int_add_r.
       lca.
       apply RtoC_neq; lra.
Qed.


Lemma DtoC_pow : forall d n,  DtoC (d ^, n) = ((DtoC d) ^ n)%C. 
Proof. intros.
       induction n.
       - lca.
       - simpl. 
         rewrite DtoC_mult, IHn.
         easy.
Qed.


#[global] Hint Rewrite DtoC_plus DtoC_opp DtoC_minus DtoC_mult DtoC_pow : DtoC_db.


Ltac lDa_try1 := apply DtoC_inj; autorewrite with DtoC_db; lca.



(* Note that once we have a injective homomorphism into C, 
   we get all the ring axioms for free! *)
(* TODO: generalize this in Summation.v *)


Lemma Dplus_comm : forall d1 d2, d1 +, d2 = d2 +, d1.
Proof. intros. lDa_try1. Qed.

Lemma Dplus_assoc : forall d1 d2 d3, d1 +, (d2 +, d3) = d1 +, d2 +, d3.
Proof. intros. lDa_try1. Qed.

Lemma Dplus_0_r : forall d, d +, D0 = d.
Proof. intros. lDa_try1. Qed.

Lemma Dplus_0_l : forall d, D0 +, d = d.
Proof. intros. lDa_try1. Qed.

Lemma Dminus_0_r : forall d, d -, D0 = d.
Proof. intros. lDa_try1. Qed.

Lemma Dminus_0_l : forall d, D0 -, d = -, d.
Proof. intros. lDa_try1. Qed.

Lemma Dmult_0_r : forall d, d *, D0 = D0.
Proof. intros. lDa_try1. Qed.

Lemma Dmult_0_l : forall d, D0 *, d = D0.
Proof. intros. lDa_try1. Qed.

Lemma Dmult_comm : forall d1 d2, d1 *, d2 = d2 *, d1.
Proof. intros. lDa_try1. Qed.

Lemma Dmult_assoc : forall d1 d2 d3, d1 *, (d2 *, d3) = d1 *, d2 *, d3.
Proof. intros. lDa_try1. Qed.

Lemma Dmult_1_r : forall d, d *, D1 = d.
Proof. intros. lDa_try1. Qed.

Lemma Dmult_1_l : forall d, D1 *, d = d.
Proof. intros. lDa_try1. Qed.

Lemma Dopp_mult_distr_l : forall d1 d2, -, (d1 *, d2) = (-, d1) *, d2.
Proof. intros. lDa_try1. Qed.

Lemma Dopp_mult_distr_r : forall d1 d2, -, (d1 *, d2) = d1 *, (-, d2).
Proof. intros. lDa_try1. Qed.

Lemma Dopp_mult_neg_l : forall d, -, d = (-, D1) *, d.
Proof. intros. lDa_try1. Qed.

Lemma Dopp_mult_neg_r : forall d, -, d = d *, (-, D1).
Proof. intros. lDa_try1. Qed.


Lemma Dminus_diag : forall d1 d2 : Dyadic, d1 = d2 -> d1 -, d2 = D0.
Proof. intros; subst.
       apply DtoC_inj.
       rewrite DtoC_minus.
       replace (DtoC D0) with C0 by lca.
       apply Cminus_diag.
       easy. 
Qed.


Lemma Dminus_eq_0 : forall r1 r2 : Dyadic, r1 -, r2 = D0 -> r1 = r2.
Proof. intros.
       unfold Dminus, Dopp, Dplus.
       apply DtoC_inj.
       apply Cminus_eq_0.
       rewrite <- DtoC_minus, H.
       easy. 
Qed.


Lemma Dmult_neq_0 : forall d1 d2 : Dyadic, d1 <> D0 -> d2 <> D0 -> d1 *, d2 <> D0.
Proof. intros. 
       unfold not; intros. 
       apply (f_equal_gen DtoC DtoC) in H1; auto.
       rewrite DtoC_mult, DtoC_D0 in H1.
       apply Cmult_integral in H1.
       destruct H1.
       apply H; apply DtoC_inj; easy.
       apply H0; apply DtoC_inj; easy.
Qed.

Lemma Dmult_integral : forall d1 d2 : Dyadic, d1 *, d2 = D0 -> d1 = D0 \/ d2 = D0.
Proof. intros. 
       destruct (Deq_dec d1 D0); try (left; easy).
       destruct (Deq_dec d2 D0); try (right; easy).
       apply (Dmult_neq_0 d1 d2) in n0; auto.
       easy. 
Qed.

Lemma Dpow_add : forall (d : Dyadic) (n m : nat), d ^, (n + m) = d^,n *, d^,m.
Proof. intros.
       apply DtoC_inj.
       rewrite DtoC_mult.
       do 3 rewrite DtoC_pow.
       rewrite Cpow_add; easy.
Qed.


Lemma Dpow_mult : forall (d : Dyadic) (n m : nat), d ^, (n * m) = (d ^, n) ^, m.
Proof. intros.
       apply DtoC_inj.       
       do 3 rewrite DtoC_pow.
       rewrite Cpow_mult; easy.
Qed.



(* we showcase two different approaches to numerical proofs based on the above *)
Lemma Dhalf_double_1 : Dhalf +, Dhalf = D1.
Proof. unfold Dhalf, Dplus; simpl.
       replace (0 / 2) with 0%Z.
       easy.
       rewrite Zdiv.Zdiv_0_l.
       easy.
Qed.

Lemma Dhalf_double_2 : Dhalf +, Dhalf = D1.
Proof. apply DtoC_inj. 
       rewrite DtoC_plus.
       rewrite DtoC_Dhalf, DtoC_D1.
       lca.
Qed.


(* I prefer the second way *)
Lemma Dmult_2_half : D2 *, Dhalf = D1.
Proof. apply DtoC_inj. 
       rewrite DtoC_mult.
       rewrite DtoC_Dhalf, DtoC_D2, DtoC_D1.
       lca.
Qed.


Lemma Dmult_half_2 : Dhalf *, D2 = D1.
Proof. apply DtoC_inj. 
       rewrite DtoC_mult.
       rewrite DtoC_Dhalf, DtoC_D2, DtoC_D1.
       lca.
Qed.



Lemma Dpow_2_pos : forall (n : positive), D2 ^, (Pos.to_nat n) = Dn (Z.pos n) 0.
Proof. intros.
       apply DtoC_inj.
       rewrite DtoC_pow; simpl.
       rewrite Cpow_pos_to_nat, Cmult_0_r, Cplus_0_l, Cmult_1_r, Cmult_1_r.
       easy. 
Qed.       

Lemma Dpow_2_nat : forall (n : nat), D2 ^, (S n) = Dn (Z.of_nat (S n)) 0.
Proof. intros; simpl. 
       rewrite <- Dpow_2_pos.
       replace (D2 *, D2 ^, n) with (D2 ^, (S n)) by easy. 
       apply f_equal_gen; auto.
       rewrite SuccNat2Pos.id_succ; easy.
Qed.


(* some more specific lemmas: *)

Lemma Dyadic_real : forall (d : Dyadic), snd (DtoC d) = 0.
Proof. intros. 
       destruct d; unfold DtoC; simpl; try lra.  
       rewrite Cpow_int_real; simpl; try lra.
       apply RtoC_neq; lra.
Qed.

Lemma Cmult_d_l : forall (d : Dyadic) (r1 r2 : R),
  (d * (r1, r2))%C = (fst (DtoC d) * r1, fst (DtoC d) * r2)%R.
Proof. intros.
       unfold Cmult, DtoC; destruct d; simpl.
       all : apply injective_projections; simpl; try lra.
       all : replace (snd (C2 ^^ z)) with 0%R; try lra.
       all : rewrite Cpow_int_real; auto.
       all : apply C0_fst_neq; simpl; lra.
Qed.

Lemma Cconj_D : forall (d : Dyadic), Cconj d = d.
Proof. intros.
       destruct (DtoC d) eqn:E.
       unfold Cconj; simpl.
       replace r0 with (snd (DtoC d)) by (rewrite E; easy).
       rewrite Dyadic_real. 
       apply c_proj_eq; simpl; lra.
Qed.

Lemma Dyadic_is_0 : forall (d : Dyadic), 
  fst (DtoC d) = 0 ->
  d = D0.
Proof. intros. 
       apply DtoC_inj.
       apply injective_projections; auto.
       do 2 rewrite Dyadic_real.
       easy.
Qed.



(*
 *
 *
 *)


(* now we add Z *)

Close Scope Z_scope.
Open Scope D_scope.


(* the nonzero case is quite adhoc here, might want to use more machinery from above *)
Definition ZtoD (z : Z) : Dyadic := 
  match z with
  | Z0 => D0
  | Zpos p => Dn (two_val z) ((odd_part z - 1) / 2)
  | Zneg p => Dn (two_val z) ((odd_part z - 1) / 2)
  end.



Lemma ZtoD_0 : ZtoD 0 = D0.
Proof. easy. Qed.


Lemma ZtoD_1 : ZtoD 1 = D1.
Proof. easy. Qed.


Lemma ZtoD_2 : ZtoD 2 = D2.
Proof. easy. Qed.


Lemma ZtoDtoC_is_ZtoRtoC : forall (z : Z), DtoC (ZtoD z) = RtoC (IZR z).
Proof. intros. 
       destruct z; try lca; 
         destruct p; 
           unfold ZtoD, DtoC;
           rewrite <- RtoC_mult, <- mult_IZR, <- RtoC_plus, <- plus_IZR, odd_part_odd; 
           try lia; rewrite <- ZtoC_pow; try apply two_val_ge_0;
           rewrite <- RtoC_mult, <- mult_IZR, <- twoadic_breakdown; try lia;
           easy.
Qed.


(*
(*TODO: deal with this warning *)
(* This should really be Z -> D -> Q -> R -> C *)
Coercion ZtoD : Z >-> Dyadic.
*)


(* we now see the power of the injections and ZtoDtoC_is_ZtoRtoC for these next lemmas ! *)
(* TODO: automate proofs like this? *)

Lemma ZtoD_inj : forall (x y : Z),
  ZtoD x = ZtoD y -> x = y.
Proof. intros.
       apply eq_IZR; apply RtoC_inj.
       do 2 rewrite <- ZtoDtoC_is_ZtoRtoC.
       rewrite H.
       easy.
Qed.


Lemma ZtoD_plus : forall (z1 z2 : Z), ZtoD (z1 + z2)%Z = ZtoD z1 +, ZtoD z2.
Proof. intros.
       apply DtoC_inj.
       rewrite DtoC_plus.
       do 3 rewrite ZtoDtoC_is_ZtoRtoC.
       fastZtoC.
       easy. 
Qed.


Lemma ZtoD_opp : forall d, ZtoD (- d) = -, (ZtoD d). 
Proof. intros.
       apply DtoC_inj.
       rewrite DtoC_opp.
       do 2 rewrite ZtoDtoC_is_ZtoRtoC.
       fastZtoC.
       easy. 
Qed.

Lemma ZtoD_minus : forall (z1 z2 : Z), ZtoD (z1 - z2)%Z = ZtoD z1 -, ZtoD z2.
Proof. intros.
       apply DtoC_inj.
       rewrite DtoC_minus.
       do 3 rewrite ZtoDtoC_is_ZtoRtoC.
       fastZtoC.
       easy. 
Qed.

Lemma ZtoD_mult : forall z1 z2, ZtoD (z1 * z2)%Z = ZtoD z1 *, ZtoD z2.
Proof. intros.
       apply DtoC_inj.
       rewrite DtoC_mult.
       do 3 rewrite ZtoDtoC_is_ZtoRtoC.
       fastZtoC.
       easy. 
Qed.


(*
(* we can go Z -> Dyadic -> C or Z -> R -> C, so its actually ambiguous! 
   thus, we must specify *)
Lemma ZtoD_C0 : forall (z : Z),
  DtoC (ZtoD z) = C0 <-> (z = 0)%Z.
Proof. intros; split; intros.
       - apply ZtoD_inj.
         apply DtoC_inj.
         rewrite H.
         unfold ZtoD, DtoC; lca.
       - rewrite H.
         lca.
Qed.
*)



(** Going back from D to Z *)

Definition DtoZ (d : Dyadic) : Z :=
  match d with
  | D0 => 0
  | Dn n x => 2^n * (2 * x + 1)
  end. 



Definition DisZ (d : Dyadic) : Prop :=
  match d with
  | D0 => True
  | Dn n x => (n >= 0)%Z
  end.



Lemma DisZ_plus : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 ->
  DisZ (d1 +, d2).
Proof. intros.
       destruct d1; destruct d2; try easy.
       unfold Dplus, DisZ in *.
       destruct (Ztrichotomy_inf z z1); try lia.
       destruct s; try lia.  
       destruct (odd_part (2 * z0 + 1 + (2 * z2 + 1))); auto; 
         apply Z.le_ge; apply Z.add_nonneg_nonneg; try lia.
       all : apply Z.ge_le; apply two_val_ge_0.
Qed.

Lemma DisZ_opp : forall (d : Dyadic),
  DisZ d -> DisZ (-, d).
Proof. intros.
       destruct d; try easy.
Qed.

Lemma DisZ_minus : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 ->
  DisZ (d1 -, d2).
Proof. intros.
       unfold Dminus.
       apply DisZ_plus; auto.
       apply DisZ_opp; easy.
Qed.


Lemma DisZ_mult : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 ->
  DisZ (d1 *, d2).
Proof. intros.
       destruct d1; destruct d2; try easy.
       unfold Dmult, DisZ in *.
       lia. 
Qed.

Lemma DisZ_pow : forall (d : Dyadic) (n : nat),
  DisZ d -> DisZ (d ^, n).
Proof. intros.
       induction n; try easy.
       simpl.
       apply DisZ_mult; easy. 
Qed.


Lemma DisZ_dec : forall (d : Dyadic),
  { DisZ d } + { ~ DisZ d }.
Proof. intros. 
       destruct d; try (left; easy).
       simpl.
       apply Z_ge_dec.
Qed.


Lemma DtoZtoD : forall (d : Dyadic), 
  DisZ d -> d = ZtoD (DtoZ d).
Proof. intros. 
       destruct d; try easy.
       unfold ZtoD, DtoZ.
       simpl in H.
       destruct (2 ^ z * (2 * z0 + 1))%Z eqn:E.
       - apply Zmult_integral in E; destruct E. 
         all: try (contradict H0; apply Z.pow_nonzero; lia); lia.
       - rewrite <- E.
         rewrite get_two_val, get_odd_part; auto.
         replace (2 * z0 + 1 - 1)%Z with (2 * z0)%Z by lia.
         rewrite Zmult_comm, Zdiv.Z_div_mult; try lia.
         easy. 
       - rewrite <- E.
         rewrite get_two_val, get_odd_part; auto.
         replace (2 * z0 + 1 - 1)%Z with (2 * z0)%Z by lia.
         rewrite Zmult_comm, Zdiv.Z_div_mult; try lia.
         easy. 
Qed.


Lemma ZtoDtoZ : forall (z : Z),
  z = DtoZ (ZtoD z).
Proof. intros.
       destruct z; try easy;
         unfold DtoZ, ZtoD;
         rewrite odd_part_odd, <- twoadic_breakdown; try lia.
Qed.       


(* a stronger converse to this is just DtoZtoD *)
Lemma DisZ_ver : forall (d : Dyadic), (exists (z : Z), d = ZtoD z) -> DisZ d.
Proof. intros. 
       destruct H; subst. 
       unfold DisZ, ZtoD.
       destruct x; try easy.
       all : apply two_val_ge_0.
Qed.   
       
  


Lemma DtoZ_plus : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 -> 
  DtoZ (d1 +, d2) = (DtoZ d1 + DtoZ d2)%Z.
Proof. intros.
       apply ZtoD_inj.
       rewrite ZtoD_plus.
       do 3 (try rewrite <- DtoZtoD; auto).
       apply DisZ_plus; easy.
Qed.


Lemma DtoZ_mult : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 -> 
  DtoZ (d1 *, d2) = (DtoZ d1 * DtoZ d2)%Z.
Proof. intros.
       apply ZtoD_inj.
       rewrite ZtoD_mult.
       do 3 (try rewrite <- DtoZtoD; auto).
       apply DisZ_mult; easy.
Qed.



Lemma DtoZ_0 : DtoZ D0 = 0%Z.
Proof. easy. Qed.

Lemma DtoZ_1 : DtoZ D1 = 1%Z.
Proof. easy. Qed.

Lemma DtoZ_2 : DtoZ D2 = 2%Z.
Proof. easy. Qed.


(** proof that sqrt2 cannot be written as the ratio of Dyadics *)

Lemma Dyadic_is_rational : forall (d : Dyadic), 
  exists (z : Z), z <> 0%Z /\ DisZ (ZtoD z *, d). 
Proof. intros.
       destruct d.
       - exists 1%Z; split; try lia.
         easy.
       - destruct z.
         + exists 1%Z; split; try lia. 
           easy.
         + exists 1%Z; split; try lia. 
           easy.
         + exists (DtoZ (Dn (Z.pos p) z0)); split; try lia.
           unfold DtoZ.
           apply twoadic_nonzero; lia.
           rewrite <- DtoZtoD; try easy.
           unfold ZtoD, Dmult.
           simpl.
           rewrite Z.pos_sub_diag; lia.
Qed.


Theorem one_sqrt2_Dbasis : forall (a b : Dyadic),
  (DtoC a) + (DtoC b) * √2 = 0 -> 
  (a = D0 /\ b = D0).
Proof. intros. 
       destruct (Dyadic_is_rational a) as [Na [Ha1 Ha2]].
       destruct (Dyadic_is_rational b) as [Nb [Hb1 Hb2]].
       apply (f_equal_gen (Cmult (Cmult Na Nb)) (Cmult (Cmult Na Nb))) in H; auto.
       replace (Na * Nb * (a + b * √ 2)) with 
         (Nb * (Na * a) + Na * (Nb * b) * √ 2) in H by lca.
       rewrite Cmult_0_r in H.
       do 2 rewrite <- ZtoDtoC_is_ZtoRtoC in H.
       do 4 rewrite <- DtoC_mult in H.
       rewrite (DtoZtoD (ZtoD Na *, a)) in H; auto.
       rewrite (DtoZtoD (ZtoD Nb *, b)) in H; auto.
       do 2 rewrite <- ZtoD_mult in H.
       do 2 rewrite ZtoDtoC_is_ZtoRtoC in H.
       apply one_sqrt2_Cbasis in H.
       destruct H.
       apply Z.mul_eq_0_r in H; auto.
       apply Z.mul_eq_0_r in H0; auto.
       apply (f_equal_gen ZtoD ZtoD) in H; auto.
       apply (f_equal_gen ZtoD ZtoD) in H0; auto.
       rewrite <- DtoZtoD in *; auto; simpl in *.
       apply Dmult_integral in H.
       apply Dmult_integral in H0.
       destruct H; rewrite <- ZtoD_0 in H. 
       apply ZtoD_inj in H; easy.
       destruct H0; rewrite <- ZtoD_0 in H0. 
       apply ZtoD_inj in H0; easy.
       split; subst; easy.
Qed.





Close Scope D_scope.
Open Scope Z_scope.

(* TODO: move to finite_group, or field *)
Inductive F2 :=
| F0
| F1.


Definition F2opp (x : F2) : F2 :=
  match x with
  | F0 => F0
  | F1 => F1
  end.

Definition F2plus (x y : F2) : F2 :=
  match (x, y) with
  | (F0, F0) => F0
  | (F0, F1) => F1
  | (F1, F0) => F1
  | (F1, F1) => F0
  end.

Definition F2mult (x y : F2) : F2 :=
  match (x, y) with
  | (F0, F0) => F0
  | (F0, F1) => F0
  | (F1, F0) => F0
  | (F1, F1) => F1
  end.

 

Global Program Instance F2_is_monoid : Monoid F2 := 
  { Gzero := F0
  ; Gplus := F2plus
  }.
Solve All Obligations with program_simpl; destruct g; try easy; destruct h; destruct i; easy. 

Global Program Instance F2_is_group : Group F2 :=
  { Gopp := F2opp }.
Solve All Obligations with program_simpl; destruct g; easy.

Global Program Instance F2_is_comm_group : Comm_Group F2.
Solve All Obligations with program_simpl; destruct a; destruct b; easy.
                                             
Global Program Instance F2_is_ring : Ring F2 :=
  { Gone := F1
  ; Gmult := F2mult
  }.
Solve All Obligations with program_simpl; destruct a; try easy.
Next Obligation.
  destruct a; destruct b; destruct c; try easy. 
Qed.
Next Obligation.
  destruct a; destruct b; destruct c; try easy. 
Qed.
Next Obligation.
  destruct a; destruct b; destruct c; try easy. 
Qed.
Next Obligation.
  destruct a; destruct b; try (left; easy); right; easy. 
Qed.


Global Program Instance F2_is_comm_ring : Comm_Ring F2.
Solve All Obligations with program_simpl; destruct a; destruct b; easy.

Global Program Instance F2_is_field : Field F2 :=
  { Ginv := F2opp }.
Next Obligation.
  destruct f; try easy.
Qed.


(* TODO: make Z a ring as well? *)



(* this is rho from the paper *)
Definition ZtoF2 (z : Z) : F2 :=
  match z with
  | Z0 => F0
  | Zpos p =>
      match p with
      | xI _ => F1
      | xO _ => F0
      | xH => F1
      end
  | Zneg p =>
      match p with
      | xI _ => F1
      | xO _ => F0
      | xH => F1
      end
  end.


Lemma ZtoF2_pos_is_neg : forall p, ZtoF2 (Zpos p) = ZtoF2 (Zneg p).
Proof. intros; easy. Qed. 

(* TODO: learn how to match on match's, so this can all be done with a short Ltac that
         destruct everything. Maybe use this: 
         https://stackoverflow.com/questions/28454977/how-to-match-a-match-expression *)
Lemma ZtoF2_plus : forall z1 z2, ZtoF2 (z1 + z2) = (ZtoF2 z1 + ZtoF2 z2)%G.
Proof. intros.
       replace Gplus with F2plus by easy.
       destruct z1; destruct z2; try easy;  
       destruct p; try easy; destruct p0; try easy; simpl.
       all : try (destruct (Z.pos_sub p p0); easy).
       all : try (destruct (Z.pos_sub p0 p); easy).
       all : try (destruct (Z.pos_sub p p0); try destruct p1; easy).
       all : try (destruct (Z.pos_sub p0 p); try destruct p1; easy).
       all : try (destruct p; easy).
       all : try (destruct p0; easy).
Qed.

Lemma ZtoF2_opp : forall z, ZtoF2 (- z)%Z = (- ZtoF2 z)%G.
Proof. intros.
       destruct z; try easy;
       destruct p; try easy; destruct p0; try easy; simpl.
Qed.

Lemma ZtoF2_mult : forall z1 z2, ZtoF2 (z1 * z2) = (ZtoF2 z1 * ZtoF2 z2)%G.
Proof. intros.
       replace Gmult with F2mult by easy.
       destruct z1; destruct z2; try easy;  
       destruct p; try easy; destruct p0; try easy; simpl.
Qed.


Lemma F2opp_id : forall p, F2opp p = p.
Proof. intros. destruct p; easy. Qed.


(* note how the representation of integers actually makes this really easy, easier
   than the nat version *)
Lemma ZtoF2_even : forall z,
  ZtoF2 z = F0 <-> exists y, 2 * y = z.
Proof. intros; split; intros.
       - destruct z.
         + exists 0; easy.
         + destruct p; try easy.
           exists (Z.pos p); easy.
         + destruct p; try easy.
           exists (Z.neg p); easy.
       - destruct H.
         rewrite <- H, ZtoF2_mult; simpl.
         destruct (ZtoF2 x); easy.
Qed.


Lemma ZtoF2_odd : forall z,
  ZtoF2 z = F1 <-> exists y, 2 * y + 1 = z.
Proof. intros; split; intros.
       - destruct z; try easy.
         + destruct p; try easy.
           exists (Z.pos p); easy.
           exists 0; easy.
         + destruct p; try easy.
           exists (Z.neg p - 1).
           rewrite Pos2Z.neg_xI, Z.mul_sub_distr_l. 
           unfold Z.sub.
           rewrite <- Z.add_assoc.
           apply f_equal; easy.
           exists (-1); easy.
       - destruct H.
         rewrite <- H, ZtoF2_plus, ZtoF2_mult; simpl.
         destruct (ZtoF2 x); easy. 
Qed.








(* NEXT STEP: introducing 4th ROU into the picture *)



Open Scope C_scope.



Definition Cz8 : C := Cexp (PI / 4).


Lemma Cz8_to_RR : Cz8 = (/ √2, / √2)%R. 
Proof. unfold Cz8. 
       rewrite Cexp_PI4.
       replace (/ √ 2) with ((/ √ 2)%R, 0%R).
       lca. 
       unfold RtoC, Cinv; simpl.
       apply injective_projections; simpl; try lra.
       rewrite Rmult_1_r, Rmult_0_l, Rplus_0_r.
       unfold Rdiv.
       rewrite Rinv_mult, <- Rmult_assoc, Rinv_r. lra.
       all: apply sqrt2_neq_0.
Qed.

      
(* TODO: make this better... *)
Lemma Cz8_4ROU : Cz8^8 = C1.
Proof. unfold Cz8.
       rewrite Cexp_pow, <- Cexp_2PI.
       unfold Rdiv.
       rewrite Rmult_assoc.
       replace (/ 4 * INR 8)%R with 2%R.
       rewrite Rmult_comm; easy.
       replace (INR 8) with 8%R.
       lra.
       unfold INR, IZR, IPR, IPR_2; lra.
Qed.

Lemma Cz8_pow2 : Cz8^2 = Ci.
Proof. unfold Cz8.
       rewrite Cexp_pow, <- Cexp_PI2.
       unfold Rdiv.
       rewrite Rmult_assoc.
       replace (/ 4 * INR 2)%R with (/2)%R.
       rewrite Rmult_comm; easy.
       replace (INR 2) with 2%R.
       lra.
       unfold INR, IZR, IPR, IPR_2; lra.
Qed.

Lemma Cz8_pow3 : Cz8^3 = -Cz8^*.
Proof. unfold Cz8.      
       rewrite Cexp_pow, Cexp_conj_neg, <- Cexp_plus_PI. 
       apply f_equal.
       replace (INR 3) with 3%R. 
       lra. 
       unfold INR, IZR, IPR, IPR_2; lra.
Qed.

Lemma Cz8_pow4 : Cz8^4 = -C1.
Proof. unfold Cz8.
       rewrite <- RtoC_opp, <- opp_IZR, Pos2Z.opp_pos, Cexp_pow, <- Cexp_PI.
       unfold Rdiv.
       rewrite Rmult_assoc.
       replace (/ 4 * INR 4)%R with (1)%R.
       rewrite Rmult_1_r; easy.
       replace (INR 4) with 4%R.
       lra.
       unfold INR, IZR, IPR, IPR_2; lra.
Qed.

Lemma Cz8_pow5 : Cz8^5 = -Cz8.
Proof. replace 5%nat with (4 + 1)%nat by easy.
       rewrite Cpow_add, Cz8_pow4. 
       lca.
Qed.       

Lemma Cz8_pow6 : Cz8^6 = -Cz8^2.
Proof. replace 6%nat with (4 + 2)%nat by easy.
       rewrite Cpow_add, Cz8_pow4. 
       lca.
Qed.       




Lemma Cz8_conj : Cz8 ^* = -Cz8^3.
Proof. unfold Cz8.
       rewrite Cexp_pow, Cexp_conj_neg, <- Cexp_minus_PI. 
       apply f_equal.
       replace (INR 3) with 3%R. 
       lra. 
       unfold INR, IZR, IPR, IPR_2; lra.
Qed.

Lemma Cz8_pow2_conj : (Cz8^2) ^* = -Cz8^2.
Proof. rewrite Cz8_pow2.
       lca.
Qed.

Lemma Cz8_pow3_conj : (Cz8^3) ^* = -Cz8.
Proof. rewrite Cz8_pow3, Cconj_opp, Cconj_involutive.
       easy.
Qed.       




Open Scope D_scope.


Definition D8 := (Dyadic * Dyadic * Dyadic * Dyadic)%type.


(* there are probably built in functions for this, but I could not find them *)
Notation "x .1" := (fst (fst (fst x))) (at level 0). 
Notation "x .2" := (snd (fst (fst x))) (at level 0). 
Notation "x .3" := (snd (fst x)) (at level 0). 
Notation "x .4" := (snd x) (at level 0). 



Definition D8toC (x : D8) : C :=
  x.1 + x.2 * Cz8 + x.3 * Cz8^2 + x.4 *Cz8^3.

Coercion D8toC : D8 >-> C.



(* TODO: figure out how to minimize repeated code, since this is the same as Z8 *)
Definition D8plus (x y : D8) : D8 :=
  (x.1 +, y.1, x.2 +, y.2, x.3 +, y.3, x.4 +, y.4).


Definition D8opp (x : D8) : D8 :=
  (-, x.1, -, x.2, -, x.3, -, x.4).


Definition D8mult (x y : D8) : D8 := 
  (x.1 *, y.1 -, x.2 *, y.4 -, x.3 *, y.3 -, x.4 *, y.2,
   x.1 *, y.2 +, x.2 *, y.1 -, x.3 *, y.4 -, x.4 *, y.3,
   x.1 *, y.3 +, x.2 *, y.2 +, x.3 *, y.1 -, x.4 *, y.4, 
   x.1 *, y.4 +, x.2 *, y.3 +, x.3 *, y.2 +, x.4 *, y.1).


Definition D80 := (D0, D0, D0, D0).
Definition D81 := (D1, D0, D0, D0).
Definition D82 := (D2, D0, D0, D0).
Definition D8half := (Dhalf, D0, D0, D0).



Fixpoint D8pow (z : D8) (n : nat) : D8 :=  
  match n with
  | 0%nat => D81
  | S n' => D8mult z (D8pow z n')
  end.


Lemma DtoC_fst : forall (a b c d : Dyadic),
  fst (a + b * Cz8 + c * Ci + d * - Cz8 ^*) = 
  (fst (DtoC a) + (fst (DtoC b) - fst (DtoC d)) * / √2)%R. 
Proof. intros.     
       rewrite Cz8_to_RR. 
       unfold Cconj, Copp; simpl.
       repeat rewrite Dyadic_real.
       lra.
Qed.

Lemma DtoC_snd : forall (a b c d : Dyadic),
  snd (a + b * Cz8 + c * Ci + d * - Cz8 ^*) = 
  (fst (DtoC c) + (fst (DtoC b) + fst (DtoC d)) * / √2)%R. 
Proof. intros.     
       rewrite Cz8_to_RR. 
       unfold Cconj, Copp; simpl.
       repeat rewrite Dyadic_real.
       lra.
Qed.


Lemma DtoCtoRtoC : forall d,
  RtoC (fst (DtoC d)) = DtoC d.
Proof. intros.
       unfold RtoC.
       apply c_proj_eq; auto; simpl.
       rewrite Dyadic_real; easy.
Qed.

   
(* this will be annoying. Must use irrationality of sqrt 2 or that Phi_4(x) is irred over Q *)
Lemma Cz8_is_basis : forall (a b c d : Dyadic),
  D8toC (a, b, c, d) = C0 -> 
  a = D0 /\ b = D0 /\ c = D0 /\ d = D0.
Proof. intros. 
       unfold D8toC in H.
       rewrite Cz8_pow2, Cz8_pow3 in H.
       simpl in H.
       assert (H0 := H). 
       apply (f_equal_gen fst fst) in H; auto.
       apply (f_equal_gen snd snd) in H0; auto.
       rewrite DtoC_fst in H; simpl in H.
       rewrite DtoC_snd in H0; simpl in H0.
       apply (f_equal_gen (Rmult (√ 2)) (Rmult (√ 2))) in H; auto.
       apply (f_equal_gen (Rmult (√ 2)) (Rmult (√ 2))) in H0; auto.
       rewrite Rmult_comm, Rmult_plus_distr_r, Rmult_assoc, Rinv_l,
         Rmult_0_r, Rmult_1_r, Rplus_comm in *; try apply sqrt2_neq_0.
       apply (f_equal_gen RtoC RtoC) in H; auto.
       apply (f_equal_gen RtoC RtoC) in H0; auto.
       autorewrite with RtoC_db in *.
       repeat rewrite DtoCtoRtoC in *.
       rewrite <- DtoC_minus in H.
       rewrite <- DtoC_plus in H0.
       apply one_sqrt2_Dbasis in H.
       apply one_sqrt2_Dbasis in H0.
       destruct H; destruct H0.
       apply (f_equal_gen (Dplus (b +, d)) (Dplus D0)) in H; try (apply f_equal; easy).
       replace (b +, d +, (b -, d)) with (D2 *, b) in H by lDa_try1.
       rewrite Dplus_0_l in H.
       apply Dmult_integral in H.
       destruct H; try easy.
       rewrite H, Dplus_0_l in H0.
       easy.
Qed.




Lemma D8toC_inj : forall (x y : D8),
  D8toC x = D8toC y -> x = y.
Proof.
  intros. 
  unfold D8toC in *. 
  destruct x; repeat destruct p; destruct y; repeat destruct p; simpl in *.
  apply Cminus_diag in H.
  replace (Cz8 * (Cz8 * (Cz8 * C1))) with (Cz8 ^ 3) in H by easy.  
  replace (Cz8 * (Cz8 * C1)) with (Cz8 ^ 2) in H by easy.    
  replace (d1 + d2 * Cz8 + d0 * Cz8 ^ 2 + d * Cz8 ^ 3 -
      (d5 + d6 * Cz8 + d4 * Cz8 ^ 2 + d3 * Cz8 ^ 3)) with
    ((d1 - d5) + (d2 - d6) * Cz8 + (d0 - d4) * Cz8 ^ 2 + (d - d3) * Cz8 ^ 3) in H by lca.
  assert (H' := Cz8_is_basis (d1 -, d5) (d2 -, d6) (d0 -, d4) (d -, d3)).
  unfold D8toC in H'; simpl in *.
  do 4 rewrite DtoC_minus in H'.
  apply H' in H.
  destruct H; destruct H0; destruct H1.
  repeat apply injective_projections; simpl; apply Dminus_eq_0; easy.
Qed.  




(* this is actually overkill because Z is decible, but shows usefulness of DtoC_inj *)
Lemma D8eq_dec (d1 d2 : D8) : { d1 = d2 } + { ~ (d1 = d2) }.
Proof.
  destruct (Ceq_dec (D8toC d1) (D8toC d2)).
  - apply D8toC_inj in e.
    left; easy.
  - right. 
    unfold not; intros; apply n. 
    rewrite H; easy. 
Qed.
    


(*TODO: make the order of these lemmas to be uniform. Perhaps compatability lemmas first, then 
everything else *)




Lemma D8toC_plus : forall d1 d2 : D8, D8toC (D8plus d1 d2) = D8toC d1 + D8toC d2.
Proof. intros.
       destruct d1; repeat destruct p; destruct d2; repeat destruct p.
       unfold D8toC, D8plus; simpl.  
       repeat rewrite DtoC_plus.
       lca.
Qed.


Lemma D8toC_opp : forall d : D8, D8toC (D8opp d) = - (D8toC d). 
Proof. intros.
       destruct d; repeat destruct p. 
       unfold D8toC, D8opp; simpl.
       repeat rewrite DtoC_opp.
       lca.
Qed.       


(* this is surprisingly easy! *)
Lemma D8toC_mult : forall d1 d2 : D8, D8toC (D8mult d1 d2) = D8toC d1 * D8toC d2.
Proof. intros.
       destruct d1; repeat destruct p; destruct d2; repeat destruct p.
       unfold D8toC, D8mult, Dminus; simpl.
       replace (Cz8 * (Cz8 * (Cz8 * C1))) with (Cz8 ^ 3) by easy.  
       replace (Cz8 * (Cz8 * C1)) with (Cz8 ^ 2) by easy.    
       replace (DtoC d1) with (DtoC d1 * (Cz8 ^ 0)) by lca. 
       replace (DtoC d5) with (DtoC d5 * (Cz8 ^ 0)) by lca. 
       replace (DtoC d3 * Cz8) with (DtoC d3 * (Cz8 ^ 1)) by lca. 
       replace (DtoC d6 * Cz8) with (DtoC d6 * (Cz8 ^ 1)) by lca.
       repeat rewrite Cmult_plus_distr_l.
       repeat rewrite Cmult_plus_distr_r.
       assert (H' : forall (d1 d2 : Dyadic) n1 n2, d1 * Cz8 ^ n1 * (d2 * Cz8 ^ n2) = 
                                   (Dmult d1 d2) * Cz8 ^ (n1 + n2)).
       { intros.
         replace (d7 * Cz8 ^ n1 * (d8 * Cz8 ^ n2)) with
           ((d7 * d8) * (Cz8 ^ n1 * Cz8 ^ n2)) by lca.
         rewrite DtoC_mult, Cpow_add. 
         easy. }
       do 16 rewrite H'.
       simpl plus.
       repeat rewrite DtoC_plus.
       repeat rewrite DtoC_opp. 
       rewrite Cz8_pow4, Cz8_pow5, Cz8_pow6.
       lca.
Qed.


#[global] Hint Rewrite D8toC_plus D8toC_opp D8toC_mult : D8toC_db.


(*TODO: show that the above proves defacto that D8 is a ring *)

Lemma D8toC_0 : D8toC D80 = C0.
Proof. lca. Qed.

Lemma D8toC_1 : D8toC D81 = C1.
Proof. lca. Qed.

Lemma D8toC_2 : D8toC D82 = C2.
Proof. lca. Qed.

Lemma D8toC_half : D8toC D8half = / C2.
Proof. lca. Qed.



(* TODO: look at all this repeated code! *) 
Lemma D8plus_comm : forall d1 d2, D8plus d1 d2 = D8plus d2 d1.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8plus_assoc : forall d1 d2 d3, D8plus d1 (D8plus d2 d3) = D8plus (D8plus d1 d2) d3.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8plus_0_l : forall d, D8plus D80 d = d.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8plus_0_r : forall d, D8plus d D80 = d.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_comm : forall d1 d2, D8mult d1 d2 = D8mult d2 d1.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_assoc : forall d1 d2 d3, D8mult d1 (D8mult d2 d3) = D8mult (D8mult d1 d2) d3.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.


Lemma D8mult_plus_distr_l : forall d1 d2 d3, 
    D8mult d1 (D8plus d2 d3) = D8plus (D8mult d1 d2) (D8mult d1 d3).
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_plus_distr_r : forall d1 d2 d3, 
    D8mult (D8plus d2 d3) d1 = D8plus (D8mult d2 d1) (D8mult d3 d1).
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_0_l : forall d, D8mult D80 d = D80.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_0_r : forall d, D8mult d D80 = D80.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_1_l : forall d, D8mult D81 d = d.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.

Lemma D8mult_1_r : forall d, D8mult d D81 = d.
Proof. intros.
       apply D8toC_inj.
       autorewrite with D8toC_db.
       lca.
Qed.
     

(* TODO: perhaps also coerce D into D8? *)
Lemma D8mult_d_l : forall (d d1 d2 d3 d4 : Dyadic), 
  D8mult (d, D0, D0, D0) (d1, d2, d3, d4) = (d *, d1, d *, d2, d *, d3, d *, d4).
Proof. intros. 
       repeat apply injective_projections; simpl. 
       all : repeat (try rewrite Dmult_0_r; try rewrite Dminus_0_r;
                     try rewrite Dplus_0_r; try rewrite Dplus_0_l); easy.
Qed. 


Lemma D8pow_add : forall (d : D8) (n m : nat), D8pow d (n + m) = D8mult (D8pow d n) (D8pow d m).
Proof. intros.
       induction n; simpl.
       - rewrite D8mult_1_l; easy.
       - rewrite IHn, D8mult_assoc; easy.
Qed.


Lemma D8pow_mult : forall (d : D8) (n m : nat), D8pow d (n * m) = D8pow (D8pow d n) m.
Proof. intros.
       induction m; simpl. 
       - replace (n * 0)%nat with 0%nat by lia. 
         easy.
       - simpl. 
         rewrite <- IHm, <- D8pow_add.
         apply f_equal_gen; auto.
         lia.
Qed.


(*TODO(again!): should probably define DtoD8 somewhere *)
Lemma DtoD8_pow : forall (d : Dyadic) (n : nat),
  D8pow (d, D0, D0, D0) n = (Dpow d n, D0, D0, D0).
Proof. intros.
       induction n; try easy; simpl. 
       rewrite IHn.
       rewrite D8mult_d_l, Dmult_0_r.
       easy.
Qed.


Lemma D8mult_2_half : D8mult D82 D8half = D81.
Proof. unfold D82, D8half.
       rewrite D8mult_d_l, Dmult_2_half, Dmult_0_r.
       easy.
Qed.       


Lemma D8mult_half_2 : D8mult D8half D82 = D81.
Proof. rewrite D8mult_comm.
       apply D8mult_2_half.
Qed.




Lemma D8_conj : forall (a b c d : Dyadic),
  Cconj (D8toC (a, b, c, d)) = D8toC (a, -,d, -,c, -,b).
Proof. intros.
       unfold D8toC; simpl fst; simpl snd.
       repeat rewrite Cconj_plus_distr.
       repeat rewrite Cconj_mult_distr.
       repeat rewrite Cconj_D.
       replace (a + b * Cz8 ^* + c * (Cz8 ^ 2) ^* + d * (Cz8 ^ 3) ^*) with
               (a + d * (Cz8 ^ 3) ^* + c * (Cz8 ^ 2) ^* + b * Cz8 ^*) by lca.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto. 
       - rewrite Cz8_pow3_conj.
         rewrite DtoC_opp.
         lca. 
       - rewrite Cz8_pow2_conj.
         rewrite DtoC_opp.
         lca. 
       - rewrite Cz8_conj.
         rewrite DtoC_opp.
         lca. 
Qed.




Ltac naive_lD8a := repeat (repeat rewrite D8mult_plus_distr_l;
                         repeat rewrite D8mult_plus_distr_r;
                         repeat rewrite D8mult_assoc;
                         repeat rewrite D8mult_1_l;
                         repeat rewrite D8mult_1_r; 
                         repeat rewrite D8mult_0_l;
                         repeat rewrite D8mult_0_r;
                         repeat rewrite D8plus_0_l;
                         repeat rewrite D8plus_0_r).


(* TODO: try using ring *)
Ltac lD8a_try1 := apply D8toC_inj; autorewrite with D8toC_db; lca.


Global Program Instance D8_is_monoid : Monoid D8 := 
  { Gzero := D80
  ; Gplus := D8plus
  }.
Solve All Obligations with program_simpl; lD8a_try1.

Global Program Instance D8_is_group : Group D8 :=
  { Gopp := D8opp }.
Solve All Obligations with program_simpl; lD8a_try1.
        
Global Program Instance D8_is_comm_group : Comm_Group D8.
Solve All Obligations with program_simpl; lD8a_try1.

                                             
Global Program Instance D8_is_ring : Ring D8 :=
  { Gone := D81
  ; Gmult := D8mult
  }.
Solve All Obligations with program_simpl; try lD8a_try1; apply D8eq_dec.

Global Program Instance D8_is_comm_ring : Comm_Ring D8.
Solve All Obligations with program_simpl; lD8a_try1.







Definition Z8 := (Z * Z * Z * Z)%type.

Definition Z8toD8 (z : Z8) : D8 :=
  (ZtoD z.1, ZtoD z.2, ZtoD z.3, ZtoD z.4).

Coercion Z8toD8 : Z8 >-> D8.


(* TODO: think of better names for these *)
Definition Z80 : Z8 := (0,0,0,0).

Definition Z81 : Z8 := (1,0,0,0).

Definition Z82 : Z8 := (2,0,0,0).

Definition Z8w : Z8 := (0,1,0,0).

Definition Z8i : Z8 := (0,0,1,0).


(* TODO: figure out how to minimize repeated code, since this should also be for D8 *)
Definition Z8plus (x y : Z8) : Z8 :=
  (x.1 + y.1, x.2 + y.2, x.3 + y.3, x.4 + y.4)%Z.

Definition Z8opp (x : Z8) : Z8 :=
  (- x.1, - x.2, - x.3, - x.4)%Z.

Definition Z8mult (x y : Z8) : Z8 :=
  (x.1 * y.1 - x.2 * y.4 - x.3 * y.3 - x.4 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.3 * y.4 - x.4 * y.3,
   x.1 * y.3 + x.2 * y.2 + x.3 * y.1 - x.4 * y.4,
   x.1 * y.4 + x.2 * y.3 + x.3 * y.2 + x.4 * y.1)%Z.


Fixpoint Z8pow (z : Z8) (n : nat) : Z8 :=  
  match n with
  | 0%nat => Z81%Z
  | S n' => Z8mult z (Z8pow z n')
  end.


(*TODO: this proof is horrible... *)
Lemma Z8toD8_inj : forall (x y : Z8),
  Z8toD8 x = Z8toD8 y -> x = y.
Proof. intros. 
       repeat apply injective_projections; simpl in *.
       assert (H1 : (Z8toD8 x).1 = (Z8toD8 y).1). rewrite H; easy.
       unfold Z8toD8 in *; simpl in *.
       apply ZtoD_inj; rewrite H1; easy. 
       assert (H2 : (Z8toD8 x).2 = (Z8toD8 y).2). rewrite H; easy.
       unfold Z8toD8 in *; simpl in *.
       apply ZtoD_inj; rewrite H2; easy.  
       assert (H3 : (Z8toD8 x).3 = (Z8toD8 y).3). rewrite H; easy.
       unfold Z8toD8 in *; simpl in *.
       apply ZtoD_inj; rewrite H3; easy. 
       assert (H4 : (Z8toD8 x).4 = (Z8toD8 y).4). rewrite H; easy.
       unfold Z8toD8 in *; simpl in *.
       apply ZtoD_inj; rewrite H4; easy. 
Qed.


Lemma Z8toD8_plus : forall (z1 z2 : Z8),
  Z8toD8 (Z8plus z1 z2) = D8plus z1 z2.
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold D8plus, Z8plus, Z8toD8; simpl.
       repeat rewrite ZtoD_plus.
       easy. 
Qed.


Lemma Z8toD8_opp : forall (z : Z8),
  Z8toD8 (Z8opp z) = D8opp z.
Proof. intros. 
       destruct z; repeat destruct p.
       unfold D8opp, Z8opp, Z8toD8; simpl.
       repeat rewrite ZtoD_opp.
       easy. 
Qed.

Lemma Z8toD8_mult : forall (z1 z2 : Z8),
  Z8toD8 (Z8mult z1 z2) = D8mult z1 z2.
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold D8mult, Z8mult, Z8toD8; simpl.
       repeat rewrite ZtoD_plus.
       repeat rewrite ZtoD_minus.
       repeat rewrite ZtoD_mult.
       repeat rewrite ZtoD_plus.
       repeat rewrite ZtoD_mult.
       easy. 
Qed.



(* some basic lemmas *)

Lemma Z8toD8_0 : Z8toD8 Z80 = D80.
Proof. easy. Qed.

Lemma Z8toD8_1 : Z8toD8 Z81 = D81.
Proof. easy. Qed.

Lemma Z8toD8_2 : Z8toD8 Z82 = D82.
Proof. easy. Qed.

Lemma Z8toC_w : D8toC (Z8toD8 Z8w) = Cz8.
Proof. unfold D8toC, Z8toD8; simpl.
       rewrite Zdiv.Zdiv_0_l.
       lca.
Qed.  

Lemma Z8toC_i : D8toC (Z8toD8 Z8i) = Ci.
Proof. unfold D8toC, Z8toD8; simpl. 
       rewrite Zdiv.Zdiv_0_l.
       replace (Cz8 * (Cz8 * C1)) with (Cz8 ^ 2) by lca.
       rewrite Cz8_pow2.
       lca.
Qed.  


(* TODO: make tactic that inputs Z8toD8, etc... and that makes these all trivial *)
Lemma Z8plus_comm : forall (z1 z2 : Z8), Z8plus z1 z2 = Z8plus z2 z1.
Proof. intros.
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8plus; simpl.  
       repeat apply injective_projections; simpl; lia.
Qed.       

Lemma Z8plus_assoc : forall (z1 z2 z3 : Z8), Z8plus z1 (Z8plus z2 z3) = Z8plus (Z8plus z1 z2) z3.
Proof. intros.
       destruct z1; repeat destruct p; destruct z2; 
         repeat destruct p; destruct z3; repeat destruct p.
       unfold Z8plus; simpl.  
       repeat apply injective_projections; simpl; lia.
Qed.   

Lemma Z8mult_comm : forall (z1 z2 : Z8), Z8mult z1 z2 = Z8mult z2 z1.
Proof. intros.
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8mult; simpl.   
       repeat apply injective_projections; simpl; lia.
Qed.       

Lemma Z8mult_assoc : forall (z1 z2 z3 : Z8), Z8mult z1 (Z8mult z2 z3) = Z8mult (Z8mult z1 z2) z3.
Proof. intros.
       destruct z1; repeat destruct p; destruct z2; 
         repeat destruct p; destruct z3; repeat destruct p.
       unfold Z8mult; simpl.  
       repeat apply injective_projections; simpl; lia.
Qed.   



Lemma Z8mult_1_l : forall z, Z8mult Z81 z = z.
Proof. intros. 
       destruct z; repeat destruct p.
       unfold Z8mult; simpl.
       destruct z; destruct z0; destruct z1; destruct z2;
       repeat apply injective_projections; simpl; easy.
Qed.

Lemma Z8mult_1_r : forall z, Z8mult z Z81 = z.
Proof. intros.  
       destruct z; repeat destruct p.
       unfold Z8mult; simpl.
       repeat apply injective_projections; simpl; lia.
Qed.


Lemma Z8mult_cancel_l : forall z1 z2 z3, 
    z1 <> Z80 -> 
    Z8mult z1 z2 = Z8mult z1 z3 -> z2 = z3.
Proof. intros. 
       apply Z8toD8_inj; apply D8toC_inj.
       apply (Cmult_cancel_l (D8toC (Z8toD8 z1))).
       unfold not; intros; apply H.
       apply Z8toD8_inj; apply D8toC_inj.
       rewrite H1, Z8toD8_0, D8toC_0; easy.
       do 2 rewrite <- D8toC_mult, <- Z8toD8_mult.
       rewrite H0; easy. 
Qed. 


(* TODO: perhaps also coerce Z into Z8? *)
Lemma Z8mult_z_l : forall (z : Z) (z1 : Z8), 
  Z8mult (z, 0, 0, 0)%Z z1 = (z * z1.1, z * z1.2, z * z1.3, z * z1.4)%Z.
Proof. intros. 
       destruct z1; repeat destruct p; simpl.
       repeat apply injective_projections; simpl; lia.
Qed. 

Lemma Z8mult_neg1 : forall z,
  Z8mult (Z8opp Z81) z = Z8opp z.
Proof. intros. 
       replace (Z8opp Z81) with (-1,0,0,0)%Z by easy.
       destruct z; repeat destruct p.
       rewrite Z8mult_z_l.
       easy. 
Qed.

Lemma Z8mult_w_l : forall z,
  Z8mult Z8w z = (- z.4, z.1, z.2, z.3)%Z.      
Proof. intros.
       destruct z; repeat destruct p; simpl.
       repeat apply injective_projections; simpl; try lia.
       destruct z; destruct z0; destruct z1; destruct z2; try lia.
       destruct z1; lia.
       destruct z2; lia.
       destruct z0; lia.
Qed.


(* Some pow lemmas *)

Lemma Z8toC_pow : forall (z : Z8) (n : nat), (z ^ n)%C = (Z8pow z n).
Proof. intros.
       induction n.
       - simpl; rewrite Z8toD8_1, D8toC_1. 
         easy. 
       - simpl.
         rewrite IHn, Z8toD8_mult, D8toC_mult.
         easy. 
Qed.

Lemma Z8pow_add : forall (z : Z8) (n m : nat), Z8pow z (n + m) = Z8mult (Z8pow z n) (Z8pow z m).
Proof. intros. 
       induction n.
       - simpl. 
         rewrite Z8mult_1_l; easy.
       - simpl.
         rewrite IHn. 
         rewrite <- Z8mult_assoc.
         easy.
Qed.


Lemma Z8pow_mult : forall (z : Z8) (n m : nat), Z8pow z (n * m) = Z8pow (Z8pow z n) m.
Proof.
  intros. induction m. rewrite Nat.mul_0_r. easy.
  replace (n * (S m))%nat with (n * m + n)%nat by lia.
  simpl. rewrite Z8pow_add. rewrite IHm. 
  rewrite Z8mult_comm. easy. 
Qed.



(** Coercion of D8 back to Z8 *)


Definition D8toZ8 (d : D8) : Z8 :=
  (DtoZ d.1, DtoZ d.2, DtoZ d.3, DtoZ d.4).


Definition D8isZ8 (d : D8) : Prop := 
  DisZ d.1 /\ DisZ d.2 /\ DisZ d.3 /\ DisZ d.4.
  


Lemma D8isZ8_plus : forall (d1 d2 : D8),
  D8isZ8 d1 -> D8isZ8 d2 ->
  D8isZ8 (D8plus d1 d2).
Proof. intros.
       destruct d1; repeat destruct p; destruct d2; repeat destruct p.
       destruct H; destruct H0; destruct H1; destruct H2; destruct H3; destruct H4.
       unfold D8plus; repeat split; simpl in *.
       all : apply DisZ_plus; easy.
Qed.

Lemma D8isZ8_opp : forall (d : D8),
  D8isZ8 d -> D8isZ8 (D8opp d).
Proof. intros.
       destruct d; repeat destruct p.
       destruct H; destruct H0; destruct H1.
       unfold D8opp; repeat split; simpl in *.
       all : apply DisZ_opp; easy.
Qed.



Lemma D8isZ8_mult : forall (d1 d2 : D8),
  D8isZ8 d1 -> D8isZ8 d2 ->
  D8isZ8 (D8mult d1 d2).
Proof. intros.
       destruct d1; repeat destruct p; destruct d2; repeat destruct p.
       destruct H; destruct H0; destruct H1; destruct H2; destruct H3; destruct H4.
       unfold D8mult; repeat split; simpl in *.
       all : repeat (try apply DisZ_plus; try apply DisZ_minus;
                    try apply DisZ_opp; try apply DisZ_mult); easy.
Qed.


Lemma D8isZ8_pow : forall (d : D8) (n : nat),
  D8isZ8 d -> D8isZ8 (D8pow d n).
Proof. intros.
       induction n; try easy.
       simpl.
       apply D8isZ8_mult; easy. 
Qed.



Lemma D8isZ8_dec : forall d : D8,
  { D8isZ8 d } + { ~ D8isZ8 d }.
Proof. intros. 
       destruct d; repeat destruct p.
       unfold D8isZ8; simpl.
       destruct (DisZ_dec d); destruct (DisZ_dec d0);
         destruct (DisZ_dec d1); destruct (DisZ_dec d2); 
         try (left; easy); right; easy.
Qed.



Lemma D8toZ8toD8 : forall (d : D8), 
  D8isZ8 d -> d = Z8toD8 (D8toZ8 d).
Proof. intros. 
       destruct d; repeat destruct p.
       destruct H; destruct H0; destruct H1.
       repeat apply injective_projections; simpl in *.
       all : rewrite <- DtoZtoD; easy.
Qed.

Lemma Z8toD8toZ8 : forall (z : Z8),
  z = D8toZ8 (Z8toD8 z).
Proof. intros.
       destruct z; repeat destruct p. 
       repeat apply injective_projections; simpl. 
       all : rewrite <- ZtoDtoZ; easy. 
Qed.       


Lemma D8isZ8_ver : forall (d : D8), (exists (z : Z8), d = Z8toD8 z) -> D8isZ8 d.
Proof. intros. 
       destruct H; subst. 
       destruct x; repeat destruct p.
       unfold D8isZ8, Z8toD8; simpl.
       repeat split. 
       all : apply DisZ_ver. 
       exists z1; easy.
       exists z2; easy. 
       exists z0; easy. 
       exists z; easy. 
Qed.
       
  

(* Note repeated code to DtoZ_plus! TODO: generalize *)
Lemma D8toZ8_plus : forall (d1 d2 : D8),
  D8isZ8 d1 -> D8isZ8 d2 -> 
  D8toZ8 (D8plus d1 d2) = (Z8plus (D8toZ8 d1) (D8toZ8 d2)).
Proof. intros.
       apply Z8toD8_inj.
       rewrite Z8toD8_plus.
       do 3 (try rewrite <- D8toZ8toD8; auto).
       apply D8isZ8_plus; easy.
Qed.


Lemma D8toZ8_mult : forall (d1 d2 : D8),
  D8isZ8 d1 -> D8isZ8 d2 -> 
  D8toZ8 (D8mult d1 d2) = Z8mult (D8toZ8 d1) (D8toZ8 d2).
Proof. intros.
       apply Z8toD8_inj.
       rewrite Z8toD8_mult.
       do 3 (try rewrite <- D8toZ8toD8; auto).
       apply D8isZ8_mult; easy.
Qed.


Lemma D8isZ8_0 : D8isZ8 D80.
Proof. easy. Qed.

Lemma D8isZ8_1 : D8isZ8 D81.
Proof. easy. Qed.

Lemma D8isZ8_2 : D8isZ8 D82.
Proof. easy. Qed.


Lemma D8toZ8_0 : D8toZ8 D80 = Z80.
Proof. easy. Qed.

Lemma D8toZ8_1 : D8toZ8 D81 = Z81.
Proof. easy. Qed.

Lemma D8toZ8_2 : D8toZ8 D82 = Z82.
Proof. easy. Qed.




(** some root2 and root2_recip defs and lemmas *)

Definition root2 : Z8 := (0, 1, 0, -1)%Z.

Definition root2_recip : D8 := (D0, Dhalf, D0, -,Dhalf).


Lemma root2_sqr : Z8mult root2 root2 = Z82.
Proof. easy. Qed. 


Lemma root2_root2_recip : D8mult root2_recip root2 = D81.
Proof. repeat apply injective_projections; simpl; easy. Qed.


Lemma root2_recip_proper : root2_recip = D8mult D8half root2.
Proof. repeat apply injective_projections; simpl; try easy. Qed.

(* TODO: make this proof nice *)
Lemma Z8toC_root2 : D8toC (Z8toD8 root2) = RtoC (√ 2). 
Proof. unfold root2, Z8toD8, D8toC; simpl fst; simpl snd.
       replace (DtoC (Dn 0 (0 / 2))) with C1.
       replace (DtoC (Dn 0 (-2 / 2))) with (-C1).
       replace (D0 + C1 * Cz8 + D0 * Cz8 ^ 2 + - C1 * Cz8 ^ 3) with (Cz8 - Cz8^3) by lca.
       unfold Cz8; rewrite Cexp_pow.
       replace (PI / 4 * INR 3)%R with (3 * PI / 4)%R.
       rewrite Cexp_PI4, Cexp_3PI4.
       replace (/ √ 2 + / √ 2 * Ci - (- / √ 2 + / √ 2 * Ci)) with (2 / √ 2) by lca.
       rewrite <- Csqrt2_sqrt.
       unfold Cdiv. 
       rewrite <- Cmult_assoc, Cinv_r; try lca.
       apply Csqrt2_neq_0.
       replace (INR 3) with (IZR 3). lra.
       unfold INR, IZR, IPR, IPR_2; lra. 
       unfold DtoC, Z.div, Z.div_eucl, Z.pos_div_eucl; lca. 
       rewrite Zdiv.Zdiv_0_l. 
       lca.
Qed.


Lemma Z8root2_neq_0 : root2 <> Z80.
Proof. assert (H : RtoC (√ 2) <> C0).
       { apply RtoC_neq; apply sqrt2_neq_0. }
       unfold not; intros; apply H.
       rewrite <- Z8toC_root2, H0, Z8toD8_0, D8toC_0; easy.
Qed.

(* note how we use all the tools we have developted to show this indirectly *)
Lemma root2_recip_ver : D8toC root2_recip = / RtoC (√ 2).
Proof. rewrite root2_recip_proper, Cinv_sqrt2_proper.
       unfold Cdiv. 
       rewrite Cmult_comm, D8toC_mult.
       apply f_equal_gen; try apply f_equal.
       rewrite D8toC_half; easy.
       rewrite Z8toC_root2; easy.
Qed. 




(** some more defs and lemmas about norm *)


(* a more adhoc conjugation *)
Definition Z8conj (z : Z8) : Z8 :=
  (z.1, -z.4, -z.3, -z.2)%Z.


(* could define Z[√2] as domain here, but defining Z[√2] would be annoying. 
   TODO: doing this well could be cool *)
Definition Z8norm (z : Z8) : Z8 := 
  Z8mult (Z8conj z) z.
  

Definition Z8weight (z : Z8) : Z :=
  z.1*z.1 + z.2*z.2 + z.3*z.3 + z.4*z.4.


Lemma Z8conj_ver : forall (z : Z8),
  Cconj z = Z8conj z.
Proof. intros.
       destruct z; repeat destruct p. 
       unfold Z8toD8; simpl. 
       rewrite D8_conj.
       do 3 rewrite ZtoD_opp.
       easy. 
Qed.       
      
Lemma Z8conj_mult : forall (z1 z2 : Z8),
  Z8conj (Z8mult z1 z2) = Z8mult (Z8conj z1) (Z8conj z2).
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8conj, Z8mult; simpl.
       repeat apply injective_projections; simpl; lia.
Qed.


Lemma Z8norm_weight : forall (z : Z8), 
  Z8norm z = (Z8weight z,
               z.1*z.2 + z.2*z.3 + z.3*z.4 - z.4*z.1,
               0,
               (z.1*z.2 + z.2*z.3 + z.3*z.4 - z.4*z.1) * (-1))%Z.
Proof. intros. 
       unfold Z8norm, Z8weight, Z8conj, Z8mult;
       destruct z; repeat destruct p; simpl.
       repeat apply injective_projections; simpl; lia. 
Qed.






Definition F28 := (F2 * F2 * F2 * F2)%type.



Definition Z8toF28 (z : Z8) : F28 :=
  (ZtoF2 z.1, ZtoF2 z.2, ZtoF2 z.3, ZtoF2 z.4).

Definition F28opp (x : F28) : F28 :=
  (- x.1, -x.2, -x.3, -x.4)%G.

Definition F28plus (x y : F28) : F28 :=
  (x.1 + y.1, x.2 + y.2, x.3 + y.3, x.4 + y.4)%G.

(* note that -x = x for x ∈ F2, so we can use plus here *)
Definition F28mult (x y : F28) : F28 :=
  (x.1 * y.1 + x.2 * y.4 + x.3 * y.3 + x.4 * y.2,
   x.1 * y.2 + x.2 * y.1 + x.3 * y.4 + x.4 * y.3,
   x.1 * y.3 + x.2 * y.2 + x.3 * y.1 + x.4 * y.4,
   x.1 * y.4 + x.2 * y.3 + x.3 * y.2 + x.4 * y.1)%G.

(* nonetheless, having this is also helpful to show the mults are the same accross the rings *)
Definition F28mult' (x y : F28) : F28 :=
  (x.1 * y.1 - x.2 * y.4 - x.3 * y.3 - x.4 * y.2,
   x.1 * y.2 + x.2 * y.1 - x.3 * y.4 - x.4 * y.3,
   x.1 * y.3 + x.2 * y.2 + x.3 * y.1 - x.4 * y.4,
   x.1 * y.4 + x.2 * y.3 + x.3 * y.2 + x.4 * y.1)%G.


Lemma F28mult_eqiv : forall p p0, F28mult p p0 = F28mult' p p0.
Proof. intros.   
       repeat (destruct p; destruct p0); simpl. 
       destruct f; destruct f0; destruct f1; destruct f2; 
         destruct f3; destruct f4; destruct f5; destruct f6; easy. 
Qed.



Lemma F28eq_dec : forall (p p0 : F28), { p = p0 } + { p <> p0 }. 
Proof. intros. 
       repeat (destruct p; destruct p0); simpl. 
       destruct f; destruct f0; destruct f1; destruct f2; 
         destruct f3; destruct f4; destruct f5; destruct f6;
         try (left; easy); right; easy. 
Qed.



Lemma F28_double : forall (p p0 : F28), p = p0 -> F28plus p p0 = (F0, F0, F0, F0).
Proof. intros; subst.
       destruct p0; repeat destruct p.
       destruct f; destruct f0; destruct f1; destruct f2; try easy.
Qed.


(* could make this a ring, but I wont for now *)
(* also, could do this in a less bashy way. Wont generalize well for the version over Z *)
Lemma F28plus_comm : forall p p0, F28plus p p0 = F28plus p0 p.
Proof. intros.   
       repeat (destruct p; destruct p0); simpl. 
       destruct f; destruct f0; destruct f1; destruct f2; 
         destruct f3; destruct f4; destruct f5; destruct f6; easy. 
Qed. 

Lemma F28mult_comm : forall p p0, F28mult p p0 = F28mult p0 p.
Proof. intros.   
       repeat (destruct p; destruct p0); simpl. 
       destruct f; destruct f0; destruct f1; destruct f2; 
         destruct f3; destruct f4; destruct f5; destruct f6; easy. 
Qed.


Lemma Z8toF28_plus : forall p p0, 
  Z8toF28 (Z8plus p p0) = F28plus (Z8toF28 p) (Z8toF28 p0).
Proof. intros. 
       repeat (destruct p; destruct p0); simpl. 
       unfold Z8plus, F28plus; simpl.
       repeat rewrite <- ZtoF2_plus.
       easy.
Qed.


Lemma Z8toF28_opp : forall p, 
  Z8toF28 (Z8opp p) = F28opp (Z8toF28 p). 
Proof. intros. 
       repeat (destruct p); simpl. 
       unfold Z8toF28, Z8opp; simpl.
       repeat rewrite ZtoF2_opp.
       easy.
Qed.

                
Lemma Z8toF28_mult : forall p p0, 
  Z8toF28 (Z8mult p p0) = F28mult (Z8toF28 p) (Z8toF28 p0).
Proof. intros.  
       rewrite F28mult_eqiv.
       repeat (destruct p; destruct p0); simpl. 
       unfold Z8mult, F28mult'; simpl. 
       repeat rewrite <- ZtoF2_mult.
       repeat rewrite <- ZtoF2_opp.
       repeat rewrite <- ZtoF2_plus.
       unfold Z8toF28; simpl.
       easy. 
Qed.


Lemma F28opp_id : forall p, F28opp p = p.
Proof. intros. 
       repeat destruct p.
       unfold F28opp; simpl. 
       repeat rewrite F2opp_id. 
       easy. 
Qed.


(* helpful for some lemmas about Z8conj *)
Definition F28conj (z : F28) : F28 :=
  (z.1, -z.4, -z.3, -z.2)%G.


(* helpful for some lemmas about multiplication by w *)
Definition F28cycle (z : F28) : F28 :=
  (z.4, z.1, z.2, z.3)%G. 



Lemma Z8conj_F28conj : forall z, Z8toF28 (Z8conj z) = F28conj (Z8toF28 z).
Proof. intros. 
       unfold Z8toF28, Z8conj, F28conj. 
       destruct z; repeat destruct p; simpl.
       do 3 rewrite ZtoF2_opp.
       easy.
Qed.


Lemma Z8mult_w_l_F28cycle : forall z, Z8toF28 (Z8mult Z8w z) = F28cycle (Z8toF28 z).
Proof. intros. 
       rewrite Z8mult_w_l.
       unfold Z8toF28, F28cycle.
       destruct z; repeat destruct p; simpl.
       repeat apply injective_projections; auto; simpl.
       destruct z; try easy.
Qed.




(* creating a map that describes the effect of multiplication by root2 *)
(* note that the order I use differs from the paper, may want to change this... *)
Definition mult_by_root2 (x : F28) : F28 :=
  match x with
  | (F0, F0, F0, F0) => (F0, F0, F0, F0)
  | (F0, F0, F0, F1) => (F1, F0, F1, F0)
  | (F0, F0, F1, F0) => (F0, F1, F0, F1)
  | (F0, F0, F1, F1) => (F1, F1, F1, F1)
  | (F0, F1, F0, F0) => (F1, F0, F1, F0)
  | (F0, F1, F0, F1) => (F0, F0, F0, F0)
  | (F0, F1, F1, F0) => (F1, F1, F1, F1)
  | (F0, F1, F1, F1) => (F0, F1, F0, F1)
  | (F1, F0, F0, F0) => (F0, F1, F0, F1)
  | (F1, F0, F0, F1) => (F1, F1, F1, F1)
  | (F1, F0, F1, F0) => (F0, F0, F0, F0)
  | (F1, F0, F1, F1) => (F1, F0, F1, F0)
  | (F1, F1, F0, F0) => (F1, F1, F1, F1)
  | (F1, F1, F0, F1) => (F0, F1, F0, F1)
  | (F1, F1, F1, F0) => (F1, F0, F1, F0)
  | (F1, F1, F1, F1) => (F0, F0, F0, F0)
  end. 




Lemma mult_by_root2_ver : forall (z : Z8),
  mult_by_root2 (Z8toF28 z) = Z8toF28 (Z8mult root2 z).
Proof. intros.
       rewrite Z8toF28_mult.
       destruct (Z8toF28 z) as [p p0].
       repeat destruct p.
       unfold F28mult, root2, Z8toF28; simpl.
       destruct f0; destruct f1; destruct f; destruct p0; easy.
Qed.


(* creating a map that describes the effect of taking the squared norm *)
Definition square_norm (x : F28) : F28 :=
  match x with
  | (F0, F0, F0, F0) => (F0, F0, F0, F0)
  | (F0, F0, F0, F1) => (F1, F0, F0, F0)
  | (F0, F0, F1, F0) => (F1, F0, F0, F0)
  | (F0, F0, F1, F1) => (F0, F1, F0, F1)
  | (F0, F1, F0, F0) => (F1, F0, F0, F0)
  | (F0, F1, F0, F1) => (F0, F0, F0, F0)
  | (F0, F1, F1, F0) => (F0, F1, F0, F1)
  | (F0, F1, F1, F1) => (F1, F0, F0, F0)
  | (F1, F0, F0, F0) => (F1, F0, F0, F0)
  | (F1, F0, F0, F1) => (F0, F1, F0, F1)
  | (F1, F0, F1, F0) => (F0, F0, F0, F0)
  | (F1, F0, F1, F1) => (F1, F0, F0, F0)
  | (F1, F1, F0, F0) => (F0, F1, F0, F1)
  | (F1, F1, F0, F1) => (F1, F0, F0, F0)
  | (F1, F1, F1, F0) => (F1, F0, F0, F0)
  | (F1, F1, F1, F1) => (F0, F0, F0, F0)
  end. 




Lemma square_norm_ver : forall (z : Z8),
  square_norm (Z8toF28 z) = Z8toF28 (Z8mult (Z8conj z) z).
Proof. intros.
       rewrite Z8toF28_mult.
       rewrite Z8conj_F28conj.
       destruct (Z8toF28 z) as [p p0].
       repeat destruct p.
       unfold F28mult, F28conj, Z8toF28; simpl.
       destruct f0; destruct f1; destruct f; destruct p0; easy.
Qed.

(* 
 *
 *
 *)



Open Scope D_scope.



(* TODO: could move everything that follows to a new file *)
Definition denom_exp (t : D8) (k : nat) : Prop :=
  D8isZ8 (D8mult (D8pow root2 k) t). 

Definition least_denom_exp (t : D8) (k : nat) : Prop :=
  denom_exp t k /\ forall k', denom_exp t k' -> (k <= k')%nat.




(*
 * some helpers to show that there always exists a denom_exp: 
 *)


Lemma exists_two_bound_Dyad : forall (d : Dyadic), 
  exists k, DisZ (D2 ^, k *, d).
Proof. intros. 
       destruct d.
       - exists 0%nat.
         rewrite Dmult_0_r.
         easy.
       - destruct z.
         + exists 0%nat; simpl; easy.
         + exists 0%nat; simpl; easy.
         + exists (Pos.to_nat p).
           rewrite Dpow_2_pos; simpl. 
           rewrite Z.pos_sub_diag. 
           lia.
Qed.

Lemma get_weaker_two_bound : forall (d : Dyadic) (k k' : nat),
  (k <= k')%nat -> 
  DisZ (D2 ^, k *, d) -> DisZ (D2 ^, k' *, d). 
Proof. intros.
       apply (Nat.sub_add k k') in H; rewrite Nat.add_comm in H; auto.
       rewrite <- H, Dpow_add, Dmult_comm, Dmult_assoc. 
       apply DisZ_mult.
       rewrite Dmult_comm; easy.
       apply DisZ_pow.
       easy.
Qed.       


Lemma get_weaker_denom_exp : forall (d : D8) (k k' : nat),
  (k <= k')%nat -> 
  denom_exp d k -> denom_exp d k'.
Proof. intros. 
       unfold denom_exp.
       apply (Nat.sub_add k k') in H; rewrite Nat.add_comm in H; auto.
       rewrite <- H, D8pow_add, D8mult_comm, D8mult_assoc. 
       apply D8isZ8_mult.
       rewrite D8mult_comm; easy.
       apply D8isZ8_pow.
       easy.
Qed.       


Lemma exists_two_bound_D8 : forall (d : D8), 
  exists k, D8isZ8 (D8mult (D8pow D82 k) d). 
Proof. intros. 
       destruct d; repeat destruct p.
       destruct (exists_two_bound_Dyad d); destruct (exists_two_bound_Dyad d0);
       destruct (exists_two_bound_Dyad d1); destruct (exists_two_bound_Dyad d2).
       exists (x + x0 + x1 + x2)%nat.
       unfold D82.
       rewrite DtoD8_pow, D8mult_d_l.
       repeat split; simpl.
       apply (get_weaker_two_bound _ x1); try lia; easy.
       apply (get_weaker_two_bound _ x2); try lia; easy.
       apply (get_weaker_two_bound _ x0); try lia; easy.
       apply (get_weaker_two_bound _ x); try lia; easy.
Qed.



Theorem exists_denom_exp : forall d,
  exists k, denom_exp d k.
Proof. intros.
       destruct (exists_two_bound_D8 d).
       exists (2*x)%nat. 
       unfold denom_exp.
       rewrite D8pow_mult.
       replace (D8pow root2 2) with D82; easy.
Qed. 



Lemma denom_exp_dec : forall t k, 
  { denom_exp t k } + { ~ denom_exp t k }.
Proof. intros. 
       unfold denom_exp.
       apply D8isZ8_dec.
Qed.


Corollary exists_least_denom_exp : forall t,
  exists k, least_denom_exp t k.
Proof. intros.
       assert (H' := exists_denom_exp t).
       apply (dec_inh_nat_subset_has_unique_least_element (denom_exp t)) in H'.
       destruct H'; do 2 destruct H. 
       exists x; split; auto.
       intros.  
       destruct (denom_exp_dec t n).
       left; easy.
       right; easy.
Qed.

Corollary least_denom_exp_dec : forall t k,
  { least_denom_exp t k } + { ~ least_denom_exp t k }.
Proof. intros. 
       destruct (denom_exp_dec t k).
       - destruct k.
         left; split; intros; auto; lia.
         destruct (denom_exp_dec t k).
         + right.
           unfold not; intros. 
           destruct H.
           apply H0 in d0; lia.
         + left.
           split; auto; intros. 
           bdestruct (k' <=? k)%nat; try lia.
           apply (get_weaker_denom_exp t k' k) in H0; auto.
           easy. 
       - right.  
         unfold not; intros; apply n.
         apply H.
Qed.


Lemma denom_exp_plus : forall (d1 d2 : D8) (a : nat),
  denom_exp d1 a -> denom_exp d2 a -> 
  denom_exp (D8plus d1 d2) a.
Proof. intros.
       unfold denom_exp in *.
       rewrite D8mult_plus_distr_l.
       apply D8isZ8_plus; easy. 
Qed.

Lemma denom_exp_mult : forall (d1 d2 : D8) (a b : nat),
  denom_exp d1 a -> denom_exp d2 b -> 
  denom_exp (D8mult d1 d2) (a + b).
Proof. intros.
       unfold denom_exp in *.
       rewrite D8pow_add, <- D8mult_assoc, (D8mult_assoc _ d1), (D8mult_comm _ d1),
         <- D8mult_assoc, (D8mult_assoc _ d1).
       apply D8isZ8_mult; easy.
Qed.

Lemma denom_exp_reduce : forall (d : D8) (k : nat),
  denom_exp (D8mult root2 d) k <->
  denom_exp d (S k).
Proof. intros; split; intros; unfold denom_exp in *; simpl in *. 
       - rewrite (D8mult_comm root2), <- D8mult_assoc.
         easy.
       - rewrite D8mult_assoc, (D8mult_comm _ root2).
         easy.
Qed.



(* we assume denom_exp t k before we hit t with rho k *)
(* note that rho k = rho_k from paper, not to confuse this function with rho *)
(* TODO: since there are so many notions, it would be helpful to reorganize *)
Definition rho (k : nat) (t : D8)  : Z8 :=
  D8toZ8 (D8mult (D8pow root2 k) t).
 

Lemma rho_plus : forall (d1 d2 : D8) (k : nat),
  denom_exp d1 k ->
  denom_exp d2 k ->
  rho k (D8plus d1 d2) = Z8plus (rho k d1) (rho k d2).
Proof. intros. 
       unfold rho.
       rewrite D8mult_plus_distr_l, D8toZ8_plus; auto.
Qed.

Lemma rho_mult_z : forall (d : D8) (z : Z8) (k : nat),
  denom_exp d k ->
  rho k (D8mult z d) = Z8mult z (rho k d). 
Proof. intros. 
       unfold rho.
       rewrite D8mult_assoc, (D8mult_comm _ z), <- D8mult_assoc, 
         D8toZ8_mult, <- Z8toD8toZ8; auto.
       apply D8isZ8_ver; exists z; easy.
Qed.


Lemma rho_mult_root2 : forall (d : D8) (k : nat),
  denom_exp d k ->
  rho (S k) d = Z8mult root2 (rho k d).
Proof. intros.
       rewrite <- rho_mult_z; auto.
       unfold rho; simpl.
       rewrite (D8mult_comm root2), <- D8mult_assoc; easy.
Qed.
  




(* NOTE: for the first few lemmas from the paper, I stay pretty close to the paper, but it 
   may be possible/better to do things slightly faster *)


(* the paper has these definition on F28, but I have them on Z8 *)
Definition reducible (z : Z8) : Prop :=
  exists (y : Z8), Z8mult root2 y = z.

Definition irreducible (z : Z8) : Prop :=
  ~ (reducible z).

Definition twice_reducible (z : Z8) : Prop :=
  exists (y : Z8), Z8mult Z82 y = z.


(* I first prove the second part of Lemma 2: *)
Lemma twice_reducible_iff_0_res : forall z,
  twice_reducible z <-> Z8toF28 z = (F0, F0, F0, F0).
Proof. intros; split; intros.
       - destruct H.
         rewrite <- H, Z8toF28_mult.
         unfold Z8toF28, F28mult; simpl. 
         destruct x; repeat destruct p; simpl.
         destruct (ZtoF2 z3); destruct (ZtoF2 z0); 
           destruct (ZtoF2 z1); destruct (ZtoF2 z2); easy.
       - destruct z; repeat destruct p.
         unfold Z8toF28 in H; simpl in H.
         assert (H0 := H).
         apply (f_equal_gen snd snd) in H0; simpl in H0; auto.
         apply (f_equal_gen fst fst) in H; simpl in H; auto.
         assert (H1 := H).
         apply (f_equal_gen snd snd) in H1; simpl in H1; auto.
         apply (f_equal_gen fst fst) in H; simpl in H; auto.
         assert (H2 := H).
         apply (f_equal_gen snd snd) in H2; simpl in H2; auto.
         apply (f_equal_gen fst fst) in H; simpl in H; auto.
         apply ZtoF2_even in H;
           apply ZtoF2_even in H0;
           apply ZtoF2_even in H1;
           apply ZtoF2_even in H2.
         destruct H; destruct H0; destruct H1; destruct H2.
         exists (x, x2, x1, x0).
         rewrite <- H, <- H0, <- H1, <- H2.  
         unfold Z8mult.
         repeat apply injective_projections; simpl; 
           lia. 
Qed.



(* Note that I changed up the order a bit from the paper *)
Lemma Lemma2_1 : forall z,
  reducible z -> 
  Z8toF28 z = (F0, F0, F0, F0) \/ Z8toF28 z = (F1, F0, F1, F0) \/ 
  Z8toF28 z = (F0, F1, F0, F1) \/ Z8toF28 z = (F1, F1, F1, F1). 
Proof. intros. 
       destruct H; subst.
       rewrite <- mult_by_root2_ver.
       destruct (Z8toF28 x); repeat destruct p;
         destruct f; destruct f0; destruct f1; destruct f2; auto.
Qed.

Lemma Lemma2_2 : forall z,
  Z8toF28 z = (F0, F0, F0, F0) \/ Z8toF28 z = (F1, F0, F1, F0) \/ 
  Z8toF28 z = (F0, F1, F0, F1) \/ Z8toF28 z = (F1, F1, F1, F1) ->
  Z8toF28 (Z8mult (Z8conj z) z) = (F0, F0, F0, F0).
Proof. intros. 
       rewrite Z8toF28_mult, Z8conj_F28conj. 
       destruct (Z8toF28 z); repeat destruct p.
       destruct f; destruct f0; destruct f1; destruct f2; simpl; try easy.
       all : repeat (destruct H; try easy).
Qed.

Lemma Lemma2_3 : forall z,
  Z8toF28 (Z8mult (Z8conj z) z) = (F0, F0, F0, F0) ->
  Z8toF28 (Z8mult root2 z) = (F0, F0, F0, F0).  
Proof. intros. 
       rewrite Z8toF28_mult, Z8conj_F28conj in *. 
       destruct (Z8toF28 z); repeat destruct p.
       destruct f; destruct f0; destruct f1; destruct f2; simpl in *; try easy.
Qed.

Lemma Lemma2_4 : forall z,
  Z8toF28 (Z8mult root2 z) = (F0, F0, F0, F0) ->
  reducible z.
Proof. intros. 
       apply twice_reducible_iff_0_res in H.
       destruct H.
       rewrite <- root2_sqr in H.
       rewrite <- Z8mult_assoc in H.
       apply Z8mult_cancel_l in H.
       exists x; easy.
       apply Z8root2_neq_0.
Qed.

Lemma irreducible_dec : forall z, 
  { reducible z } + { irreducible z }.
Proof. intros. 
       destruct (F28eq_dec (Z8toF28 (Z8mult root2 z)) (F0, F0, F0, F0)).
       - left. 
         apply Lemma2_4; easy.
       - right.
         unfold irreducible, not; intros; apply n.
         apply Lemma2_3; apply Lemma2_2; apply Lemma2_1; easy.
Qed.


Lemma Lemma3_1 : forall (d : D8),
  D8isZ8 d -> 
  D8isZ8 (D8mult D8half d) <-> twice_reducible (D8toZ8 d).
Proof. intros; split; intros.
       - assert (H1 := H0).
         unfold twice_reducible.
         apply D8toZ8toD8 in H0; auto.
         exists (D8toZ8 (D8mult D8half d)).
         rewrite <- D8toZ8_2, <- D8toZ8_mult, D8mult_assoc, 
           D8mult_2_half, D8mult_1_l; auto.       
         apply D8isZ8_2.
       - destruct H0.
         apply D8isZ8_ver.
         exists x.
         apply (f_equal_gen Z8toD8 Z8toD8) in H0; auto.
         rewrite <- D8toZ8toD8 in H0; auto.
         rewrite <- H0, Z8toD8_mult, D8mult_assoc.
         (* TODO: this step suggests we define all constants in terms of the base type Z
            this is what we do in Complex.v *)
         rewrite Z8toD8_2.
         rewrite D8mult_half_2, D8mult_1_l.
         easy.
Qed.



Lemma Lemma3_2 : forall (d : D8),
  D8isZ8 d -> 
  D8isZ8 (D8mult root2_recip d) <-> reducible (D8toZ8 d).
Proof. intros; split; intros.
       - assert (H1 := H0).
         unfold reducible.
         apply D8toZ8toD8 in H0; auto.
         exists (D8toZ8 (D8mult root2_recip d)).
         rewrite (Z8toD8toZ8 root2), <- D8toZ8_mult, D8mult_assoc, 
           (D8mult_comm root2), root2_root2_recip, D8mult_1_l; auto.
         apply D8isZ8_ver.
         exists root2; easy.
       - apply Lemma2_1 in H0; apply Lemma2_2 in H0; apply Lemma2_3 in H0.
         apply twice_reducible_iff_0_res in H0. 
         rewrite (Z8toD8toZ8 root2), <- D8toZ8_mult in H0; auto.
         apply Lemma3_1  in H0. 
         rewrite D8mult_assoc in H0.
         rewrite <- root2_recip_proper in H0; easy.
         apply D8isZ8_mult; auto.
         all : apply D8isZ8_ver; exists root2; easy.
Qed.

(* inverse version of Lemma3_2 *)
Lemma Lemma3_2' : forall (d : D8),
  D8isZ8 d -> 
  ~ (D8isZ8 (D8mult root2_recip d)) <-> irreducible (D8toZ8 d).
Proof. intros; split; intros.
       - unfold irreducible, not; intros; apply H0.
         apply Lemma3_2; auto.
       - unfold not; intros; apply H0.
         apply Lemma3_2; auto.
Qed.


Lemma Corollary1 : forall (d : D8) (k : nat),
  k <> 0%nat ->
  denom_exp d k -> 
  least_denom_exp d k <-> irreducible (rho k d).  
Proof. intros; split; intros; destruct k; try easy.
       - destruct H1.
         unfold denom_exp in H0.
         apply Lemma3_2'; auto; simpl.
         repeat rewrite D8mult_assoc.
         rewrite root2_root2_recip, D8mult_1_l.         
         destruct (D8isZ8_dec (D8mult (D8pow root2 k) d)). 
         + apply H2 in d0; lia.
         + easy. 
       - apply Lemma3_2' in H1; auto; simpl in *.
         repeat rewrite D8mult_assoc in H1.
         rewrite root2_root2_recip, D8mult_1_l in H1.          
         split; auto; intros.
         destruct (ge_dec k' (S k)); try lia. 
         assert (k' <= k)%nat. lia.
         apply (get_weaker_denom_exp d k' k) in H3; auto.
         easy. 
Qed.



(* in terms of rho_k: *)

Lemma reducible_reduce : forall (d : D8) (k : nat),
  denom_exp d (S k) ->
  reducible (rho (S k) d) -> 
  denom_exp d k.
Proof. intros.
       apply Lemma3_2 in H0; auto; simpl in *.
       rewrite <- D8mult_assoc, (D8mult_assoc root2_recip), 
         root2_root2_recip, D8mult_1_l in H0.
       easy. 
Qed.   

Lemma twice_reducible_reduce : forall (d : D8) (k : nat),
  denom_exp d (S (S k)) ->
  twice_reducible (rho (S (S k)) d) -> 
  denom_exp d k.
Proof. intros; subst.
       apply Lemma3_1 in H0; auto; simpl in *.
       rewrite D8mult_assoc, (D8mult_assoc root2) in H0.
       replace (D8mult root2 root2) with D82 in H0.
       rewrite D8mult_assoc, D8mult_half_2, D8mult_1_l in H0.
       easy.
       rewrite <- Z8toD8_mult, root2_sqr.
       easy.
Qed.






(*
 *
 *
 *
 *)

