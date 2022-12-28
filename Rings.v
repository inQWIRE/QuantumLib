
Require Import List.       
Require Export Complex.
Require Export Quantum. 
Require Import FTA.





Lemma Cdiv_1_r : forall c, c / C1 = c.
Proof. intros. lca. Qed.





Definition Dyadic := (nat * Z)%type.


Declare Scope D_scope.
Delimit Scope D_scope with D.
 

Open Scope D_scope.
Bind Scope D_scope with Dyadic.



Coercion Z.of_nat : nat >-> Z.
Coercion IZR : Z >-> R.

Definition DtoC (x : Dyadic) : C := (snd x) / (C2^(fst x)).

Coercion DtoC : Dyadic >-> C.

(* this will be useful *)
Lemma Dyadic_as_C : forall (x : Dyadic), DtoC x = Cdiv (snd x) (C2 ^ (fst x)).
Proof. intros.
       unfold DtoC.
       Admitted. 
       
(* Coercions make things soo nice! *)


(* TODO: I open Z_scope here, but perhaps want to think more carefully about what type 
         we want equality here. We maybe want all equality over C *)
Open Scope Z_scope.

(* this assesses equality at the complex level *)
Definition Deq (x y : Dyadic) : Prop := DtoC x = DtoC y.

Infix "==" := Deq (at level 70) : D_scope.

(* this assesses equality at the integral level *)
Definition Deq' (x y : Dyadic) : Prop := 2^(fst y) * (snd x) = 2^(fst x) * (snd y).

Lemma Deq_is_Deq' : forall x y, Deq x y <-> Deq' x y.
Proof. intros.
       unfold Deq, Deq', DtoC. 
       destruct x; destruct y; simpl.
       split; intros.
       - Admitted.
(* 
rewrite <- pow_IZR in H.
         
         do 2 rewrite mult_IZR, <- pow_IZR, RtoC_mult, <- RtoC_pow in H.


         apply eq_IZR; apply RtoC_inj.
         do 2 rewrite mult_IZR, <- pow_IZR, RtoC_mult, <- RtoC_pow.
         easy.

       
       - apply (f_equal_gen IZR IZR _ _) in H; auto.
         apply (f_equal_gen RtoC RtoC _ _) in H; auto. 
         do 2 rewrite mult_IZR, <- pow_IZR, RtoC_mult, <- RtoC_pow in H.
         easy.
       - apply eq_IZR; apply RtoC_inj.
         do 2 rewrite mult_IZR, <- pow_IZR, RtoC_mult, <- RtoC_pow.
         easy.
Qed.          *)


Lemma DtoC_inj : forall (x y : Dyadic),
  DtoC x = DtoC y -> x == y.
Proof.
  intros. easy.
Qed.

Lemma Deq_dec (d1 d2 : Dyadic) : { d1 == d2 } + { ~ (d1 == d2) }.
Proof.
  destruct (Ceq_dec d1 d2).
  - left; easy.
  - right. 
    unfold not; intros; apply n; easy. 
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

Definition Dplus (x y : Dyadic) : Dyadic :=
  ((fst x + fst y)%nat, 2^(fst y) * snd x + 2^(fst x) * snd y).
Definition Dopp (x : Dyadic) : Dyadic := (fst x, -snd x).
Definition Dminus (x y : Dyadic) : Dyadic := Dplus x (Dopp y).
Definition Dmult (x y : Dyadic) : Dyadic :=
  ((fst x + fst y)%nat, snd x * snd y).



Infix "+," := Dplus (at level 50, left associativity) : D_scope. 
Infix "*," := Dmult (at level 40, left associativity) : D_scope.
Notation "-, d" := (Dopp d) (at level 30) : D_scope. 
Infix "-," := Dminus (at level 40, left associativity) : D_scope.


(* showing compatability *)

Lemma Deq_refl : forall (d : Dyadic), d == d.
Proof. easy. Qed.

Lemma Deq_symm : forall (d1 d2 : Dyadic), d1 == d2 -> d2 == d1.
Proof. easy. Qed. 

Lemma Deq_trans : forall (d1 d2 d3 : Dyadic), 
  d1 == d2 -> d2 == d3 -> d1 == d3.
Proof. intros. 
       unfold Deq in *; rewrite H; easy. 
Qed.


Lemma DtoC_plus : forall d1 d2, (DtoC d1 + DtoC d2)%C = DtoC (d1 +, d2).
Proof. intros.
       unfold Dplus.
       destruct d1; destruct d2; simpl.
       do 3 rewrite Dyadic_as_C; simpl.
       unfold Cdiv.
       Admitted. 

Lemma DtoC_opp : forall d, (- (DtoC d))%C = DtoC (-, d). 
Proof. intros.
       unfold Dopp.
       destruct d; simpl.
       do 2 rewrite Dyadic_as_C; simpl.
       rewrite Ropp_Ropp_IZR, RtoC_opp. 
       lca.
Qed.

Lemma DtoC_mult : forall d1 d2, (DtoC d1 * DtoC d2)%C = DtoC (d1 *, d2).
Proof. intros.
       Admitted. 

 
Lemma Dplus_eq_compat : forall (d1 d1' d2 d2' : Dyadic),
  d1 == d1' -> d2 == d2' -> d1 +, d2 == d1' +, d2'.
Proof. intros.
       unfold Deq in *; simpl.
       do 2 rewrite <- DtoC_plus. 
       rewrite H, H0.
       easy. 
Qed.

Lemma Dmult_eq_compat : forall (d1 d1' d2 d2' : Dyadic),
  d1 == d1' -> d2 == d2' -> d1 *, d2 == d1' *, d2'.
Proof. intros.
       unfold Deq in *; simpl.
       do 2 rewrite <- DtoC_mult. 
       rewrite H, H0.
       easy. 
Qed.



(*
 *
 *
 *)

Close Scope Z_scope.
Open Scope D_scope.


Definition ZtoD (z : Z) : Dyadic := (0%nat, z).


Lemma ZtoDtoC_is_ZtoRtoC : forall (z : Z), DtoC (ZtoD z) = RtoC (IZR z).
Proof. intros. 
       unfold DtoC, ZtoD, RtoC, IZR; simpl.
       lca.
Qed.


(*TODO: deal with this warning *)
Coercion ZtoD : Z >-> Dyadic.

Lemma ZtoD_inj : forall (x y : Z),
  ZtoD x == ZtoD y -> x = y.
Proof.
  intros.
  unfold ZtoD, Deq, DtoC in *; simpl in *.
  do 2 rewrite Cdiv_1_r in H.
  apply RtoC_inj in H.
  apply eq_IZR in H.
  easy.
Qed.



Lemma ZtoD_plus : forall (z1 z2 : Z), ZtoD z1 +, ZtoD z2 = ZtoD (z1 + z2)%Z.
Proof. intros.
       unfold Dplus, ZtoD; simpl.
       destruct z1; destruct z2; easy.
Qed.

Lemma ZtoD_opp : forall d, -, (ZtoD d) = ZtoD (- d). 
Proof. intros.
       unfold Dopp.
       destruct d; simpl; try easy.
Qed.

Lemma ZtoD_mult : forall z1 z2, ZtoD z1 *, ZtoD z2 = ZtoD (z1 * z2)%Z.
Proof. intros.
       unfold Dmult, ZtoD; simpl.
       easy.
Qed.


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




Definition DtoZ (d : Dyadic) : Z :=
  (snd d / 2^(fst d)).

Definition DisZ (d : Dyadic) : Prop :=
  Z.divide (2^(fst d)) (snd d).


Lemma DtoZtoD : forall (d : Dyadic), 
  DisZ d -> d == ZtoD (DtoZ d).
Proof. intros. 
       unfold Deq, DtoZ, ZtoD, DtoC.
       destruct d; simpl in *. 
       Search (Z.divide).
       Admitted.



Lemma ZtoDtoZ : forall (z : Z),
  z = DtoZ (ZtoD z).
Proof. intros.
       unfold DtoZ, ZtoD; simpl. 
       rewrite Z.div_1_r.
       easy.
Qed.



(* might not even need DisZ assumption? *)
Lemma DtoZ_plus : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 -> 
  DtoZ d1 + DtoZ d2 = DtoZ (d1 +, d2).
Proof. intros.
       unfold DtoZ, DisZ in *.
       destruct d1; destruct d2; simpl in *.
       Admitted.





(* NEXT STEP: introducing 4th ROU into the picture *)




Definition Cz8 : C := Cexp (PI / 4).

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
Proof. unfold Cz8.
       rewrite Cexp_pow, Cexp_conj_neg, <- Cexp_minus_PI. 
       apply f_equal.
       replace (INR 3) with 3%R. 
       lra. 
       unfold INR, IZR, IPR, IPR_2; lra.
Qed.








Definition D8 := (Dyadic * Dyadic * Dyadic * Dyadic)%type.


(* there are probably built in functions for this, but I could not find them *)
Notation "x .1" := (fst (fst (fst x))) (at level 0). 
Notation "x .2" := (snd (fst (fst x))) (at level 0). 
Notation "x .3" := (snd (fst x)) (at level 0). 
Notation "x .4" := (snd x) (at level 0). 

(* this is terrible, how to make better? *)
Definition D8toC (x : D8) : C :=
  x.1 + x.2 * Cz8 + x.3 * Cz8^2 + x.4 *Cz8^3.

Coercion D8toC : D8 >-> C.

(* because the above is so bad, this also helps *)
Definition DtuptoC (a b c d : Dyadic) : C := 
  a + b*Cz8 + c*Cz8^2 + d*Cz8^3.

(* annoyingly, we need this for rho_k. seems bad because Deq is weak. 
   maybe use different approach? *)
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


(* TODO: this takes a long time to compile for some reason. 
Fixpoint D8pow (z : D8) (n : nat) : D8 :=  
  match n with
  | 0%nat => ((O,1),(O,0),(O,0),(O,0))%Z
  | S n' => D8mult z (D8pow z n')
  end.
*)




Lemma Dyadic_real : forall (d : Dyadic), Cconj d = d.
Proof. intros.
       unfold Cconj, DtoC, RtoC, Cmult; destruct d; simpl.
       apply c_proj_eq; simpl; try easy. 
       rewrite Rmult_0_l.
       Admitted.
       (* lra. *)
(* Qed.  *)

Lemma D8_conj : forall (a b c d : Dyadic),
  Cconj (D8toC (a, b, c, d)) = D8toC (a, -,d, -,c, -,b).
Proof. intros.
       unfold D8toC; simpl fst; simpl snd.
       repeat rewrite Cconj_plus_distr.
       repeat rewrite Cconj_mult_distr.
       repeat rewrite Dyadic_real.
       replace (a + b * Cz8 ^* + c * (Cz8 ^ 2) ^* + d * (Cz8 ^ 3) ^*) with
               (a + d * (Cz8 ^ 3) ^* + c * (Cz8 ^ 2) ^* + b * Cz8 ^*) by lca.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto.
       apply f_equal_gen; auto. 
       - rewrite Cz8_pow3_conj.
         rewrite <- DtoC_opp.
         lca. 
       - rewrite Cz8_pow2_conj.
         rewrite <- DtoC_opp.
         lca. 
       - rewrite Cz8_conj.
         rewrite <- DtoC_opp.
         lca. 
Qed.



(* character theory? *)
Lemma Cz8_is_basis : forall (a b c d : Dyadic),
  D8toC (a, b, c, d) = C0 -> 
  a == (0%nat,0%Z) /\ b == (0%nat,0%Z) /\ c == (0%nat,0%Z) /\ d == (0%nat,0%Z).
Proof. intros. 
       unfold D8toC in H; simpl in H.
       Admitted. 





Definition Z8 := (Z * Z * Z * Z)%type.

Definition Z8toD8 (z : Z8) : D8 :=
  (ZtoD z.1, ZtoD z.2, ZtoD z.3, ZtoD z.4).

Coercion Z8toD8 : Z8 >-> D8.


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
  | 0%nat => (1,0,0,0)%Z
  | S n' => Z8mult z (Z8pow z n')
  end.




(* some basic lemmas *)

Lemma Z8plus_comm : forall (z1 z2 : Z8), Z8plus z1 z2 = Z8plus z2 z1.
Proof. intros.
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8plus; simpl.  
       repeat apply injective_projections; simpl; lia.
Qed.       

Lemma Z8plus_assoc : forall (z1 z2 z3 : Z8), Z8plus z1 (Z8plus z2 z3) = Z8plus (Z8plus z2 z1) z3.
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

Lemma Z8mult_assoc : forall (z1 z2 z3 : Z8), Z8mult z1 (Z8mult z2 z3) = Z8mult (Z8mult z2 z1) z3.
Proof. intros.
       destruct z1; repeat destruct p; destruct z2; 
         repeat destruct p; destruct z3; repeat destruct p.
       unfold Z8mult; simpl.  
       repeat apply injective_projections; simpl; lia.
Qed.   


(* I go straight from Z8 to C, since I really dont want to define D8mult... maybe I should? *)
Lemma Z8toC_plus : forall (z1 z2 : Z8),
  (z1 + z2)%C = (Z8plus z1 z2)%C.
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8toD8, D8toC, Z8plus; simpl.  
       repeat rewrite <- ZtoD_plus.
       repeat rewrite <- DtoC_plus.
       lca.
Qed.

Lemma Z8toC_opp : forall (z1 z2 : Z8),
  (z1 + z2)%C = (Z8plus z1 z2)%C.
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8toD8, D8toC, Z8plus; simpl.  
       repeat rewrite <- ZtoD_plus.
       repeat rewrite <- DtoC_plus.
       lca.
Qed.

Lemma Z8toC_mult : forall (z1 z2 : Z8),
  (z1 * z2)%C = (Z8mult z1 z2)%C.
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8toD8, D8toC, Z8mult, Zminus; simpl.   
       repeat rewrite <- ZtoD_plus.
       repeat rewrite <- DtoC_plus.
       repeat rewrite <- ZtoD_opp.
       repeat rewrite <- DtoC_opp.
       repeat rewrite <- ZtoD_mult.
       repeat rewrite <- DtoC_mult.       
       Admitted.


Lemma Z8mult_1_l : forall z, Z8mult (1,0,0,0)%Z z = z.
Proof. intros. 
       destruct z; repeat destruct p.
       unfold Z8mult; simpl.
       destruct z; destruct z0; destruct z1; destruct z2;
       repeat apply injective_projections; simpl; easy.
Qed.

Lemma Z8mult_1_r : forall z, Z8mult z (1,0,0,0)%Z = z.
Proof. intros.  
       destruct z; repeat destruct p.
       unfold Z8mult; simpl.
       destruct z; destruct z0; destruct z1; destruct z2;
       repeat apply injective_projections; simpl; lia.
Qed.
 
(* TODO: perhaps also coerce Z into Z8? *)
Lemma Z8mult_z_l : forall (z : Z) (z1 : Z8), 
  Z8mult (z, 0, 0, 0)%Z z1 = (z * z1.1, z * z1.2, z * z1.3, z * z1.4)%Z.
Proof. intros. 
       destruct z1; repeat destruct p; simpl.
       repeat apply injective_projections; simpl; lia.
Qed.       


(* Some pow lemmas *)

Lemma Z8toC_pow : forall (z : Z8) (n : nat), (z ^ n)%C = (Z8pow z n).
Proof. intros.
       induction n.
       - lca.
       - simpl.
         rewrite IHn, Z8toC_mult.
         easy. 
Qed.

Lemma Z8pow_add : forall (z : Z8) (n m : nat), Z8pow z (n + m) = Z8mult (Z8pow z n) (Z8pow z m).
Proof. intros. 
       induction n.
       - simpl. 
         rewrite Z8mult_1_l; easy.
       - simpl.
         rewrite IHn. 
         rewrite Z8mult_assoc, (Z8mult_comm _ z).
         easy.
Qed.


Lemma Z8pow_mult : forall (z : Z8) (n m : nat), Z8pow z (n * m) = Z8pow (Z8pow z n) m.
Proof.
  intros. induction m. rewrite Nat.mul_0_r. easy.
  replace (n * (S m))%nat with (n * m + n)%nat by lia.
  simpl. rewrite Z8pow_add. rewrite IHm. 
  rewrite Z8mult_comm. easy. 
Qed.




(* a more adhoc conjugation that we will eventually show is consistent with Cconj *)
Definition Z8conj (z : Z8) : Z8 :=
  (z.1, -z.4, -z.3, -z.2)%Z.


Lemma Z8conj_ver : forall (z : Z8),
  Cconj z = Z8conj z.
Proof. intros.
       destruct z; repeat destruct p. 
       unfold Z8toD8; simpl. 
       rewrite D8_conj.
       easy. 
Qed.       
       

Lemma Z8conj_mult : forall (z1 z2 : Z8),
  Z8conj (Z8mult z1 z2) = Z8mult (Z8conj z1) (Z8conj z2).
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8conj, Z8mult; simpl.
       repeat apply injective_projections; simpl; lia.
Qed.







Definition root2 : Z8 := (0, 1, 0, -1)%Z.


Definition root2_recip : D8 := ((0%nat,0), (1%nat,1), (0%nat,0), (1%nat,-1))%Z.


(* TODO: make this proof nice *)
Lemma root2_ver : D8toC (Z8toD8 root2) = RtoC (√ 2). 
Proof. unfold root2, Z8toD8, D8toC; simpl fst; simpl snd.
       repeat rewrite ZtoDtoC_is_ZtoRtoC.
       replace (0 + C1 * Cz8 + 0 * Cz8 ^ 2 + -1 * Cz8 ^ 3) with (Cz8 - Cz8^3) by lca.
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
Qed.

(* 
Lemma root2_recip_ver : D8toC root2_recip = / RtoC (√ 2).
Proof. unfold root2_recip, Z8toD8, D8toC; simpl fst; simpl snd.
       repeat rewrite ZtoDtoC_is_ZtoRtoC.
       rewrite Cmult_0_l, Cplus_0_l, Cplus_0_r.
       unfold Cz8; rewrite Cexp_pow.
       replace (PI / 4 * INR 3)%R with (3 * PI / 4)%R.
       rewrite Cexp_PI4, Cexp_3PI4.
       replace (DtoC (1%nat, 1%Z)) with (1/2)%C.
       replace (DtoC (1%nat, (-1)%Z)) with (- (1/2))%C.

       replace (C1 / C2 * (/ √ 2 + / √ 2 * Ci) + - (C1 / C2) * (- / √ 2 + / √ 2 * Ci)) 
         with (C1 / C2 * (2 / √ 2)) by lca.
       rewrite <- Csqrt2_sqrt.
       unfold Cdiv. 
       2 : { unfold DtoC. ; simpl.  Set Printing All.

       rewrite <- Cmult_assoc, Cinv_r. ; try lca.
       apply Csqrt2_neq_0.
       replace (INR 3) with (IZR 3). lra.
       unfold INR, IZR, IPR, IPR_2; lra. 

Lemma root2_sqr : Z8mult root2 root2 = (2, 0, 0, 0)%Z.
Proof. easy. Qed. 


Lemma root2_root2_recip : D8mult root2_recip root2 = ((2%nat,2), (2%nat,0), (2%nat,0), (2%nat,0))%Z.
Proof. repeat apply injective_projections; simpl; easy. Qed.





Definition D8toZ8 (d : D8) : Z8 :=
  (DtoZ d.1, DtoZ d.2, DtoZ d.3, DtoZ d.4).






(* TODO: should have all the F2 and Z stuff before the D8, Z8, F28 stuff *)


Close Scope D_scope.
Open Scope Z_scope.

(* TODO: move to finite_group, or field *)
Inductive F2 :=
| F0
| F1.


Definition F2neg (x : F2) : F2 :=
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



Program Instance F2_is_monoid : Monoid F2 := 
  { Gzero := F0
  ; Gplus := F2plus
  }.
Solve All Obligations with program_simpl; destruct g; try easy; destruct h; destruct i; easy. 

Program Instance F2_is_group : Group F2 :=
  { Gopp := F2neg }.
Solve All Obligations with program_simpl; destruct g; easy.

Program Instance F2_is_comm_group : Comm_Group F2.
Solve All Obligations with program_simpl; destruct a; destruct b; easy.
                                             
Program Instance F2_is_ring : Ring F2 :=
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

Program Instance F2_is_comm_ring : Comm_Ring F2.
Solve All Obligations with program_simpl; destruct a; destruct b; easy.

Program Instance F2_is_field : Field F2 :=
  { Ginv := F2neg }.
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
Lemma ZtoF2_plus : forall z1 z2, (ZtoF2 z1 + ZtoF2 z2)%G = ZtoF2 (z1 + z2).
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

Lemma ZtoF2_neg : forall z, (- (ZtoF2 z))%G = ZtoF2 (- z)%Z.
Proof. intros.
       destruct z; try easy;
       destruct p; try easy; destruct p0; try easy; simpl.
Qed.

Lemma ZtoF2_mult : forall z1 z2, (ZtoF2 z1 * ZtoF2 z2)%G = ZtoF2 (z1 * z2).
Proof. intros.
       replace Gmult with F2mult by easy.
       destruct z1; destruct z2; try easy;  
       destruct p; try easy; destruct p0; try easy; simpl.
Qed.


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
         rewrite <- H, <- ZtoF2_mult; simpl.
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
         rewrite <- H, <- ZtoF2_plus, <- ZtoF2_mult; simpl.
         destruct (ZtoF2 x); easy. 
Qed.



Definition F28 := (F2 * F2 * F2 * F2)%type.



Definition Z8toF28 (z : Z8) : F28 :=
  (ZtoF2 z.1, ZtoF2 z.2, ZtoF2 z.3, ZtoF2 z.4).

Definition F28neg (x : F28) : F28 :=
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


Lemma Z8toF28_plus_compact : forall p p0, 
  Z8toF28 (Z8plus p p0) = F28plus (Z8toF28 p) (Z8toF28 p0).
Proof. intros. 
       repeat (destruct p; destruct p0); simpl. 
       unfold Z8plus, F28plus; simpl.
       repeat rewrite  ZtoF2_plus.
       easy.
Qed.


Lemma Z8toF28_mult_compact : forall p p0, 
  Z8toF28 (Z8mult p p0) = F28mult (Z8toF28 p) (Z8toF28 p0).
Proof. intros. 
       rewrite F28mult_eqiv.
       repeat (destruct p; destruct p0); simpl. 
       unfold Z8mult, F28mult'; simpl.
       repeat rewrite ZtoF2_mult.
       repeat rewrite ZtoF2_neg.
       repeat rewrite ZtoF2_plus.
       unfold Z8toF28; simpl.
       easy. 
Qed.


(* helpful for some lemmas about Z8conj *)
Definition F28conj (z : F28) : F28 :=
  (z.1, -z.4, -z.3, -z.2)%G.

Lemma Z8conj_F28conj : forall z, Z8toF28 (Z8conj z) = F28conj (Z8toF28 z).
Proof. intros. 
       unfold Z8toF28, Z8conj, F28conj. 
       destruct z; repeat destruct p; simpl.
       do 3 rewrite ZtoF2_neg.
       easy.
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
       rewrite Z8toF28_mult_compact.
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
       rewrite Z8toF28_mult_compact.
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




Close Scope Z_scope.
Open Scope D_scope.



(* note that this is over C, but this seems correct since we use root2_ver *)
(* since powers are used, could need to define powers over Z8, which seems annoying *)
Definition denom_exp (t : D8) (k : nat) : Prop :=
  exists (z : Z8), (root2^k) * t = z. 

Definition least_denom_exp (t : D8) (k : nat) : Prop :=
  denom_exp t k /\ forall k', denom_exp t k' -> (k <= k')%nat.


Lemma exists_denom_exp : forall t,
  exists k, denom_exp t k.
Proof. intros.
       destruct t; repeat destruct p.
       destruct d; destruct d0; destruct d1; destruct d2.
       exists (2 * (n + n0 + n1 + n2))%nat.
       exists (2^(n + n0 + n2) * z1, 2^(n + n0 + n1) * z2, 
           2^(n + n1 + n2) * z0, 2^(n0 + n1 + n2) * z)%Z.
(*       rewrite Z8pow_mult.
       replace (Z8pow (Z8pow root2 2) (n + n0 + n1 + n2)) with
         (2^(n + n0 + n1 + n2)%Z, 0, 0, 0)%Z. *)
       rewrite root2_ver, Cpow_mult.
       replace (√ 2 ^ 2)%C with C2 by (rewrite RtoC_pow, pow2_sqrt2; easy).
       unfold D8toC, DtoC; simpl. 
       repeat rewrite Cmult_plus_distr_l.
       apply f_equal_gen.
       apply f_equal_gen; auto.
       apply f_equal_gen.
       apply f_equal_gen; auto.
       apply f_equal_gen.
       apply f_equal_gen; auto.
       Admitted. 

Lemma exists_least_denom_exp : forall t,
  exists k, least_denom_exp t k.
Proof. intros.
       assert (H' := exists_denom_exp t).
       apply (dec_inh_nat_subset_has_unique_least_element (denom_exp t)) in H'.
       destruct H'; do 2 destruct H. 
       exists x; split; auto.
       intros. 
       Admitted.




Definition rho_k (t : D8) (k : nat) : F28 :=
  Z8toF28 (D8toZ8 (D8mult (Z8pow root2 k) t)).
 





(* the paper has these definition on F28, but I have them on Z8 *)
Definition reducible (z : Z8) : Prop :=
  exists (y : Z8), Z8mult root2 y = z.

Definition twice_reducible (z : Z8) : Prop :=
  exists (y : Z8), Z8mult (2, 0, 0, 0)%Z y = z.


(* TODO: might be able to delete these. 4 => 1 is the hardest anyways *)
Lemma Lemma2_1 : forall z,
  reducible z -> 
  Z8toF28 z = (F0, F0, F0, F0) \/ Z8toF28 z = (F1, F0, F1, F0) \/ 
  Z8toF28 z = (F0, F1, F0, F1) \/ Z8toF28 z = (F1, F1, F1, F1). 
Proof. intros. 
       destruct H; subst.
       rewrite <- mult_by_root2_ver.
       destruct (Z8toF28 x); repeat destruct p;
         destruct f; destruct f0; destruct f1; destruct f2; simpl;
         try (left; easy); try (right; left; easy); 
         try (right; right; left; easy); right; right; right; easy.
Qed.

Lemma Lemma2_2 : forall z,
  Z8toF28 z = (F0, F0, F0, F0) \/ Z8toF28 z = (F1, F0, F1, F0) \/ 
  Z8toF28 z = (F0, F1, F0, F1) \/ Z8toF28 z = (F1, F1, F1, F1) ->
  Z8toF28 (Z8mult root2 z) = (F0, F0, F0, F0).
Proof. intros. 
       rewrite Z8toF28_mult_compact.
       repeat (destruct H; try (rewrite H; easy)).
Qed.

Lemma Lemma2_3 : forall z,
  Z8toF28 (Z8mult root2 z) = (F0, F0, F0, F0) ->
  Z8toF28 (Z8mult (Z8conj z) z) = (F0, F0, F0, F0).
Proof. intros. 
       rewrite <- square_norm_ver.
       rewrite <- mult_by_root2_ver in H.
       destruct (Z8toF28 z); repeat destruct p;
         destruct f; destruct f0; destruct f1; destruct f2; simpl; try easy.
Qed.

Lemma twice_reducible_iff_0_res : forall z,
  twice_reducible z <-> Z8toF28 z = (F0, F0, F0, F0).
Proof. intros; split; intros.
       - destruct H.
         rewrite <- H, Z8toF28_mult_compact.
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




(*
 *
 *
 *
 *)


(* NEXT STEP: defining matrices that can be used *)

(*TODO: figure out how to do this*)
(*possible ideas: 
  - generaize Matrix.v, so we can get rid of C entirely 
  - define predicate to determine if a C matrix is actually a D8 matrix 
  - continue how I do here*)


Definition H_gate (p : D8 * D8) : (D8 * D8) :=
  (





Lemma Lemma4 : forall (d1 d2 : D8) (k : nat),
  k > 0 -> 
  denom_exp d1 k -> denom_exp d2 k ->
  







Set Printing All.

Search (IZR (Z.pow _ _ )).


Search (Z.opp (Z.of_nat _)).

rewrite <- pow_IZR.
       2 : {  rewrite RtoC_pow, pow2_sqrt2.
              Search ((√ 2 ^ 2)%R).
         Set Printing All.
         Search (Cpow (RtoC _ )).


       replace ((Cpow (RtoC (sqrt (IZR (Zpos (xO xH))))) (S (S O)))) with C2.
       Search ((√ 2))%C.
Set Printing All.

       Search ((_ ^ (_ * _)))%C.

       rewrite 
       destruct z; do 2 destruct p.
       unfold Z8toF28.
       simpl fst. 





(* could define as an actual set and then coerce to C *)
Inductive Dyadic : Cset :=
| Dy_half : Dyadic (1/2)
| Dy_inv : forall (d : C), Dyadic d -> Dyadic (-d)
| Dy_plus : forall (d1 d2 : C), Dyadic d1 -> Dyadic d2 -> Dyadic (d1 + d2)
| Dy_mult : forall (d1 d2 : C), Dyadic d1 -> Dyadic d2 -> Dyadic (d1 * d2). 


(*
Definition Dyadic_C (c : C) : Prop :=
  exists d, DtoC d = c.
*)


Lemma Dyadic_plus : forall (z1 z2 : Z) (n1 n2 : nat),
  (IZR z1 / (2^n1)) + (IZR z2 / (2^n2)) = 
    IZR (z1 * (2^(Z.of_nat n2))%Z + z2 * 2^(Z.of_nat n1)) / (2^(n1 + n2)).
Proof. intros. 
       Admitted. 

Lemma Dyadic_mult : forall (z1 z2 : Z) (n1 n2 : nat),
  (IZR z1 / (2^n1)) * (IZR z2 / (2^n2)) = 
    IZR (z1 * z2) / 2^(n1 + n2). 
Proof. intros. 
       Admitted. 


Lemma Dyadic_ver : forall (c : C),
  Dyadic c <-> exists (n : nat) (z : Z), IZR z / (2^n) = c.
Proof. intros; split; intros.  
       - induction H. 
         exists (1%nat), 1%Z.
         lca.
         destruct IHDyadic as [n [z H0] ].
         exists n, (-z)%Z.
         rewrite Ropp_Ropp_IZR, <- H0.
         lca. 
         destruct IHDyadic1 as [n1 [z1 H1] ].
         destruct IHDyadic2 as [n2 [z2 H2] ].
         exists (n1 + n2)%nat, (z1 * (2^(Z.of_nat n2))%Z + z2 * 2^(Z.of_nat n1))%Z. 
         rewrite <- Dyadic_plus; subst; easy.
         destruct IHDyadic1 as [n1 [z1 H1] ].
         destruct IHDyadic2 as [n2 [z2 H2] ].       
         exists (n1 + n2)%nat, (z1 * z2)%Z. 
         rewrite <- Dyadic_mult; subst; easy.
       - destruct H as [n [z H] ]. 
         apply Dyadic_ind; intros.
         apply Dy_half.
         apply Dy_inv; auto.
         apply Dy_plus; auto.
         apply Dy_mult; auto.
         

       Search (IZR (- _)).

       unfold IZR.

       apply Dyadic_ind.


Search IZR.                                              


| otI_add : forall (A : Square n) (x y : nat) (c : C), x < n -> y < n -> x <> y -> 
                                         op_to_I A -> op_to_I (col_add A x y c).






(* creating a map that describes the effect of multiplication by root2 *)
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

*)
