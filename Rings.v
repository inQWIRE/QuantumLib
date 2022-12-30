
Require Import List.       
Require Export Complex.
Require Export Quantum. 
Require Import FTA.




Open Scope C_scope.

(* exponentiation by positives *)
Fixpoint Cpow_pos (c : C) (p : positive) : C :=
  match p with 
  | xH => c
  | xO p' => (Cpow_pos c p') * (Cpow_pos c p')
  | xI p' => c * (Cpow_pos c p') * (Cpow_pos c p')
  end.             


(* exponentiation by integers *)
Definition Cpow_int (c : C) (z : Z) : C :=  
  match z with
    | Z0 => C1
    | Zpos p => Cpow_pos c p
    | Zneg p => / Cpow_pos c p
  end.


Infix "^^" := Cpow_int (at level 10) : C_scope.


(* could be good for slick use of Cpow_int_cons below *)
Coercion Z.of_nat : nat >-> Z.


Lemma Cpow_int_nonzero : forall (c : C) (z : Z), c <> C0 -> c ^^ z <> C0. 
Proof. intros.
       Admitted.


Lemma Cpow_int_add : forall (c : C) (z1 z2 : Z), c ^^ (z1 + z2) = c^^z1 * c^^z2.
Proof. intros.
       Admitted.


Lemma Cpow_int_mult : forall (c : C) (z1 z2 : Z), c ^^ (z1 * z2) = (c ^^ z1) ^^ z2.
Proof. intros. 
       Admitted.



Lemma Cpow_inv1 : forall (c : C) (z : Z), c <> C0 -> c^^(-z) = / (c^^z).
Proof. intros.
       Admitted.

Lemma Cpow_inv2 : forall (c : C) (z : Z), c <> C0 -> (/ c)^^z = / (c^^z).
Proof. intros.
       Admitted.


(* checking that Cpow_int is consistent with Cpow on nats *)
Lemma Cpow_int_cons : forall (c : C) (n : nat),
  c^n = c ^^ n.
Proof. intros. 
       induction n as [| n'].
       - easy.
       - simpl. 
         Admitted. 



Lemma Cpow_int_real : forall (c : C) (z : Z), 
  snd c = 0 -> snd (c ^^ z) = 0.
Proof. intros.
       Admitted.


(* foreboding: translating between Cpow_int and Zpow *)
Lemma ZtoC_pow_nat : forall (z : Z) (n : nat), 
  RtoC (IZR (z^n)%Z) = (RtoC (IZR z))^^n.
Proof. intros. 
       induction n; try easy.
       rewrite <- Cpow_int_cons in *.
       simpl. 
       rewrite <- IHn.
       Admitted. 

(* foreboding: translating between Cpow_int and Zpow *)
Lemma ZtoC_pow : forall (z n : Z), 
  (n >= 0)%Z ->
  RtoC (IZR (z^n)%Z) = (RtoC (IZR z))^^n.
Proof. intros.
       Admitted. 
       


(* NB: use plus_IZR, mult_IZR, RtoC_plus, RtoC_mult to move between types: *)
(* quick helper tactic. TODO: centralize these *)
Ltac fastZtoC := 
  repeat (repeat rewrite plus_IZR, RtoC_plus;
          repeat rewrite minus_IZR, RtoC_minus;
          repeat rewrite opp_IZR, RtoC_opp;
          repeat rewrite mult_IZR, RtoC_mult;
          repeat (rewrite ZtoC_pow; try lia)).





   
(*
 *
 *
 *)




(* Defining 2-adic valuation of an integer and properties *)

Open Scope Z_scope.


(* could return nat, but int seem better *)
Fixpoint two_val_pos (p : positive) : Z :=
  match p with 
  | xO p' => 1 + (two_val_pos p')
  | _ => 0
  end.


Fixpoint odd_part_pos (p : positive) : positive :=
  match p with 
  | xO p' => odd_part_pos p'
  | _ => p
  end.

(*
Fixpoint n_minus_1_over_2 : (p : positive) : positive :=
  match p with 
  | xO p' => odd_part_pos p'
  | _ => p
  end.
*)


(* CHECK: maybe only need these for positives since we split on 0, pos, neg, anyways *)

Definition two_val (z : Z) : Z :=
  match z with 
  | Z0 => 0 (* poorly defined on 0 *)
  | Zpos p => two_val_pos p
  | Zneg p => two_val_pos p
  end.


Definition odd_part (z : Z) : Z :=
  match z with 
  | Z0 => 0  (* poorly defined on 0 *)
  | Zpos p => Zpos (odd_part_pos p)
  | Zneg p => Zneg (odd_part_pos p)
  end.



Lemma twoadic_nonzero : forall (a b : Z),
  a >= 0 -> 2^a * (2 * b + 1) <> 0.
Proof. intros. 
       apply Z.neq_mul_0; split; try lia.
       apply Z.ge_le in H.
       apply (Z.pow_nonzero 2 a); lia.
Qed.

Lemma get_two_val : forall (a b : Z),
  a >= 0 -> 
  two_val (2^a * (2 * b + 1)) = a.
Proof. Admitted. 


Lemma get_odd_part : forall (a b : Z),
  a >= 0 -> 
  odd_part (2^a * (2 * b + 1)) = 2 * b + 1.
Proof. Admitted. 



Lemma twoadic_breakdown : forall (z : Z),
  z <> 0 -> z = (2^(two_val z)) * (odd_part z).
Proof. Admitted.



Lemma odd_part_pos_odd : forall (p : positive),
  (exists p', odd_part_pos p = xI p') \/ (odd_part_pos p = xH).
Proof. intros.
       induction p.
       - left; exists p; easy. 
       - destruct IHp.
         + left. 
           destruct H.
           exists x; simpl; easy.
         + right; simpl; easy.
       - right; easy.
Qed.


Lemma odd_part_odd : forall (z : Z),
  z <> 0 -> 
  2 * ((odd_part z - 1) / 2) + 1 = odd_part z.
Proof. intros. 
       rewrite <- (Zdiv.Z_div_exact_full_2 _ 2); try lia.
       destruct z; try easy; simpl;
         destruct (odd_part_pos_odd p).
       - destruct H0; rewrite H0; simpl.
         rewrite Pos2Z.pos_xO, Zmult_comm, Zdiv.Z_mod_mult.
         easy.
       - rewrite H0; easy.
       - destruct H0; rewrite H0; simpl.
         rewrite (Pos2Z.neg_xO (Pos.succ x)), Zmult_comm, Zdiv.Z_mod_mult. 
         easy.
       - rewrite H0; easy. 
Qed.


Lemma two_val_ge_0 : forall (z : Z),
  two_val z >= 0.
Proof. intros. 
       destruct z; simpl; try lia.
       - induction p; try (simpl; lia). 
         replace (two_val_pos p~0) with (1 + two_val_pos p) by easy.
         lia. 
       - induction p; try (simpl; lia). 
         replace (two_val_pos p~0) with (1 + two_val_pos p) by easy.
         lia. 
Qed.
     

Lemma two_val_mult : forall (z1 z2 : Z),
  z1 <> 0 -> z2 <> 0 ->
  two_val (z1 * z2) = two_val z1 + two_val z2.
Proof. Admitted. 


Lemma two_val_plus : forall (z1 z2 : Z),
  z1 <> 0 -> z2 <> 0 ->
  two_val (z1 + z2) >= Z.min (two_val z1) (two_val z2).
Proof. Admitted. 






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
Definition Dhalf : Dyadic := Dn (Z.opp 1) 0.


Declare Scope D_scope.
Delimit Scope D_scope with D.
 
Open Scope D_scope.
Bind Scope D_scope with Dyadic.



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

Lemma DtoC_Dhalf : DtoC Dhalf = / C2.
Proof. unfold DtoC, Dhalf.
       rewrite Cpow_inv1. 
       lca.
       apply RtoC_neq.
       lra.
Qed.
     

(* idea: WLOG v(x) <= v(y), equality case is easy, then reflect back to Z *)
Lemma DtoC_inj : forall (x y : Dyadic),
  DtoC x = DtoC y -> x = y.
Proof.
  intros. 
  unfold DtoC in *.
  Admitted.



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
      | inright _ => Dn m (2^(n-m-1) * (2*x'+1) + y')             (* y has lower power of 2 *)
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




Infix "+," := Dplus (at level 50, left associativity) : D_scope. 
Infix "*," := Dmult (at level 40, left associativity) : D_scope.
Notation "-, d" := (Dopp d) (at level 30) : D_scope. 
Infix "-," := Dminus (at level 50, left associativity) : D_scope.


(* showing compatability *)

Lemma DtoC_plus : forall d1 d2, (DtoC d1 + DtoC d2)%C = DtoC (d1 +, d2).
Proof. intros.
       destruct d1; destruct d2; simpl; try lca.
       unfold Dplus; destruct (Ztrichotomy_inf z z1); try destruct s.
       - unfold DtoC. 
         fastZtoC. 
         rewrite (Cmult_plus_distr_l _ _ z0), (Cmult_assoc C2).
         replace (C2 * C2 ^^ (z1 - z - 1))%C with (C2 ^^ (z1 - z)).
         rewrite <- Cplus_assoc, (Cmult_plus_distr_l _ _ (C2 * z0 + C1)), Cmult_assoc.
         replace (C2 ^^ z * C2 ^^ (z1 - z))%C with (C2 ^^ z1).
         lca.
         rewrite <- Cpow_int_add.
         apply f_equal; lia.
         replace (Cmult C2) with (Cmult (C2 ^^ 1)) by (apply f_equal; easy).
         rewrite <- Cpow_int_add.
         apply f_equal; lia.
       - Admitted. 





Lemma DtoC_opp : forall d, (- (DtoC d))%C = DtoC (-, d). 
Proof. intros.
       destruct d; try lca. 
       unfold Dopp, DtoC, Zminus.
       fastZtoC.
       rewrite Copp_mult_distr_r. 
       lca.
Qed.       


Lemma DtoC_minus : forall d1 d2, ((DtoC d1) - (DtoC d2))%C = DtoC (d1 -, d2). 
Proof. intros.
       unfold Cminus, Dminus.
       rewrite DtoC_opp, DtoC_plus.
       easy.
Qed.     


(* this is surprisingly easy! *)
Lemma DtoC_mult : forall d1 d2, (DtoC d1 * DtoC d2)%C = DtoC (d1 *, d2).
Proof. intros.
       destruct d1; destruct d2; try lca.
       unfold Dmult, DtoC.
       fastZtoC.
       rewrite Cpow_int_add.
       lca.
Qed.



(* Note that once we have a injective homomorphism into C, 
   we get all the ring axioms for free! *)
(* TODO: generalize this in Summation.v *)


Lemma Dplus_comm : forall d1 d2, d1 +, d2 = d2 +, d1.
Proof. intros.
       apply DtoC_inj.
       do 2 rewrite <- DtoC_plus.
       lca.
Qed.

Lemma Dplus_assoc : forall d1 d2 d3, d1 +, d2 +, d3 = d1 +, (d2 +, d3).
Proof. intros.
       apply DtoC_inj.
       do 4 rewrite <- DtoC_plus.
       lca.
Qed.

Lemma Dplus_0_r : forall d, d +, D0 = d.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_plus.
       lca.
Qed.

Lemma Dplus_0_l : forall d, D0 +, d = d.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_plus.
       lca.
Qed.

Lemma Dminus_0_r : forall d, d -, D0 = d.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_minus.
       lca.
Qed.

Lemma Dminus_0_l : forall d, D0 -, d = -, d.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_minus, <- DtoC_opp.
       lca.
Qed.

Lemma Dmult_0_r : forall d, d *, D0 = D0.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_mult.
       lca.
Qed.

Lemma Dmult_0_l : forall d, D0 *, d = D0.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_mult.
       lca.
Qed.

Lemma Dmult_comm : forall d1 d2, d1 *, d2 = d2 *, d1.
Proof. intros.
       apply DtoC_inj.
       do 2 rewrite <- DtoC_mult.
       lca.
Qed.

Lemma Dmult_assoc : forall d1 d2 d3, d1 *, d2 *, d3 = d1 *, (d2 *, d3).
Proof. intros.
       apply DtoC_inj.
       do 4 rewrite <- DtoC_mult.
       lca.
Qed.

Lemma Dmult_1_r : forall d, d *, D1 = d.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_mult.
       lca.
Qed.

Lemma Dmult_1_l : forall d, D1 *, d = d.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_mult.
       lca.
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
       rewrite <- DtoC_plus.
       rewrite DtoC_Dhalf, DtoC_D1.
       lca.
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


Lemma ZtoD_plus : forall (z1 z2 : Z), ZtoD z1 +, ZtoD z2 = ZtoD (z1 + z2)%Z.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_plus.
       do 3 rewrite ZtoDtoC_is_ZtoRtoC.
       fastZtoC.
       easy. 
Qed.


Lemma ZtoD_opp : forall d, -, (ZtoD d) = ZtoD (- d). 
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_opp.
       do 2 rewrite ZtoDtoC_is_ZtoRtoC.
       fastZtoC.
       easy. 
Qed.

Lemma ZtoD_mult : forall z1 z2, ZtoD z1 *, ZtoD z2 = ZtoD (z1 * z2)%Z.
Proof. intros.
       apply DtoC_inj.
       rewrite <- DtoC_mult.
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



(* TODO: fix this proof after changing def of Dplus *)
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


Lemma DisZ_mult : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 ->
  DisZ (d1 *, d2).
Proof. intros.
       destruct d1; destruct d2; try easy.
       unfold Dmult, DisZ in *.
       lia. 
Qed.



Lemma DtoZtoD : forall (d : Dyadic), 
  DisZ d -> d = ZtoD (DtoZ d).
Proof. intros. 
       destruct d; try easy.
       unfold ZtoD, DtoZ.
       simpl in H.
       destruct (2 ^ z * (2 * z0 + 1))%Z eqn:E.
       - apply Zmult_integral in E; destruct E; try lia.
         apply Z.ge_le in H.
         apply (Z.pow_nonzero 2 z) in H; lia.
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




Lemma DtoZ_plus : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 -> 
  (DtoZ d1 + DtoZ d2)%Z = DtoZ (d1 +, d2).
Proof. intros.
       apply ZtoD_inj.
       rewrite <- ZtoD_plus.
       do 3 (rewrite <- DtoZtoD; auto).
       apply DisZ_plus; easy.
Qed.

Lemma DtoZ_mult : forall (d1 d2 : Dyadic),
  DisZ d1 -> DisZ d2 -> 
  (DtoZ d1 * DtoZ d2)%Z = DtoZ (d1 *, d2).
Proof. intros.
       apply ZtoD_inj.
       rewrite <- ZtoD_mult.
       do 3 (rewrite <- DtoZtoD; auto).
       apply DisZ_mult; easy.
Qed.







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








(* NEXT STEP: introducing 4th ROU into the picture *)



Open Scope C_scope.



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
Definition D8half := (Dhalf, D0, D0, D0).



Fixpoint D8pow (z : D8) (n : nat) : D8 :=  
  match n with
  | 0%nat => D81
  | S n' => D8mult z (D8pow z n')
  end.




(* this will be annoying. Must use irrationality of sqrt 2 or that Phi_4(x) is irred over Q *)
Lemma Cz8_is_basis : forall (a b c d : Dyadic),
  D8toC (a, b, c, d) = C0 -> 
  a = D0 /\ b = D0 /\ c = D0 /\ d = D0.
Proof. intros. 
       unfold D8toC in H.
       rewrite Cz8_pow2, Cz8_pow3 in H.
       simpl in H.
       Admitted. 



Lemma D8toC_inj : forall (x y : D8),
  D8toC x = D8toC y -> x = y.
Proof.
  intros. 
  unfold D8toC in *.
  destruct x; repeat destruct p; destruct y; repeat destruct p; simpl in *.
  Search (_ - _ = C0)%C.
  Admitted.



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
    










Lemma D8toC_0 : D8toC D80 = C0.
Proof. lca. Qed.

Lemma D8toC_1 : D8toC D81 = C1.
Proof. lca. Qed.



Lemma Dyadic_real : forall (d : Dyadic), snd (DtoC d) = 0.
Proof. intros. 
       destruct d; unfold DtoC; simpl; try lra.
       rewrite Cpow_int_real; simpl; lra.
Qed.


Lemma Cconj_D : forall (d : Dyadic), Cconj d = d.
Proof. intros.
       destruct (DtoC d) eqn:E.
       unfold Cconj; simpl.
       replace r0 with (snd (DtoC d)) by (rewrite E; easy).
       rewrite Dyadic_real. 
       apply c_proj_eq; simpl; lra.
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
         rewrite <- DtoC_opp.
         lca. 
       - rewrite Cz8_pow2_conj.
         rewrite <- DtoC_opp.
         lca. 
       - rewrite Cz8_conj.
         rewrite <- DtoC_opp.
         lca. 
Qed.








Lemma D8mult_1_r : forall d, D8mult d D81 = d.
Proof. intros.  
       destruct d; repeat destruct p.
       unfold D8mult; simpl.
       repeat apply injective_projections; simpl. 
       all : repeat (try rewrite Dmult_0_r; try rewrite Dminus_0_r;
                     try rewrite Dplus_0_r; try rewrite Dplus_0_l).
       all : rewrite Dmult_1_r; easy.
Qed.       


 
(* TODO: perhaps also coerce D into D8? *)
Lemma D8mult_d_l : forall (d d1 d2 d3 d4 : Dyadic), 
  D8mult (d, D0, D0, D0) (d1, d2, d3, d4) = (d *, d1, d *, d2, d *, d3, d *, d4).
Proof. intros. 
       repeat apply injective_projections; simpl. 
       all : repeat (try rewrite Dmult_0_r; try rewrite Dminus_0_r;
                     try rewrite Dplus_0_r; try rewrite Dplus_0_l); easy.
Qed. 






Definition Z8 := (Z * Z * Z * Z)%type.

Definition Z8toD8 (z : Z8) : D8 :=
  (ZtoD z.1, ZtoD z.2, ZtoD z.3, ZtoD z.4).

Coercion Z8toD8 : Z8 >-> D8.


(* TODO: think of better names for these *)
Definition Z80 : Z8 := (0,0,0,0).

Definition Z81 : Z8 := (1,0,0,0).

Definition Z8w : Z8 := (0,1,0,0).

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




(* some basic lemmas *)

Lemma Z8toD8_0 : Z8toD8 Z80 = D80.
Proof. easy. Qed.

Lemma Z8toD8_1 : Z8toD8 Z81 = D81.
Proof. easy. Qed.

Lemma Z8toC_w : D8toC (Z8toD8 Z8w) = Cz8.
Proof. unfold D8toC, Z8toD8; simpl.
       rewrite Zdiv.Zdiv_0_l.
       lca.
Qed.  
       

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
  z1 + z2 = Z8plus z1 z2.
Proof. intros. 
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.
       unfold Z8toD8, D8toC, Z8plus; simpl.  
       repeat rewrite <- ZtoD_plus.
       repeat rewrite <- DtoC_plus.
       lca.
Qed.

(* this gets a bit ugly with all the replace's, but without a tactic, this is super efficient *)
Lemma Z8toC_mult : forall (z1 z2 : Z8),
  z1 * z2 = Z8mult z1 z2.
Proof. intros.  
       destruct z1; repeat destruct p; destruct z2; repeat destruct p.  
       unfold Z8toD8, D8toC, Z8mult, Zminus; simpl.
       replace (Cz8 * (Cz8 * (Cz8 * C1))) with (Cz8 ^ 3) by easy.  
       replace (Cz8 * (Cz8 * C1)) with (Cz8 ^ 2) by easy.    
       replace (DtoC (ZtoD z1)) with ((DtoC (ZtoD z1)) * (Cz8 ^ 0)) by lca. 
       replace (DtoC (ZtoD z5)) with ((DtoC (ZtoD z5)) * (Cz8 ^ 0)) by lca. 
       replace ((DtoC (ZtoD z3)) * Cz8) with ((DtoC (ZtoD z3)) * (Cz8 ^ 1)) by lca. 
       replace ((DtoC (ZtoD z6)) * Cz8) with ((DtoC (ZtoD z6)) * (Cz8 ^ 1)) by lca. 
       repeat rewrite Cmult_plus_distr_l.
       repeat rewrite Cmult_plus_distr_r.
       assert (H' : forall z1 z2 n1 n2, ZtoD z1 * Cz8 ^ n1 * (ZtoD z2 * Cz8 ^ n2) = 
                                   ZtoD (z1 * z2) * Cz8 ^ (n1 + n2)).
       { intros.
         replace (ZtoD z7 * Cz8 ^ n1 * (ZtoD z8 * Cz8 ^ n2)) with
           ((ZtoD z7 * ZtoD z8) * (Cz8 ^ n1 * Cz8 ^ n2)) by lca.
         rewrite DtoC_mult, ZtoD_mult, Cpow_add. 
         easy. }
       do 16 rewrite H'.
       simpl plus.
       repeat rewrite <- ZtoD_plus, <- DtoC_plus.
       repeat rewrite <- ZtoD_opp, <- DtoC_opp. 
       rewrite Cz8_pow4, Cz8_pow5, Cz8_pow6.
       lca.
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
 
(* TODO: perhaps also coerce Z into Z8? *)
Lemma Z8mult_z_l : forall (z : Z) (z1 : Z8), 
  Z8mult (z, 0, 0, 0)%Z z1 = (z * z1.1, z * z1.2, z * z1.3, z * z1.4)%Z.
Proof. intros. 
       destruct z1; repeat destruct p; simpl.
       repeat apply injective_projections; simpl; lia.
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







Definition root2 : Z8 := (0, 1, 0, -1)%Z.


Definition root2_recip : D8 := (D0, Dhalf, D0, -,Dhalf).


(* TODO: make this proof nice *)
Lemma root2_ver : D8toC (Z8toD8 root2) = RtoC (√ 2). 
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


Lemma Cdiv_root2 : / RtoC (√ 2) = RtoC (√ 2) / 2.
Proof. rewrite <- Csqrt2_sqrt.
       unfold Cdiv.
       rewrite Cinv_mult_distr, Cmult_assoc, Cinv_r. 
       lca.
       all : apply RtoC_neq; apply sqrt2_neq_0.
Qed.


Lemma root2_recip_ver : D8toC root2_recip = / RtoC (√ 2).
Proof. unfold root2_recip.

       replace (D0, Dhalf, D0, -, Dhalf) with 
         (Dhalf *, D0, Dhalf *, D1, Dhalf *, D0, Dhalf *, (-, D1)).
       rewrite Cdiv_root2, <- D8mult_d_l.
       rewrite D8toC_mult.

 unfold root2_recip, Z8toD8, D8toC; simpl fst; simpl snd.
       repeat rewrite ZtoDtoC_is_ZtoRtoC.
       rewrite Cmult_0_l, Cplus_0_l, Cplus_0_r.
       unfold Cz8; rewrite Cexp_pow.
       replace (PI / 4 * INR 3)%R with (3 * PI / 4)%R.
       rewrite Cexp_PI4, Cexp_3PI4.
       replace (DtoC (1%nat, 1%Z)) with (1/2)%C.
       replace (DtoC (1%nat, (-1)%Z)) with (- (1/2))%C.

       replace (C1 / C2 * (/ √ 2 + / √ 2 * Ci) + - (C1 / C2) * (- / √ 2 + / √ 2 * Ci)) 
         with (C1 / C2 * (2 / √ 2)) by lca.
       (* rewrite <- Csqrt2_sqrt.
       unfold Cdiv. 
       2 : { unfold DtoC. ; simpl.  Set Printing All.

       rewrite <- Cmult_assoc, Cinv_r. ; try lca.
       apply Csqrt2_neq_0.
       replace (INR 3) with (IZR 3). lra.
       unfold INR, IZR, IPR, IPR_2; lra. 
       *) Admitted. 

Lemma root2_sqr : Z8mult root2 root2 = (2, 0, 0, 0)%Z.
Proof. easy. Qed. 


Lemma root2_root2_recip : D8mult root2_recip root2 = ((2%nat,2), (2%nat,0), (2%nat,0), (2%nat,0))%Z.
Proof. repeat apply injective_projections; simpl; easy. Qed.





Definition D8toZ8 (d : D8) : Z8 :=
  (DtoZ d.1, DtoZ d.2, DtoZ d.3, DtoZ d.4).












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

(*

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
