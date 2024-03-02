
Require Import Prelim. 
Require Export Summation.
Require Import FiniteGroups.
Require Import FinFun. 

(** defining ring homomorphisms *)

(* these could be classes *)
Inductive ring_homomorphism (H G : Type) `{Ring H} `{Ring G} (HtoG : H -> G) : Prop :=
| ring_homo :    
  HtoG 1 = 1 ->
  group_homomorphism H G HtoG ->
  (forall h1 h2, HtoG (h1 * h2) = HtoG h1 * HtoG h2) ->
  ring_homomorphism H G HtoG.


         
Inductive ring_inclusion_map (H G : Type) `{Ring H} `{Ring G}  (HtoG : H -> G) : Prop :=
| ring_inc : 
  Injective HtoG -> 
  ring_homomorphism H G HtoG ->
  ring_inclusion_map H G HtoG.


Definition sub_ring (H G : Type) `{Ring H} `{Ring G} : Prop :=
  exists f, inclusion_map H G f.


Lemma ring_homo_id : forall H G `{Ring H} `{Ring G} (HtoG : H -> G),
  ring_homomorphism H G HtoG -> HtoG 0 = 0.
Proof. intros.
       inversion H8; subst.
       apply homo_id in H10.
       easy.
Qed.

Lemma ring_homo_opp : forall H G `{Ring H} `{Ring G} (HtoG : H -> G) (h : H),
  ring_homomorphism H G HtoG -> HtoG (- h) = - (HtoG h).
Proof. intros. 
       inversion H8; subst.
       apply (homo_inv _ _ _ h) in H10.
       easy. 
Qed.

Lemma rim_implies_comm : forall H G `{Ring H} `{Comm_Ring G} (HtoG : H -> G) (a b : H),
  ring_inclusion_map H G HtoG -> 
  a * b = b * a.
Proof. intros. 
       inversion H9; inversion H11; subst. 
       apply H10.       
       do 2 rewrite H14.
       rewrite Gmult_comm; easy.
Qed.

Lemma rim_implies_Comm_Ring : forall H G `{Ring H} `{Comm_Ring G} (HtoG : H -> G) (a b : H),
  ring_inclusion_map H G HtoG -> 
  Comm_Ring H.
Proof. intros. 
       inversion H9; inversion H11; subst. 
       apply Build_Comm_Ring; intros. 
       eapply rim_implies_comm; try easy.
       apply H9.
Qed.



(** Showing that Z is a comm ring, the cononical example *)

Open Scope Z_scope. 

Global Program Instance Z_is_monoid : Monoid Z := 
  { Gzero := 0
  ; Gplus := Z.add
  }.
Solve All Obligations with program_simpl; try lia.

Global Program Instance Z_is_group : Group Z :=
  { Gopp := Z.opp }.
Solve All Obligations with program_simpl; try lia.

Global Program Instance Z_is_comm_group : Comm_Group Z.
Solve All Obligations with program_simpl; lia. 

Global Program Instance Z_is_ring : Ring Z :=
  { Gone := 1
  ; Gmult := Z.mul
  }.
Solve All Obligations with program_simpl; try lia. 
Next Obligation. destruct a; auto. Qed.
Next Obligation. apply Z.eq_dec. Qed.

Global Program Instance Z_is_comm_ring : Comm_Ring Z.
Solve All Obligations with program_simpl; lia. 

Global Program Instance Z_is_Domain : Domain Z.
Next Obligation. apply Z.neq_mul_0; easy. Qed.


Open Scope group_scope. 

(* now we begin to show that every ring contains a version of Z *)


Definition Z_to_F {F} `{Ring F} : Z -> F := times_z 1.


Lemma Z_to_F_homo : forall F `{Ring F}, ring_homomorphism Z F Z_to_F.
Proof. intros. 
       apply ring_homo; try easy.
       unfold group_homomorphism, Z_to_F; intros. 
       rewrite times_z_add_r; auto.
       intros. 
       unfold Z_to_F.
       rewrite <- times_z_mult; auto.
       rewrite Gmult_1_r; auto.
Qed.





(** * Defining Z mod nZ, the finite ring of n elements *)

Open Scope nat_scope.

Definition Zmodn (n : nat) : Type := {x : nat | x < n }.

Lemma Zmodn_add_wd : forall {n : nat} (a b : nat),
  (a + b) mod (S n) < S n.
Proof. intros.  
       apply Nat.mod_upper_bound.
       lia.
Qed.

Lemma Zmodn_opp_wd : forall {n : nat} (a : nat),
  (S n - a) mod (S n) < S n.
Proof. intros.  
       apply Nat.mod_upper_bound.
       lia.
Qed.

Lemma Zmodn_mul_wd : forall {n : nat} (a b : nat),
  (a * b) mod (S n) < S n.
Proof. intros. 
       apply Nat.mod_upper_bound.
       lia.
Qed.

Lemma Zmodn_1_wd : forall (n : nat), (1 mod S n) < (S n).
Proof. intros. 
       apply Nat.mod_upper_bound.
       lia.
Qed.


Definition Zmodn_add {n : nat} (a b : Zmodn (S n)) : Zmodn (S n) :=
  match a, b with
  | exist _ a' _, exist _ b' _ 
    => exist _ ((a' + b') mod (S n)) (Zmodn_add_wd a' b')
  end.  

Definition Zmodn_opp {n : nat} (a : Zmodn (S n)) : Zmodn (S n) :=
  match a with
  | exist _ a' _
    => exist _ ((S n - a') mod (S n)) (Zmodn_opp_wd a')
  end.  

Definition Zmodn_mul {n : nat} (a b : Zmodn (S n)) : Zmodn (S n) :=
  match a, b with
  | exist _ a' _, exist _ b' _ 
    => exist _ ((a' * b') mod (S n)) (Zmodn_mul_wd a' b')
  end. 

Definition Zmodn_0 {n : nat} : Zmodn (S n) := exist _ O (Nat.lt_0_succ n).

(* TODO: use 1 mod n so that we don't need to write S (S n)) *)
Definition Zmodn_1 {n : nat} : Zmodn (S n) := exist _ (1 mod S n) (Zmodn_1_wd n).

Lemma Zmodn_add_0_l : forall {n : nat} (a : Zmodn (S n)), Zmodn_add Zmodn_0 a = a.
Proof. intros. 
       destruct a. 
       unfold Zmodn_add, Zmodn_0.
       apply subset_eq_compat. 
       rewrite Nat.add_0_l, Nat.mod_small; auto.
Qed.

Lemma Zmodn_add_0_r : forall {n : nat} (a : Zmodn (S n)), Zmodn_add a Zmodn_0 = a.
Proof. intros. 
       destruct a. 
       unfold Zmodn_add, Zmodn_0.
       apply subset_eq_compat. 
       rewrite Nat.add_0_r, Nat.mod_small; auto.
Qed.

Lemma Zmodn_add_comm : forall {n : nat} (a b : Zmodn (S n)), 
  Zmodn_add a b = Zmodn_add b a.
Proof. intros. 
       unfold Zmodn_add; destruct a; destruct b.
       apply subset_eq_compat. 
       rewrite Nat.add_comm.
       easy.
Qed.

Lemma Zmodn_add_assoc : forall {n : nat} (a b c : Zmodn (S n)), 
  Zmodn_add a (Zmodn_add b c) = Zmodn_add (Zmodn_add a b) c.
Proof. intros. 
       unfold Zmodn_add; destruct a; destruct b; destruct c.
       apply subset_eq_compat. 
       rewrite Nat.add_mod_idemp_r, Nat.add_mod_idemp_l; auto.
       apply f_equal_gen; auto; try apply f_equal.
       lia.
Qed.

Lemma Zmodn_opp_l : forall {n : nat} (a : Zmodn (S n)), 
  Zmodn_add (Zmodn_opp a) a = Zmodn_0.
Proof. intros. 
       destruct a. 
       unfold Zmodn_add, Zmodn_opp, Zmodn_0.
       apply subset_eq_compat. 
       destruct x.
       rewrite Nat.sub_0_r, Nat.mod_same; simpl; lia.  
       rewrite (Nat.mod_small (S n - S x)), Nat.sub_add, Nat.mod_same; try lia.
Qed.

Lemma Zmodn_opp_r : forall {n : nat} (a : Zmodn (S n)), 
  Zmodn_add a (Zmodn_opp a) = Zmodn_0.
Proof. intros. 
       destruct a. 
       unfold Zmodn_add, Zmodn_opp, Zmodn_0.
       apply subset_eq_compat. 
       destruct x.
       rewrite Nat.sub_0_r, Nat.mod_same; simpl; lia.  
       rewrite (Nat.mod_small (S n - S x)), <- le_plus_minus', Nat.mod_same; try lia.
Qed.

Lemma Zmodn_mul_1_l : forall {n : nat} (a : Zmodn (S n)), 
  Zmodn_mul Zmodn_1 a = a. 
Proof. intros. 
       destruct a. 
       unfold Zmodn_mul, Zmodn_opp, Zmodn_1.
       apply subset_eq_compat. 
       destruct n.
       destruct x; simpl; lia. 
       rewrite Nat.mod_1_l, Nat.mul_1_l, Nat.mod_small; try lia. 
Qed.

Lemma Zmodn_mul_1_r : forall {n : nat} (a : Zmodn (S n)), 
  Zmodn_mul a Zmodn_1 = a. 
Proof. intros. 
       destruct a. 
       unfold Zmodn_mul, Zmodn_opp, Zmodn_1.
       apply subset_eq_compat. 
       destruct n.
       destruct x; simpl; lia. 
       rewrite Nat.mod_1_l, Nat.mul_1_r, Nat.mod_small; try lia. 
Qed.

Lemma Zmodn_mul_comm : forall {n : nat} (a b : Zmodn (S n)), 
  Zmodn_mul a b = Zmodn_mul b a.
Proof. intros. 
       unfold Zmodn_mul; destruct a; destruct b.
       apply subset_eq_compat. 
       rewrite Nat.mul_comm.
       easy.
Qed.

Lemma Zmodn_mul_assoc : forall {n : nat} (a b c : Zmodn (S n)), 
  Zmodn_mul a (Zmodn_mul b c) = Zmodn_mul (Zmodn_mul a b) c.
Proof. intros. 
       unfold Zmodn_mul; destruct a; destruct b; destruct c.
       apply subset_eq_compat. 
       rewrite Nat.mul_mod_idemp_r, Nat.mul_mod_idemp_l; auto.
       apply f_equal_gen; auto; try apply f_equal.
       lia.
Qed.

Lemma Zmodn_mul_add_distr_l : forall {n : nat} (a b c : Zmodn (S n)),
  Zmodn_mul c (Zmodn_add a b) = Zmodn_add (Zmodn_mul c a) (Zmodn_mul c b).
Proof. intros. 
       unfold Zmodn_mul, Zmodn_add; destruct a; destruct b; destruct c.
       apply subset_eq_compat. 
       rewrite Nat.mul_mod_idemp_r, Nat.add_mod_idemp_l, Nat.add_mod_idemp_r; auto.
       apply f_equal_gen; auto; try apply f_equal.
       lia.
Qed.

Lemma Zmodn_mul_add_distr_r : forall {n : nat} (a b c : Zmodn (S n)),
  Zmodn_mul (Zmodn_add a b) c = Zmodn_add (Zmodn_mul a c) (Zmodn_mul b c).
Proof. intros. 
       unfold Zmodn_mul, Zmodn_add; destruct a; destruct b; destruct c.
       apply subset_eq_compat. 
       rewrite Nat.mul_mod_idemp_l, Nat.add_mod_idemp_r, Nat.add_mod_idemp_l; auto.
       apply f_equal_gen; auto; try apply f_equal.
       lia.
Qed.

Lemma Zmodn_eq_dec : forall {n : nat} (a b : Zmodn (S n)), { a = b } + { a <> b }.
Proof. intros. 
       destruct a; destruct b.
       bdestruct (x =? x0).
       left; subst.
       apply subset_eq_compat; auto.
       right. 
       unfold not; intros; apply H.
       apply EqdepFacts.eq_sig_fst in H0; auto.
Qed.


(** * Showing that C is a field, and a vector space over itself *)
            
Global Program Instance Zmodn_is_monoid : forall n, Monoid (Zmodn (S n)) := 
  { Gzero := Zmodn_0
  ; Gplus := Zmodn_add 
  }. 
Next Obligation. apply Zmodn_add_0_l. Qed.
Next Obligation. apply Zmodn_add_0_r. Qed.
Next Obligation. apply Zmodn_add_assoc. Qed.

Global Program Instance Zmodn_is_group : forall n, Group (Zmodn (S n)) :=
  { Gopp := Zmodn_opp }.
Next Obligation. apply Zmodn_opp_l. Qed.
Next Obligation. apply Zmodn_opp_r. Qed.
        
Global Program Instance Zmodn_is_comm_group : forall n, Comm_Group (Zmodn (S n)).
Next Obligation. apply Zmodn_add_comm. Qed. 

Global Program Instance Zmodn_is_ring : forall n, Ring (Zmodn (S n)) :=
  { Gone := Zmodn_1
  ; Gmult := Zmodn_mul
  }.
Next Obligation. apply Zmodn_mul_1_l. Qed.
Next Obligation. apply Zmodn_mul_1_r. Qed.
Next Obligation. apply Zmodn_mul_assoc. Qed.
Next Obligation. apply Zmodn_mul_add_distr_l. Qed.
Next Obligation. apply Zmodn_mul_add_distr_r. Qed.
Next Obligation. apply Zmodn_eq_dec. Qed.

Global Program Instance Zmodn_is_comm_ring : forall n, Comm_Ring (Zmodn (S n)).
Next Obligation. apply Zmodn_mul_comm. Qed.








(* 
 *
 *
 *)
