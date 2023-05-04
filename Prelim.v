 
 
(** This file contains basic utility, definitions, and proofs. *)

Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export Program. 
Require Export List.

Export ListNotations.


(* a lemma that was removed from Coq in 8.16 that I found quite helpful *)
Lemma le_plus_minus' : forall m n, m <= n -> n = m + (n - m).
Proof. lia. Qed.



(***)


(** Boolean notation, lemmas *)

Notation "¬ b" := (negb b) (at level 75, right associativity). (* Level/associativity defined such that it does not clash with the standard library *)
Infix  "⊕" := xorb (at level 20).


Lemma xorb_nb_b : forall b, (¬ b) ⊕ b = true. Proof. destruct b; easy. Qed.
Lemma xorb_b_nb : forall b, b ⊕ (¬ b) = true. Proof. destruct b; easy. Qed.


Lemma xorb_involutive_l : forall b b', b ⊕ (b ⊕ b') = b'. Proof. destruct b, b'; easy. Qed.
Lemma xorb_involutive_r : forall b b', b ⊕ b' ⊕ b' = b. Proof. destruct b, b'; easy. Qed.

Lemma andb_xorb_dist : forall b b1 b2, b && (b1 ⊕ b2) = (b && b1) ⊕ (b && b2).
Proof. destruct b, b1, b2; easy. Qed.

(** Nat lemmas *)

Lemma Sn_minus_1 : forall (n : nat), S n - 1 = n. Proof. lia. Qed.

(** Useful reflections from Software Foundations Vol 3 *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply Nat.eqb_eq.
Qed.

Lemma blt_reflect : forall x y, reflect (x < y) (x <? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.ltb_lt.
Qed.

Lemma ble_reflect : forall x y, reflect (x <= y) (x <=? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.leb_le.
Qed.

#[export] Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

Ltac bdestructΩ X := bdestruct X; simpl; try lia.

Ltac bdestruct_all :=
  repeat match goal with
  | |- context[?a <? ?b] => bdestruct (a <? b)
  | |- context[?a <=? ?b] => bdestruct (a <=? b)                                       
  | |- context[?a =? ?b] => bdestruct (a =? b)
  end; try (exfalso; lia).

(** Distribute functions over conditional *)

Lemma if_dist : forall (A B : Type) (b : bool) (f : A -> B) (x y : A), 
  f (if b then x else y) = if b then f x else f y.
Proof. destruct b; reflexivity. Qed.

(** Generalizations of f_equals *)

Lemma f_equal_inv : forall {A B} (x : A) (f g : A -> B), f = g -> f x = g x.
Proof. intros. rewrite H. easy. Qed.

Lemma f_equal2_inv : forall {A B C} x y (f g : A -> B -> C), f = g -> f x y = g x y.
Proof. intros. rewrite H. easy. Qed.

Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.

(** Currying *)

Definition curry {A B C : Type} (f : A * B -> C) : (A -> B -> C) :=
  fun x y => f (x,y).

Definition uncurry {A B C : Type} (f : A -> B -> C) : (A * B -> C) :=
  fun p => f (fst p) (snd p).

(** Lists *)

Notation "l !! i" := (nth_error l i) (at level 20).

Fixpoint remove_at {A} (i : nat) (ls : list A) :=
  match i, ls with
  | _   ,[]        => []
  | 0   , _ :: ls' => ls'
  | S i', a :: ls' => a :: remove_at i' ls'
  end.

Fixpoint update_at {A} (ls : list A) (i : nat) (a : A) : list A :=
  match ls, i with
  | []      , _    => []
  | _ :: ls', 0    => a :: ls'
  | b :: ls', S i' => b :: update_at ls' i' a
  end.

Lemma update_length : forall A (l: list A) (a : A) (n : nat), 
    length (update_at l n a) = length l.
Proof.
  induction l; auto. 
  simpl.
  destruct n.
  easy.
  simpl.
  rewrite IHl; easy.
Qed.

Lemma repeat_combine : forall A n1 n2 (a : A), 
  List.repeat a n1 ++ List.repeat a n2 = List.repeat a (n1 + n2).
Proof.
  induction n1; trivial. 
  intros. simpl. 
  rewrite IHn1.
  reflexivity.
Qed.

Lemma rev_repeat : forall A (a : A) n, rev (repeat a n) = repeat a n.
Proof.
  induction n; simpl; trivial.
  rewrite IHn.
  rewrite (repeat_combine A n 1).
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

Lemma firstn_repeat_le : forall A (a : A) m n, (m <= n)%nat -> 
  firstn m (repeat a n) = repeat a m.  
Proof.
  induction m; trivial.
  intros n L.
  destruct n; [inversion L|].  
  simpl.
  rewrite IHm by lia. 
  reflexivity.
Qed.

Lemma firstn_repeat_ge : forall A (a : A) m n, (m >= n)%nat -> 
  firstn m (repeat a n) = repeat a n.  
Proof.
  intros A a m n H.
  generalize dependent m.
  induction n; intros m L; simpl.
  - apply firstn_nil.
  - destruct m; [inversion L|].
    simpl.
    rewrite IHn by lia.
    reflexivity.
Qed.

Lemma firstn_repeat : forall A (a : A) m n, 
  firstn m (repeat a n) = repeat a (min m n).  
Proof.
  intros.
  bdestruct (m <=? n).
  - rewrite firstn_repeat_le, Nat.min_l; easy.
  - rewrite firstn_repeat_ge, Nat.min_r; trivial; lia.
Qed.

Lemma skipn_repeat : forall A (a : A) m n, 
  skipn m (repeat a n) = repeat a (n-m).
Proof.  
  induction m; intros n; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct n; trivial.
    simpl.
    apply IHm.
Qed.

Lemma skipn_length : forall {A} (l : list A) n, 
  length (skipn n l) = (length l - n)%nat. 
Proof.
  Transparent skipn.
  intros A l.
  induction l.
  intros [|n]; easy.
  intros [|n].
  easy.
  simpl.
  rewrite IHl.
  easy.
  Opaque skipn.
Qed.

Lemma nth_firstn : forall {A} i n (l : list A) d,
  (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A i n l d Hi.
  generalize dependent n.
  generalize dependent i.
  induction l; intros i n Hi.
  rewrite firstn_nil.
  reflexivity.
  destruct n. lia.
  rewrite firstn_cons.
  simpl.
  destruct i.
  reflexivity.
  apply IHl.
  lia.
Qed.

(** Option type *)

Definition maybe {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.

(** General purpose tactics *)

Ltac simpl_rewrite lem :=
  let H := fresh "H" in 
  specialize lem as H; simpl in H; rewrite H; clear H.

Ltac simpl_rewrite' lem := 
  let H := fresh "H" in
  specialize lem as H; simpl in H; rewrite <- H; clear H.

Ltac simpl_rewrite_h lem hyp := 
  let H := fresh "H" in
  specialize lem as H; simpl in H; rewrite <- H in hyp; clear H.

Ltac apply_with_obligations H :=
  match goal with
  | [|- ?P ?a]    => match type of H with ?P ?a' => 
    replace a with a'; [apply H|]; trivial end
  | [|- ?P ?a ?b] => match type of H with ?P ?a' ?b' => 
    replace a with a'; [replace b with b'; [apply H|]|]; trivial end
  | [|- ?P ?a ?b ?c ] => match type of H with ?P ?a' ?b' ?c' => 
    replace a with a'; [replace b with b'; [replace c with c'; [apply H|]|]|]; trivial end
  | [|- ?P ?a ?b ?c ?d] => match type of H with ?P ?a' ?b' ?c' ?d' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [apply H|]|]|]|]; trivial end
  | [|- ?P ?a ?b ?c ?d ?e] => match type of H with ?P ?a' ?b' ?c' ?d' ?e' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [replace e with e'; [apply H|]|]|]|]|]; 
    trivial end 
  | [|- ?P ?a ?b ?c ?d ?e ?f] => match type of H with ?P ?a' ?b' ?c' ?d' ?e' ?f' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [replace e with e'; [replace f with f'; 
    [apply H|]|]|]|]|]|]; trivial end 
  | [|- ?P ?a ?b ?c ?d ?e ?f ?g] => match type of H with ?P ?a' ?b' ?c' ?d' ?e' ?f' ?g' => 
    replace a with a'; [replace b with b'; [replace c with c'; [replace d with d'; [replace e with e'; [replace f with f'; 
    [replace g with g'; [apply H|]|]|]|]|]|]|]; trivial end 
  end.

(** From SF - up to five arguments *)
Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.

(** Powers of 2 *)

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. lia. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite Nat.mul_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.
Lemma pow_positive : forall a b, a <> 0 -> 0 < a ^ b.
Proof. intros. induction b; simpl; lia. Qed.  

Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite Nat.add_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite Nat.add_0_r 
  | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
  | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite Nat.add_assoc
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
  end.

(** Subsets *)

Definition subset_gen {X : Type} (l1 l2 : list X) :=
  forall (x : X), In x l1 -> In x l2.

(* an alternate version of subset *)
Fixpoint subset_gen' {X : Type} (l1 l2 : list X) :=
  match l1 with
  | [] => True
  | (l :: l1') => In l l2 /\ subset_gen' l1' l2
  end.

Lemma subset_is_subset' : forall (X : Type) (l1 l2 : list X),
    subset_gen' l1 l2 <-> subset_gen l1 l2.
Proof. intros X l1 l2. split.
       - induction l1 as [| l].
         * easy.
         * simpl. intros [H1 H2].
           unfold subset_gen'. intros x. simpl. intros [H3 | H4].
           + rewrite H3 in H1. apply H1.
           + apply IHl1 in H2. unfold subset_gen' in H2. 
             apply H2. apply H4.
       - induction l1 as [| l].
         * easy. 
         * unfold subset_gen'. intros H.
           simpl. split.
           + apply H. simpl. left. reflexivity.
           + apply IHl1. unfold subset_gen'. 
             intros x H'. apply H. simpl. 
             right. apply H'.
Qed.           

Infix "⊆" := subset_gen (at level 70, no associativity).

Lemma subset_cons : forall (X : Type) (l1 l2 : list X) (x : X),
  l1 ⊆ l2 -> l1 ⊆ (x :: l2).
Proof. intros X l1 l2 x.
       intros H.
       intros x0 H0.
       simpl; right.
       apply H; apply H0.
Qed.

Lemma subset_concat_l : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l1 ++ l2).
Proof. intros X l1 l2.
       intros x H.
       apply in_or_app.
       left; apply H.
Qed.

Lemma subset_concat_r : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l2 ++ l1).
Proof. intros X l1 l2.
       intros x H.
       apply in_or_app.
       right; apply H.
Qed.

Corollary subset_self : forall (X : Type) (l1 : list X),
  l1 ⊆ l1. 
Proof. intros X l1. assert (H: l1 ⊆ (l1 ++ [])). { apply subset_concat_l. }
       rewrite <- app_nil_end in H. apply H. 
Qed.

Lemma subsets_add : forall (X : Type) (l1 l2 l3 : list X),
  l1 ⊆ l3 -> l2 ⊆ l3 -> (l1 ++ l2) ⊆ l3.
Proof. intros X l1 l2 l3.
       intros H1 H2 x H.
       apply in_app_or in H.
       destruct H as [Hl1 | Hl2].
       - apply H1; apply Hl1.
       - apply H2; apply Hl2.
Qed.

Lemma subset_trans : forall (X : Type) (l1 l2 l3 : list X),
    l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3.
Proof. intros X l1 l2 l3.
       intros H1 H2. 
       intros x H.
       apply H1 in H; apply H2 in H.
       apply H.
Qed.

#[export] Hint Resolve subset_concat_l subset_concat_r subset_self 
                       subsets_add subset_trans : sub_db.

Lemma firstn_subset : forall {X : Type} (n : nat) (ls : list X),
    firstn n ls ⊆ ls.
Proof. induction n as [| n']. 
       - easy.
       - intros. destruct ls. 
         easy. simpl. 
         unfold subset_gen in *.
         intros. 
         destruct H as [H | H].
         left; easy. 
         right; apply IHn'; apply H.
Qed.

Lemma skipn_subset : forall {X : Type} (n : nat) (ls : list X),
    skipn n ls ⊆ ls.
Proof. induction n as [| n']. 
       - easy.
       - intros. destruct ls. 
         easy. simpl. 
         unfold subset_gen in *.
         intros. 
         right; apply IHn'; apply H.
Qed.

#[export] Hint Resolve firstn_subset skipn_subset : sub_db.





(** Defining 2-adic valuation of an integer and properties *)

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


Lemma two_val_pos_mult : forall (p1 p2 : positive),
  two_val_pos (p1 * p2) = two_val_pos p1 + two_val_pos p2.
Proof. induction p1; try easy; intros. 
       - replace (two_val_pos p1~1) with 0 by easy.
         induction p2; try easy.
         replace ((xI p1) * (xO p2))%positive with (xO ((xI p1) * p2))%positive by lia.
         replace (two_val_pos (xO ((xI p1) * p2))%positive) with 
           (1 + (two_val_pos ((xI p1) * p2)%positive)) by easy.
         rewrite IHp2; easy.
       - replace (two_val_pos (xO p1)) with (1 + two_val_pos p1) by easy.
         rewrite <- Z.add_assoc, <- IHp1.
         replace ((xO p1) * p2)%positive with (xO (p1 * p2))%positive by lia.
         easy.
Qed.

(* TODO: prove at some point, don't actually need this now though. *)
(*
Lemma two_val_pos_plus : forall (p1 p2 : positive),
  two_val_pos (p1 + p2) >= Z.min (two_val_pos p1) (two_val_pos p2).
Proof. induction p1; try easy; intros.
       - replace (two_val_pos p1~1) with 0 by easy.
         induction p2; try easy.
         replace ((xI p1) * (xO p2))%positive with (xO ((xI p1) * p2))%positive by lia.
         replace (two_val_pos (xO ((xI p1) * p2))%positive) with 
           (1 + (two_val_pos ((xI p1) * p2)%positive)) by easy.
         rewrite IHp2; easy.
       - replace (two_val_pos (xO p1)) with (1 + two_val_pos p1) by easy.
         rewrite <- Z.add_assoc, <- IHp1.
         replace ((xO p1) * p2)%positive with (xO (p1 * p2))%positive by lia.
         easy.
Qed. *)




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


(* useful for below since its easier to induct on nats rather than ints *)
Coercion Z.of_nat : nat >-> Z.

(* helper for the next section to go from nats to ints *)
Lemma Z_plusminus_nat : forall z : Z, 
  (exists n : nat, z = n \/ z = - n)%Z.
Proof. intros. 
       destruct z.
       - exists O; left; easy.
       - exists (Pos.to_nat p); left; lia.
       - exists (Pos.to_nat p); right; lia.
Qed.

Lemma two_val_mult : forall (z1 z2 : Z),
  z1 <> 0 -> z2 <> 0 ->
  two_val (z1 * z2) = two_val z1 + two_val z2.
Proof. intros.
       destruct z1; destruct z2; simpl; try easy.
       all : rewrite two_val_pos_mult; easy.
Qed.
         
(* TODO: should prove this, but don't actually need it. 
Lemma two_val_plus : forall (z1 z2 : Z),
  z1 <> 0 -> z2 <> 0 -> 
  z1 + z2 <> 0 ->
  two_val (z1 + z2) >= Z.min (two_val z1) (two_val z2).
Proof. intros.
       destruct z1; destruct z2; try easy.
*)
       


Lemma two_val_odd_part : forall (z : Z),
  two_val (2 * z + 1) = 0.
Proof. intros. 
       destruct z; auto.
       destruct p; auto.
Qed.

Lemma two_val_even_part : forall (a : Z),
  a >= 0 -> two_val (2 ^ a) = a.
Proof. intros.
       destruct (Z_plusminus_nat a) as [x [H0 | H0]]; subst.
       induction x; auto.
       replace (S x) with (1 + x)%nat by lia.
       rewrite Nat2Z.inj_add, Z.pow_add_r, two_val_mult; try lia.
       rewrite IHx; auto; try lia.
       try (apply (Z.pow_nonzero 2 x); lia).
       induction x; auto.
       replace (S x) with (1 + x)%nat by lia.
       rewrite Nat2Z.inj_add, Z.opp_add_distr, Z.pow_add_r, two_val_mult; try lia.
Qed.

Lemma twoadic_nonzero : forall (a b : Z),
  a >= 0 -> 2^a * (2 * b + 1) <> 0.
Proof. intros. 
       apply Z.neq_mul_0; split; try lia;
       try (apply Z.pow_nonzero; lia).
Qed.

Lemma get_two_val : forall (a b : Z),
  a >= 0 -> 
  two_val (2^a * (2 * b + 1)) = a.
Proof. intros. 
       rewrite two_val_mult; auto.
       rewrite two_val_odd_part, two_val_even_part; try lia.
       apply Z.pow_nonzero; try lia.
       lia.
Qed.       

Lemma odd_part_reduce : forall (a : Z),
  odd_part (2 * a) = odd_part a.
Proof. intros.
       induction a; try easy.
Qed.

Lemma get_odd_part : forall (a b : Z),
  a >= 0 -> 
  odd_part (2^a * (2 * b + 1)) = 2 * b + 1.
Proof. intros. 
       destruct (Z_plusminus_nat a) as [x [H0 | H0]]; subst.
       induction x; try easy.
       - replace (2 ^ 0%nat * (2 * b + 1)) with (2 * b + 1) by lia.
         destruct b; simpl; auto.
         induction p; simpl; easy.
       - replace (2 ^ S x * (2 * b + 1)) with (2 * (2 ^ x * (2 * b + 1))).
         rewrite odd_part_reduce, IHx; try lia.
         replace (S x) with (1 + x)%nat by lia.
         rewrite Nat2Z.inj_add, Z.pow_add_r; try lia.
       - destruct x; try easy.
         replace (2 ^ (- 0%nat) * (2 * b + 1)) with (2 * b + 1) by lia.
         destruct b; simpl; auto.
         induction p; simpl; easy.
Qed.       

Lemma break_into_parts : forall (z : Z),
  z <> 0 -> exists a b, a >= 0 /\ z = (2^a * (2 * b + 1)).
Proof. intros. 
       destruct z; try easy.
       - induction p.
         + exists 0, (Z.pos p); try easy.
         + destruct IHp as [a [b [H0 H1]]]; try easy.
           exists (1 + a), b.
           replace (Z.pos (xO p)) with (2 * Z.pos p) by easy.
           split; try lia.
           rewrite H1, Z.pow_add_r; try lia.
         + exists 0, 0; split; try lia.
       - induction p.
         + exists 0, (Z.neg p - 1); try easy; try lia.
         + destruct IHp as [a [b [H0 H1]]]; try easy.
           exists (1 + a), b.
           replace (Z.neg (xO p)) with (2 * Z.neg p) by easy.
           split; try lia.
           rewrite H1, Z.pow_add_r; try lia.
         + exists 0, (-1); split; try lia.
Qed.

Lemma twoadic_breakdown : forall (z : Z),
  z <> 0 -> z = (2^(two_val z)) * (odd_part z).
Proof. intros. 
       destruct (break_into_parts z) as [a [b [H0 H1]]]; auto.
       rewrite H1, get_two_val, get_odd_part; easy.
Qed.

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

Lemma odd_part_0 : forall (z : Z),
  odd_part z = 0 -> z = 0.
Proof. intros.
       destruct z; simpl in *; easy.
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
     

(*
 *
 *
 *)

Close Scope Z_scope.
