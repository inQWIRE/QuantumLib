Require Export Bool.
Require Export Arith.
Require Export Reals.
Require Export Psatz.
Require Export Program.
Require Export List.

Export ListNotations.


(* Some more than basic nat lemmas that are useful to have *)

Lemma easy_sub : forall (n : nat), S n - 1 = n. Proof. lia. Qed.


Lemma easy_sub3 : forall (n k : nat), n <> 0 -> n + k - 0 - 1 = n - 0 - 1 + k. 
Proof. intros. 
       destruct n as [| n].
       - easy.
       - simpl. lia. 
Qed.

Lemma easy_sub6 : forall (a c b : nat), 
  b < c -> a < b -> c = (a + S (b - a) + (c - b - 1)).
Proof. intros. lia. Qed.




Lemma easy_pow : forall (a n m : nat), a^(n + m) = a^n * a^m.
Proof. intros. induction n as [| n'].
       - simpl. nia.
       - simpl. rewrite IHn'. nia.
Qed.
Lemma easy_pow2 : forall (a p : nat), p <> 0 -> a^p = a * a ^ (p - 0 - 1). 
Proof. intros. destruct p as [| p']. easy. simpl. 
       rewrite Nat.sub_0_r.  easy.
Qed.
Lemma easy_pow3 : forall (n m : nat), m < n -> 2^n = (2^m) * 2 * 2^(n - m - 1).
Proof. intros. 
       assert (H' : 2^m * 2 = 2^(m + 1)). 
       { rewrite easy_pow. reflexivity. } 
       rewrite H'. 
       rewrite <- easy_pow.
       assert (H'' : m < n -> m + 1 + (n - m - 1) = n).
       { nia. }
       rewrite H''. 
       reflexivity.
       assumption. 
Qed.
Lemma easy_pow4 : forall (n : nat), (0 >= 2^n) -> False. 
Proof. intros. induction n as [| n'].
       - simpl in *. nia.
       - simpl in *. 
         assert (H' : forall (a : nat), a + 0 = a). { nia. }
         rewrite H' in H.
         assert (H'' : forall (a : nat), a + a >= a). { nia. }
         apply IHn'.
         nia. 
Qed.
Lemma easy_pow5 : forall (a b c : nat), 
  b < c -> a < b ->
  2^c = (2^a * (2^(b - a) + (2^(b - a) + 0))) * 2^(c - b - 1).
Proof. intros.
       assert (H' : forall n, 2^n + (2^n + 0) = 2^(S n)).
       { reflexivity. } 
       rewrite H'.
       do 2 (rewrite <- easy_pow).  
       rewrite <- (easy_sub6 a c b); try easy.
Qed.
Lemma easy_pow5' : forall (a b c : nat), 
  b < c ->  a < b ->
  2^c = (2^a * (2^(b - a) * 2)) * 2^(c - b - 1).
Proof. intros.
       assert (H' : 2 ^ (b - a) * 2 = 2 ^ (b - a) * 2^1).
       { reflexivity. } 
       rewrite H'.
       do 3 (rewrite <- easy_pow).
       assert (H'' : b - a + 1 = S (b - a)). { nia. }
       rewrite H''.
       rewrite <- (easy_sub6 a c b); try easy.
Qed.
Lemma easy_pow6 : forall (n : nat), n <> 0 -> 2*2^n = (2*2^(n-1))*2. 
Proof. destruct n.
       - easy.
       - intros. 
         simpl.  
         replace (n - 0) with n by lia. 
         nia. 
Qed.

Lemma easy_pow6' : forall (n : nat), n <> 0 -> (2^n)*2 = (2*2^(n-1))*2. 
Proof. intros. rewrite mult_comm.
       apply easy_pow6; easy.
Qed.



(* Boolean notations, lemmas *)

Notation "¬ b" := (negb b) (at level 10).
Infix  "⊕" := xorb (at level 20).

Lemma xorb_nb_b : forall b, ¬ b ⊕ b = true. Proof. destruct b; easy. Qed.
Lemma xorb_b_nb : forall b, b ⊕ ¬ b = true. Proof. destruct b; easy. Qed.

Lemma xorb_involutive_l : forall b b', b ⊕ (b ⊕ b') = b'. Proof. destruct b, b'; easy. Qed.
Lemma xorb_involutive_r : forall b b', b ⊕ b' ⊕ b' = b. Proof. destruct b, b'; easy. Qed.

Lemma andb_xorb_dist : forall b b1 b2, b && (b1 ⊕ b2) = (b && b1) ⊕ (b && b2).
Proof. destruct b, b1, b2; easy. Qed.

(* A bit of useful reflection from Software Foundations Vol 3 *)

Lemma beq_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry.  apply beq_nat_true_iff.
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

Hint Resolve blt_reflect ble_reflect beq_reflect : bdestruct.

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


(* Distribute functions over lists *)

Lemma if_dist : forall (A B : Type) (b : bool) (f : A -> B) (x y : A), f (if b then x else y) = if b then f x else f y.
Proof. destruct b; reflexivity. Qed.

Lemma if_dist2 : forall (A B C : Type) (b : bool) (f : A -> B -> C) (x y : A) (z : B), f (if b then x else y) z = if b then f x z else f y z.
Proof. destruct b; reflexivity. Qed.

(* Generalizing f_equals *)

Lemma f_equal_inv : forall {A B} (x : A) (f g : A -> B), f = g -> f x = g x.
Proof. intros. rewrite H. easy. Qed.

Lemma f_equal2_inv : forall {A B C} x y (f g : A -> B -> C), f = g -> f x y = g x y.
Proof. intros. rewrite H. easy. Qed.

Lemma f_equal_gen : forall {A B} (f g : A -> B) a b, f = g -> a = b -> f a = g b.
Proof. intros. subst. reflexivity. Qed.

(* Currying *)

Definition curry {A B C : Type} (f : A * B -> C) : (A -> B -> C) :=
  fun x y => f (x,y).
Definition uncurry {A B C : Type} (f : A -> B -> C) : (A * B -> C) :=
  fun p => f (fst p) (snd p).

(* Lists *)

(* Precondition: x must appear in li *)
Fixpoint lookup (x : nat) (li : list nat) : nat :=
  match li with
  | nil => 0
  | y :: ys => if x =? y then 0 else S (lookup x ys)
  end.

(*
Fixpoint index {A} (i : nat) (li : list A) : option A :=
  match i, li with
  | _, nil => None
  | 0, x :: _ => Some x
  | S i', _ :: li' => index i' li'
  end.
*)
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

Fixpoint Injective {A} (ls : list A) :=
  match ls with
  | [] => True
  | x :: ls' => ~ In x ls' /\ Injective ls'
  end.
  
Lemma nth_nil : forall {A} x, ([] : list A) !! x = None.
Proof.
  destruct x; auto.
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

Lemma firstn_repeat_le : forall A (a : A) m n, (m <= n)%nat -> firstn m (repeat a n) = repeat a m.  
Proof.
  induction m; trivial.
  intros n L.
  destruct n; [inversion L|].  
  simpl.
  rewrite IHm by lia. 
  reflexivity.
Qed.

Lemma firstn_repeat_ge : forall A (a : A) m n, (m >= n)%nat -> firstn m (repeat a n) = repeat a n.  
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

Lemma firstn_repeat : forall A (a : A) m n, firstn m (repeat a n) = repeat a (min m n).  
Proof.
  intros.
  bdestruct (m <=? n).
  - rewrite firstn_repeat_le, Min.min_l; easy.
  - rewrite firstn_repeat_ge, Min.min_r; trivial; lia.
Qed.

Lemma skipn_repeat : forall A (a : A) m n, skipn m (repeat a n) = repeat a (n-m).
Proof.  
  induction m; intros n; simpl.
  - rewrite Nat.sub_0_r. reflexivity.
  - destruct n; trivial.
    simpl.
    apply IHm.
Qed.

Lemma skipn_length : forall {A} (l : list A) n, length (skipn n l) = (length l - n)%nat. 
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


(* option type *)

Definition maybe {A} (o : option A) (default : A) : A :=
  match o with
  | Some a => a
  | None => default
  end.



(************************************)
(* Helpful, general purpose tactics *)
(************************************)

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


(* From SF - up to five arguments *)
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


(***************)
(* Powers of 2 *)
(***************)

Lemma double_mult : forall (n : nat), (n + n = 2 * n)%nat. Proof. intros. lia. Qed.
Lemma pow_two_succ_l : forall x, (2^x * 2 = 2 ^ (x + 1))%nat.
Proof. intros. rewrite mult_comm. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma pow_two_succ_r : forall x, (2 * 2^x = 2 ^ (x + 1))%nat.
Proof. intros. rewrite <- Nat.pow_succ_r'. intuition. Qed.
Lemma double_pow : forall (n : nat), (2^n + 2^n = 2^(n+1))%nat. 
Proof. intros. rewrite double_mult. rewrite pow_two_succ_r. reflexivity. Qed.
Lemma pow_components : forall (a b m n : nat), a = b -> m = n -> (a^m = b^n)%nat.
Proof. intuition. Qed.
Lemma pow_positive : forall a b, a <> 0 -> 0 < a ^ b.
Proof. intros. induction b; simpl; try lia; 
  (* for Coq < 8.12 *)
  try (apply Nat.lt_0_mul'; split; lia). 
Qed.  


Ltac unify_pows_two :=
  repeat match goal with
  (* NB: this first thing is potentially a bad idea, do not do with 2^1 *)
  | [ |- context[ 4%nat ]]                  => replace 4%nat with (2^2)%nat by reflexivity
  | [ |- context[ (0 + ?a)%nat]]            => rewrite plus_0_l 
  | [ |- context[ (?a + 0)%nat]]            => rewrite plus_0_r 
  | [ |- context[ (1 * ?a)%nat]]            => rewrite Nat.mul_1_l 
  | [ |- context[ (?a * 1)%nat]]            => rewrite Nat.mul_1_r 
  | [ |- context[ (2 * 2^?x)%nat]]          => rewrite <- Nat.pow_succ_r'
  | [ |- context[ (2^?x * 2)%nat]]          => rewrite pow_two_succ_l
  | [ |- context[ (2^?x + 2^?x)%nat]]       => rewrite double_pow 
  | [ |- context[ (2^?x * 2^?y)%nat]]       => rewrite <- Nat.pow_add_r 
  | [ |- context[ (?a + (?b + ?c))%nat ]]   => rewrite plus_assoc 
  | [ |- (2^?x = 2^?y)%nat ]                => apply pow_components; try lia 
  end.



(* general subset to be used in Heisenberg.v *)
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

           
  
Infix "⊆" := subset_gen (at level 30, no associativity).


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


Hint Resolve subset_concat_l subset_concat_r subset_self subsets_add subset_trans : sub_db.


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


Hint Resolve firstn_subset skipn_subset : sub_db.

(******************************)
(* Some more basic list stuff *)
(******************************)


Definition zipWith {X Y Z: Type} (f : X -> Y -> Z) (As : list X) (Bs : list Y) : list Z :=
  map (uncurry f) (combine As Bs).


Lemma zipWith_len_pres : forall {X Y Z : Type} (f : X -> Y -> Z) (n : nat) 
                                (As : list X) (Bs : list Y),
  length As = n -> length Bs = n -> length (zipWith f As Bs) = n.
Proof. intros. 
       unfold zipWith.
       rewrite map_length.
       rewrite combine_length.
       rewrite H, H0; lia.
Qed.


Lemma zipWith_app_product : forall {X Y Z: Type} (f : X -> Y -> Z) (n : nat) 
                               (l0s l2s : list X) (l1s l3s : list Y),
  length l0s = n -> length l1s = n -> 
  (zipWith f l0s l1s) ++ (zipWith f l2s l3s) = zipWith f (l0s ++ l2s) (l1s ++ l3s).
Proof. induction n as [| n'].
       - intros. destruct l0s; destruct l1s; easy. 
       - intros. destruct l0s; destruct l1s; try easy.
         unfold zipWith in *.
         simpl in *. 
         rewrite <- IHn'; try nia. 
         reflexivity. 
Qed.


Lemma zipWith_cons : forall {X Y Z : Type} (f : X -> Y -> Z) (a : X) (b : Y) (A : list X) (B : list Y),
  zipWith f (a :: A) (b :: B) = (f a b) :: (zipWith f A B).
Proof. intros. 
       unfold zipWith. simpl. 
       unfold uncurry. 
       simpl. easy. 
Qed.


Fixpoint first_n (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => n :: first_n n'
  end.

Lemma first_n_contains : forall (n i : nat),
  i <= n <-> In i (first_n n).
Proof. split.
       - induction n as [| n'].
         * intros. bdestruct (i =? 0). 
           + rewrite H0. simpl. left. easy.
           + apply le_n_0_eq in H. rewrite H in H0. easy.
         * intros. simpl. bdestruct (i =? S n').
           + left. rewrite H0. easy. 
           + right. apply IHn'. 
             apply le_lt_eq_dec in H. destruct H.
             ** apply Nat.lt_succ_r. apply l.
             ** rewrite e in H0. easy.
       - induction n as [| n'].
         * intros [H | F]. 
           + rewrite H. easy.
           + simpl in F. easy.
         * intros. simpl in H. destruct H.
           + rewrite H. easy.
           + apply IHn' in H. 
             apply le_n_S in H. apply le_Sn_le.
             apply H.
Qed.


(* defining switch and many lemmas having to do with switch and nth *)

Fixpoint switch {X : Type} (ls : list X) (x : X) (n : nat) :=
  match ls with
  | [] => []
  | (h :: ls') =>
    match n with
    | 0 => x :: ls'
    | S n' => h :: (switch ls' x n')
    end
  end.

Lemma switch_len : forall {X : Type} (n : nat) (ls : list X) (x : X),
    length (switch ls x n) = length ls. 
Proof. induction n as [| n'].
       - destruct ls. easy. easy.
       - intros. destruct ls. 
         easy. simpl. 
         rewrite IHn'. 
         reflexivity. 
Qed.


Lemma switch_map : forall {X Y : Type} (n : nat) (ls : list X) (x : X) (f : X -> Y),
    map f (switch ls x n) = switch (map f ls) (f x) n.
Proof. induction n as [| n'].
       - intros. destruct ls; easy.
       - intros. destruct ls. easy.
         simpl. rewrite IHn'. easy.
Qed.
         
Lemma switch_switch_diff : forall {X : Type} (n m : nat) (ls : list X) (a b : X), 
  n <> m ->
  switch (switch ls a n) b m = switch (switch ls b m) a n.
Proof. induction n as [| n'].
       - intros. 
         destruct m; destruct ls; easy. 
       - intros. 
         destruct m; try (destruct ls; easy). 
         destruct ls; try easy. 
         simpl. 
         rewrite IHn'; try easy.
         bdestruct (n' =? m); lia. 
Qed.

Lemma switch_base : forall {X : Type} (ls : list X) (x : X),
    ls <> [] -> switch ls x 0 = x :: (skipn 1 ls).
Proof. intros. 
       destruct ls. 
       easy. 
       reflexivity. 
Qed.



Lemma nth_switch_hit : forall {X : Type} (n : nat) (ls : list X) (x def : X),
    n < length ls ->
    nth n (switch ls x n) def = x.
Proof. induction n as [| n'].
       - destruct ls; easy.
       - intros. 
         destruct ls; try easy.
         apply IHn'. 
         simpl in H.
         nia. 
Qed.



Lemma nth_switch_miss : forall {X : Type} (sn n : nat) (ls : list X) (x def : X),
    n <> sn ->
    nth n (switch ls x sn) def = nth n ls def.
Proof. induction sn as [| sn'].
       - destruct ls.
         easy.
         destruct n; easy.
       - intros. 
         destruct n.
         + destruct ls; easy.
         + assert (H' : n <> sn'). { nia. }
           destruct ls.                                   
           easy. simpl.  
           apply IHsn'.
           apply H'.
Qed.


Lemma switch_inc_helper : forall {X : Type} (n : nat) (l1 l2 : list X) (x : X),
    length l1 = n -> 
    switch (l1 ++ l2) x n = l1 ++ switch l2 x 0.
Proof. induction n as [| n'].
       - destruct l1. 
         reflexivity. 
         easy.
       - intros. destruct l1.  
         easy. 
         simpl. 
         rewrite <- IHn'.
         reflexivity. 
         simpl in H. 
         injection H. 
         easy. 
Qed.


Lemma switch_inc_helper2 : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch ls x n = (firstn n ls) ++ switch (skipn n ls) x 0.
Proof. intros. 
       assert (H' : switch ls x n = switch (firstn n ls ++ skipn n ls) x n).
       { rewrite (firstn_skipn n ls). reflexivity. }
       rewrite H'.
       rewrite switch_inc_helper.
       reflexivity. 
       rewrite firstn_length_le.
       reflexivity. 
       nia.  
Qed.



Lemma skipn_nil_length : forall {X : Type} (n : nat) (ls : list X),
    skipn n ls = [] -> length ls <= n. 
Proof. intros. 
       rewrite <- (firstn_skipn n ls).
       rewrite H. 
       rewrite <- app_nil_end.
       apply firstn_le_length.
Qed.


Lemma skipskip : forall {X : Type} (ls : list X) (n : nat),
    skipn (S n) ls = skipn 1 (skipn n ls).
Proof. induction ls as [| h].
       - destruct n. easy. easy. 
       - destruct n. easy.  
         assert (H : skipn (S n) (h :: ls) = skipn n ls). 
         { reflexivity. } 
         rewrite H.
         rewrite <- IHls. 
         reflexivity. 
Qed.


Lemma switch_inc_helper3 : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch (skipn n ls) x 0 = [x] ++ (skipn (S n) ls).
Proof. intros. destruct (skipn n ls) as [| h] eqn:E.
       - apply skipn_nil_length in E. nia. 
       - assert (H' : skipn (S n) ls = l).
         { rewrite skipskip. 
           rewrite E.
           reflexivity. }
         rewrite H'.
         reflexivity.
Qed.


Lemma switch_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch ls x n = (firstn n ls) ++ [x] ++ (skipn (S n) ls). 
Proof. intros. 
       rewrite switch_inc_helper2.
       rewrite switch_inc_helper3.
       reflexivity. 
       apply H. apply H.
Qed.


Lemma nth_base : forall {X : Type} (ls : list X) (x : X),
    ls <> [] -> ls = (nth 0 ls x) :: (skipn 1 ls).
Proof. intros.
       destruct ls.
       easy. 
       reflexivity. 
Qed.


Lemma nth_helper : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> skipn n ls = [nth n ls x] ++ skipn (S n) ls.
Proof. induction n as [| n']. 
       - destruct ls. easy. easy. 
       - intros. destruct ls. 
         assert (H' : forall (n : nat), S n < 0 -> False). { nia. }
         apply H' in H. easy.
         rewrite skipn_cons.
         assert (H'' : nth (S n') (x0 :: ls) x = nth n' ls x). { easy. }
         rewrite H''.
         rewrite (IHn' ls x). 
         easy. 
         simpl in H. 
         assert (H''' : forall (n m : nat), S m < S n -> m < n). { nia. } 
         apply H''' in H.
         easy.
Qed.
         


Lemma nth_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> ls = (firstn n ls) ++ [nth n ls x] ++ (skipn (S n) ls). 
Proof. intros.
       rewrite <- nth_helper.  
       rewrite (firstn_skipn n ls).
       reflexivity. easy. 
Qed.




Lemma length_change : forall {X : Type} (A B : list X) (x : X),
  2 ^ (length (A ++ [x] ++ B)) = (2 ^ (length A)) * (2 * (2 ^ (length B))).
Proof. intros. 
       do 2 (rewrite app_length).
       simpl. 
       rewrite easy_pow.
       reflexivity. 
Qed.




(* a similar lemma to the one defined by Coq, but better for our purposes *)
Lemma skipn_length' : forall {X : Type} (n : nat) (ls : list X),
    length (skipn (S n) ls) = length ls - n - 1.
Proof. intros. 
       rewrite skipn_length.
       nia. 
Qed.


