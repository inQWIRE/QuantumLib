Require Export CauchySchwarz.
Require Import Modulus.

Local Open Scope nat_scope. 

(* General facts about (nat -> A) functions.

   TODO #1: These lemmas are probably already defined in Coq somewhere.
   TODO #2: For efficiency, instead of using functions indexed by natural
            numbers, we should use vectors/arrays. *)

(* update_at is the same function on lists.
   update is also defined in SF. *)

(* Update the value at one index of a boolean function. *)
Definition update {A} (f : nat -> A) (i : nat) (x : A) :=
  fun j => if j =? i then x else f j.

Lemma update_index_eq : forall {A} (f : nat -> A) i b, (update f i b) i = b.
Proof.
  intros. 
  unfold update.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma update_index_neq : forall {A} (f : nat -> A) i j b, i <> j -> (update f i b) j = f j.
Proof.
  intros. 
  unfold update.
  bdestruct_all; auto. 
Qed.

Lemma update_same : forall {A} (f : nat -> A) i b,
  b = f i -> update f i b = f.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.

Lemma update_twice_eq : forall {A} (f : nat -> A) i b b',
  update (update f i b) i b' = update f i b'.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); subst; reflexivity.
Qed.  

Lemma update_twice_neq : forall {A} (f : nat -> A) i j b b',
  i <> j -> update (update f i b) j b' = update (update f j b') i b.
Proof.
  intros.
  apply functional_extensionality.
  intros.
  unfold update.
  bdestruct (x =? i); bdestruct (x =? j); subst; easy.
Qed.

Definition shift {A} (f : nat -> A) k := fun i => f (i + k).

Lemma shift_0 : forall {A} (f : nat -> A), shift f 0 = f.
Proof.
  intros A f.
  unfold shift.
  apply functional_extensionality; intro x.
  rewrite Nat.add_0_r.
  reflexivity.
Qed.

Lemma shift_plus : forall {A} (f : nat -> A) i j, shift (shift f j) i = shift f (i + j).
Proof.
  intros A f i j.
  unfold shift.
  apply functional_extensionality; intro x.
  rewrite Nat.add_assoc.
  reflexivity.
Qed.

Lemma shift_simplify : forall {A} (f : nat -> A) i j ,
  shift f i j = f (j + i).
Proof. intros. unfold shift. reflexivity. Qed.

Definition fswap {A} (f : nat -> A) x y :=
  fun i => if i =? x then f y else if i =? y then f x else f i.

Lemma fswap_simpl1 : forall A f x y, @fswap A f x y x = f y.
Proof. 
  intros. 
  unfold fswap. 
  rewrite Nat.eqb_refl. 
  reflexivity. 
Qed.

Lemma fswap_simpl2 : forall A f x y, @fswap A f x y y = f x.
Proof. 
  intros.
  unfold fswap. 
  bdestruct (y =? x).
  subst. reflexivity.
  rewrite Nat.eqb_refl. 
  reflexivity. 
Qed.

Lemma fswap_same : forall A f x, @fswap A f x x = f.
Proof.
  intros.
  unfold fswap.
  apply functional_extensionality.
  intro i.
  bdestruct_all; auto.
Qed.

Lemma fswap_neq : forall {A} (f : nat -> A) a b x, a <> x -> b <> x -> fswap f a b x = f x.
Proof.
  intros. unfold fswap. bdestructΩ (x =? a). bdestructΩ (x =? b). auto.
Qed.

Lemma fswap_rewrite : forall {A} (f : nat -> A) a b, 
  fswap f a b = update (update f b (f a)) a (f b).
Proof.
  intros.
  unfold fswap.
  apply functional_extensionality.
  intro x.
  bdestruct_all; subst.
  rewrite update_index_eq; auto.
  rewrite update_index_neq by lia.
  rewrite update_index_eq; auto.
  rewrite update_index_neq by lia.
  rewrite update_index_neq by lia.
  reflexivity.
Qed.

Lemma fswap_involutive : forall {A} (f : nat -> A) x y,
  fswap (fswap f x y) x y = f.
Proof.
  intros A f x y.
  unfold fswap.
  apply functional_extensionality.
  intros k.
  bdestruct_all; subst; easy.
Qed.

(* f_to_vec and basis_vector allow us to represent the same set of states.
   To prove this we need lemmas about converting between natural numbers
   and their binary representation. *)

(* takes [1;1;0;0] to 3, [0;0;1;0] to 4 *)
Local Coercion Nat.b2n : bool >-> nat.

Fixpoint binlist_to_nat (l : list bool) : nat :=
  match l with
  | [] => 0
  | b :: l' => b + 2 * binlist_to_nat l'
  end.

Fixpoint funbool_to_list (len : nat) (f : nat -> bool) :=
  match len with
  | O => []
  | S len' => f len' :: funbool_to_list len' f
  end.

Definition funbool_to_nat (len : nat) (f : nat -> bool) :=
  binlist_to_nat (funbool_to_list len f).

Lemma funbool_to_nat_bound : forall n f, (funbool_to_nat n f < 2 ^ n)%nat.
Proof.
  intros n f.
  unfold funbool_to_nat.
  induction n; simpl. lia.
  destruct (f n); simpl; lia.
Qed.

Lemma funbool_to_nat_eq : forall n f f',
  (forall x, x < n -> f x = f' x)%nat ->
  funbool_to_nat n f = funbool_to_nat n f'.
Proof.
  intros.
  unfold funbool_to_nat.
  apply f_equal.
  induction n.
  reflexivity.
  simpl.
  rewrite H by lia.
  rewrite IHn; auto.
Qed.

Local Opaque Nat.mul.
Lemma funbool_to_nat_shift : forall n f k, (k < n)%nat ->
  funbool_to_nat n f  = (2 ^ (n - k) * funbool_to_nat k f + funbool_to_nat (n - k) (shift f k))%nat.
Proof.
  intros.
  unfold shift, funbool_to_nat.
  destruct n; try lia.
  induction n.
  destruct k; try lia.
  replace (1 - 0)%nat with (S O) by lia; simpl. reflexivity.
  remember (S n) as n'.
  replace (S n' - k)%nat with (S (n' - k))%nat by lia.
  simpl.
  replace (n' - k + k)%nat with n' by lia.
  bdestruct (n' =? k).
  subst.
  replace (S n - S n)%nat with O by lia; simpl.
  lia.
  rewrite IHn; lia.
Qed.
Local Transparent Nat.mul.

Fixpoint incr_bin (l : list bool) :=
  match l with
  | []        => [true]
  | false :: t => true :: t
  | true :: t  => false :: (incr_bin t)
  end.

Fixpoint nat_to_binlist' n :=
  match n with
  | O    => []
  | S n' => incr_bin (nat_to_binlist' n')
  end.
Definition nat_to_binlist len n := 
  let l := nat_to_binlist' n in
  l ++ (repeat false (len - length l)).

Fixpoint list_to_funbool len (l : list bool) : nat -> bool :=
  match l with
  | []    => fun _ => false
  | h :: t => update (list_to_funbool (len - 1)%nat t) (len - 1) h
  end.

Definition nat_to_funbool len n : nat -> bool :=
  list_to_funbool len (nat_to_binlist len n).

Lemma binlist_to_nat_append : forall l1 l2,
  binlist_to_nat (l1 ++ l2) = 
    (binlist_to_nat l1 +  2 ^ (length l1) * binlist_to_nat l2)%nat.
Proof. intros l1 l2. induction l1; simpl; lia. Qed.

Lemma binlist_to_nat_false : forall n, binlist_to_nat (repeat false n) = O.
Proof. induction n; simpl; lia. Qed.

Lemma binlist_to_nat_true : forall n, binlist_to_nat (repeat true n) = 2^n - 1.
Proof.
  induction n; simpl; trivial.
  rewrite IHn. clear.
  repeat rewrite Nat.add_0_r.
  rewrite <- Nat.add_succ_l.
  replace (S (2 ^ n - 1)) with (1 + (2 ^ n - 1)) by easy.
  rewrite <- le_plus_minus'.
  rewrite <- Nat.add_sub_assoc.
  reflexivity.
  all: induction n; simpl; try lia.
Qed.

Lemma nat_to_binlist_eq_nat_to_binlist' : forall len n, 
  binlist_to_nat (nat_to_binlist len n) = binlist_to_nat (nat_to_binlist' n).
Proof.
  intros len n.
  unfold nat_to_binlist. 
  rewrite binlist_to_nat_append.
  rewrite binlist_to_nat_false. 
  lia.
Qed.

Lemma nat_to_binlist_inverse : forall len n,
  binlist_to_nat (nat_to_binlist len n) = n.
Proof.
  intros len n.
  rewrite nat_to_binlist_eq_nat_to_binlist'.
  induction n; simpl.
  reflexivity.
  assert (H : forall l, binlist_to_nat (incr_bin l) = S (binlist_to_nat l)).
  { clear.
    induction l; simpl.
    reflexivity.
    destruct a; simpl; try reflexivity.
    rewrite IHl. lia. }
  rewrite H, IHn.
  reflexivity.
Qed.

Lemma nat_to_binlist_corr : forall l n,
   nat_to_binlist' n = l ->
   binlist_to_nat l = n. (* Lemma this *)
Proof.
  intros.
  rewrite <- H.
  erewrite <- (nat_to_binlist_eq_nat_to_binlist' n n).
  rewrite nat_to_binlist_inverse.
  reflexivity.
Qed.

Lemma incr_bin_true_length : forall l,
  Forall (fun b => b = true) l ->
  length (incr_bin l) = S (length l).
Proof.
  intros.
  induction l; trivial.
  - inversion H; subst.
    simpl in *.
    rewrite IHl; easy.
Qed.

Lemma incr_bin_false_length : forall l,
  Exists (fun b => b <> true) l ->
  length (incr_bin l) = length l.
Proof.
  intros.
  induction l; inversion H; subst.
  - destruct a; simpl; easy.
  - destruct a; simpl; trivial.
    rewrite IHl; easy.
Qed.

Lemma all_true_repeat : forall l,
  Forall (fun b : bool => b = true) l ->
  l = repeat true (length l).
Proof.
  intros.
  induction l; simpl; trivial.
  inversion H; subst.
  rewrite <- IHl; easy.
Qed.  
  
Lemma nat_to_binlist_length' : forall k n,
    n < 2 ^ k -> length (nat_to_binlist' n) <= k.
Proof.
  intros.
  induction n; simpl; try lia.
  destruct (Forall_Exists_dec (fun b => b = true) (fun b => bool_dec b true)
                              (nat_to_binlist' n)) as [ALL | NALL].
  - rewrite incr_bin_true_length; trivial.
    apply le_lt_eq_dec in IHn; [| lia].
    destruct IHn; try lia.
    exfalso.
    apply all_true_repeat in ALL.
    apply nat_to_binlist_corr in ALL.
    rewrite binlist_to_nat_true in ALL.
    rewrite e in ALL.
    lia.
  - rewrite incr_bin_false_length; trivial.
    apply IHn; lia.
Qed.

Lemma nat_to_binlist_length : forall len n,
  (n < 2 ^ len)%nat -> length (nat_to_binlist len n) = len.
Proof.
  intros len n Hlen.
  unfold nat_to_binlist.
  rewrite app_length, repeat_length. 
  bdestruct (n =? 0); subst; simpl. lia.
  apply nat_to_binlist_length' in Hlen.
  lia.
Qed.

Lemma funbool_to_list_update_oob : forall f dim b n, (dim <= n)%nat ->
  funbool_to_list dim (update f n b) = funbool_to_list dim f.
Proof.
  intros.
  induction dim; trivial.
  simpl.
  rewrite IHdim by lia.
  unfold update.
  bdestruct (dim =? n); try lia.
  reflexivity.
Qed.

Lemma list_to_funbool_inverse : forall len l,
  length l = len ->
  funbool_to_list len (list_to_funbool len l) = l.
Proof.
  intros len l.
  generalize dependent len.
  induction l; intros len Hlen.
  simpl in Hlen; rewrite <- Hlen.
  simpl. reflexivity.
  simpl in Hlen; rewrite <- Hlen.
  simpl.
  replace (length l - 0)%nat with (length l) by lia.
  rewrite update_index_eq.
  rewrite funbool_to_list_update_oob by lia.
  rewrite IHl; reflexivity.
Qed.

Lemma nat_to_funbool_inverse : forall len n, 
  (n < 2 ^ len)%nat -> funbool_to_nat len (nat_to_funbool len n) = n.
Proof.
  intros.
  unfold nat_to_funbool, funbool_to_nat.
  rewrite list_to_funbool_inverse.
  apply nat_to_binlist_inverse.
  apply nat_to_binlist_length.
  assumption.
Qed.

Lemma nat_lt_pow2_funbool_to_nat_ind (P : nat -> Prop) n
  (H : forall f, P (funbool_to_nat n f)) : 
  forall i, i < 2 ^ n -> P i.
Proof.
  intros i Hi.
  rewrite <- (nat_to_funbool_inverse n i Hi).
  apply H.
Qed.

Local Opaque Nat.mul.
Lemma nat_to_binlist'_even : forall n, (n > 0)%nat -> 
  nat_to_binlist' (2 * n) = false :: nat_to_binlist' n.
Proof.
  intros n Hn. 
  destruct n; try lia. clear.
  induction n.
  rewrite Nat.mul_1_r. simpl. reflexivity. 
  replace (2 * S (S n))%nat with (S (S (2 * S n))) by lia.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma nat_to_binlist'_odd : forall n,
  nat_to_binlist' (2 * n + 1) = true :: nat_to_binlist' n.
Proof.
  induction n.
  rewrite Nat.mul_0_r, Nat.add_0_l. simpl. reflexivity. 
  replace (2 * S n + 1)%nat with (S (S (2 * n + 1))) by lia.
  simpl. rewrite IHn. reflexivity.
Qed.

Lemma binlist_to_nat_inverse : forall l n i, 
  list_to_funbool n (nat_to_binlist' (binlist_to_nat l)) i = list_to_funbool n l i.
Proof.
  intros.
  generalize dependent n.
  induction l.
  reflexivity.
  intros.
  simpl.
  destruct a; simpl Nat.b2n. 
  rewrite Nat.add_comm.
  rewrite nat_to_binlist'_odd.
  simpl. unfold update.
  rewrite IHl. reflexivity.
  rewrite Nat.add_0_l.
  bdestruct (binlist_to_nat l =? 0).
  rewrite H in *.
  rewrite Nat.mul_0_r.
  simpl.
  unfold update.
  rewrite <- IHl.
  simpl.
  bdestruct_all; reflexivity.
  rewrite nat_to_binlist'_even by lia.
  simpl. unfold update.
  rewrite IHl. reflexivity.
Qed.

Lemma list_to_funbool_repeat_false : forall n i,
  list_to_funbool n (repeat false n) i = false.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl. rewrite Nat.sub_0_r.
  unfold update.
  rewrite IHn.
  bdestruct_all; reflexivity.
Qed.

Lemma funbool_to_nat_0 : forall n f, 
  funbool_to_nat n f = O -> forall i, (i < n)%nat -> f i = false.
Proof.
  intros.
  induction n.
  lia.
  intros.
  unfold funbool_to_nat in *. 
  simpl in *.
  destruct (f n) eqn:fn; simpl in *.
  inversion H.
  bdestruct (i =? n). subst. 
  assumption.
  apply IHn; lia.
Qed.

Lemma testbit_binlist {n : nat} {k : list bool} :
  Nat.testbit (binlist_to_nat k) n = nth n k false.
Proof.
  revert k;
  induction n;
  intros k.
  - cbn.
    destruct k; [easy|].  
    destruct b; cbn.
    2: rewrite <- Nat.negb_even;
      symmetry; apply negb_sym; cbn.
    1: rewrite Nat.odd_succ.
    all: rewrite Nat.even_mul; easy.
  - destruct k.
    + rewrite Nat.testbit_0_l; easy.
    + simpl. 
      destruct b;
      simpl Nat.b2n.
      * rewrite Nat.add_1_l.
        rewrite div2_S_double.
        apply IHn.
      * rewrite Nat.add_0_l.
        rewrite Nat.div2_double.
        apply IHn.
Qed.

Lemma testbit_funbool_to_nat {n0 n} {f} :
  Nat.testbit (funbool_to_nat n0 f) n = if n <? n0 then f (n0 - (S n)) else false.
Proof.
  unfold funbool_to_nat.
  rewrite testbit_binlist.
  gen n0 f;
  induction n; intros n0 f.
  - induction n0.
    + easy.
    + cbn.
      rewrite Nat.sub_0_r.
      easy.
  - induction n0.
    + easy.
    + cbn. rewrite IHn. easy.
Qed.

Lemma nth_nat_to_binlist {len n} : forall k,
  nth k (nat_to_binlist len n) false = Nat.testbit n k.
Proof.
  intros k.
  rewrite <- testbit_binlist, nat_to_binlist_inverse.
  easy.
Qed.

Lemma list_to_funbool_eq {k : list bool} {n0} :
  (list_to_funbool n0 k) = fun n => if n <=? (n0 - 1) then nth (n0 - S n) k false else false.
Proof.
  gen n0;
  induction k; intros n0.
  - apply functional_extensionality; intros n.
    destruct (n0 - S n); rewrite Tauto.if_same; easy.
  - destruct n0.
    1: apply functional_extensionality; intros n; destruct n; try easy.
      simpl. rewrite IHk.
      unfold update. easy.
    simpl list_to_funbool. 
    rewrite IHk.
    apply functional_extensionality.
    intros n.
    unfold update.
    rewrite Nat.sub_0_r.
    replace (S n0 - 1) with n0 by lia.
    bdestruct (n <=? n0).
    + bdestruct (n =? n0).
      * subst.
        replace (S n0 - S n0) with 0 by lia.
        easy.
      * bdestruct (n <=? n0 - 1); [|lia].
        destruct (S n0 - S n) as [|n'] eqn:Hn'; [lia|].
        simpl nth.
        replace (n0 - S n) with n' by lia.
        easy.
    + bdestruct (n =? n0); subst; try lia.
      bdestruct (n <=? n0 - 1); subst; try lia.
Qed.

Lemma list_to_funbool_eq' {k : list bool} {n0 n} :
  list_to_funbool n0 k n = if n <=? (n0 - 1) then nth (n0 - S n) k false else false.
Proof.
  rewrite list_to_funbool_eq. easy.
Qed.

Lemma nat_to_funbool_eq {n j} :
  nat_to_funbool n j = fun k => if k <=? n - 1 then Nat.testbit j (n - S k) else false.
Proof.
  apply functional_extensionality; intros k.
  unfold nat_to_funbool.
  rewrite list_to_funbool_eq', nth_nat_to_binlist.
  easy.
Qed.

Lemma funbool_to_nat_inverse : forall len f i, (i < len)%nat -> 
  nat_to_funbool len (funbool_to_nat len f) i = f i.
Proof.
  intros.
  rewrite nat_to_funbool_eq.
  rewrite testbit_funbool_to_nat.
  rewrite sub_S_sub_S by easy.
  bdestructΩ'.
Qed.
Local Transparent Nat.mul.

Lemma binlist_mod {k : list bool} {n0 : nat} :
  (binlist_to_nat k) mod (2^n0) = binlist_to_nat (firstn n0 k).
Proof.
  apply Nat.bits_inj.
  intros n.
  rewrite testbit_binlist.
  bdestruct (n <? n0).
  - rewrite Nat.mod_pow2_bits_low.
    rewrite testbit_binlist.
    rewrite nth_firstn.
    easy.
    1,2: exact H.
  - rewrite Nat.mod_pow2_bits_high; [|easy].
    rewrite nth_overflow; [easy|].
    transitivity n0; [|easy].
    apply firstn_le_length.
Qed.

Lemma binlist_div {k : list bool} {n0 : nat} :
  (binlist_to_nat k) / (2^n0) = binlist_to_nat (skipn n0 k).
Proof.
  apply Nat.bits_inj.
  intros n.
  rewrite Nat.div_pow2_bits.
  rewrite 2!testbit_binlist.
  rewrite nth_skipn.
  rewrite Nat.add_comm.
  easy. 
Qed.

Lemma funbool_to_nat_div {n0 n1 : nat} {f}:
  (funbool_to_nat (n0 + n1) f) / (2^n1) = funbool_to_nat n0 f.
Proof.
  destruct n1.
  - rewrite Nat.pow_0_r, Nat.div_1_r, Nat.add_0_r.
    easy.
  - rewrite (funbool_to_nat_shift _ _ n0); [|lia].
    replace (n0 + S n1 - n0) with (S n1) by lia.
    rewrite Nat.mul_comm.
    rewrite Nat.div_add_l; [|apply Nat.pow_nonzero; easy].
    rewrite Nat.div_small; [easy|].
    apply funbool_to_nat_bound.
Qed.

Lemma funbool_to_nat_mod {n0 n1 : nat} {f}:
  (funbool_to_nat (n0 + n1) f) mod (2^n1) = funbool_to_nat n1 (shift f n0).
Proof.
  destruct n1.
  - rewrite Nat.pow_0_r, Nat.mod_1_r.
    easy.
  - rewrite (funbool_to_nat_shift _ _ n0); [|lia].
    replace (n0 + S n1 - n0) with (S n1) by lia.
    rewrite Nat.add_comm, Nat.mul_comm, Nat.mod_add;
    [|apply Nat.pow_nonzero; easy].
    rewrite Nat.mod_small; [|apply funbool_to_nat_bound].
    easy.
Qed.

Lemma nat_to_funbool_mod {n1 j} {k} (n0:nat) : k < n1 ->
  nat_to_funbool n1 (j mod 2 ^ n1) k = nat_to_funbool (n0 + n1) j (k + n0).
Proof.
  intros Hk.
  rewrite 2!nat_to_funbool_eq.
  bdestruct_all; try lia.
  rewrite Nat.mod_pow2_bits_low; [|lia].
  f_equal.
  lia.
Qed.

Lemma nat_to_funbool_div {n0 n1 j} {k} : k < n0 -> 
  nat_to_funbool n0 (j / 2 ^ n1) k = nat_to_funbool (n0 + n1) j k.
Proof.
  intros Hk.
  rewrite 2!nat_to_funbool_eq.
  bdestruct_all; try lia.
  rewrite Nat.div_pow2_bits.
  f_equal.
  lia.
Qed.

Lemma funbool_to_nat_add_pow2_join n f g m : 
  funbool_to_nat n f * 2 ^ m + funbool_to_nat m g = 
  funbool_to_nat (n + m) (fun k => if k <? n then f k else g (k - n)).
Proof.
  apply bits_inj.
  intros s.
  rewrite testbit_add_pow2_split by apply funbool_to_nat_bound.
  rewrite 3!testbit_funbool_to_nat.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma funbool_to_nat_div_pow2 n m f : 
  funbool_to_nat n f / 2 ^ m = funbool_to_nat (n - m) f.
Proof.
  apply bits_inj.
  intros s.
  rewrite testbit_div_pow2, 2!testbit_funbool_to_nat.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma funbool_to_nat_mod_pow2 n m f : 
  (funbool_to_nat n f) mod 2 ^ m = 
  funbool_to_nat (min n m) (fun k => f (n + k - (min n m))).
Proof.
  apply bits_inj.
  intros s.
  rewrite testbit_mod_pow2, 2!testbit_funbool_to_nat.
  rewrite min_ltb.
  bdestructΩ'; f_equal; lia.
Qed.

Lemma funbool_to_nat_eq_iff n f g  :
  (forall k, k < n -> f k = g k) <-> funbool_to_nat n f = funbool_to_nat n g.
Proof.
  split; 
  [apply funbool_to_nat_eq|].
  intros H k Hk.
  apply (f_equal (fun f => Nat.testbit f (n - S k))) in H.
  revert H.
  rewrite 2!testbit_funbool_to_nat.
  simplify_bools_lia.
  now replace (n - S (n - S k)) with k by lia.
Qed.

Lemma nat_to_funbool_eq' n j k :
  nat_to_funbool n j k = 
  if k <=? n - 1 then Nat.testbit j (n - S k) else false.
Proof.
  now rewrite nat_to_funbool_eq.
Qed.

Fixpoint product (x y : nat -> bool) n :=
  match n with
  | O => false
  | S n' => xorb ((x n') && (y n')) (product x y n')
  end.

Lemma product_comm : forall f1 f2 n, product f1 f2 n = product f2 f1 n.
Proof.
  intros f1 f2 n.
  induction n; simpl; auto.
  rewrite IHn, andb_comm.
  reflexivity.
Qed.

Lemma product_update_oob : forall f1 f2 n b dim, (dim <= n)%nat ->
  product f1 (update f2 n b) dim = product f1 f2 dim.
Proof.
  intros.
  induction dim; trivial.
  simpl.
  rewrite IHdim by lia.
  unfold update.
  bdestruct (dim =? n); try lia.
  reflexivity.
Qed.

Lemma product_0 : forall f n, product (fun _ : nat => false) f n = false.
Proof.
  intros f n.
  induction n; simpl.
  reflexivity.
  rewrite IHn; reflexivity.
Qed.

Lemma nat_to_funbool_0 : forall n, nat_to_funbool n 0 = (fun _ => false).
Proof.
  intro n.
  unfold nat_to_funbool, nat_to_binlist.
  simpl.
  replace (n - 0)%nat with n by lia.
  induction n; simpl.
  reflexivity.
  replace (n - 0)%nat with n by lia.
  rewrite update_same; rewrite IHn; reflexivity.
Qed.

Lemma nat_to_funbool_1 : forall n, nat_to_funbool n 1 = (fun x => x =? n - 1).
Proof.
  intro n.
  unfold nat_to_funbool, nat_to_binlist.
  simpl.
  apply functional_extensionality.
  intro x.
  bdestruct (x =? n - 1).
  subst. rewrite update_index_eq. reflexivity.
  rewrite update_index_neq by lia.
  rewrite list_to_funbool_repeat_false.
  reflexivity.
Qed.

Lemma nat_to_funbool_add_pow2_split i j n m 
  (Hi : i < 2 ^ n) (Hj : j < 2 ^ m) : 
  nat_to_funbool (n + m) (i * 2 ^ m + j) =
  (fun s => 
    if s <? n then nat_to_funbool n i s
    else nat_to_funbool m j (s - n)).
Proof.
  apply functional_extensionality; intros s.
  rewrite !nat_to_funbool_eq.
  rewrite testbit_add_pow2_split by easy.
  bdestructΩ'; try (f_equal; lia).
  - replace n with 0 in * by lia.
    replace m with 0 in * by lia.
    destruct i, j; [|cbn in Hi, Hj; lia..].
    easy.
  - replace m with 0 in * by lia.
    destruct j; [|cbn in Hj; lia].
    easy.
Qed.

Lemma nat_to_funbool_inj_upto_small i j n (Hi : i < 2^n) (Hj : j < 2^n) :
  (forall s, s < n -> nat_to_funbool n i s = nat_to_funbool n j s) <->
  i = j.
Proof.
  split; [|now intros ->].
  intros Hij.
  rewrite <- (bits_inj_upto_small i j n) by assumption.
  intros s Hs.
  generalize (Hij (n - S s) ltac:(lia)).
  rewrite 2!nat_to_funbool_eq.
  simplify_bools_lia_one_kernel.
  now rewrite sub_S_sub_S.
Qed.