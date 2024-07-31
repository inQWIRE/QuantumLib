Require Import Modulus.
Require Export Permutations.
Require Import PermutationAutomation.
Require Export Bits.
Require Export Prelim.
Import Setoid.

(* Definitions of particular permutations, operations on permutations,
  and their interactions *)
Local Open Scope program_scope.
Local Open Scope nat_scope.

Definition stack_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => 
  if (n <? n0) then f n else 
  if (n <? n0 + n1) then (g (n - n0) + n0)%nat else n.

Definition tensor_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => if (n0 * n1 <=? n) then n else
  (f (n / n1) * n1 + g (n mod n1)).

Definition swap_perm a b n := 
  fun k => if n <=? k then k else 
  if k =? a then b else
  if k =? b then a else k.


(* TODO: Implement things for this *)
Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (Bits.fswap f k n')
  end.

Fixpoint swap_list_spec l : bool :=
  match l with 
  | [] => true
  | k :: ks => (k <? S (length ks)) && swap_list_spec ks
  end.

Fixpoint perm_of_swap_list l :=
  match l with
  | [] => idn
  | k :: ks => let n := length ks in
    (swap_perm k n (S n) ∘ (perm_of_swap_list ks))%prg
  end.

Fixpoint invperm_of_swap_list l :=
  match l with 
  | [] => idn
  | k :: ks => let n := length ks in
    ((invperm_of_swap_list ks) ∘ swap_perm k n (S n))%prg
  end.

Definition perm_inv' n f :=
  fun k => if n <=? k then k else perm_inv n f k.

Definition contract_perm f a :=
  fun k => 
  if k <? a then 
    if f k <? f a then f k else f k - 1
  else
    if f (k + 1) <? f a then f (k + 1) else f (k + 1) - 1.

Definition swap_2_perm : nat -> nat :=
  swap_perm 0 1 2.

Definition rotr n m : nat -> nat :=
	fun k => if n <=? k then k else (k + m) mod n.

Definition rotl n m : nat -> nat :=
	fun k => if n <=? k then k else (k + (n - (m mod n))) mod n.

Definition swap_block_perm padl padm a :=
  fun k => 
  if k <? padl then k else
  if k <? padl + a then k + (a + padm) else
  if k <? padl + a + padm then k else
  if k <? padl + a + padm + a then k - (a + padm) else
  k.

Definition big_swap_perm p q :=
  fun k =>
  if k <? p then k + q else
  if k <? p + q then k - p else k.

Definition reflect_perm n := 
  fun k => 
  if n <=? k then k else n - S k.






Lemma permutation_change_dims n m (H : n = m) f : 
	permutation n f <-> permutation m f.
Proof.
	now subst.
Qed.

Lemma permutation_eqb_iff {n f} a b : permutation n f -> 
  a < n -> b < n ->
  f a =? f b = (a =? b).
Proof.
  intros Hperm Hk Hfk.
  bdestruct_one.
  apply (permutation_is_injective n f Hperm) in H; [bdestruct_one| |]; lia.
  bdestruct_one; subst; easy.
Qed.

Lemma permutation_eq_iff {n f} a b : permutation n f -> 
  a < n -> b < n ->
  f a = f b <-> a = b.
Proof.
  intros Hperm Hk Hfk.
  generalize (permutation_eqb_iff _ _ Hperm Hk Hfk).
  bdestructΩ'.
Qed.

(* TODO: Move somewhere else *)
Lemma perm_eq_iff_forall n (f g : nat -> nat) : 
	perm_eq n f g <-> forallb (fun k => f k =? g k) (seq 0 n) = true.
Proof.
	rewrite forallb_seq0.
	now setoid_rewrite Nat.eqb_eq.
Qed.

Lemma perm_eq_dec n (f g : nat -> nat) : 
	{perm_eq n f g} + {~ perm_eq n f g}.
Proof.
	generalize (perm_eq_iff_forall n f g).
	destruct (forallb (fun k => f k =? g k) (seq 0 n)); intros H;
	[left | right]; rewrite H; easy.
Qed.

Lemma not_forallb_seq_exists f start len : 
	forallb f (seq start len) = false -> 
	exists n, n < len /\ f (n + start) = false.
Proof.
	revert start; induction len; [easy|].
	intros start.
	simpl.
	rewrite andb_false_iff.
	intros [H | H].
	- exists 0. split; [lia | easy].
	- destruct (IHlen (S start) H) as (n & Hn & Hfn).
		exists (S n); split; rewrite <- ?Hfn; f_equal; lia.
Qed.

Lemma not_forallb_seq0_exists f n : 
	forallb f (seq 0 n) = false -> 
	exists k, k < n /\ f k = false.
Proof.
	intros H.
	apply not_forallb_seq_exists in H.
	setoid_rewrite Nat.add_0_r in H.
	exact H.
Qed.

Lemma not_perm_eq_not_eq_at n (f g : nat -> nat) : 
	~ (perm_eq n f g) -> exists k, k < n /\ f k <> g k.
Proof.
	rewrite perm_eq_iff_forall.
	rewrite not_true_iff_false.
	intros H.
	apply not_forallb_seq0_exists in H.
	setoid_rewrite Nat.eqb_neq in H.
	exact H.
Qed.

Lemma perm_bounded_of_eq {n f g} : 
  perm_eq n g f -> perm_bounded n f -> 
  perm_bounded n g.
Proof.
  intros Hfg Hf k Hk.
  rewrite Hfg; auto. 
Qed.

(* Section on perm_inv *)
Lemma perm_inv'_eq n f : 
  perm_eq n (perm_inv' n f) (perm_inv n f).
Proof.
  intros k Hk.
  unfold perm_inv'.
  bdestructΩ'.
Qed.

#[export] Hint Extern 0
  (perm_eq ?n (perm_inv' ?n ?f) ?g) => 
  apply (perm_eq_trans (perm_inv'_eq n _)) : perm_inv_db.

#[export] Hint Extern 0
  (perm_eq ?n ?g (perm_inv' ?n ?f)) => 
  apply (fun H => perm_eq_trans 
    H (perm_eq_sym (perm_inv'_eq n _))) : perm_inv_db.

Lemma perm_inv'_bounded n f : 
  perm_bounded n (perm_inv' n f).
Proof.
  apply (perm_bounded_of_eq (perm_inv'_eq n f)).
  auto with perm_bounded_db.
Qed.

Lemma perm_inv'_WF n f : 
  WF_Perm n (perm_inv' n f).
Proof.
  intros k Hk;
  unfold perm_inv';
  bdestructΩ'.
Qed.

#[export] Hint Resolve perm_inv'_bounded : perm_bounded_db.
#[export] Hint Resolve perm_inv'_WF : WF_Perm_db.

Lemma permutation_of_le_permutation_WF f m n : (m <= n)%nat -> permutation m f ->
  WF_Perm m f -> permutation n f.
Proof.
  intros Hmn [finv_m Hfinv_m] HWF.
  exists (fun k => if m <=? k then k else finv_m k).
  intros k Hk.
  bdestruct (m <=? k).
  - rewrite !HWF; bdestructΩ'.
  - specialize (Hfinv_m _ H).
    bdestructΩ'.
Qed.


#[global] Hint Resolve perm_inv'_bounded : perm_bounded_db.
#[export] Hint Resolve perm_inv_permutation : perm_db.


Lemma perm_inv_is_linv_of_permutation_compose (n : nat) (f : nat -> nat) :
  permutation n f -> 
  perm_eq n (perm_inv n f ∘ f) idn.
Proof.
  exact (perm_inv_is_linv_of_permutation n f).
Qed.

#[export] Hint Resolve 
  perm_inv_is_linv_of_permutation
  perm_inv_is_linv_of_permutation_compose : perm_inv_db.

Lemma perm_inv_is_rinv_of_permutation_compose (n : nat) (f : nat -> nat) :
  permutation n f -> 
  perm_eq n (f ∘ perm_inv n f) idn.
Proof.
  exact (perm_inv_is_rinv_of_permutation n f).
Qed.

#[export] Hint Resolve 
  perm_inv_is_rinv_of_permutation
  perm_inv_is_rinv_of_permutation_compose : perm_inv_db.

Lemma perm_eq_compose_proper n (f f' g g' : nat -> nat) : 
  perm_bounded n g -> perm_eq n f f' -> perm_eq n g g' ->
  perm_eq n (f ∘ g) (f' ∘ g').
Proof.
  intros Hg Hf' Hg' k Hk.
  unfold compose.
  now rewrite Hf', Hg' by auto.
Qed.

#[export] Hint Resolve perm_eq_compose_proper : perm_inv_db.

Lemma perm_inv'_is_linv_of_permutation_compose (n : nat) (f : nat -> nat) :
  permutation n f -> 
  perm_eq n (perm_inv' n f ∘ f) idn.
Proof.
  intros Hf k Hk.
  unfold compose.
  rewrite perm_inv'_eq by auto with perm_db.
  auto with perm_inv_db.
Qed.

#[export] Hint Resolve perm_inv'_is_linv_of_permutation_compose : perm_inv_db.

Lemma perm_inv'_is_rinv_of_permutation_compose (n : nat) (f : nat -> nat) :
  permutation n f -> 
  perm_eq n (f ∘ perm_inv' n f) idn.
Proof.
  intros Hf k Hk.
  unfold compose.
  rewrite perm_inv'_eq by auto with perm_db.
  auto with perm_inv_db.
Qed.

#[export] Hint Resolve perm_inv'_is_rinv_of_permutation_compose : perm_inv_db.

Lemma idn_WF_Perm n : WF_Perm n idn.
Proof. easy. Qed.

#[export] Hint Resolve idn_WF_Perm : WF_Perm_db.
#[export] Hint Resolve compose_WF_Perm : WF_Perm_db.


Lemma perm_inv'_linv_of_permutation_WF n f : 
	permutation n f -> WF_Perm n f -> 
	perm_inv' n f ∘ f = idn.
Proof.
	intros.
	eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

Lemma perm_inv'_rinv_of_permutation_WF n f : 
	permutation n f -> WF_Perm n f -> 
	f ∘ perm_inv' n f = idn.
Proof.
	intros.
	eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite perm_inv'_linv_of_permutation_WF
  perm_inv'_rinv_of_permutation_WF
  using (solve [auto with perm_db WF_Perm_db]) : perm_inv_db.

Lemma perm_eq_linv_injective n f finv finv' : permutation n f ->
  is_perm_linv n f finv -> is_perm_linv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hperm Hfinv Hfinv'.
  perm_eq_by_inv_inj f n.
Qed.

Lemma perm_inv_eq_inv n f finv : 
  (forall x : nat, x < n -> f x < n /\ finv x < n 
    /\ finv (f x) = x /\ f (finv x) = x)
  -> perm_eq n (perm_inv n f) finv.
Proof.
  intros Hfinv.
  assert (Hperm: permutation n f) by (exists finv; easy).
  perm_eq_by_inv_inj f n.
  intros k Hk; now apply Hfinv.
Qed.

Lemma perm_inv_is_inv n f : permutation n f ->
  forall k : nat, k < n -> perm_inv n f k < n /\ f k < n 
    /\ f (perm_inv n f k) = k /\ perm_inv n f (f k) = k.
Proof.
  intros Hperm k Hk.
  repeat split.
  - apply perm_inv_bounded, Hk.
  - destruct Hperm as [? H]; apply H, Hk.
  - rewrite perm_inv_is_rinv_of_permutation; easy.
  - rewrite perm_inv_is_linv_of_permutation; easy.
Qed.

Lemma perm_inv_perm_inv n f : permutation n f ->
  perm_eq n (perm_inv n (perm_inv n f)) f.
Proof.
  intros Hf.
  perm_eq_by_inv_inj (perm_inv n f) n.
Qed.

#[export] Hint Resolve perm_inv_perm_inv : perm_inv_db.

Lemma perm_inv_eq_of_perm_eq' n m f g : perm_eq n f g -> m <= n ->
  perm_eq n (perm_inv m f) (perm_inv m g).
Proof.
  intros Heq Hm.
  induction m; [easy|].
  intros k Hk.
  simpl.
  rewrite Heq by lia.
  rewrite IHm by lia.
  easy.
Qed.

Lemma perm_inv_eq_of_perm_eq n f g : perm_eq n f g ->
  perm_eq n (perm_inv n f) (perm_inv n g).
Proof.
  intros Heq.
  apply perm_inv_eq_of_perm_eq'; easy.
Qed.

#[export] Hint Resolve perm_inv_eq_of_perm_eq : perm_inv_db.

Lemma perm_inv'_eq_of_perm_eq n f g : perm_eq n f g ->
  perm_inv' n f = perm_inv' n g.
Proof.
  intros Heq.
  eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv_eq_of_perm_eq' : perm_inv_db.

Add Parametric Morphism n : (perm_inv n f) with signature 
  perm_eq n ==> perm_eq n.

#[export] Hint Extern 20
  (?f = ?g) => 
  eapply eq_of_WF_perm_eq;
  auto with WF_Perm_db : perm_inv_db.

Lemma perm_inv'_perm_inv n f : permutation n f ->
  perm_eq n (perm_inv' n (perm_inv n f)) f.
Proof.
  cleanup_perm_inv.
Qed.

Lemma perm_inv_perm_inv' n f : permutation n f ->
  perm_eq n (perm_inv n (perm_inv' n f)) f.
Proof.
  intros Hf k Hk.
  rewrite (perm_inv_eq_of_perm_eq _ _ _ (perm_inv'_eq _ _)) by easy.
  cleanup_perm_inv.
Qed.

Lemma perm_inv'_perm_inv_eq n f : 
  permutation n f -> WF_Perm n f ->
  perm_inv' n (perm_inv n f) = f.
Proof.
  cleanup_perm_inv.
Qed.

Lemma perm_inv'_perm_inv' n f : permutation n f ->
  perm_eq n (perm_inv' n (perm_inv' n f)) f.
Proof.
  intros Hf.
  rewrite (perm_inv'_eq_of_perm_eq _ _ _ (perm_inv'_eq n f)).
  cleanup_perm_inv.
Qed.

Lemma perm_inv'_perm_inv'_eq n f : 
  permutation n f -> WF_Perm n f ->
  perm_inv' n (perm_inv' n f) = f.
Proof.
  rewrite (perm_inv'_eq_of_perm_eq _ _ _ (perm_inv'_eq n f)).
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv'_perm_inv 
  perm_inv'_perm_inv' perm_inv_perm_inv' : perm_inv_db.
#[export] Hint Rewrite perm_inv'_perm_inv_eq 
  perm_inv'_perm_inv'_eq
  using 
  solve [auto with perm_db WF_Perm_db] : perm_inv_db.

Lemma permutation_compose' n f g : 
  permutation n f -> permutation n g -> 
  permutation n (fun x => f (g x)).
Proof.
  apply permutation_compose.
Qed.

#[export] Hint Resolve permutation_compose permutation_compose' : perm_db. 

#[export] Hint Rewrite perm_inv_is_linv_of_permutation
  perm_inv_is_rinv_of_permutation : perm_inv_db.

Lemma perm_inv_eq_iff {n g} (Hg : permutation n g) 
  {k m} (Hk : k < n) (Hm : m < n) :
  perm_inv n g k = m <-> k = g m.
Proof.
  split; 
  [intros <- | intros ->];
  rewrite ?(perm_inv_is_rinv_of_permutation _ g Hg),
    ?(perm_inv_is_linv_of_permutation _ g Hg);
  easy.
Qed.

Lemma perm_inv_eqb_iff {n g} (Hg : permutation n g) 
  {k m} (Hk : k < n) (Hm : m < n) :
  (perm_inv n g k =? m) = (k =? g m).
Proof.
  apply Bool.eq_iff_eq_true;
  rewrite 2!Nat.eqb_eq;
  now apply perm_inv_eq_iff.
Qed.

Lemma perm_inv_ge n g k : 
  n <= perm_inv n g k -> n <= k.
Proof.
  intros H.
  bdestruct (n <=? k); [lia|].
  specialize (perm_inv_bounded n g k); lia.
Qed.

Lemma compose_perm_inv_l n f g h
  (Hf : permutation n f) (Hg : perm_bounded n g)
  (Hh : perm_bounded n h) : 
  perm_eq n (perm_inv n f ∘ g) h <-> 
  perm_eq n g (f ∘ h).
Proof.
  split; unfold compose.
  - intros H k Hk.
    rewrite <- H; cleanup_perm_inv.
  - intros H k Hk.
    rewrite H; cleanup_perm_inv.
Qed.

Lemma compose_perm_inv_r n f g h
  (Hf : permutation n f) (Hg : perm_bounded n g)
  (Hh : perm_bounded n h) : 
  perm_eq n (g ∘ perm_inv n f) h <-> 
  perm_eq n g (h ∘ f).
Proof.
  split; unfold compose.
  - intros H k Hk.
    rewrite <- H; cleanup_perm_inv.
  - intros H k Hk.
    rewrite H; cleanup_perm_inv.
Qed.

Lemma compose_perm_inv_l' n f g h
  (Hf : permutation n f) (Hg : perm_bounded n g)
  (Hh : perm_bounded n h) : 
  perm_eq n h (perm_inv n f ∘ g) <-> 
  perm_eq n (f ∘ h) g.
Proof.
  split; intros H; 
  apply perm_eq_sym, 
    compose_perm_inv_l, perm_eq_sym;
  assumption.
Qed.

Lemma compose_perm_inv_r' n f g h
  (Hf : permutation n f) (Hg : perm_bounded n g)
  (Hh : perm_bounded n h) : 
  perm_eq n h (g ∘ perm_inv n f) <-> 
  perm_eq n (h ∘ f) g.
Proof.
  split; intros H; 
  apply perm_eq_sym, 
    compose_perm_inv_r, perm_eq_sym;
  assumption.
Qed.

Lemma compose_perm_inv'_l n (f g h : nat -> nat)
  (Hf : permutation n f) (HWFf : WF_Perm n f) : 
  perm_inv' n f ∘ g = h <-> g = f ∘ h.
Proof.
  split; [intros <- | intros ->]; 
  rewrite <- compose_assoc;
  cleanup_perm_inv.
Qed.

Lemma compose_perm_inv'_r n (f g h : nat -> nat)
  (Hf : permutation n f) (HWFf : WF_Perm n f) : 
  g ∘ perm_inv' n f = h <-> g = h ∘ f.
Proof.
  split; [intros <- | intros ->]; 
  rewrite compose_assoc;
  cleanup_perm_inv.
Qed.

Lemma compose_perm_inv'_l' n (f g h : nat -> nat)
  (Hf : permutation n f) (HWFf : WF_Perm n f) : 
  h = perm_inv' n f ∘ g <-> f ∘ h = g.
Proof.
  split; [intros -> | intros <-]; 
  rewrite <- compose_assoc;
  cleanup_perm_inv.
Qed.

Lemma compose_perm_inv'_r' n (f g h : nat -> nat)
  (Hf : permutation n f) (HWFf : WF_Perm n f) : 
  h = g ∘ perm_inv' n f <-> h ∘ f = g.
Proof.
  split; [intros -> | intros <-]; 
  rewrite compose_assoc;
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite perm_inv_perm_inv : perm_inv_db.

Lemma perm_inv_perm_eq_iff n f g 
  (Hf : permutation n f) (Hg : permutation n g) :
  perm_eq n (perm_inv n g) f <-> perm_eq n g (perm_inv n f).
Proof.
  rewrite <- (compose_idn_r (perm_inv n g)).
  rewrite <- (compose_idn_l (perm_inv n f)).
  rewrite compose_perm_inv_l, compose_perm_inv_r' by cleanup_perm.
  split; apply perm_eq_sym.
Qed.

Lemma perm_inv_compose {n f g} (Hf : permutation n f) (Hg : permutation n g) : 
  perm_eq n 
    (perm_inv n (f ∘ g))
    (perm_inv n g ∘ perm_inv n f).
Proof.
  apply perm_eq_sym.
  perm_eq_by_inv_inj (f ∘ g) n.
  apply compose_perm_inv_l; auto with perm_db.
  apply compose_perm_inv_l; auto with perm_db.
Qed.

#[export] Hint Resolve perm_inv_compose : perm_inv_db.

Lemma perm_inv'_compose {n f g} 
  (Hf : permutation n f) (Hg : permutation n g) : 
  perm_inv' n (f ∘ g) = 
  perm_inv' n g ∘ perm_inv' n f.
Proof.
  eq_by_WF_perm_eq n.
  apply (perm_eq_trans (perm_inv'_eq _ _)).
  apply (perm_eq_trans (perm_inv_compose Hf Hg)).
  apply perm_eq_compose_proper;
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite @perm_inv'_compose 
  using auto with perm_db : perm_inv_db.



Lemma idn_inv n :
  perm_eq n (perm_inv n idn) idn.
Proof.
  perm_eq_by_inv_inj (fun k:nat => k) n.
Qed.

#[export] Hint Resolve idn_inv : perm_inv_db.

Lemma idn_inv' n : 
  perm_inv' n idn = idn.
Proof.
  permutation_eq_by_WF_inv_inj (fun k:nat=>k) n.
Qed.

#[export] Hint Rewrite idn_inv' : perm_inv_db.


Lemma swap_perm_same a n :
  swap_perm a a n = idn.
Proof.
  unfold swap_perm.
  apply functional_extensionality; intros k.
  bdestructΩ'.
Qed.

Lemma swap_perm_comm a b n :
  swap_perm a b n = swap_perm b a n.
Proof.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_perm_WF a b n : 
  WF_Perm n (swap_perm a b n).
Proof.
  intros k Hk.
  unfold swap_perm. 
  bdestructΩ'.
Qed.

Lemma swap_perm_bounded a b n : a < n -> b < n ->
  perm_bounded n (swap_perm a b n).
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_perm_invol a b n : a < n -> b < n -> 
  (swap_perm a b n) ∘ (swap_perm a b n) = idn.
Proof.
  intros Ha Hb.
  unfold compose.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_perm_same : perm_cleanup_db.
#[export] Hint Resolve swap_perm_WF : WF_Perm_db.
#[export] Hint Resolve swap_perm_bounded : perm_bounded_db.
#[export] Hint Rewrite swap_perm_invol : perm_inv_db.

Lemma swap_perm_permutation a b n : a < n -> b < n ->
  permutation n (swap_perm a b n).
Proof.
  intros Ha Hb.
  perm_by_inverse (swap_perm a b n).
Qed.

Lemma swap_perm_S_permutation a n (Ha : S a < n) :
  permutation n (swap_perm a (S a) n).
Proof.
  apply swap_perm_permutation; lia.
Qed.

#[export] Hint Resolve swap_perm_permutation : perm_db.
#[export] Hint Resolve swap_perm_S_permutation : perm_db.


Lemma swap_perm_inv a b n : a < n -> b < n ->
  perm_eq n (perm_inv n (swap_perm a b n))
    (swap_perm a b n).
Proof.
  intros Ha Hb.
  perm_eq_by_inv_inj (swap_perm a b n) n.
Qed.

#[export] Hint Resolve swap_perm_inv : perm_inv_db.

Lemma swap_perm_inv' a b n : a < n -> b < n ->
  perm_inv' n (swap_perm a b n) = 
  swap_perm a b n.
Proof.
  intros.
  eq_by_WF_perm_eq n; cleanup_perm_inv. 
Qed.

#[export] Hint Rewrite swap_perm_inv' : perm_inv_db.

Lemma compose_swap_perm a b c n : a < n -> b < n -> c < n -> 
  b <> c -> a <> c ->
  (swap_perm a b n ∘ swap_perm b c n ∘ swap_perm a b n) = swap_perm a c n.
Proof.
  intros Ha Hb Hc Hbc Hac.
  eq_by_WF_perm_eq n.
  unfold compose, swap_perm.
  intros k Hk.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite compose_swap_perm : perm_cleanup_db.





(* Section on insertion_sort_list *)

Lemma fswap_eq_compose_swap_perm {A} (f : nat -> A) n m o : n < o -> m < o ->
  fswap f n m = f ∘ swap_perm n m o.
Proof.
  intros Hn Hm.
  apply functional_extensionality; intros k.
  unfold compose, fswap, swap_perm.
  bdestruct_all; easy.
Qed.

Lemma fswap_perm_invol_n_permutation f n : permutation (S n) f ->
  permutation n (fswap f (perm_inv (S n) f n) n).
Proof.
  intros Hperm.
  apply fswap_at_boundary_permutation.
  - apply Hperm.
  - apply perm_inv_bounded_S.
  - apply perm_inv_is_rinv_of_permutation; auto.
Qed.


Lemma perm_of_swap_list_WF l : swap_list_spec l = true ->
  WF_Perm (length l) (perm_of_swap_list l).
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
    rewrite IHl; [|easy|lia].
    rewrite swap_perm_WF; easy.
Qed.

Lemma invperm_of_swap_list_WF l : swap_list_spec l = true ->
  WF_Perm (length l) (invperm_of_swap_list l).
Proof.
  induction l.
  - easy.
  - simpl.
    rewrite andb_true_iff.
    intros [Ha Hl].
    intros k Hk.
    unfold compose.
    rewrite swap_perm_WF; [|easy].
    rewrite IHl; [easy|easy|lia].
Qed.

#[export] Hint Resolve perm_of_swap_list_WF invperm_of_swap_list_WF : WF_Perm_db.

Lemma perm_of_swap_list_bounded l : swap_list_spec l = true ->
  perm_bounded (length l) (perm_of_swap_list l).
Proof. 
  induction l; [easy|].
  simpl.
  rewrite andb_true_iff.
  intros [Ha Hl].
  intros k Hk.
  unfold compose.
  rewrite Nat.ltb_lt in Ha.
  apply swap_perm_bounded; try lia.
  bdestruct (k =? length l).
  - subst; rewrite perm_of_swap_list_WF; try easy; lia.
  - transitivity (length l); [|lia].
    apply IHl; [easy | lia].
Qed.

Lemma invperm_of_swap_list_bounded l : swap_list_spec l = true ->
  perm_bounded (length l) (invperm_of_swap_list l).
Proof.
  induction l; [easy|].
  simpl.
  rewrite andb_true_iff.
  intros [Ha Hl].
  rewrite Nat.ltb_lt in Ha.
  intros k Hk.
  unfold compose.
  bdestruct (swap_perm a (length l) (S (length l)) k =? length l).
  - rewrite H, invperm_of_swap_list_WF; [lia|easy|easy].
  - transitivity (length l); [|lia]. 
    apply IHl; [easy|].
    pose proof (swap_perm_bounded a (length l) (S (length l)) Ha (ltac:(lia)) k Hk).
    lia.
Qed.

#[export] Hint Resolve perm_of_swap_list_bounded 
  invperm_of_swap_list_bounded : perm_bounded_db.


Lemma invperm_linv_perm_of_swap_list l : swap_list_spec l = true ->
  invperm_of_swap_list l ∘ perm_of_swap_list l = idn.
Proof.
  induction l.
  - easy.
  - simpl. 
    rewrite andb_true_iff.
    intros [Ha Hl].
    rewrite Combinators.compose_assoc, 
    <- (Combinators.compose_assoc _ _ _ _ (perm_of_swap_list _)).
    rewrite swap_perm_invol, compose_idn_l.
    + apply (IHl Hl).
    + bdestructΩ (a <? S (length l)).
    + lia.
Qed.

Lemma invperm_rinv_perm_of_swap_list l : swap_list_spec l = true ->
  perm_of_swap_list l ∘ invperm_of_swap_list l = idn.
Proof.
  induction l.
  - easy.
  - simpl. 
    rewrite andb_true_iff.
    intros [Ha Hl].
    rewrite <- Combinators.compose_assoc,
    (Combinators.compose_assoc _ _ _ _ (invperm_of_swap_list _)).
    rewrite (IHl Hl).
    rewrite compose_idn_r.
    rewrite swap_perm_invol; [easy| |lia].
    bdestructΩ (a <? S (length l)).
Qed.

#[export] Hint Rewrite invperm_linv_perm_of_swap_list 
  invperm_rinv_perm_of_swap_list 
  using auto with perm_db  : perm_inv_db perm_cleanup_db.

(* FIX ME: Remove; for working reference*)
(* Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (fswap f k n')
  end. *)

Lemma length_insertion_sort_list n f :
  length (insertion_sort_list n f) = n.
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - simpl.
    rewrite IHn; easy.
Qed.

Local Opaque perm_inv. 
Lemma insertion_sort_list_is_swap_list n f : 
  swap_list_spec (insertion_sort_list n f) = true.
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - simpl.
    rewrite length_insertion_sort_list, IHn.
    pose proof (perm_inv_bounded_S n f n).
    bdestructΩ (perm_inv (S n) f n <? S n).
Qed.

#[export] Hint Resolve 
  insertion_sort_list_is_swap_list : perm_db.

Lemma invperm_linv_perm_of_insertion_sort_list n f : permutation n f ->
  perm_eq n (invperm_of_swap_list (insertion_sort_list n f)
  ∘ perm_of_swap_list (insertion_sort_list n f)) idn.
Proof.
  cleanup_perm_inv.
Qed.

Lemma invperm_rinv_perm_of_insertion_sort_list n f : permutation n f ->
  perm_eq n (perm_of_swap_list (insertion_sort_list n f)
  ∘ invperm_of_swap_list (insertion_sort_list n f)) idn.
Proof.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve invperm_linv_perm_of_insertion_sort_list
  invperm_rinv_perm_of_insertion_sort_list : perm_inv_db.


Lemma perm_of_insertion_sort_list_is_rinv n f : permutation n f ->
  perm_eq n (f ∘ perm_of_swap_list (insertion_sort_list n f)) idn.
Proof.
  revert f;
  induction n;
  intros f.
  - intros; exfalso; easy.
  - intros Hperm k Hk.
    simpl.
    rewrite length_insertion_sort_list.
    bdestruct (k =? n).
    + unfold compose.
      rewrite perm_of_swap_list_WF; [ |
        apply insertion_sort_list_is_swap_list |
        rewrite length_insertion_sort_list; lia
      ]. 
      unfold swap_perm.
      bdestructΩ (S n <=? k).
      bdestructΩ (k =? n).
      subst.
      bdestruct (n =? perm_inv (S n) f n).
      1: rewrite H at 1.
      all: cleanup_perm_inv.
    + rewrite <- Combinators.compose_assoc.
      rewrite <- fswap_eq_compose_swap_perm; [|apply perm_inv_bounded_S|lia].
      rewrite IHn; [easy| |lia].
      apply fswap_perm_invol_n_permutation, Hperm.
Qed.
Local Transparent perm_inv.

#[export] Hint Resolve perm_of_insertion_sort_list_is_rinv : perm_inv_db.
#[export] Hint Rewrite perm_of_insertion_sort_list_is_rinv : perm_inv_db.

Lemma perm_of_insertion_sort_list_WF n f : 
  WF_Perm n (perm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros k.
  rewrite <- (length_insertion_sort_list n f) at 1.
  revert k.
  apply perm_of_swap_list_WF.
  apply insertion_sort_list_is_swap_list.
Qed.

Lemma invperm_of_insertion_sort_list_WF n f : 
  WF_Perm n (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros k.
  rewrite <- (length_insertion_sort_list n f) at 1.
  revert k.
  apply invperm_of_swap_list_WF.
  apply insertion_sort_list_is_swap_list.
Qed.

#[export] Hint Resolve perm_of_insertion_sort_list_WF 
  invperm_of_swap_list_WF : WF_Perm_db.


Lemma perm_of_insertion_sort_list_perm_eq_perm_inv n f : permutation n f ->
  perm_eq n (perm_of_swap_list (insertion_sort_list n f)) (perm_inv n f).
Proof.
  intros Hperm.
  apply (perm_bounded_rinv_injective_of_injective n f).
  - apply permutation_is_injective, Hperm.
  - pose proof (perm_of_swap_list_bounded (insertion_sort_list n f)
      (insertion_sort_list_is_swap_list n f)) as H.
    rewrite (length_insertion_sort_list n f) in H.
    exact H.
  - auto with perm_bounded_db.
  - apply perm_of_insertion_sort_list_is_rinv, Hperm.
  - apply perm_inv_is_rinv_of_permutation, Hperm.
Qed.

#[export] Hint Resolve 
  perm_of_insertion_sort_list_perm_eq_perm_inv : perm_inv_db.

Lemma perm_of_insertion_sort_list_eq_perm_inv' n f : permutation n f ->
  perm_of_swap_list (insertion_sort_list n f) = 
  perm_inv' n f.
Proof.
  intros Hf.
  eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite
  perm_of_insertion_sort_list_eq_perm_inv' 
  using auto with perm_db : perm_inv_db.


Lemma perm_inv_of_insertion_sort_list_perm_eq n f : permutation n f ->
  perm_eq n (perm_inv n (perm_of_swap_list (insertion_sort_list n f))) f.
Proof.
  intros Hf.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv_of_insertion_sort_list_perm_eq : perm_inv_db.

Lemma perm_inv'_of_insertion_sort_list_eq n f : 
  permutation n f -> WF_Perm n f ->
  perm_inv' n (perm_of_swap_list (insertion_sort_list n f)) = f.
Proof.
  intros.
  eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite perm_inv'_of_insertion_sort_list_eq
  using solve [auto with perm_db WF_Perm_db] : perm_inv_db.

#[export] Hint Extern 100 (perm_eq ?n ?f ?g) =>
  (apply (@perm_eq_sym n g f)) : perm_inv_db.

Lemma perm_eq_perm_of_insertion_sort_list_of_perm_inv n f : permutation n f ->
  perm_eq n f (perm_of_swap_list (insertion_sort_list n (perm_inv n f))).
Proof.
  intros Hf.
  cleanup_perm_inv.
Qed.

Lemma insertion_sort_list_S n f : 
  insertion_sort_list (S n) f = 
  (perm_inv (S n) f n) :: (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)).
Proof. easy. Qed.

Lemma perm_of_swap_list_cons a l :
  perm_of_swap_list (a :: l) = swap_perm a (length l) (S (length l)) ∘ perm_of_swap_list l.
Proof. easy. Qed.

Lemma invperm_of_swap_list_cons a l :
  invperm_of_swap_list (a :: l) = invperm_of_swap_list l ∘ swap_perm a (length l) (S (length l)).
Proof. easy. Qed.

Lemma perm_of_insertion_sort_list_S n f : 
  perm_of_swap_list (insertion_sort_list (S n) f) =
  swap_perm (perm_inv (S n) f n) n (S n) ∘ 
    perm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)).
Proof. 
  rewrite insertion_sort_list_S, perm_of_swap_list_cons.
  rewrite length_insertion_sort_list.
  easy.
Qed.

Lemma invperm_of_insertion_sort_list_S n f : 
  invperm_of_swap_list (insertion_sort_list (S n) f) =
  invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n).
Proof. 
  rewrite insertion_sort_list_S, invperm_of_swap_list_cons.
  rewrite length_insertion_sort_list.
  easy.
Qed.

Lemma perm_of_swap_list_permutation l : swap_list_spec l = true ->
  permutation (length l) (perm_of_swap_list l).
Proof.
  intros Hsw.
  induction l;
  [ simpl; exists idn; easy |].
  simpl.
  apply permutation_compose.
  - apply swap_perm_permutation; [|lia].
    simpl in Hsw.
    bdestruct (a <? S (length l)); easy.
  - eapply permutation_of_le_permutation_WF.
    2: apply IHl.
    1: lia.
    2: apply perm_of_swap_list_WF.
    all: simpl in Hsw;
    rewrite andb_true_iff in Hsw; easy.
Qed.

Lemma invperm_of_swap_list_permutation l : swap_list_spec l = true ->
  permutation (length l) (invperm_of_swap_list l).
Proof.
  intros Hsw.
  induction l;
  [ simpl; exists idn; easy |].
  simpl.
  apply permutation_compose.
  - eapply permutation_of_le_permutation_WF.
    2: apply IHl.
    1: lia.
    2: apply invperm_of_swap_list_WF.
    all: simpl in Hsw;
    rewrite andb_true_iff in Hsw; easy.
  - apply swap_perm_permutation; [|lia].
    simpl in Hsw.
    bdestruct (a <? S (length l)); easy.
Qed.

Lemma perm_of_insertion_sort_list_permutation n f: 
  permutation n (perm_of_swap_list (insertion_sort_list n f)).
Proof.
  rewrite <- (length_insertion_sort_list n f) at 1.
  apply perm_of_swap_list_permutation.
  apply insertion_sort_list_is_swap_list.
Qed.

Lemma invperm_of_insertion_sort_list_permutation n f: 
  permutation n (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  rewrite <- (length_insertion_sort_list n f) at 1.
  apply invperm_of_swap_list_permutation.
  apply insertion_sort_list_is_swap_list.
Qed.

#[export] Hint Resolve  
  perm_of_swap_list_permutation
  invperm_of_swap_list_permutation
  perm_of_insertion_sort_list_permutation
  invperm_of_insertion_sort_list_permutation : perm_db.





Lemma perm_eq_invperm_of_insertion_sort_list n f : permutation n f ->
  perm_eq n f (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros Hperm.
  perm_eq_by_inv_inj (perm_of_swap_list (insertion_sort_list n f)) n.
Qed.
  

Lemma permutation_grow_l' n f : permutation (S n) f -> 
  perm_eq (S n) f (swap_perm (f n) n (S n) ∘ 
  perm_of_swap_list (insertion_sort_list n (fswap (perm_inv (S n) f) (f n) n))).
Proof.
  intros Hperm k Hk.
  rewrite (perm_eq_perm_of_insertion_sort_list_of_perm_inv _ _ Hperm) 
    at 1 by auto.
  cbn -[perm_inv].
  rewrite length_insertion_sort_list, perm_inv_perm_inv by auto.
  easy.
Qed.

Lemma permutation_grow_r' n f : permutation (S n) f -> 
  perm_eq (S n) f ( 
  invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n)).
Proof.
  intros Hperm k Hk.
  rewrite (perm_eq_invperm_of_insertion_sort_list _ _ Hperm) at 1 by auto.
  cbn -[perm_inv].
  rewrite length_insertion_sort_list by auto.
  easy.
Qed.

Lemma permutation_grow_l n f : permutation (S n) f ->
  exists g k, k < S n /\ perm_eq (S n) f (swap_perm k n (S n) ∘ g) /\ permutation n g.
Proof.
  intros Hperm.
  eexists.
  exists (f n).
  split; [apply permutation_is_bounded; [easy | lia] | split].
  pose proof (perm_eq_perm_of_insertion_sort_list_of_perm_inv _ _ Hperm) as H.
  rewrite perm_of_insertion_sort_list_S in H.
  rewrite perm_inv_perm_inv in H by (easy || lia).
  exact H.
  auto with perm_db.
Qed.

Lemma permutation_grow_r n f : permutation (S n) f ->
  exists g k, k < S n /\ perm_eq (S n) f (g ∘ swap_perm k n (S n)) /\ permutation n g.
Proof.
  intros Hperm.
  eexists.
  exists (perm_inv (S n) f n).
  split; [apply permutation_is_bounded; [auto with perm_db | lia] | split].
  pose proof (perm_eq_invperm_of_insertion_sort_list _ _ Hperm) as H.
  rewrite invperm_of_insertion_sort_list_S in H.
  exact H.
  auto with perm_db.
Qed.
  


Local Transparent perm_inv.


(* Section on stack_perms *)
Lemma stack_perms_left {n0 n1} {f g} {k} :
  k < n0 -> stack_perms n0 n1 f g k = f k.
Proof.
  intros Hk.
  unfold stack_perms.
  replace_bool_lia (k <? n0) true.
  easy.
Qed.

Lemma stack_perms_right {n0 n1} {f g} {k} :
  n0 <= k < n0 + n1 -> stack_perms n0 n1 f g k = g (k - n0) + n0.
Proof.
  intros Hk.
  unfold stack_perms.
  replace_bool_lia (k <? n0) false.
  replace_bool_lia (k <? n0 + n1) true.
  easy.
Qed.

Lemma stack_perms_right_add {n0 n1} {f g} {k} :
  k < n1 -> stack_perms n0 n1 f g (k + n0) = g k + n0.
Proof.
  intros Hk.
  rewrite stack_perms_right; [|lia].
  replace (k + n0 - n0) with k by lia.
  easy.
Qed.

Lemma stack_perms_add_right {n0 n1} {f g} {k} :
  k < n1 -> stack_perms n0 n1 f g (n0 + k) = g k + n0.
Proof.
  rewrite Nat.add_comm.
  exact stack_perms_right_add.
Qed.

Lemma stack_perms_high {n0 n1} {f g} {k} :
	n0 + n1 <= k -> (stack_perms n0 n1 f g) k = k.
Proof.
	intros H.
	unfold stack_perms.
	replace_bool_lia (k <? n0) false. 
	replace_bool_lia (k <? n0 + n1) false.
	easy.
Qed.

Lemma stack_perms_f_idn n0 n1 f :
	stack_perms n0 n1 f idn = fun k => if k <? n0 then f k else k.
Proof. solve_modular_permutation_equalities. Qed. 

Lemma stack_perms_idn_f n0 n1 f : 
	stack_perms n0 n1 idn f = 
	fun k => if (¬ k <? n0) && (k <? n0 + n1) then f (k - n0) + n0 else k.
Proof. solve_modular_permutation_equalities. Qed. 

Lemma stack_perms_idn_idn n0 n1 :
	stack_perms n0 n1 idn idn = idn.
Proof. solve_modular_permutation_equalities. Qed.

#[export] Hint Rewrite stack_perms_idn_idn : perm_cleanup_db.

Lemma stack_perms_compose {n0 n1} {f g} {f' g'} 
	(Hf' : perm_bounded n0 f') (Hg' : perm_bounded n1 g') :
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 f' g'
	= stack_perms n0 n1 (f ∘ f') (g ∘ g'))%prg.
Proof.
	(* destruct Hf' as [Hf'inv Hf']. *)
	(* destruct Hg' as [Hg'inv Hg']. *)
	unfold compose.
	(* bdestruct_one. *)
  solve_modular_permutation_equalities.
	1,2: specialize (Hf' k H); lia.
	- f_equal; f_equal. lia.
	- assert (Hk: k - n0 < n1) by lia.
	  specialize (Hg' _ Hk); lia.
Qed.

#[export] Hint Rewrite @stack_perms_compose 
	using auto with perm_db perm_bounded_db : perm_inv_db.

Lemma stack_perms_assoc {n0 n1 n2} {f g h} :
  stack_perms (n0 + n1) n2 (stack_perms n0 n1 f g) h =
  stack_perms n0 (n1 + n2) f (stack_perms n1 n2 g h).
Proof.
  apply functional_extensionality; intros k.
  unfold stack_perms.
  bdestructΩ'.
  rewrite (Nat.add_comm n0 n1), Nat.add_assoc.
  f_equal; f_equal; f_equal.
  lia.
Qed.

Lemma stack_perms_idn_of_left_right_idn {n0 n1} {f g} 
  (Hf : forall k, k < n0 -> f k = k) (Hg : forall k, k < n1 -> g k = k) :
  stack_perms n0 n1 f g = idn.
Proof.
  solve_modular_permutation_equalities.
  - apply Hf; easy.
  - rewrite Hg; lia.
Qed.

#[export] Hint Resolve stack_perms_idn_of_left_right_idn 
	stack_perms_compose : perm_inv_db.
  


Lemma contract_perm_bounded {n f} (Hf : perm_bounded n f) a : 
  a < n -> 
  perm_bounded (n - 1) (contract_perm f a).
Proof.
  intros Ha k Hk.
  pose proof (Hf a Ha).
  pose proof (Hf k ltac:(lia)).
  pose proof (Hf (k+1) ltac:(lia)).
  unfold contract_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve contract_perm_bounded : perm_bounded_db.

Lemma contract_perm_permutation {n f} (Hf : permutation n f) a :
  a < n ->
  permutation (n - 1) (contract_perm f a).
Proof.
  intros Ha.
  pose proof (fun x y => permutation_eq_iff x y Hf) as Hfinj. 
  destruct Hf as (finv & Hfinv). 
  pose proof (fun k Hk => proj1 (Hfinv k Hk)) as Hfbdd.
  pose proof (fun k Hk => proj1 (proj2 (Hfinv k Hk))) as Hfinvbdd. 
  pose proof (fun k Hk => proj1 (proj2 (proj2(Hfinv k Hk)))) as Hlinv. 
  pose proof (fun k Hk => proj2 (proj2 (proj2(Hfinv k Hk)))) as Hrinv.
  exists (contract_perm finv (f a)).
  intros k Hk.
  repeat split; auto with perm_bounded_db.
  - unfold contract_perm.
    rewrite !(if_dist _ _ _ finv).
    rewrite !Hlinv by lia.
    rewrite !(if_dist _ _ _ (fun x=>x+1)).
    rewrite !(if_dist _ _ _ finv).
    pose proof (Hfinj a k).
    pose proof (Hfinj a (k + 1)).
    bdestructΩ'; rewrite ?Nat.sub_add, ?Hlinv in *; lia.
  - unfold contract_perm.
    rewrite !(if_dist _ _ _ f).
    rewrite !Hrinv, !Hlinv by lia.
    rewrite !(if_dist _ _ _ (fun x=>x+1)).
    rewrite !(if_dist _ _ _ f).
    assert (Hfeqiff : forall a b, a < n -> b < n ->
      f a = b <-> finv b = a) by
      (intros; split; intros <-; now rewrite ?Hlinv, ?Hrinv by lia).
    pose proof (Hfeqiff a k).
    pose proof (Hfeqiff a (k+1)).
    bdestructΩ'; rewrite ?Nat.sub_add, ?Hrinv in * by lia; lia.
Qed.

#[export] Hint Resolve contract_perm_permutation : perm_db.

Lemma contract_perm_WF n f a : WF_Perm n f -> a < n -> f a < n ->
  WF_Perm (n - 1) (contract_perm f a).
Proof.
  intros Hf Ha Hfa.
  intros k Hk.
  unfold contract_perm.
  bdestruct (a =? f a); [
    replace <- (f a) in *;
    bdestructΩ'; 
    rewrite ?Hf in * by lia; try lia|
  ].
  bdestructΩ';
  rewrite ?Hf in * by lia; lia.
Qed.

#[export] Hint Extern 0 (WF_Perm _ (contract_perm _ _)) =>
  apply contract_perm_WF;
  [| auto using permutation_is_bounded 
    with perm_bounded_db..] : WF_Perm_db.

Lemma contract_perm_inv n f (Hf : permutation n f) a :
  a < n ->
  forall k, k < n - 1 -> 
  perm_inv (n - 1) (contract_perm f a) k = 
  contract_perm (perm_inv n f) (f a) k.
Proof.
  intros Ha k Hk.
  pose proof (permutation_is_bounded _ _ Hf) as Hfbdd.
  pose proof (perm_inv_bounded n f) as Hfinvbdd.
  pose proof (Hfbdd a Ha).
  pose proof (perm_inv_is_linv_of_permutation n f Hf) as Hlinv.
  pose proof (perm_inv_is_rinv_of_permutation n f Hf) as Hrinv.
  rewrite perm_inv_eq_iff; auto with perm_db perm_bounded_db.
  unfold contract_perm.
  rewrite !(if_dist _ _ _ f).
  rewrite !Hrinv, !Hlinv by lia.
  rewrite !(if_dist _ _ _ (fun x=>x+1)).
  rewrite !(if_dist _ _ _ f).
  assert (Hfeqiff : forall a b, a < n -> b < n ->
    f a = b <-> perm_inv n f b = a) by
    (intros; split; intros <-; now rewrite ?Hlinv, ?Hrinv by lia).
  pose proof (Hfeqiff a k).
  pose proof (Hfeqiff a (k+1)).
  bdestructΩ'; rewrite ?Nat.sub_add, ?Hrinv in * by lia; lia.
Qed.

#[export] Hint Resolve contract_perm_inv : perm_inv_db.

Lemma contract_perm_perm_eq_of_perm_eq n f g a : 
  a < n -> perm_eq n f g -> 
  perm_eq (n - 1) (contract_perm f a) (contract_perm g a).
Proof.
  intros Ha Hfg.
  intros k Hk.
  unfold contract_perm.
  now rewrite !Hfg by lia.
Qed.

#[export] Hint Resolve contract_perm_perm_eq_of_perm_eq : perm_inv_db.

Lemma contract_perm_inv' {n f} (Hf : permutation n f) a :
  WF_Perm n f ->
  a < n -> 
  perm_inv' (n - 1) (contract_perm f a) = 
  contract_perm (perm_inv' n f) (f a).
Proof.
  intros Hfwf Ha.
  eq_by_WF_perm_eq (n-1).
  auto with perm_inv_db.
  apply (perm_eq_trans
    (perm_inv'_eq _ _)).
  apply (perm_eq_trans
    (contract_perm_inv n f Hf a Ha)).
  eauto with perm_db perm_inv_db.
Qed.

#[export] Hint Rewrite @contract_perm_inv' 
  using (match goal with 
  | |- WF_Perm _ _ => solve [auto with WF_Perm_db perm_db perm_inv_db]
  | |- _ => auto with perm_db
  end) : perm_inv_db.

(* Section on rotr / rotl *)
Lemma rotr_WF {n m} : 
  WF_Perm n (rotr n m).
Proof. intros k Hk. unfold rotr. bdestruct_one; lia. Qed.

Lemma rotl_WF {n m} : 
	WF_Perm n (rotl n m).
Proof. intros k Hk. unfold rotl. bdestruct_one; lia. Qed.

#[export] Hint Resolve rotr_WF rotl_WF : WF_Perm_db.

Lemma rotr_bdd {n m} : 
	forall k, k < n -> (rotr n m) k < n.
Proof.
	intros. unfold rotr. bdestruct_one; [lia|].
	apply Nat.mod_upper_bound; lia.
Qed.

Lemma rotl_bdd {n m} : 
	forall k, k < n -> (rotl n m) k < n.
Proof.
	intros. unfold rotl. bdestruct_one; [lia|].
	apply Nat.mod_upper_bound; lia.
Qed.

#[export] Hint Resolve rotr_bdd rotl_bdd : perm_bounded_db.

Lemma rotr_rotl_inv n m :
	((rotr n m) ∘ (rotl n m) = idn)%prg.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, rotl, rotr.
	bdestruct (n <=? k); [bdestructΩ'|].
	assert (Hn0 : n <> 0) by lia.
	bdestruct_one.
	- pose proof (Nat.mod_upper_bound (k + (n - m mod n)) n Hn0) as Hbad.
	  lia. (* contradict Hbad *)
	- rewrite Nat.Div0.add_mod_idemp_l.
	  rewrite <- Nat.add_assoc.
	  replace (n - m mod n + m) with
	    (n - m mod n + (n * (m / n) + m mod n)) by
	    (rewrite <- (Nat.div_mod m n Hn0); easy).
	  pose proof (Nat.mod_upper_bound m n Hn0).
	  replace (n - m mod n + (n * (m / n) + m mod n)) with
	    (n * (1 + m / n)) by lia.
	  rewrite Nat.mul_comm, Nat.Div0.mod_add.
	  apply Nat.mod_small, H.
Qed.

Lemma rotl_rotr_inv n m : 
	((rotl n m) ∘ (rotr n m) = idn)%prg.
Proof.
	apply functional_extensionality; intros k.
	unfold compose, rotl, rotr.
	bdestruct (n <=? k); [bdestructΩ'|].
	assert (Hn0 : n <> 0) by lia.
	bdestruct_one.
	- pose proof (Nat.mod_upper_bound (k + m) n Hn0) as Hbad.
	  lia. (* contradict Hbad *)
	- rewrite Nat.Div0.add_mod_idemp_l.
	  rewrite <- Nat.add_assoc.
    rewrite (Nat.div_mod_eq m n) at 1.
	  pose proof (Nat.mod_upper_bound m n Hn0).
	  replace ((n * (m / n) + m mod n) + (n - m mod n)) with
	    (n * (1 + m / n)) by lia.
	  rewrite Nat.mul_comm, Nat.Div0.mod_add.
	  apply Nat.mod_small, H.
Qed.

#[export] Hint Rewrite rotr_rotl_inv rotl_rotr_inv : perm_inv_db.

Lemma rotr_perm {n m} : permutation n (rotr n m).
Proof. 
	perm_by_inverse (rotl n m).
Qed.

Lemma rotl_perm {n m} : permutation n (rotl n m).
Proof. 
	perm_by_inverse (rotr n m).
Qed.

#[export] Hint Resolve rotr_perm rotl_perm : perm_db.


(* This is the start of the actual section *)
Lemma rotr_0_r n : rotr n 0 = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold rotr.
	bdestructΩ'.
	rewrite Nat.mod_small; lia.
Qed.

Lemma rotl_0_r n : rotl n 0 = idn.
Proof.
	apply functional_extensionality; intros k.
	unfold rotl.
	bdestructΩ'.
	rewrite Nat.Div0.mod_0_l, Nat.sub_0_r.
	replace (k + n) with (k + 1 * n) by lia.
	rewrite Nat.Div0.mod_add, Nat.mod_small; lia.
Qed.

Lemma rotr_0_l k : rotr 0 k = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotr.
	bdestructΩ'.
Qed.
	
Lemma rotl_0_l k : rotl 0 k = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotl.
	bdestructΩ'.
Qed.

#[export] Hint Rewrite rotr_0_r rotl_0_r rotr_0_l rotl_0_l : perm_cleanup_db.

Lemma rotr_rotr n k l :
	((rotr n k) ∘ (rotr n l) = rotr n (k + l))%prg.
Proof.
	apply functional_extensionality; intros a.
	unfold compose, rotr.
	symmetry.
	bdestructΩ'.
	- pose proof (Nat.mod_upper_bound (a + l) n); lia.
	- rewrite Nat.Div0.add_mod_idemp_l.
	  f_equal; lia.
Qed.

Lemma rotl_rotl n k l :
	((rotl n k) ∘ (rotl n l) = rotl n (k + l))%prg.
Proof.

	permutation_eq_by_WF_inv_inj (rotr n (k + l)) n.
  rewrite Nat.add_comm, <- rotr_rotr, <- compose_assoc, 
    (compose_assoc _ _ _ _ (rotr n l)).
  cleanup_perm.
Qed.

#[export] Hint Rewrite rotr_rotr rotl_rotl : perm_cleanup_db.

Lemma rotr_n n : rotr n n = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotr.
	bdestructΩ'.
	replace (a + n) with (a + 1 * n) by lia.
	destruct n; [lia|].
	rewrite Nat.Div0.mod_add.
	rewrite Nat.mod_small; easy.
Qed.

#[export] Hint Rewrite rotr_n : perm_cleanup_db.

Lemma rotr_eq_rotr_mod n k : rotr n k = rotr n (k mod n).
Proof.
	strong induction k.
	bdestruct (k <? n).
	- rewrite Nat.mod_small; easy.
	- specialize (H (k - 1 * n)).
	  replace (rotr n k) with (rotr n (k - 1*n + n)) by (f_equal;lia).
	  destruct n.
    1: cleanup_perm; easy. (* rewrite rotr_0_l. symmetry. rewrite rotr_0_l. easy. *)
	  rewrite <- rotr_rotr, rotr_n, H; [|lia].
	  rewrite compose_idn_r.
	  rewrite sub_mul_mod; [easy|lia].
Qed.

Lemma rotl_n n : rotl n n = idn.
Proof.
  permutation_eq_by_WF_inv_inj (rotr n n) n.
Qed.

#[export] Hint Rewrite rotl_n : perm_cleanup_db.

Lemma rotl_eq_rotl_mod n k : rotl n k = rotl n (k mod n).
Proof. 
  permutation_eq_by_WF_inv_inj (rotr n k) n.
  rewrite rotr_eq_rotr_mod, rotl_rotr_inv; easy.
Qed.

Lemma rotr_eq_rotl_sub n k : 
	rotr n k = rotl n (n - k mod n).
Proof.
	rewrite rotr_eq_rotr_mod.
  permutation_eq_by_WF_inv_inj (rotl n (k mod n)) n.
  cleanup_perm.
	destruct n; [rewrite rotl_0_l; easy|].
  assert (H': S n <> 0) by easy.
  pose proof (Nat.mod_upper_bound k _ H'). 
  rewrite <- (rotl_n (S n)).
  f_equal.
  lia.
Qed.

Lemma rotl_eq_rotr_sub n k : 
	rotl n k = rotr n (n - k mod n).
Proof.
  permutation_eq_by_WF_inv_inj (rotr n k) n.
	destruct n; [cbn; rewrite 2!rotr_0_l, compose_idn_l; easy|].
  rewrite (rotr_eq_rotr_mod _ k), rotr_rotr, <- (rotr_n (S n)).
  f_equal.
  assert (H' : S n <> 0) by easy.
  pose proof (Nat.mod_upper_bound k (S n) H').
  lia.
Qed.

Lemma rotr_add_n_l n k : 
	rotr n (n + k) = rotr n k.
Proof.
	rewrite rotr_eq_rotr_mod.
	rewrite Nat.add_comm, mod_add_n_r.
	now rewrite <- rotr_eq_rotr_mod.
Qed.

Lemma rotr_add_n_r n k : 
	rotr n (k + n) = rotr n k.
Proof.
	rewrite rotr_eq_rotr_mod.
	rewrite mod_add_n_r.
	now rewrite <- rotr_eq_rotr_mod.
Qed.

#[export] Hint Rewrite rotr_add_n_r rotr_add_n_l : perm_cleanup_db.



Lemma reflect_perm_invol n k : 
  reflect_perm n (reflect_perm n k) = k.
Proof.
  unfold reflect_perm; bdestructΩ'.
Qed.

Lemma reflect_perm_invol_eq n : 
  reflect_perm n ∘ reflect_perm n = idn.
Proof.
  apply functional_extensionality, reflect_perm_invol.
Qed.

#[export] Hint Rewrite reflect_perm_invol reflect_perm_invol_eq : perm_inv_db.

Lemma reflect_perm_bounded n : perm_bounded n (reflect_perm n).
Proof.
  intros k Hk.
  unfold reflect_perm; bdestructΩ'.
Qed.

#[export] Hint Resolve reflect_perm_bounded : perm_bounded_db.

Lemma reflect_perm_permutation n : 
  permutation n (reflect_perm n).
Proof.
  perm_by_inverse (reflect_perm n).
Qed.

#[export] Hint Resolve reflect_perm_permutation : perm_db.

Lemma reflect_perm_WF n : WF_Perm n (reflect_perm n).
Proof.
  intros k Hk; unfold reflect_perm; bdestructΩ'.
Qed.

#[export] Hint Resolve reflect_perm_WF : WF_Perm_db.

Lemma reflect_perm_inv n : 
  perm_eq n (perm_inv n (reflect_perm n)) (reflect_perm n).
Proof.
  perm_eq_by_inv_inj (reflect_perm n) n.
Qed.

#[export] Hint Resolve reflect_perm_inv : perm_inv_db.
#[export] Hint Rewrite reflect_perm_inv : perm_inv_db.

Lemma reflect_perm_inv' n : 
  perm_inv' n (reflect_perm n) = reflect_perm n.
Proof.
  eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite reflect_perm_inv : perm_inv_db.



Lemma swap_block_perm_sub padl padm m a k : 
  m <= k ->
  swap_block_perm padl padm a (k - m) =
  swap_block_perm (m + padl) padm a k - m.
Proof.
  intros Hk.
  unfold swap_block_perm.
  bdestructΩ'.
Qed.

Lemma swap_block_perm_invol padl padm a k : 
  swap_block_perm padl padm a (swap_block_perm padl padm a k) = k.
Proof.
  unfold swap_block_perm.
  bdestructΩ'.
Qed.

Lemma swap_block_perm_invol_eq padl padm a : 
  swap_block_perm padl padm a ∘ swap_block_perm padl padm a = idn.
Proof.
  apply functional_extensionality, swap_block_perm_invol.
Qed.

#[export] Hint Rewrite swap_block_perm_invol 
  swap_block_perm_invol_eq : perm_inv_db.

Lemma swap_block_perm_bounded padl padm padr a : 
  perm_bounded (padl + a + padm + a + padr) (swap_block_perm padl padm a).
Proof.
  intros k Hk.
  unfold swap_block_perm.
  bdestructΩ'.
Qed.

Lemma swap_block_perm_bounded_alt padl padm padr a : 
  perm_bounded (padr + a + padm + a + padl) (swap_block_perm padl padm a).
Proof.
  replace (padr + a + padm + a + padl) 
    with (padl + a + padm + a + padr) by lia.
  apply swap_block_perm_bounded.
Qed.

#[export] Hint Resolve swap_block_perm_bounded 
  swap_block_perm_bounded_alt : perm_bounded_db.

Lemma swap_block_perm_permutation padl padm padr a : 
  permutation (padl + a + padm + a + padr) (swap_block_perm padl padm a).
Proof. 
  perm_by_inverse (swap_block_perm padl padm a).
Qed.

Lemma swap_block_perm_permutation_alt padl padm padr a : 
  permutation (padr + a + padm + a + padl) (swap_block_perm padl padm a).
Proof. 
  perm_by_inverse (swap_block_perm padl padm a).
Qed.

#[export] Hint Resolve swap_block_perm_permutation
  swap_block_perm_permutation_alt : perm_db.

Lemma swap_block_perm_WF padl padm padr a : 
  WF_Perm (padl + a + padm + a + padr) (swap_block_perm padl padm a).
Proof.
  unfold swap_block_perm.
  intros k Hk; bdestructΩ'.
Qed.

Lemma swap_block_perm_WF_alt padl padm padr a : 
  WF_Perm (padl + a + padm + a + padr) (swap_block_perm padr padm a).
Proof.
  unfold swap_block_perm.
  intros k Hk; bdestructΩ'.
Qed.

#[export] Hint Resolve swap_block_perm_WF 
  swap_block_perm_WF_alt : WF_Perm_db.

Lemma swap_block_perm_inv padl padm padr a :
  perm_eq (padl + a + padm + a + padr) 
    (perm_inv (padl + a + padm + a + padr) 
    (swap_block_perm padl padm a)) 
    (swap_block_perm padl padm a).
Proof.
  perm_eq_by_inv_inj (swap_block_perm padl padm a) 
    (padl + a + padm + a + padr).
Qed.

Lemma swap_block_perm_inv_alt padl padm padr a :
  perm_eq (padl + a + padm + a + padr) 
    (perm_inv (padl + a + padm + a + padr) 
    (swap_block_perm padr padm a)) 
    (swap_block_perm padr padm a).
Proof.
  perm_eq_by_inv_inj (swap_block_perm padr padm a) 
    (padl + a + padm + a + padr).
Qed.

#[export] Hint Resolve swap_block_perm_inv 
  swap_block_perm_inv_alt : perm_inv_db.

Lemma swap_block_perm_inv' padl padm padr a :
  perm_inv' (padl + a + padm + a + padr) 
    (swap_block_perm padl padm a) =  
  swap_block_perm padl padm a.
Proof.
  eq_by_WF_perm_eq (padl + a + padm + a + padr).
  cleanup_perm_inv.
Qed.

Lemma swap_block_perm_inv'_alt padl padm padr a :
  perm_inv' (padl + a + padm + a + padr) 
    (swap_block_perm padr padm a) =
  swap_block_perm padr padm a.
Proof.
  eq_by_WF_perm_eq (padl + a + padm + a + padr).
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite swap_block_perm_inv' 
  swap_block_perm_inv'_alt : perm_inv_db.


Lemma rotr_decomp n m : 
  rotr n m = 
  fun k =>
  if n <=? k then k else
  if k + m mod n <? n then k + m mod n else
    k + m mod n - n.
Proof.
  apply functional_extensionality; intros k.
  unfold rotr.
  bdestructΩ'.
  - rewrite Nat.Div0.add_mod.
    rewrite (Nat.mod_small k) by easy.
    now apply Nat.mod_small.
  - rewrite Nat.Div0.add_mod.
    rewrite (Nat.mod_small k) by easy.
    now rewrite mod_n_to_2n by (split; show_moddy_lt).
Qed.



#[export] Hint Resolve qubit_perm_to_nat_perm_bij : perm_db.
#[export] Hint Rewrite qubit_perm_to_nat_perm_compose : perm_inv_db.

Lemma qubit_perm_to_nat_perm_perm_eq {n} (f g : nat -> nat) 
  (Heq : perm_eq n f g) :
  perm_eq (2^n)
    (qubit_perm_to_nat_perm n f) 
    (qubit_perm_to_nat_perm n g).
Proof.
  intros k Hk.
  unfold qubit_perm_to_nat_perm.
  apply funbool_to_nat_eq.
  intros x Hx.
  unfold compose.
  rewrite Heq; easy.
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_perm_eq : perm_inv_db.

Lemma qubit_perm_to_nat_perm_idn n :
  perm_eq (2^n) (qubit_perm_to_nat_perm n idn) idn.
Proof.
  intros k Hk.
  unfold qubit_perm_to_nat_perm.
  rewrite compose_idn_r.
  now apply nat_to_funbool_inverse.
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_idn : perm_inv_db.

Lemma qubit_perm_to_nat_perm_id n f 
  (Hf : perm_eq n f idn) : 
  perm_eq (2^n) (qubit_perm_to_nat_perm n f) idn.
Proof.
  eapply (fun H => perm_eq_trans H 
    (qubit_perm_to_nat_perm_idn n)).
  auto with perm_inv_db.
Qed. 

#[export] Hint Resolve qubit_perm_to_nat_perm_id : perm_inv_db.

Lemma qubit_perm_to_nat_perm_inv n f (Hf : permutation n f) : 
  perm_eq (2^n) 
  (perm_inv (2^n) (qubit_perm_to_nat_perm n f))
  (qubit_perm_to_nat_perm n (perm_inv n f)).
Proof.
  perm_eq_by_inv_inj (qubit_perm_to_nat_perm n f) (2^n).
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_inv : perm_inv_db.

(* Section for swap_2_perm *)
Lemma swap_2_perm_invol : 
  swap_2_perm ∘ swap_2_perm = idn.
Proof.
  apply functional_extensionality; intros k.
  repeat first [easy | destruct k].
Qed.

#[export] Hint Rewrite swap_2_perm_invol : perm_inv_db.

Lemma swap_2_perm_bounded k :
  k < 2 -> swap_2_perm k < 2.
Proof.
  intros Hk.
  repeat first [easy | destruct k | cbn; lia].
Qed.

#[export] Hint Resolve swap_2_perm_bounded : perm_bounded_db.

Lemma swap_2_WF k : 1 < k -> swap_2_perm k = k.
Proof.
  intros. 
  repeat first [easy | lia | destruct k].
Qed.

Lemma swap_2_WF_Perm : WF_Perm 2 swap_2_perm.
Proof.
  intros k. 
  repeat first [easy | lia | destruct k].
Qed.

Global Hint Resolve swap_2_WF_Perm : WF_Perm_db.

Lemma swap_2_perm_permutation : permutation 2 swap_2_perm.
Proof. 
  perm_by_inverse swap_2_perm.
Qed.

Global Hint Resolve swap_2_perm_permutation : perm_db.

Lemma swap_2_perm_inv :
	perm_eq 2 
  (perm_inv 2 swap_2_perm) swap_2_perm.
Proof.
	perm_eq_by_inv_inj swap_2_perm 2.
Qed.

Lemma swap_2_perm_inv' :
	perm_inv' 2 swap_2_perm = swap_2_perm.
Proof.
	permutation_eq_by_WF_inv_inj swap_2_perm 2.
Qed.

#[export] Hint Resolve swap_2_perm_inv : perm_inv_db.
#[export] Hint Rewrite swap_2_perm_inv' : perm_inv_db.







(* Section for stack_perms *)
Lemma stack_perms_WF_idn n0 n1 f 
	(H : WF_Perm n0 f) : 
	stack_perms n0 n1 f idn = f.
Proof.
	solve_modular_permutation_equalities;
	rewrite H; lia.
Qed.

#[export] Hint Rewrite stack_perms_WF_idn 
	using (solve [auto with WF_Perm_db]) : perm_inv_db.

Lemma stack_perms_WF n0 n1 f g :
	WF_Perm (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestructΩ'.
Qed.

Global Hint Resolve stack_perms_WF : WF_Perm_db.

Lemma stack_perms_bounded {n0 n1} {f g} : 
	perm_bounded n0 f -> perm_bounded n1 g ->
  perm_bounded (n0 + n1) (stack_perms n0 n1 f g).
Proof.
	intros Hf Hg.
  intros k Hk.
  unfold stack_perms.
  bdestruct (k <? n0).
  - specialize (Hf k H). lia.
  - bdestruct (k <? n0 + n1); [|easy].
    assert (Hkn0 : k - n0 < n1) by lia.
    specialize (Hg _ Hkn0). lia.
Qed. 

#[export] Hint Resolve stack_perms_bounded : perm_bounded_db.

Lemma stack_perms_rinv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv = idn.
Proof.
  unfold compose.
  solve_modular_permutation_equalities.
  1-3: specialize (Hf _ H); lia.
  - replace (ginv (k - n0) + n0 - n0) with (ginv (k - n0)) by lia.
    assert (Hkn0: k - n0 < n1) by lia.
    specialize (Hg _ Hkn0).
    lia.
  - assert (Hkn0: k - n0 < n1) by lia.
    specialize (Hg _ Hkn0).
    lia.
Qed.

Lemma stack_perms_linv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_perms n0 n1 finv ginv ∘ stack_perms n0 n1 f g = idn.
Proof.
  rewrite stack_perms_rinv.
  2,3: rewrite is_inv_iff_inv_is.
  all: easy.
Qed.

Lemma stack_perms_perm_eq_inv_of_perm_eq_inv {n0 n1} {f g} {finv ginv}
  (Hf : perm_eq n0 (f ∘ finv) idn) 
	(Hg : perm_eq n1 (g ∘ ginv) idn) 
	(Hfinv : perm_bounded n0 finv)
	(Hginv : perm_bounded n1 ginv) :
	perm_eq (n0 + n1) 
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv)
	idn.
Proof.
  unfold compose in *.
	intros k Hk.
	unfold stack_perms.
	specialize (Hfinv k).
	specialize (Hginv (k - n0)).
	bdestructΩ'; auto.
	rewrite Nat.add_sub.
	rewrite Hg; lia.
Qed.

#[export] Hint Resolve stack_perms_perm_eq_inv_of_perm_eq_inv : perm_inv_db.

Lemma stack_perms_inv_of_perm_eq_inv {n0 n1} {f g} {finv ginv}
  (Hf : perm_eq n0 (f ∘ finv) idn) 
	(Hg : perm_eq n1 (g ∘ ginv) idn) 
	(Hfinv : perm_bounded n0 finv)
	(Hginv : perm_bounded n1 ginv) :
	stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv = idn.
Proof.
	eq_by_WF_perm_eq (n0 + n1).
	auto with perm_inv_db.
Qed.

#[export] Hint Resolve stack_perms_inv_of_perm_eq_inv : perm_inv_db.

#[export] Hint Resolve permutation_is_bounded : perm_bounded_db.

Lemma stack_perms_permutation {n0 n1 f g} (Hf : permutation n0 f) (Hg: permutation n1 g) :
  permutation (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  perm_by_inverse (stack_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Qed.

#[export] Hint Resolve stack_perms_permutation : perm_db.

Lemma perm_inv_stack_perms n m f g 
  (Hf : permutation n f) (Hg : permutation m g) : 
  perm_eq (n + m)
  (perm_inv (n + m) (stack_perms n m f g))
  (stack_perms n m (perm_inv n f) (perm_inv m g)).
Proof.
  perm_eq_by_inv_inj (stack_perms n m f g) (n+m).
Qed.


Lemma stack_perms_proper {n0 n1} {f f' g g'} 
  (Hf : perm_eq n0 f f') (Hg : perm_eq n1 g g') : 
  perm_eq (n0 + n1) 
    (stack_perms n0 n1 f g)
    (stack_perms n0 n1 f' g').
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestructΩ'; [apply Hf | f_equal; apply Hg]; lia.
Qed.

#[export] Hint Resolve stack_perms_proper : perm_inv_db.

Lemma stack_perms_proper_eq {n0 n1} {f f' g g'} 
  (Hf : perm_eq n0 f f') (Hg : perm_eq n1 g g') : 
  stack_perms n0 n1 f g =
  stack_perms n0 n1 f' g'.
Proof.
  eq_by_WF_perm_eq (n0 + n1); cleanup_perm_inv.
Qed.

#[export] Hint Resolve stack_perms_proper_eq : perm_inv_db.

Lemma perm_inv'_stack_perms n m f g 
  (Hf : permutation n f) (Hg : permutation m g) : 
  perm_inv' (n + m) (stack_perms n m f g) = 
  stack_perms n m (perm_inv' n f) (perm_inv' m g).
Proof.
  permutation_eq_by_WF_inv_inj (stack_perms n m f g) (n+m).
Qed.

#[export] Hint Rewrite @perm_inv'_stack_perms 
	using auto with perm_db : perm_inv_db.

Lemma rotr_inv n m : 
	perm_eq n (perm_inv n (rotr n m)) (rotl n m).
Proof.
	perm_eq_by_inv_inj (rotr n m) n.
Qed.

Lemma rotr_inv' n m : 
	perm_inv' n (rotr n m) = rotl n m.
Proof.
	permutation_eq_by_WF_inv_inj (rotr n m) n.
Qed.

Lemma rotl_inv n m : 
	perm_eq n (perm_inv n (rotl n m)) (rotr n m).
Proof.
	perm_eq_by_inv_inj (rotl n m) n.
Qed.

Lemma rotl_inv' n m : 
	perm_inv' n (rotl n m) = rotr n m.
Proof.
	permutation_eq_by_WF_inv_inj (rotl n m) n.
Qed.

#[export] Hint Resolve rotr_inv rotl_inv : perm_inv_db.
#[export] Hint Rewrite rotr_inv rotr_inv' rotl_inv rotl_inv' : perm_inv_db.














Definition kron_comm_perm p q :=
  fun k => if p * q <=? k then k else
  k mod p * q + k / p.

Lemma kron_comm_perm_WF p q : 
	WF_Perm (p * q) (kron_comm_perm p q).
Proof.
	intros k Hk; unfold kron_comm_perm; bdestructΩ'.
Qed.

Lemma kron_comm_perm_WF_alt p q : 
	WF_Perm (q * p) (kron_comm_perm p q).
Proof.
	rewrite Nat.mul_comm; apply kron_comm_perm_WF.
Qed.

#[export] Hint Resolve kron_comm_perm_WF kron_comm_perm_WF_alt : WF_Perm_db.

Lemma kron_comm_perm_bounded p q : 
	perm_bounded (p * q) (kron_comm_perm p q).
Proof.
	intros k Hk.
	unfold kron_comm_perm.
	bdestructΩ'.
	show_moddy_lt.
Qed.

Lemma kron_comm_perm_bounded_alt p q : 
	perm_bounded (q * p) (kron_comm_perm p q).
Proof.
	rewrite Nat.mul_comm.
	apply kron_comm_perm_bounded.
Qed.

#[export] Hint Resolve kron_comm_perm_bounded 
	kron_comm_perm_bounded_alt : perm_bounded_db.

Lemma kron_comm_perm_pseudo_invol_perm_eq p q : 
  perm_eq (p * q) (kron_comm_perm p q ∘ kron_comm_perm q p)%prg idn.
Proof.
	intros k Hk.
	unfold compose, kron_comm_perm.
	simplify_bools_lia_one_kernel.
	simplify_bools_moddy_lia_one_kernel.
	rewrite (Nat.add_comm _ (k/q)).
	rewrite Nat.Div0.mod_add, Nat.div_add by show_nonzero.
	rewrite Nat.Div0.div_div, Nat.mod_small by show_moddy_lt.
	rewrite (Nat.div_small k (q*p)) by lia.
	symmetry. 
	rewrite (Nat.div_mod_eq k q) at 1; lia.
Qed.

#[export] Hint Resolve kron_comm_perm_pseudo_invol_perm_eq : perm_inv_db.

Lemma kron_comm_perm_pseudo_invol_alt_perm_eq p q : 
  perm_eq (q * p) (kron_comm_perm p q ∘ kron_comm_perm q p)%prg idn.
Proof.
	rewrite Nat.mul_comm; cleanup_perm_inv.
Qed.

#[export] Hint Resolve kron_comm_perm_pseudo_invol_alt_perm_eq : perm_inv_db.

Lemma kron_comm_perm_pseudo_invol p q : 
	kron_comm_perm p q ∘ kron_comm_perm q p = idn.
Proof.
	eq_by_WF_perm_eq (p*q); cleanup_perm_inv.
Qed.

#[export] Hint Rewrite kron_comm_perm_pseudo_invol : perm_inv_db.

Lemma kron_comm_perm_permutation p q : 
	permutation (p * q) (kron_comm_perm p q).
Proof.
	perm_by_inverse (kron_comm_perm q p).
Qed.

Lemma kron_comm_perm_permutation_alt p q : 
	permutation (q * p) (kron_comm_perm p q).
Proof.
	perm_by_inverse (kron_comm_perm q p).
Qed.

#[export] Hint Resolve kron_comm_perm_permutation 
	kron_comm_perm_permutation_alt : perm_db.

Lemma kron_comm_perm_inv p q : 
	perm_eq (p * q) 
		(perm_inv (p * q) (kron_comm_perm p q))
		(kron_comm_perm q p).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm p q) (p * q).
Qed.

Lemma kron_comm_perm_inv_alt p q : 
	perm_eq (q * p) 
		(perm_inv (p * q) (kron_comm_perm p q))
		(kron_comm_perm q p).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm p q) (q * p).
Qed.

Lemma kron_comm_perm_swap_inv p q : 
	perm_eq (p * q) 
		(perm_inv (p * q) (kron_comm_perm q p))
		(kron_comm_perm p q).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm q p) (p * q).
Qed.

Lemma kron_comm_perm_swap_inv_alt p q : 
	perm_eq (q * p) 
		(perm_inv (p * q) (kron_comm_perm q p))
		(kron_comm_perm p q).
Proof.
	perm_eq_by_inv_inj (kron_comm_perm q p) (q * p).
Qed.

#[export] Hint Resolve kron_comm_perm_inv
	kron_comm_perm_inv_alt 
	kron_comm_perm_swap_inv 
	kron_comm_perm_swap_inv_alt : perm_inv_db.

Lemma kron_comm_perm_inv' p q : 
	perm_inv' (p * q) (kron_comm_perm p q) =
	kron_comm_perm q p.
Proof.
	eq_by_WF_perm_eq (p * q).
	cleanup_perm_inv.
Qed.

Lemma kron_comm_perm_inv'_alt p q : 
	perm_inv' (q * p) (kron_comm_perm p q) =
	kron_comm_perm q p.
Proof.
	eq_by_WF_perm_eq (q * p).
	cleanup_perm_inv.
Qed.

#[export] Hint Rewrite kron_comm_perm_inv'
	kron_comm_perm_inv'_alt : perm_inv_db.

#[export] Hint Resolve compose_WF_Perm : WF_Perm_db.

Lemma swap_block_perm_decomp_eq padl padr padm a : 
  swap_block_perm padl padm a = 
  stack_perms padl (a + padm + a + padr) idn 
    (stack_perms (a + padm + a) padr
     ((stack_perms (a + padm) a (rotr (a + padm) a) idn) ∘
     rotr (a + padm + a) (a + padm)) idn).
Proof.
  rewrite 2!stack_perms_WF_idn by 
		eauto using monotonic_WF_Perm with WF_Perm_db zarith.
  rewrite 2!rotr_decomp.
  pose proof (Nat.mod_small (a + padm) (a + padm + a)) as Hsm.
  pose proof (Nat.mod_small (a) (a + padm)) as Hsm'.
  pose proof (Nat.mod_upper_bound (a + padm) (a + padm + a)) as Hl.
  pose proof (Nat.mod_upper_bound (a) (a + padm)) as Hl'.
  assert (Hpadm0: padm = 0 -> a mod (a + padm) = 0) by 
    (intros ->; rewrite Nat.add_0_r, Nat.Div0.mod_same; easy).
  rewrite stack_perms_idn_f.
  unfold swap_block_perm.
  apply functional_extensionality; intros k.
  unfold compose.
  bdestruct (a =? 0); 
  [subst; 
  rewrite ?Nat.add_0_r, ?Nat.add_0_l, ?Nat.Div0.mod_same in *;
  bdestructΩ'|].
  rewrite Hsm in * by lia.
  bdestruct (padm =? 0);
  [subst; 
  rewrite ?Nat.add_0_r, ?Nat.add_0_l, ?Nat.Div0.mod_same in *;
  bdestructΩ'|].
  rewrite Hsm' in * by lia.
  bdestructΩ'.
Qed.



Lemma tensor_perms_bounded n0 n1 f g : 
	perm_bounded n0 f -> perm_bounded n1 g ->
	perm_bounded (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	intros Hf Hg k Hk.
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	pose proof (Hf (k / n1) ltac:(show_moddy_lt)).
	pose proof (Hg (k mod n1) ltac:(show_moddy_lt)).
	show_moddy_lt.
Qed.

#[export] Hint Resolve tensor_perms_bounded : perm_bounded_db.

Lemma tensor_perms_WF n0 n1 f g :
	WF_Perm (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	intros k Hk.
	unfold tensor_perms.
	bdestructΩ'.
Qed.

#[export] Hint Resolve tensor_perms_WF : WF_Perm_db.
#[export] Hint Extern 100 (WF_Perm ?n01 (tensor_perms ?n0 ?n1 ?f ?g)) =>
	replace n01 with (n0 * n1) by nia : WF_Perm_db.

Lemma tensor_perms_compose n0 n1 f0 f1 g0 g1 : 
	perm_bounded n0 f1 -> perm_bounded n1 g1 ->
	tensor_perms n0 n1 f0 g0 ∘ tensor_perms n0 n1 f1 g1 = 
	tensor_perms n0 n1 (f0 ∘ f1) (g0 ∘ g1).
Proof.
	intros Hf1 Hg1.
	eq_by_WF_perm_eq (n0*n1).
	intros k Hk.
	unfold compose.
	generalize (tensor_perms_bounded n0 n1 f1 g1 Hf1 Hg1 k Hk).
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	intros ?.
	simplify_bools_lia_one_kernel.
	rewrite Nat.div_add_l by lia.
	pose proof (Hf1 (k / n1) ltac:(show_moddy_lt)).
	pose proof (Hg1 (k mod n1) ltac:(show_moddy_lt)).
	rewrite (Nat.div_small (g1 _)), mod_add_l, Nat.mod_small by easy.
	now rewrite Nat.add_0_r.
Qed.

#[export] Hint Rewrite tensor_perms_compose : perm_cleanup_db perm_inv_db.

Lemma tensor_perms_0_l n1 f g : 
	tensor_perms 0 n1 f g = idn.
Proof.
	eq_by_WF_perm_eq (0 * n1).
Qed.

Lemma tensor_perms_0_r n0 f g : 
	tensor_perms n0 0 f g = idn.
Proof.
	eq_by_WF_perm_eq (n0 * 0).
	lia.
Qed.

#[export] Hint Rewrite tensor_perms_0_l 
	tensor_perms_0_r : perm_cleanup_db perm_inv_db.

Lemma tensor_perms_perm_eq_proper n0 n1 f f' g g' : 
	perm_eq n0 f f' -> perm_eq n1 g g' ->
	tensor_perms n0 n1 f g = tensor_perms n0 n1 f' g'.
Proof.
	intros Hf' Hg'.
	eq_by_WF_perm_eq (n0 * n1).
	intros k Hk.
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	now rewrite Hf', Hg' by show_moddy_lt.
Qed.

#[export] Hint Resolve tensor_perms_perm_eq_proper : perm_inv_db.

Lemma tensor_perms_idn_idn n0 n1 :
	tensor_perms n0 n1 idn idn = idn.
Proof.
	eq_by_WF_perm_eq (n0 * n1).
	unfold tensor_perms.
	intros k Hk.
	simplify_bools_lia_one_kernel.
	pose proof (Nat.div_mod_eq k n1).
	lia.
Qed.

#[export] Hint Rewrite tensor_perms_idn_idn : perm_cleanup_db.

Lemma tensor_perms_idn_idn' n0 n1 f g :
	perm_eq n0 f idn -> perm_eq n1 g idn ->
	tensor_perms n0 n1 f g = idn.
Proof.
	intros Hf Hg.
	rewrite <- (tensor_perms_idn_idn n0 n1).
	cleanup_perm_inv.
Qed.

#[export] Hint Rewrite tensor_perms_idn_idn'
	using (solve [cleanup_perm_inv]) : perm_inv_db.

Lemma tensor_perms_permutation n0 n1 f g
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	permutation (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	perm_by_inverse (tensor_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Qed.

#[export] Hint Resolve tensor_perms_permutation : perm_db.

Lemma tensor_perms_inv n0 n1 f g 
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	perm_eq (n0 * n1) 
		(perm_inv (n0 * n1) (tensor_perms n0 n1 f g))
		(tensor_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Proof.
	perm_eq_by_inv_inj (tensor_perms n0 n1 f g) (n0*n1).
Qed.

#[export] Hint Resolve tensor_perms_inv : perm_inv_db.

Lemma tensor_perms_inv' n0 n1 f g 
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	perm_inv' (n0 * n1) (tensor_perms n0 n1 f g) =
	tensor_perms n0 n1 (perm_inv' n0 f) (perm_inv' n1 g).
Proof.
	permutation_eq_by_WF_inv_inj (tensor_perms n0 n1 f g) (n0*n1).
Qed.

#[export] Hint Rewrite tensor_perms_inv' 
	using auto with perm_db : perm_inv_db.

#[export] Hint Extern 100 (WF_Perm ?npow2 (qubit_perm_to_nat_perm ?n _)) =>
	replace npow2 with (2^n) by (show_pow2_le + unify_pows_two; nia) 
		: WF_Perm_db.

Section qubit_perm_lemmas.

Import Bits.

Lemma qubit_perm_to_nat_perm_stack_perms n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	perm_eq (2^n0 * 2^n1)
		(qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g))
		(tensor_perms (2^n0) (2^n1)
			(qubit_perm_to_nat_perm n0 f)
			(qubit_perm_to_nat_perm n1 g)).
Proof.
	intros k Hk.
	unfold tensor_perms.
	simplify_bools_lia_one_kernel.
	unfold qubit_perm_to_nat_perm.
	rewrite funbool_to_nat_add_pow2_join.
	apply funbool_to_nat_eq.
	intros a Ha.
	unfold compose.
	bdestruct (a <? n0).
	- rewrite stack_perms_left by easy.
		now rewrite nat_to_funbool_div by cleanup_perm.
	- rewrite stack_perms_right by easy.
		now rewrite <- nat_to_funbool_mod by auto with perm_bounded_db zarith.
Qed.

Lemma qubit_perm_to_nat_perm_stack_perms_alt n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	perm_eq (2^(n0 + n1))
		(qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g))
		(tensor_perms (2^n0) (2^n1)
			(qubit_perm_to_nat_perm n0 f)	
			(qubit_perm_to_nat_perm n1 g)).
Proof.
	rewrite Nat.pow_add_r.
	now apply qubit_perm_to_nat_perm_stack_perms.
Qed.

Lemma qubit_perm_to_nat_perm_bounded n f : 
	perm_bounded (2 ^ n) (qubit_perm_to_nat_perm n f).
Proof.
	intros k Hk.
	unfold qubit_perm_to_nat_perm.
	apply funbool_to_nat_bound.
Qed.

End qubit_perm_lemmas.

#[export] Hint Resolve qubit_perm_to_nat_perm_bounded : perm_bounded_db.
#[export] Hint Resolve qubit_perm_to_nat_perm_stack_perms
	qubit_perm_to_nat_perm_stack_perms_alt : perm_inv_db.

Lemma rotr_add_l_eq n m :
	rotr (n + m) n = 
	(fun k => if n + m <=? k then k else
	if k <? m then k + n else k - m).
Proof.
	eq_by_WF_perm_eq (n + m);
	[intros k Hk; bdestructΩ'|].
	intros k Hk.
	unfold rotr.
	simplify_bools_lia_one_kernel.
	bdestructΩ';
	solve_simple_mod_eqns.
Qed.

Lemma rotr_add_r_eq n m :
	rotr (m + n) n = 
	(fun k => if m + n <=? k then k else
	if k <? m then k + n else k - m).
Proof.
	eq_by_WF_perm_eq (m + n);
	[intros k Hk; bdestructΩ'|].
	intros k Hk.
	unfold rotr.
	simplify_bools_lia_one_kernel.
	bdestructΩ';
	solve_simple_mod_eqns.
Qed.

Lemma stack_perms_rotr_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	stack_perms n0 n1 f g ∘ rotr (n0 + n1) n0 =
	rotr (n0 + n1) n0 ∘ stack_perms n1 n0 g f.
Proof.
	eq_by_WF_perm_eq (n0 + n1);
	[eauto using monotonic_WF_Perm with WF_Perm_db zarith|].
	intros k Hk.
	rewrite rotr_add_l_eq.
	unfold compose.
	assert (stack_perms n1 n0 g f k < n1 + n0) by 
		auto with perm_bounded_db zarith.
	do 2 simplify_bools_lia_one_kernel.
	bdestruct (k <? n1).
	- rewrite stack_perms_right, stack_perms_left by lia.
		pose proof (Hg k).
		simplify_bools_lia_one_kernel.
		do 2 f_equal; lia.
	- rewrite stack_perms_left, stack_perms_right by lia.
		bdestructΩ'.
Qed.

Lemma stack_perms_rotl_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	stack_perms n0 n1 f g ∘ rotl (n0 + n1) n1 =
	rotl (n0 + n1) n1 ∘ stack_perms n1 n0 g f.
Proof.
	rewrite rotl_eq_rotr_sub.
	eq_by_WF_perm_eq (n0 + n1);
	[eauto using monotonic_WF_Perm with WF_Perm_db zarith|].
	intros k Hk.
	pose proof (Nat.mod_small n1 (n0 + n1)).
	assert (n0 = 0 -> n1 mod (n0 + n1) = 0) by 
		(intros ->; apply Nat.Div0.mod_same).
	rewrite <- Nat.add_sub_assoc by lia.
	rewrite rotr_eq_rotr_mod.
	rewrite Nat.Div0.add_mod.
	replace ((n1 - n1 mod (n0 + n1)) mod (n0 + n1)) with 0 by
	  (bdestruct (n0 =? 0); [subst; symmetry; 
		rewrite Nat.Div0.mod_same, Nat.sub_0_r, Nat.Div0.mod_same|
		rewrite (Nat.mod_small n1), Nat.sub_diag, Nat.Div0.mod_0_l];
		lia).
	rewrite Nat.add_0_r, <- !rotr_eq_rotr_mod.
	now rewrite stack_perms_rotr_natural.
Qed.


Lemma tensor_perms_kron_comm_perm_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) :
	tensor_perms n0 n1 f g ∘ kron_comm_perm n0 n1 =
	kron_comm_perm n0 n1 ∘ tensor_perms n1 n0 g f.
Proof.
	eq_by_WF_perm_eq (n0 * n1).
	intros k Hk.
	unfold compose, kron_comm_perm. 
	assert (tensor_perms n1 n0 g f k < n1 * n0) 
		by auto with perm_bounded_db zarith.
	do 2 simplify_bools_lia_one_kernel.
	unfold tensor_perms.
	simplify_bools_moddy_lia_one_kernel.
	simplify_bools_lia_one_kernel.
	rewrite !Nat.div_add_l, !mod_add_l by lia.
	pose proof (Hf (k mod n0) ltac:(show_moddy_lt)).
	pose proof (Hg (k / n0) ltac:(show_moddy_lt)).
	rewrite Nat.Div0.div_div, Nat.div_small, Nat.add_0_r by lia.
	rewrite (Nat.mod_small (k / n0)) by (show_moddy_lt).
	rewrite (Nat.mod_small (f _)), (Nat.div_small (f _)) by lia.
	lia.
Qed.