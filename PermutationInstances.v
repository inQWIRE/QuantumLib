Require Import Modulus.
Require Export PermutationsBase.
Require Import PermutationAutomation.
Require Export Prelim.
Require Export Bits.

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

(** Given a permutation p over n qubits, construct a permutation over 2^n indices. *)
Definition qubit_perm_to_nat_perm n (p : nat -> nat) :=
  fun k => 
    if 2 ^ n <=? k then k else
    funbool_to_nat n ((nat_to_funbool n k) ∘ p)%prg.

Definition kron_comm_perm p q :=
  fun k => if p * q <=? k then k else
  k mod p * q + k / p.

Definition perm_eq_id_mid (padl padm : nat) (f : nat -> nat) : Prop :=
  forall a, a < padm -> f (padl + a) = padl + a.

Definition expand_perm_id_mid (padl padm padr : nat) 
  (f : nat -> nat) : nat -> nat :=
  stack_perms padl (padm + padr) idn (rotr (padm + padr) padm) 
  ∘ (stack_perms (padl + padr) padm f idn)
  ∘ stack_perms padl (padm + padr) idn (rotr (padm + padr) padr).

Definition contract_perm_id_mid (padl padm padr : nat) 
  (f : nat -> nat) : nat -> nat :=
  stack_perms padl (padm + padr) idn (rotr (padm + padr) padr) ∘ 
  f ∘ stack_perms padl (padm + padr) idn (rotr (padm + padr) padm).

#[export] Hint Unfold 
  stack_perms compose
  rotr rotl 
  swap_2_perm swap_perm : perm_unfold_db.




Lemma permutation_change_dims n m (H : n = m) f : 
	permutation n f <-> permutation m f.
Proof.
	now subst.
Qed.

Lemma perm_bounded_change_dims n m (Hnm : n = m) f (Hf : perm_bounded m f) : 
  perm_bounded n f.
Proof.
  now subst.
Qed.

Lemma perm_eq_dim_change_if_nonzero n m f g :  
  perm_eq m f g -> (n <> 0 -> n = m) -> perm_eq n f g.
Proof.
  intros Hfg H k Hk.
  rewrite H in Hk by lia.
  now apply Hfg.
Qed.

Lemma perm_eq_dim_change n m f g :  
  perm_eq m f g -> n = m -> perm_eq n f g.
Proof.
  intros.
  now apply (perm_eq_dim_change_if_nonzero n m f g).
Qed.

Lemma permutation_defn n f : 
  permutation n f <-> exists g, 
    (perm_bounded n f) /\ (perm_bounded n g) /\ 
    (perm_eq n (f ∘ g) idn) /\ (perm_eq n (g ∘ f) idn).
Proof.
  split; intros [g Hg]; exists g.
  - repeat split; hnf; intros; now apply Hg.
  - intros; repeat split; now apply Hg.
Qed.

Lemma permutation_of_le_permutation_idn_above n m f :
  permutation n f -> m <= n -> (forall k, m <= k < n -> f k = k) -> 
  permutation m f.
Proof.
  intros Hf Hm Hfid.
  pose proof Hf as Hf'.
  destruct Hf' as [finv Hfinv].
  exists finv.
  intros k Hk; repeat split; try (apply Hfinv; lia).
  - pose proof (Hfinv k ltac:(lia)) as (?&?&?&?).
    bdestructΩ (f k <? m).
    specialize (Hfid (f k) ltac:(lia)).
    pose proof (Hfinv (f k) ltac:(easy)) as Hfinvk.
    rewrite Hfid in Hfinvk. 
    lia.
  - pose proof (Hfinv k ltac:(lia)) as (?&?&?&?).
    bdestructΩ (finv k <? m).
    specialize (Hfid (finv k) ltac:(lia)).
    replace -> (f (finv k)) in Hfid.
    lia.
Qed.

Add Parametric Morphism n : (permutation n) 
  with signature perm_eq n ==> iff as permutation_perm_eq_proper.
Proof.
  intros f g Hfg.
  split; intros [inv Hinv];
  exists inv;
  intros k Hk;
  [rewrite <- 2!Hfg by (destruct (Hinv k Hk); easy) |
   rewrite 2!Hfg by (destruct (Hinv k Hk); easy)];
  apply Hinv, Hk.
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

Lemma compose_perm_bounded n f g : perm_bounded n f -> perm_bounded n g ->
  perm_bounded n (f ∘ g).
Proof.
  unfold compose.
  auto.
Qed.

#[export] Hint Resolve compose_perm_bounded : perm_bounded_db.

(* Section on perm_inv *)
Lemma perm_inv_linv_of_permutation n f (Hf : permutation n f) : 
  perm_eq n (perm_inv n f ∘ f) idn.
Proof.
  exact (perm_inv_is_linv_of_permutation n f Hf).
Qed.

Lemma perm_inv_rinv_of_permutation n f (Hf : permutation n f) : 
  perm_eq n (f ∘ perm_inv n f) idn.
Proof.
  exact (perm_inv_is_rinv_of_permutation n f Hf).
Qed.

#[export] Hint Rewrite 
  perm_inv_linv_of_permutation
  perm_inv_rinv_of_permutation
  using (solve [auto with perm_db]) : perm_inv_db. 

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

#[export] Hint Rewrite perm_inv'_eq : perm_inv_db.

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

Lemma perm_inv'_permutation n f : permutation n f ->
  permutation n (perm_inv' n f).
Proof.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv'_permutation : perm_db.

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

Lemma perm_eq_compose_proper n (f f' g g' : nat -> nat) : 
  perm_bounded n g -> perm_eq n f f' -> perm_eq n g g' ->
  perm_eq n (f ∘ g) (f' ∘ g').
Proof.
  intros Hg Hf' Hg' k Hk.
  unfold compose.
  now rewrite Hf', Hg' by auto.
Qed.

#[export] Hint Resolve perm_eq_compose_proper : perm_inv_db.

Add Parametric Morphism n f : (@compose nat nat nat f) with signature
  perm_eq n ==> perm_eq n as compose_perm_eq_proper_r.
Proof.
  intros g g' Hg k Hk.
  unfold compose.
  now rewrite Hg.
Qed.

Add Parametric Morphism n : (@compose nat nat nat) with signature
  perm_eq n ==> 
  on_predicate_relation_l (fun f => perm_bounded n f) (perm_eq n) ==>
  perm_eq n as compose_perm_eq_proper_l.
Proof.
  intros f f' Hf g g' [Hgbdd Hg] k Hk.
  unfold compose.
  rewrite <- Hg by easy.
  auto.
Qed.

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

#[export] Hint Rewrite perm_inv_is_linv_of_permutation_compose
  perm_inv_is_rinv_of_permutation_compose
  using solve [auto with perm_db] : perm_inv_db.

#[export] Hint Rewrite 
  ###perm_l -> perm_inv_is_linv_of_permutation_compose
  using solve [auto with perm_bounded_db perm_db] : perm_inv_db.

#[export] Hint Rewrite 
  ###perm_r -> perm_inv_is_linv_of_permutation_compose
  using solve [auto with perm_bounded_db perm_db] : perm_inv_db.

#[export] Hint Rewrite 
  ###perm_l -> perm_inv_is_rinv_of_permutation_compose
  using solve [auto with perm_bounded_db perm_db] : perm_inv_db.

#[export] Hint Rewrite 
  ###perm_r -> perm_inv_is_rinv_of_permutation_compose
  using solve [auto with perm_bounded_db perm_db] : perm_inv_db.

Lemma perm_inv'_is_linv_of_permutation_compose (n : nat) (f : nat -> nat) :
  permutation n f -> 
  perm_eq n (perm_inv' n f ∘ f) idn.
Proof.
  intros.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv'_is_linv_of_permutation_compose : perm_inv_db.

Lemma perm_inv'_is_rinv_of_permutation_compose (n : nat) (f : nat -> nat) :
  permutation n f -> 
  perm_eq n (f ∘ perm_inv' n f) idn.
Proof.
  intros.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv'_is_rinv_of_permutation_compose : perm_inv_db.

Lemma permutation_iff_perm_inv'_inv n f : 
  permutation n f <-> 
  perm_eq n (f ∘ perm_inv' n f) idn /\ 
  perm_eq n (perm_inv' n f ∘ f) idn.
Proof.
  split; [auto_perm|].
  intros [Hrinv Hlinv].
  assert (Hfbdd : perm_bounded n f). {
    intros k Hk.
    generalize (Hlinv k Hk).
    unfold compose, perm_inv'.
    bdestructΩ'.
  }
  exists (perm_inv' n f).
  intros k Hk.
  repeat split; [auto_perm.. | |].
  - now apply Hlinv.
  - now apply Hrinv.
Qed.


Lemma idn_WF_Perm n : WF_Perm n idn.
Proof. easy. Qed.

#[export] Hint Resolve idn_WF_Perm : WF_Perm_db.


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

#[export] Hint Rewrite 
  (###comp_l -> perm_inv'_linv_of_permutation_WF)
  (###comp_r -> perm_inv'_linv_of_permutation_WF)
  (###comp_l -> perm_inv'_rinv_of_permutation_WF)
  (###comp_r -> perm_inv'_rinv_of_permutation_WF)
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
#[export] Hint Rewrite perm_inv_perm_inv 
  using solve [auto with perm_db] : perm_inv_db.

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

Add Parametric Morphism n : (perm_inv n) with signature 
  perm_eq n ==> perm_eq n as perm_inv_perm_eq_proper.
Proof.
  apply perm_inv_eq_of_perm_eq.
Qed.

Add Parametric Morphism n : (perm_inv' n) with signature 
  perm_eq n ==> eq as perm_inv'_perm_eq_to_eq_proper.
Proof.
  apply perm_inv'_eq_of_perm_eq.
Qed.

Add Parametric Morphism n : (perm_inv' n) with signature 
  perm_eq n ==> perm_eq n as perm_inv'_perm_eq_proper.
Proof.
  now intros f g ->.
Qed.

#[export] Hint Extern 20
  (?f = ?g) => 
  eapply eq_of_WF_perm_eq;
  [solve [auto with WF_Perm_db]..|] : perm_inv_db.

#[export] Hint Extern 20 
  (?f ?k = ?g ?k) =>
  match goal with 
  | Hk : k < ?n |- _ => 
    let Heq := fresh in 
    enough (Heq : perm_eq n f g) by (exact (Heq k Hk))
  end : perm_inv_db.

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
  intros.
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

Lemma perm_inv_perm_eq_iff n f g 
  (Hf : permutation n f) (Hg : permutation n g) :
  perm_eq n (perm_inv n g) f <-> perm_eq n g (perm_inv n f).
Proof.
  split; [intros <- | intros ->];
  cleanup_perm_inv.
Qed.

Lemma perm_inv_compose {n f g} (Hf : permutation n f) (Hg : permutation n g) : 
  perm_eq n 
    (perm_inv n (f ∘ g))
    (perm_inv n g ∘ perm_inv n f).
Proof.
  apply perm_eq_sym.
  perm_eq_by_inv_inj (f ∘ g) n.
  rewrite !compose_assoc.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv_compose : perm_inv_db.
#[export] Hint Rewrite @perm_inv_compose
  using solve [auto with perm_db] : perm_inv_db.

Lemma perm_inv_compose_alt n f g
  (Hf : permutation n f) (Hg : permutation n g) :
  perm_eq n 
    (perm_inv n (fun x => f (g x)))
    (fun x => perm_inv n g (perm_inv n f x))%prg.
Proof.
  now apply perm_inv_compose.
Qed.

Lemma perm_inv'_compose {n f g} 
  (Hf : permutation n f) (Hg : permutation n g) : 
  perm_inv' n (f ∘ g) = 
  perm_inv' n g ∘ perm_inv' n f.
Proof.
  eq_by_WF_perm_eq n.
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite @perm_inv'_compose 
  using solve [auto with perm_db] : perm_inv_db.

Lemma perm_inv_inj n f g : 
  permutation n f -> permutation n g -> 
  perm_eq n (perm_inv n f) (perm_inv n g) -> 
  perm_eq n f g.
Proof.
  intros Hf Hg Hfg.
  rewrite <- (perm_inv_perm_inv n f Hf).
  rewrite Hfg.
  rewrite perm_inv_perm_inv by easy.
  easy.
Qed.

(* Permute bounded predicates *)
Lemma forall_lt_iff n (P Q : nat -> Prop) 
  (HPQ : forall k, k < n -> P k <-> Q k) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  auto.
Qed.

Lemma forall_lt_iff_permute n f (Hf : permutation n f) 
  (P : nat -> Prop) : 
  (forall k, k < n -> P k) <-> (forall k, k < n -> P (f k)).
Proof.
  split; intros HP.
  - intros k Hk.
    apply HP.
    auto with perm_db.
  - intros k Hk.
    generalize (HP (perm_inv n f k) (perm_inv_bounded n f k Hk)).
    now rewrite perm_inv_is_rinv_of_permutation by easy.
Qed.

Lemma forall_lt_iff_of_permute_l n f (Hf : permutation n f) 
  (P Q : nat -> Prop) (HPQ : forall k, k < n -> P (f k) <-> Q k) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  rewrite (forall_lt_iff_permute n f Hf).
  apply forall_iff; intros k.
  apply impl_iff; intros Hk.
  now apply HPQ.
Qed.

Lemma forall_lt_iff_of_permute_r n f (Hf : permutation n f) 
  (P Q : nat -> Prop) (HPQ : forall k, k < n -> P k <-> Q (f k)) :
  (forall k, k < n -> P k) <-> (forall k, k < n -> Q k).
Proof.
  symmetry.
  apply (forall_lt_iff_of_permute_l n f Hf).
  intros k Hk.
  now rewrite HPQ.
Qed.


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

Lemma swap_perm_defn a b n : a < n -> b < n -> 
  perm_eq n (swap_perm a b n) 
  (fun x => 
  if x =? a then b else 
  if x =? b then a else x).
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_perm_same a n :
  swap_perm a a n = idn.
Proof.
  unfold swap_perm.
  apply functional_extensionality; intros k.
  bdestructΩ'.
Qed.

Lemma swap_perm_left a b n : a < n ->
  swap_perm a b n a = b.
Proof.
  unfold swap_perm; bdestructΩ'.
Qed.

Lemma swap_perm_right a b n : b < n ->
  swap_perm a b n b = a.
Proof.
  unfold swap_perm; bdestructΩ'.
Qed.

Lemma swap_perm_neither a b n x : x <> a -> x <> b ->
  swap_perm a b n x = x.
Proof.
  unfold swap_perm; bdestructΩ'.
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
#[export] Hint Rewrite swap_perm_invol using lia : perm_inv_db.

Lemma swap_perm_big a b n : n <= a -> n <= b ->
  perm_eq n (swap_perm a b n) idn.
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_perm_big using lia : perm_cleanup_db.

Lemma swap_perm_big_eq a b n : 
  n <= a -> n <= b -> 
  swap_perm a b n = idn.
Proof.
  intros.
  eq_by_WF_perm_eq n.
  cleanup_perm.
Qed.

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

Lemma swap_perm_permutation_alt a b n : 
  n <= a -> n <= b ->
  permutation n (swap_perm a b n).
Proof.
  intros Ha Hb.
  cleanup_perm.
Qed.


Lemma swap_perm_inv a b n : a < n -> b < n ->
  perm_eq n (perm_inv n (swap_perm a b n))
    (swap_perm a b n).
Proof.
  intros Ha Hb.
  perm_eq_by_inv_inj (swap_perm a b n) n.
Qed.

#[export] Hint Resolve swap_perm_inv : perm_inv_db.
#[export] Hint Rewrite swap_perm_inv using lia : perm_inv_db.

Lemma swap_perm_inv' a b n : a < n -> b < n ->
  perm_inv' n (swap_perm a b n) = 
  swap_perm a b n.
Proof.
  intros.
  eq_by_WF_perm_eq n; cleanup_perm_inv. 
Qed.

#[export] Hint Rewrite swap_perm_inv' using lia : perm_inv_db.

Lemma swap_perm_even_S_even_permutation a n : 
  Nat.even a = true -> Nat.even n = true ->
  permutation n (swap_perm a (S a) n).
Proof.
  intros Ha Hn.
  bdestruct (a <? n).
  - pose proof (succ_even_lt_even a n Ha Hn ltac:(easy)).
    auto with perm_db.
  - apply swap_perm_permutation_alt; lia.
Qed.

(* #[export] Hint Extern 0 (perm_bounded ?n (swap_perm ?a ?b ?n')) =>
  replace n with n' by lia;
  apply swap_perm_bounded; 
  lia + auto with zarith : perm_bounded_db. *)



Lemma compose_swap_perm a b c n : a < n -> b < n -> c < n -> 
  b <> c -> a <> c ->
  (swap_perm a b n ∘ swap_perm b c n ∘ swap_perm a b n) = swap_perm a c n.
Proof.
  intros Ha Hb Hc Hbc Hac.
  eq_by_WF_perm_eq n.
  rewrite <- swap_perm_inv at 1 by easy.
  rewrite compose_assoc.
  apply compose_perm_inv_l; [cleanup_perm_inv..|].
  rewrite !swap_perm_defn by easy.
  unfold compose.
  intros k Hk.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite compose_swap_perm using lia : perm_cleanup_db.




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

Lemma insertion_sort_list_is_swap_list n f : 
  swap_list_spec (insertion_sort_list n f) = true.
Proof.
  revert f;
  induction n;
  intros f.
  - easy.
  - cbn -[perm_inv].
    rewrite length_insertion_sort_list, IHn.
    pose proof (perm_inv_bounded_S n f n).
    bdestructΩ'.
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
  - easy. 
  - intros Hperm k Hk.
    cbn -[perm_inv].
    rewrite length_insertion_sort_list.
    bdestruct (k =? n).
    + unfold compose.
      rewrite perm_of_swap_list_WF; [ |
        apply insertion_sort_list_is_swap_list |
        rewrite length_insertion_sort_list; lia
      ]. 
      unfold swap_perm.
      bdestructΩ';
      [replace -> n at 1|];
      cleanup_perm.
    + rewrite <- compose_assoc.
      rewrite <- fswap_eq_compose_swap_perm by
        auto with perm_bounded_db.
      rewrite IHn; [easy| |lia].
      apply fswap_perm_invol_n_permutation, Hperm.
Qed.

#[export] Hint Resolve perm_of_insertion_sort_list_is_rinv : perm_inv_db.
#[export] Hint Rewrite perm_of_insertion_sort_list_is_rinv
  using solve [auto with perm_db] : perm_inv_db.

Lemma perm_of_insertion_sort_list_WF n f : 
  WF_Perm n (perm_of_swap_list (insertion_sort_list n f)).
Proof.
  rewrite <- (length_insertion_sort_list n f) at 1.
  auto with WF_Perm_db perm_db.
Qed.

Lemma invperm_of_insertion_sort_list_WF n f : 
  WF_Perm n (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  rewrite <- (length_insertion_sort_list n f) at 1.
  auto with WF_Perm_db perm_db.
Qed.

#[export] Hint Resolve perm_of_insertion_sort_list_WF 
  invperm_of_swap_list_WF : WF_Perm_db.


Lemma perm_of_insertion_sort_list_perm_eq_perm_inv n f : permutation n f ->
  perm_eq n (perm_of_swap_list (insertion_sort_list n f)) (perm_inv n f).
Proof.
  intros Hperm.
  apply (perm_bounded_rinv_injective_of_injective n f); try cleanup_perm_inv.
  pose proof (perm_of_swap_list_bounded (insertion_sort_list n f)
    (insertion_sort_list_is_swap_list n f)) as H.
  rewrite (length_insertion_sort_list n f) in H.
  exact H.
Qed.

#[export] Hint Resolve 
  perm_of_insertion_sort_list_perm_eq_perm_inv : perm_inv_db.

#[export] Hint Rewrite 
  perm_of_insertion_sort_list_perm_eq_perm_inv
  using solve [auto with perm_db] : perm_inv_db.


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
  using solve [auto with perm_db] : perm_inv_db.


Lemma perm_inv_of_insertion_sort_list_perm_eq n f : permutation n f ->
  perm_eq n (perm_inv n (perm_of_swap_list (insertion_sort_list n f))) f.
Proof.
  intros Hf.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve perm_inv_of_insertion_sort_list_perm_eq : perm_inv_db.
#[export] Hint Rewrite perm_inv_of_insertion_sort_list_perm_eq 
  using solve [auto with perm_db] : perm_inv_db.

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

Lemma perm_eq_perm_of_insertion_sort_list_of_perm_inv n f : permutation n f ->
  perm_eq n f (perm_of_swap_list (insertion_sort_list n (perm_inv n f))).
Proof.
  intros Hf.
  cleanup_perm_inv.
Qed.

Lemma insertion_sort_list_S n f : 
  insertion_sort_list (S n) f = 
  (perm_inv (S n) f n) :: 
  (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)).
Proof. easy. Qed.

Lemma perm_of_swap_list_cons a l :
  perm_of_swap_list (a :: l) = 
  swap_perm a (length l) (S (length l)) ∘ perm_of_swap_list l.
Proof. easy. Qed.

Lemma invperm_of_swap_list_cons a l :
  invperm_of_swap_list (a :: l) = 
  invperm_of_swap_list l ∘ swap_perm a (length l) (S (length l)).
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
  [ exists idn; easy |].
  simpl in *.
  rewrite andb_true_iff, Nat.ltb_lt in Hsw.
  destruct Hsw.
  pose proof (fun f => permutation_of_le_permutation_WF f 
    (length l) (S (length l)) ltac:(lia)).
  cleanup_perm_inv.
Qed.

Lemma invperm_of_swap_list_permutation l : swap_list_spec l = true ->
  permutation (length l) (invperm_of_swap_list l).
Proof.
  intros Hsw.
  induction l;
  [ exists idn; easy |].
  simpl in *.
  rewrite andb_true_iff, Nat.ltb_lt in Hsw.
  destruct Hsw.
  pose proof (fun f => permutation_of_le_permutation_WF f 
    (length l) (S (length l)) ltac:(lia)).
  cleanup_perm_inv.
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

#[export] Hint Rewrite <- perm_eq_invperm_of_insertion_sort_list
  using solve [auto with perm_db] : perm_inv_db.

Lemma permutation_grow_l' n f : permutation (S n) f -> 
  perm_eq (S n) f (swap_perm (f n) n (S n) ∘ 
  perm_of_swap_list (insertion_sort_list n (fswap (perm_inv (S n) f) (f n) n))).
Proof.
  intros Hperm.
  rewrite (perm_eq_perm_of_insertion_sort_list_of_perm_inv _ _ Hperm) 
    at 1.
  cbn -[perm_inv].
  rewrite length_insertion_sort_list, perm_inv_perm_inv by auto.
  easy.
Qed.

Lemma permutation_grow_r' n f : permutation (S n) f -> 
  perm_eq (S n) f ( 
  invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n)).
Proof.
  intros Hperm.
  rewrite (perm_eq_invperm_of_insertion_sort_list _ _ Hperm) at 1.
  cbn -[perm_inv].
  rewrite length_insertion_sort_list by auto.
  easy.
Qed.

Lemma permutation_grow_l n f : permutation (S n) f ->
  exists g k, k < S n /\ 
  perm_eq (S n) f (swap_perm k n (S n) ∘ g) /\ permutation n g.
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

Lemma stack_perms_WF n0 n1 f g :
	WF_Perm (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestructΩ'.
Qed.

#[export] Hint Resolve stack_perms_WF : WF_Perm_db.
#[export] Hint Extern 10 (WF_Perm ?n (stack_perms ?n0 ?n1 ?f ?g)) =>
  replace (WF_Perm n) with (WF_Perm (n0 + n1)) by (f_equal; lia);
  apply stack_perms_WF : WF_Perm_db.

Lemma stack_perms_bounded {n0 n1} {f g} : 
	perm_bounded n0 f -> perm_bounded n1 g ->
  perm_bounded (n0 + n1) (stack_perms n0 n1 f g).
Proof.
	intros Hf Hg.
  intros k Hk.
  specialize (Hf k).
  specialize (Hg (k - n0)).
  unfold stack_perms.
  bdestructΩ'.
Qed. 

#[export] Hint Resolve stack_perms_bounded : perm_bounded_db.
#[export] Hint Extern 10 (perm_bounded ?n (stack_perms ?n0 ?n1 ?f ?g)) =>
  apply (perm_bounded_change_dims n (n0 + n1) ltac:(lia));
  apply stack_perms_bounded : perm_bounded_db.

Lemma stack_perms_defn n0 n1 f g : 
  perm_eq (n0 + n1) (stack_perms n0 n1 f g)
    (fun k => if k <? n0 then f k else g (k - n0) + n0).
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestructΩ'.
Qed.

Add Parametric Morphism n0 n1 : (stack_perms n0 n1) with signature
  perm_eq n0 ==> perm_eq n1 ==> eq as stack_perms_perm_eq_to_eq_proper.
Proof.
  intros f f' Hf g g' Hg.
  eq_by_WF_perm_eq (n0 + n1).
  rewrite 2!stack_perms_defn.
  intros k Hk.
  bdestructΩ'; f_equal; auto with zarith.
Qed.

Lemma stack_perms_compose {n0 n1} {f g} {f' g'} 
	(Hf' : perm_bounded n0 f') (Hg' : perm_bounded n1 g') :
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 f' g'
	= stack_perms n0 n1 (f ∘ f') (g ∘ g'))%prg.
Proof.
  eq_by_WF_perm_eq (n0 + n1).
  intros k Hk.
  specialize (Hf' k).
  specialize (Hg' (k - n0)).
  autounfold with perm_unfold_db.
  bdestructΩ'.
  now rewrite Nat.add_sub.
Qed.

#[export] Hint Rewrite @stack_perms_compose 
	using solve [auto with perm_db perm_bounded_db] : perm_inv_db.

Lemma stack_perms_assoc {n0 n1 n2} {f g h} :
  stack_perms (n0 + n1) n2 (stack_perms n0 n1 f g) h =
  stack_perms n0 (n1 + n2) f (stack_perms n1 n2 g h).
Proof.
  eq_by_WF_perm_eq (n0 + n1 + n2).
  do 3 rewrite_strat innermost stack_perms_defn.
  rewrite <- Nat.add_assoc.
  rewrite stack_perms_defn.
  intros k Hk.
  rewrite Nat.add_assoc, Nat.sub_add_distr.
  bdestructΩ'.
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
	stack_perms_compose | 10 : perm_inv_db.


Lemma stack_perms_idn_compose n0 n1 f g 
  (Hg : perm_bounded n1 g) : 
  stack_perms n0 n1 idn (f ∘ g) =
  stack_perms n0 n1 idn f ∘ stack_perms n0 n1 idn g.
Proof.
  cleanup_perm.
Qed.

Lemma stack_perms_compose_idn n0 n1 f g 
  (Hg : perm_bounded n0 g) : 
  stack_perms n0 n1 (f ∘ g) idn =
  stack_perms n0 n1 f idn ∘ stack_perms n0 n1 g idn.
Proof.
  cleanup_perm.
Qed.


Lemma stack_perms_WF_idn n0 n1 f 
	(H : WF_Perm n0 f) : 
	stack_perms n0 n1 f idn = f.
Proof.
	solve_modular_permutation_equalities;
	rewrite H; lia.
Qed.

#[export] Hint Rewrite stack_perms_WF_idn 
	using (solve [auto with WF_Perm_db]) : perm_inv_db.

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

Lemma is_inv_iff_inv_is n f finv :
  (forall k, k < n -> finv k < n /\ f k < n /\ f (finv k) = k /\ finv (f k) = k)%nat
  <-> (forall k, k < n -> f k < n /\ finv k < n /\ finv (f k) = k /\ f (finv k) = k)%nat.
Proof.
  split; intros H k Hk; specialize (H k Hk); easy.
Qed.

Lemma stack_perms_linv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  stack_perms n0 n1 finv ginv ∘ stack_perms n0 n1 f g = idn.
Proof.
  now rewrite stack_perms_rinv
    by now apply is_inv_iff_inv_is.
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
  rewrite stack_perms_compose by easy.
  now rewrite Hf, Hg, stack_perms_idn_idn.
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

Lemma stack_perms_permutation {n0 n1 f g} 
  (Hf : permutation n0 f) (Hg: permutation n1 g) :
  permutation (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  perm_by_inverse (stack_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Qed.

#[export] Hint Resolve stack_perms_permutation : perm_db.
#[export] Hint Extern 10 (permutation ?n (stack_perms ?n0 ?n1 ?f ?g)) =>
  replace (permutation n) with (permutation (n0 + n1)) by (f_equal; lia);
  apply stack_perms_permutation : perm_db.

Lemma perm_inv_stack_perms n m f g 
  (Hf : permutation n f) (Hg : permutation m g) : 
  perm_eq (n + m)
  (perm_inv (n + m) (stack_perms n m f g))
  (stack_perms n m (perm_inv n f) (perm_inv m g)).
Proof.
  perm_eq_by_inv_inj (stack_perms n m f g) (n+m).
Qed.

#[export] Hint Rewrite perm_inv_stack_perms 
  using solve [auto with perm_db] : perm_inv_db.

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
	using solve [auto with perm_db] : perm_inv_db.

Lemma stack_perms_diag_split n m f g 
  (Hg : perm_bounded m g) : 
  stack_perms n m f g = stack_perms n m f idn ∘ stack_perms n m idn g.
Proof. cleanup_perm. Qed.

Lemma stack_perms_antidiag_split n m f g (Hf : perm_bounded n f) :
  stack_perms n m f g = stack_perms n m idn g ∘ stack_perms n m f idn.
Proof. cleanup_perm. Qed.


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

Add Parametric Morphism n : contract_perm with signature
  perm_eq n ==> on_predicate_relation_l (fun k => k < n) eq ==>
  perm_eq (n - 1) as compose_perm_perm_eq_proper.
Proof.
  intros f g Hfg k l [? ->].
  now apply contract_perm_perm_eq_of_perm_eq.
Qed.

#[export] Hint Extern 0 (_ < _) =>
  lia : proper_side_conditions_db.

#[export] Hint Extern 2 (_ < _) =>
  solve [auto with perm_bounded_db perm_db] : proper_side_conditions_db.

#[export] Hint Extern 5 (?f ?k < ?n) =>
  (* idtac "TRYNG" f k n; *)
  let Hk := fresh "Hk" in 
  assert (Hk : k < n) by (easy + lia);
  (* idtac "SECOND STEP"; *)
  let Hfbdd := fresh "Hfbdd" in
  assert (Hfbdd : perm_bounded f n) by 
    (auto with perm_bounded_db perm_db zarith);
  (* idtac "THIRD STEP"; *)
  exact (Hfbdd k Hk) : proper_side_conditions_db.

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

Lemma contract_perm_compose a n (Ha : a < n) f g 
  (Hg : permutation n g) 
  (Hf : perm_inj n f) : 
  perm_eq (n - 1) (contract_perm f (g a) ∘ contract_perm g a)
  (contract_perm (f ∘ g) a).
Proof.
  intros k Hk.
  pose proof (permutation_is_injective n g Hg k a ltac:(lia) Ha) as Hgka.
  pose proof (permutation_is_injective n g Hg (k + 1) a ltac:(lia) Ha) 
    as HgSka.
  pose proof (Hf a (g k) Ha (permutation_is_bounded n g Hg k ltac:(lia))) 
    as Hfk.
  unfold contract_perm, compose.
  bdestructΩ'_with ltac:(rewrite ?Nat.sub_add in * by lia; 
    try lia).
Qed.

Lemma contract_perm_compose' a b n (Ha : a < n) f g 
  (Hg : permutation n g) 
  (Hf : perm_inj n f) 
  (Hb : b = g a) : 
  perm_eq (n - 1) (contract_perm f b ∘ contract_perm g a)
  (contract_perm (f ∘ g) a).
Proof.
  subst.
  now apply contract_perm_compose.
Qed.

Lemma contract_perm_idn a : contract_perm idn a = idn.
Proof.
  unfold contract_perm.
  solve_modular_permutation_equalities.
Qed.

#[export] Hint Rewrite contract_perm_idn : perm_cleanup_db.

Lemma contract_perm_permutation {n f} (Hf : permutation n f) a :
  a < n ->
  permutation (n - 1) (contract_perm f a).
Proof.
  intros Ha.
  pose proof (fun x y => permutation_eq_iff x y Hf) as Hfinj.
  perm_by_inverse ((contract_perm (perm_inv n f) (f a)));
  change (?f (?g k)) with ((f ∘ g) k);
  match goal with |- ?f ?k = ?k => 
    enough (Heq : perm_eq (n - 1) f idn) by (exact (Heq k Hk))
  end;
  rewrite contract_perm_compose'; cleanup_perm.
Qed.

#[export] Hint Resolve contract_perm_permutation : perm_db.

Lemma contract_perm_inv n f (Hf : permutation n f) a :
  a < n ->
  perm_eq (n - 1)
  (perm_inv (n - 1) (contract_perm f a)) 
  (contract_perm (perm_inv n f) (f a)).
Proof.
  intros Ha.
  perm_eq_by_inv_inj (contract_perm f a) (n - 1).
  rewrite contract_perm_compose; cleanup_perm.
Qed.

#[export] Hint Resolve contract_perm_inv : perm_inv_db.

#[export] Hint Rewrite contract_perm_inv
  using solve [lia + auto with perm_db perm_bounded_db] : perm_inv_db.

Lemma contract_perm_big n a f (Ha : n <= a) (Hfa : n <= f a) 
  (Hf : perm_bounded n f) : 
  perm_eq (n - 1) (contract_perm f a) f.
Proof.
  intros k Hk.
  unfold contract_perm.
  pose proof (Hf k ltac:(lia)).
  bdestructΩ'.
Qed.

Lemma contract_perm_big_WF n a f (Ha : n <= a) (HfWF : WF_Perm n f)
  (Hf : perm_bounded n f) : 
  perm_eq (n - 1) (contract_perm f a) f.
Proof.
  apply contract_perm_big; try rewrite HfWF; easy.
Qed.  

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

Lemma contract_perm_inv' {n f} (Hf : permutation n f) a :
  WF_Perm n f ->
  a < n -> 
  perm_inv' (n - 1) (contract_perm f a) = 
  contract_perm (perm_inv' n f) (f a).
Proof.
  intros Hfwf Ha.
  eq_by_WF_perm_eq (n-1).
  cleanup_perm.
Qed.

#[export] Hint Rewrite @contract_perm_inv' 
  using (match goal with 
  | |- WF_Perm _ _ => solve [auto with WF_Perm_db perm_db perm_inv_db]
  | |- _ => auto with perm_db
  end) : perm_inv_db.



(* Section on rotr / rotl *)
Lemma rotr_defn n m : 
  perm_eq n (rotr n m) (fun k => (k + m) mod n).
Proof.
  intros k Hk.
  unfold rotr.
  bdestructΩ'.
Qed.

Lemma rotl_defn n m : 
  perm_eq n (rotl n m) (fun k => (k + (n - m mod n)) mod n).
Proof.
  intros k Hk.
  unfold rotl.
  bdestructΩ'.
Qed.

Lemma rotr_WF n m : 
  WF_Perm n (rotr n m).
Proof. intros k Hk. unfold rotr. bdestruct_one; lia. Qed.

Lemma rotl_WF n m : 
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
  eq_by_WF_perm_eq n.
  intros a Ha.
  unfold rotr.
  simplify_bools_lia_one_kernel.
  now rewrite Nat.Div0.add_mod, (Nat.mod_small a n Ha).
Qed.

Lemma rotl_n n : rotl n n = idn.
Proof.
  permutation_eq_by_WF_inv_inj (rotr n n) n.
Qed.

#[export] Hint Rewrite rotl_n : perm_cleanup_db.

Lemma rotl_eq_rotl_mod n k : rotl n k = rotl n (k mod n).
Proof. 
  permutation_eq_by_WF_inv_inj (rotr n k) n.
  rewrite rotr_eq_rotr_mod; cleanup_perm_inv.
Qed.

Lemma rotr_eq_rotl_sub n k : 
	rotr n k = rotl n (n - k mod n).
Proof.
	rewrite rotr_eq_rotr_mod.
  permutation_eq_by_WF_inv_inj (rotl n (k mod n)) n.
  cleanup_perm.
	destruct n; [rewrite rotl_0_l; easy|].
  pose proof (Nat.mod_upper_bound k (S n)). 
  rewrite Nat.sub_add by lia.
  cleanup_perm.
Qed.

Lemma rotl_eq_rotr_sub n k : 
	rotl n k = rotr n (n - k mod n).
Proof.
  permutation_eq_by_WF_inv_inj (rotr n k) n.
	destruct n; [cbn; rewrite 2!rotr_0_l, compose_idn_l; easy|].
  rewrite (rotr_eq_rotr_mod _ k), rotr_rotr.
  pose proof (Nat.mod_upper_bound k (S n)).
  rewrite Nat.sub_add by lia.
  cleanup_perm.
Qed.

Lemma rotl_eq_rotr_sub_le n k : k <= n -> 
	rotl n k = rotr n (n - k).
Proof.
  intros Hk.
  bdestruct (k =? n);
  [subst; rewrite Nat.sub_diag; cleanup_perm|].
  now rewrite rotl_eq_rotr_sub, Nat.mod_small by lia.
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



Lemma big_swap_perm_defn n m : 
  perm_eq (n + m) (big_swap_perm n m) 
  (fun k => if k <? n then k + m else k - n).
Proof.
  intros k Hk.
  unfold big_swap_perm.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma big_swap_perm_defn_alt n m : 
  perm_eq (m + n) (big_swap_perm n m) 
  (fun k => if k <? n then k + m else k - n).
Proof.
  rewrite Nat.add_comm.
  apply big_swap_perm_defn.
Qed.

Lemma big_swap_perm_bounded p q : 
  perm_bounded (p + q) (big_swap_perm p q).
Proof.
  intros k Hk.
  unfold big_swap_perm.
  bdestructΩ'.
Qed.

Lemma big_swap_perm_bounded_comm p q : 
  perm_bounded (q + p) (big_swap_perm p q).
Proof.
  rewrite Nat.add_comm.
  apply big_swap_perm_bounded.
Qed.

#[export] Hint Resolve big_swap_perm_bounded
  big_swap_perm_bounded_comm : perm_bounded_db.
#[export] Hint Extern 10 (perm_bounded ?n (big_swap_perm ?p ?q)) =>  
  apply (perm_bounded_change_dims n (p * q)
    ltac:(show_pow2_le + unify_pows_two; nia));
  apply big_swap_perm_bounded : perm_bounded_db.

Lemma big_swap_perm_WF p q : 
  WF_Perm (p + q) (big_swap_perm p q).
Proof.
  intros k Hk.
  unfold big_swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve big_swap_perm_WF : WF_Perm_db.
#[export] Hint Extern 1 (WF_Perm ?n (big_swap_perm ?p ?q)) =>  
  replace (WF_Perm n) with (WF_Perm (p + q)) by (f_equal; lia);
  apply big_swap_perm_WF : WF_Perm_db.

Lemma big_swap_perm_invol p q : 
  big_swap_perm p q ∘ big_swap_perm q p = idn.
Proof.
  eq_by_WF_perm_eq (p + q).
  intros k Hk.
  unfold big_swap_perm, compose.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite big_swap_perm_invol : perm_inv_db perm_cleanup_db.

Lemma big_swap_perm_permutation p q :
  permutation (p + q) (big_swap_perm p q).
Proof.
  perm_by_inverse (big_swap_perm q p).
Qed.

#[export] Hint Resolve big_swap_perm_permutation : perm_db.
#[export] Hint Extern 1 (permutation ?n (big_swap_perm ?p ?q)) =>  
  replace (permutation n) with (permutation (p + q)) by (f_equal; lia);
  apply big_swap_perm_permutation : perm_db.

Lemma big_swap_perm_inv p q : 
  perm_eq (p + q) (perm_inv (p + q) (big_swap_perm p q)) 
    (big_swap_perm q p).
Proof.
  perm_eq_by_inv_inj (big_swap_perm p q) (p + q).
Qed.

Lemma big_swap_perm_inv_change_dims p q n : n = p + q ->
  perm_eq n (perm_inv n (big_swap_perm p q)) 
    (big_swap_perm q p).
Proof.
  intros ->.
  apply big_swap_perm_inv.
Qed.

#[export] Hint Resolve big_swap_perm_inv : perm_inv_db.

#[export] Hint Rewrite big_swap_perm_inv : perm_inv_db.
#[export] Hint Rewrite big_swap_perm_inv_change_dims 
  using lia : perm_inv_db.

Lemma big_swap_perm_inv' p q : 
  perm_inv' (p + q) (big_swap_perm p q) =
  big_swap_perm q p.
Proof.
  eq_by_WF_perm_eq (p + q).
  cleanup_perm_inv.
Qed.

Lemma big_swap_perm_inv'_change_dims p q n : n = p + q ->
  perm_inv' n (big_swap_perm p q) =
  big_swap_perm q p.
Proof.
  intros ->.
  apply big_swap_perm_inv'.
Qed.

#[export] Hint Rewrite big_swap_perm_inv' : perm_inv_db.
#[export] Hint Rewrite big_swap_perm_inv'_change_dims 
  using lia : perm_inv_db.

Lemma big_swap_perm_0_l q : 
  big_swap_perm 0 q = idn.
Proof.
  eq_by_WF_perm_eq q.
  intros k Hk.
  unfold big_swap_perm; bdestructΩ'.
Qed.

Lemma big_swap_perm_0_r p : 
  big_swap_perm p 0 = idn.
Proof.
  eq_by_WF_perm_eq p.
  intros k Hk.
  unfold big_swap_perm; bdestructΩ'.
Qed.

#[export] Hint Rewrite big_swap_perm_0_l big_swap_perm_0_r : perm_cleanup_db.

Lemma big_swap_perm_ltb_r n m k : 
  big_swap_perm n m k <? m = ((¬ k <? n) && (k <? n + m)).
Proof.
  unfold big_swap_perm.
  bdestructΩ'.
Qed.


Lemma rotr_eq_big_swap n m : 
  rotr n m = big_swap_perm (n - m mod n) (m mod n).
Proof.
  rewrite rotr_decomp.
  unfold big_swap_perm.
  apply functional_extensionality.
  intros k.
  pose proof (Nat.mod_upper_bound m n).
  bdestructΩ'.
Qed.

Lemma rotl_eq_big_swap n m : 
  rotl n m = big_swap_perm (m mod n) (n - m mod n).
Proof.
  permutation_eq_by_WF_inv_inj (rotr n m) n.
  rewrite rotr_eq_big_swap.
  cleanup_perm_inv.
Qed.


Lemma big_swap_perm_eq_rotr p q : 
  big_swap_perm p q = rotr (p + q) q.
Proof.
  rewrite rotr_eq_big_swap.
  bdestruct (p =? 0).
  - subst.
    simpl.
    rewrite Nat.Div0.mod_same, Nat.sub_0_r.
    cleanup_perm.
  - now rewrite Nat.mod_small, Nat.add_sub by lia.
Qed.

Lemma big_swap_perm_eq_rotl p q : 
  big_swap_perm p q = rotl (p + q) p.
Proof.
  permutation_eq_by_WF_inv_inj (rotr (p + q) p) (p + q);
  cleanup_perm.
  rewrite Nat.add_comm, <- big_swap_perm_eq_rotr.
  cleanup_perm.
Qed.


Lemma rotr_add_l p q : 
  rotr (p + q) p = big_swap_perm q p.
Proof.
  rewrite big_swap_perm_eq_rotr; f_equal; lia.
Qed.

Lemma rotr_add_r p q : 
  rotr (p + q) q = big_swap_perm p q.
Proof.
  rewrite big_swap_perm_eq_rotr; f_equal; lia.
Qed.

Lemma rotl_add_l p q : 
  rotl (p + q) p = big_swap_perm p q.
Proof.
  rewrite big_swap_perm_eq_rotl; f_equal; lia.
Qed.

Lemma rotl_add_r p q : 
  rotl (p + q) q = big_swap_perm q p.
Proof.
  rewrite big_swap_perm_eq_rotl; f_equal; lia.
Qed.



Lemma reflect_perm_defn n : 
  perm_eq n (reflect_perm n) (fun k => n - S k).
Proof.
  intros k Hk.
  unfold reflect_perm.
  bdestructΩ'.
Qed.

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

Lemma swap_perm_conj_reflect_eq a b n 
  (Ha : a < n) (Hb : b < n) : 
  reflect_perm n ∘ swap_perm a b n ∘ reflect_perm n = 
  swap_perm (n - S a) (n - S b) n.
Proof.
  eq_by_WF_perm_eq n.
  rewrite reflect_perm_defn at 1. 
  rewrite reflect_perm_defn, 2!swap_perm_defn by lia.
  intros k Hk.
  unfold compose.
  replace_bool_lia (n - S k =? a) (k =? n - S a).
  replace_bool_lia (n - S k =? b) (k =? n - S b).
  bdestructΩ'.
Qed.



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




Lemma qubit_perm_to_nat_perm_defn n p : 
  perm_eq (2 ^ n) (qubit_perm_to_nat_perm n p) 
  (fun k => funbool_to_nat n ((nat_to_funbool n k) ∘ p)%prg).
Proof.
  unfold qubit_perm_to_nat_perm.
  intros k Hk.
  simplify_bools_lia_one_kernel.
  easy.
Qed.

Lemma qubit_perm_to_nat_perm_WF n f : 
  WF_Perm (2^n) (qubit_perm_to_nat_perm n f).
Proof.
  intros k Hk.
  unfold qubit_perm_to_nat_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_WF : WF_Perm_db.
#[export] Hint Extern 100 (WF_Perm ?npow2 (qubit_perm_to_nat_perm ?n _)) =>
	replace (WF_Perm npow2) with (WF_Perm (2^n)) 
    by (show_pow2_le + unify_pows_two; nia) : WF_Perm_db.

Add Parametric Morphism n : (qubit_perm_to_nat_perm n) with signature 
  perm_eq n ==> eq 
  as qubit_perm_to_nat_perm_perm_eq_to_eq_proper.
Proof.
  intros f g Hfg.
  eq_by_WF_perm_eq (2^n).
  intros k Hk.
  rewrite 2!qubit_perm_to_nat_perm_defn by easy.
  apply funbool_to_nat_eq.
  intros l Hl.
  unfold compose.
  now rewrite Hfg.
Qed.

Lemma qubit_perm_to_nat_perm_bounded n f : 
	perm_bounded (2 ^ n) (qubit_perm_to_nat_perm n f).
Proof.
	intros k Hk.
  rewrite qubit_perm_to_nat_perm_defn by easy.
	apply funbool_to_nat_bound.
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_bounded : perm_bounded_db.

Lemma qubit_perm_to_nat_perm_compose n f g :
  perm_bounded n f ->
  (qubit_perm_to_nat_perm n f ∘ qubit_perm_to_nat_perm n g = 
    qubit_perm_to_nat_perm n (g ∘ f))%prg.
Proof.
  intros Hf.
  eq_by_WF_perm_eq (2^n).
  rewrite 3!qubit_perm_to_nat_perm_defn.
  unfold compose.
  intros k Hk.
  apply funbool_to_nat_eq.
  intros y Hy.
  now rewrite funbool_to_nat_inverse by auto.
Qed.

#[export] Hint Rewrite qubit_perm_to_nat_perm_compose 
  using solve [auto with perm_bounded_db perm_db] : perm_inv_db.

Lemma qubit_perm_to_nat_perm_compose_alt n f g (Hf : perm_bounded n f) k : 
  qubit_perm_to_nat_perm n f (qubit_perm_to_nat_perm n g k) = 
    qubit_perm_to_nat_perm n (g ∘ f)%prg k.
Proof.
  now rewrite <- qubit_perm_to_nat_perm_compose.
Qed.

#[export] Hint Rewrite qubit_perm_to_nat_perm_compose_alt
  using solve [auto with perm_bounded_db perm_db] : perm_inv_db.

Lemma qubit_perm_to_nat_perm_perm_eq_idn n :
  perm_eq (2^n) (qubit_perm_to_nat_perm n idn) idn.
Proof.
  rewrite qubit_perm_to_nat_perm_defn.
  intros k Hk.
  rewrite compose_idn_r.
  now apply nat_to_funbool_inverse.
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_perm_eq_idn : perm_inv_db.

Lemma qubit_perm_to_nat_perm_idn n :
  qubit_perm_to_nat_perm n idn = idn.
Proof.
  eq_by_WF_perm_eq (2^n).
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite qubit_perm_to_nat_perm_idn : perm_cleanup_db.

Lemma qubit_perm_to_nat_perm_permutation : forall n p,
  permutation n p -> permutation (2^n) (qubit_perm_to_nat_perm n p).
Proof.
  intros n p Hp.
  perm_by_inverse (qubit_perm_to_nat_perm n (perm_inv n p)).
Qed. 

#[export] Hint Resolve qubit_perm_to_nat_perm_permutation : perm_db.

Lemma qubit_perm_to_nat_perm_inv n f (Hf : permutation n f) : 
  perm_eq (2^n) 
  (perm_inv (2^n) (qubit_perm_to_nat_perm n f))
  (qubit_perm_to_nat_perm n (perm_inv n f)).
Proof.
  perm_eq_by_inv_inj (qubit_perm_to_nat_perm n f) (2^n).
Qed.

#[export] Hint Resolve qubit_perm_to_nat_perm_inv : perm_inv_db.
#[export] Hint Rewrite qubit_perm_to_nat_perm_inv
  using solve [auto with perm_db] : perm_inv_db.

Lemma qubit_perm_to_nat_perm_inv' n f (Hf : permutation n f) : 
  perm_inv' (2^n) (qubit_perm_to_nat_perm n f) =
  qubit_perm_to_nat_perm n (perm_inv' n f).
Proof.
  eq_by_WF_perm_eq (2^n).
  cleanup_perm_inv.
Qed.

#[export] Hint Rewrite qubit_perm_to_nat_perm_inv'
  using solve [auto with perm_db] : perm_inv_db.

Lemma qubit_perm_to_nat_perm_inj n f g 
  (Hf : perm_bounded n f) : 
  perm_eq (2^n) (qubit_perm_to_nat_perm n f) (qubit_perm_to_nat_perm n g) ->
  perm_eq n f g.
Proof.
  rewrite 2!qubit_perm_to_nat_perm_defn.
  intros H i Hi.
  specialize (H (2^(n - S (f i))) ltac:(apply Nat.pow_lt_mono_r; 
    auto with perm_bounded_db zarith)).
  unfold qubit_perm_to_nat_perm in H.
  rewrite <- funbool_to_nat_eq_iff in H.
  specialize (H i Hi).
  revert H.
  unfold compose.
  rewrite Bits.nat_to_funbool_eq.
  pose proof (Hf i Hi).
  simplify_bools_lia_one_kernel.
  rewrite 2!Nat.pow2_bits_eqb.
  rewrite Nat.eqb_refl.
  bdestructΩ'.
Qed.



Lemma tensor_perms_defn n0 n1 f g : 
  perm_eq (n0 * n1) (tensor_perms n0 n1 f g) 
  (fun k => f (k / n1) * n1 + g (k mod n1)).
Proof.
  intros k Hk.
  unfold tensor_perms.
  now simplify_bools_lia_one_kernel.
Qed.

Lemma tensor_perms_defn_alt n0 n1 f g : 
  perm_eq (n1 * n0) (tensor_perms n0 n1 f g) 
  (fun k => f (k / n1) * n1 + g (k mod n1)).
Proof.
  now rewrite Nat.mul_comm, tensor_perms_defn.
Qed.

Lemma tensor_perms_bounded n0 n1 f g : 
	perm_bounded n0 f -> perm_bounded n1 g ->
	perm_bounded (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	intros Hf Hg k Hk.
	rewrite tensor_perms_defn by easy.
	pose proof (Hf (k / n1) ltac:(show_moddy_lt)).
	pose proof (Hg (k mod n1) ltac:(show_moddy_lt)).
	show_moddy_lt.
Qed.

#[export] Hint Resolve tensor_perms_bounded : perm_bounded_db.
#[export] Hint Extern 10 (perm_bounded ?n01 (tensor_perms ?n0 ?n1 ?f ?g)) =>
  apply (perm_bounded_change_dims n01 (n0 * n1)
  ltac:(show_pow2_le + unify_pows_two; nia));
  apply tensor_perms_bounded : perm_bounded_db.

Lemma tensor_perms_WF n0 n1 f g :
	WF_Perm (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	intros k Hk.
	unfold tensor_perms.
	bdestructΩ'.
Qed.

#[export] Hint Resolve tensor_perms_WF : WF_Perm_db.
#[export] Hint Extern 100 (WF_Perm ?n01 (tensor_perms ?n0 ?n1 ?f ?g)) =>
	replace (WF_Perm n01) with (WF_Perm (n0 * n1)) by 
    (f_equal; nia + show_pow2_le) : WF_Perm_db.

Lemma tensor_perms_compose n0 n1 f0 f1 g0 g1 : 
	perm_bounded n0 f1 -> perm_bounded n1 g1 ->
	tensor_perms n0 n1 f0 g0 ∘ tensor_perms n0 n1 f1 g1 = 
	tensor_perms n0 n1 (f0 ∘ f1) (g0 ∘ g1).
Proof.
	intros Hf1 Hg1.
	eq_by_WF_perm_eq (n0*n1).
  rewrite 3!tensor_perms_defn.
	intros k Hk.
	unfold compose.
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
  easy.
Qed.

Lemma tensor_perms_0_r n0 f g : 
	tensor_perms n0 0 f g = idn.
Proof.
	eq_by_WF_perm_eq (n0 * 0).
	intros k Hk; lia.
Qed.

#[export] Hint Rewrite tensor_perms_0_l 
	tensor_perms_0_r : perm_cleanup_db perm_inv_db.

Lemma tensor_perms_perm_eq_proper n0 n1 f f' g g' : 
	perm_eq n0 f f' -> perm_eq n1 g g' ->
	tensor_perms n0 n1 f g = tensor_perms n0 n1 f' g'.
Proof.
	intros Hf' Hg'.
	eq_by_WF_perm_eq (n0 * n1).
  rewrite 2!tensor_perms_defn.
	intros k Hk.
	now rewrite Hf', Hg' by show_moddy_lt.
Qed.

#[export] Hint Resolve tensor_perms_perm_eq_proper : perm_inv_db.

Add Parametric Morphism n0 n1 : (tensor_perms n0 n1) with signature
  perm_eq n0 ==> perm_eq n1 ==> eq
  as tensor_perms_perm_eq_to_eq_proper.
Proof.
  intros; now apply tensor_perms_perm_eq_proper.
Qed.

Lemma tensor_perms_idn_idn n0 n1 :
	tensor_perms n0 n1 idn idn = idn.
Proof.
	eq_by_WF_perm_eq (n0 * n1).
  rewrite tensor_perms_defn.
	intros k Hk.
	pose proof (Nat.div_mod_eq k n1).
	lia.
Qed.

#[export] Hint Rewrite tensor_perms_idn_idn : perm_cleanup_db.

Lemma tensor_perms_idn_idn' n0 n1 f g :
	perm_eq n0 f idn -> perm_eq n1 g idn ->
	perm_eq (n0 * n1) (tensor_perms n0 n1 f g) idn.
Proof.
	intros -> ->.
	cleanup_perm.
Qed.

#[export] Hint Resolve tensor_perms_idn_idn' : perm_inv_db.

Lemma tensor_perms_permutation n0 n1 f g
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	permutation (n0 * n1) (tensor_perms n0 n1 f g).
Proof.
	perm_by_inverse (tensor_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Qed.

#[export] Hint Resolve tensor_perms_permutation : perm_db.

Lemma tensor_perms_n_2_permutation n f g 
  (Hf : permutation n f) (Hg : permutation 2 g) : 
  permutation (n + n) (tensor_perms n 2 f g).
Proof.
  replace (n + n) with (n * 2) by lia.
  cleanup_perm.
Qed.

#[export] Hint Resolve tensor_perms_n_2_permutation : perm_db.

Lemma tensor_perms_inv n0 n1 f g 
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	perm_eq (n0 * n1) 
		(perm_inv (n0 * n1) (tensor_perms n0 n1 f g))
		(tensor_perms n0 n1 (perm_inv n0 f) (perm_inv n1 g)).
Proof.
	perm_eq_by_inv_inj (tensor_perms n0 n1 f g) (n0*n1).
Qed.

#[export] Hint Resolve tensor_perms_inv : perm_inv_db.
#[export] Hint Rewrite tensor_perms_inv 
  using solve [auto with perm_db] : perm_inv_db.

Lemma tensor_perms_inv' n0 n1 f g 
	(Hf : permutation n0 f) (Hg : permutation n1 g) : 
	perm_inv' (n0 * n1) (tensor_perms n0 n1 f g) =
	tensor_perms n0 n1 (perm_inv' n0 f) (perm_inv' n1 g).
Proof.
	permutation_eq_by_WF_inv_inj (tensor_perms n0 n1 f g) (n0*n1).
Qed.

#[export] Hint Rewrite tensor_perms_inv' 
	using solve [auto with perm_db] : perm_inv_db.

Lemma tensor_rotr_idn_eq_rotr_mul n m p : 
  tensor_perms n p (rotr n m) idn = 
  rotr (n * p) (m * p).
Proof.
  eq_by_WF_perm_eq (n * p).
  rewrite 2!rotr_defn, tensor_perms_defn.
  intros k Hk.
  symmetry.
  rewrite (Nat.mul_comm n p).
  rewrite Nat.Div0.mod_mul_r.
  rewrite Nat.Div0.mod_add.
  rewrite Nat.div_add by lia.
  lia.
Qed.



Lemma qubit_perm_to_nat_perm_stack_perms n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	qubit_perm_to_nat_perm (n0 + n1) (stack_perms n0 n1 f g) =
  tensor_perms (2^n0) (2^n1)
    (qubit_perm_to_nat_perm n0 f)
    (qubit_perm_to_nat_perm n1 g).
Proof.
  eq_by_WF_perm_eq (2^(n0+n1)).
  rewrite stack_perms_defn.
  rewrite !qubit_perm_to_nat_perm_defn, Nat.pow_add_r.
  rewrite tensor_perms_defn.
	intros k Hk.
	rewrite funbool_to_nat_add_pow2_join.
	apply funbool_to_nat_eq.
	intros a Ha.
	unfold compose.
	bdestruct (a <? n0).
	- now rewrite nat_to_funbool_div by cleanup_perm.
	- now rewrite <- nat_to_funbool_mod by auto with perm_bounded_db zarith.
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
	now rewrite qubit_perm_to_nat_perm_stack_perms.
Qed.


#[export] Hint Resolve qubit_perm_to_nat_perm_stack_perms
	qubit_perm_to_nat_perm_stack_perms_alt : perm_inv_db.

#[export] Hint Rewrite qubit_perm_to_nat_perm_stack_perms : perm_cleanup_db.



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




Lemma kron_comm_perm_defn p q : 
  perm_eq (p * q) (kron_comm_perm p q)
    (fun k => k mod p * q + k / p).
Proof.
  intros k Hk.
  unfold kron_comm_perm.
  bdestructΩ'.
Qed.

Lemma kron_comm_perm_defn_alt p q : 
  perm_eq (q * p) (kron_comm_perm p q)
    (fun k => k mod p * q + k / p).
Proof.
  intros k Hk.
  unfold kron_comm_perm.
  bdestructΩ'.
Qed.

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
#[export] Hint Extern 10 (WF_Perm ?n (kron_comm_perm ?p ?q)) =>
  replace (WF_Perm n) with (WF_Perm (p * q)) by 
  (f_equal; show_pow2_le + unify_pows_two; nia);
  apply kron_comm_perm_WF : WF_Perm_db.

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
#[export] Hint Extern 10 (perm_bounded ?n (kron_comm_perm ?p ?q)) =>
  apply (perm_bounded_change_dims n (p * q)
  ltac:(show_pow2_le + unify_pows_two; nia));
  apply kron_comm_perm_bounded : perm_bounded_db.

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
#[export] Hint Extern 10 (permutation ?n (kron_comm_perm ?p ?q)) =>
  replace (permutation n) with (permutation (p * q)) by 
  (f_equal; show_pow2_le + unify_pows_two; nia);
  apply kron_comm_perm_WF : perm_db.

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
  rewrite Nat.mul_comm.
  cleanup_perm_inv.
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
  rewrite Nat.mul_comm.
  cleanup_perm_inv.
Qed.

#[export] Hint Resolve kron_comm_perm_inv
	kron_comm_perm_inv_alt 
	kron_comm_perm_swap_inv 
	kron_comm_perm_swap_inv_alt : perm_inv_db.
#[export] Hint Rewrite kron_comm_perm_inv
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






Lemma stack_perms_big_swap_natural n0 n1 f g 
  (Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
  stack_perms n0 n1 f g ∘ big_swap_perm n1 n0 =
  big_swap_perm n1 n0 ∘ stack_perms n1 n0 g f.
Proof.
  eq_by_WF_perm_eq (n0 + n1).
  rewrite stack_perms_defn.
  rewrite Nat.add_comm.
  rewrite stack_perms_defn.
  intros k Hk.
  unfold compose, big_swap_perm.
  pose proof (Hf (k - n1)).
  pose proof (Hg k).
  bdestructΩ'.
  now rewrite Nat.add_sub.
Qed.

Lemma stack_perms_rotr_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	stack_perms n0 n1 f g ∘ rotr (n0 + n1) n0 =
	rotr (n0 + n1) n0 ∘ stack_perms n1 n0 g f.
Proof.
  rewrite rotr_add_l.
  now apply stack_perms_big_swap_natural.
Qed.

Lemma stack_perms_rotl_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) : 
	stack_perms n0 n1 f g ∘ rotl (n0 + n1) n1 =
	rotl (n0 + n1) n1 ∘ stack_perms n1 n0 g f.
Proof.
  rewrite rotl_add_r.
  now apply stack_perms_big_swap_natural.
Qed.

Lemma tensor_perms_kron_comm_perm_natural n0 n1 f g 
	(Hf : perm_bounded n0 f) (Hg : perm_bounded n1 g) :
	tensor_perms n0 n1 f g ∘ kron_comm_perm n0 n1 =
	kron_comm_perm n0 n1 ∘ tensor_perms n1 n0 g f.
Proof.
	eq_by_WF_perm_eq (n0 * n1).
  rewrite tensor_perms_defn, kron_comm_perm_defn, tensor_perms_defn_alt.
	intros k Hk.
	unfold compose.
	rewrite !Nat.div_add_l, !mod_add_l by lia.
	pose proof (Hf (k mod n0) ltac:(show_moddy_lt)).
	pose proof (Hg (k / n0) ltac:(show_moddy_lt)).
	rewrite Nat.Div0.div_div, Nat.div_small, Nat.add_0_r by lia.
	rewrite (Nat.mod_small (k / n0)) by (show_moddy_lt).
	rewrite (Nat.mod_small (f _)), (Nat.div_small (f _)) by lia.
	lia.
Qed.


Lemma inv_perm_eq_id_mid {padl padm padr f} 
  (Hf : permutation (padl + padm + padr) f)
  (Hfidn : perm_eq_id_mid padl padm f) :
  forall k, k < padl + padm + padr ->
   padl <= f k < padl + padm -> f k = k.
Proof.
  intros k Hk [].
  apply (permutation_is_injective _ _ Hf); [lia..|].
  replace (f k) with (padl + (f k - padl)) by lia.
  (* unfold perm_eq_id_mid in Hfidn. *)
  apply Hfidn; lia.
Qed.

Arguments compose_assoc [_ _ _ _].

Lemma expand_perm_id_mid_compose (f g : nat -> nat) (padl padm padr : nat) 
  (Hf : perm_bounded (padl + padr) f)
  (Hg : perm_bounded (padl + padr) g) :
  expand_perm_id_mid padl padm padr f ∘ expand_perm_id_mid padl padm padr g =
  expand_perm_id_mid padl padm padr (f ∘ g).
Proof.
  unfold expand_perm_id_mid.
  (* cleanup_perm. *)
  rewrite (compose_assoc _ (stack_perms _ _ idn (rotr _ padr))), 
    <- !(compose_assoc _ _ (stack_perms _ _ idn (rotr _ padr))).
  cleanup_perm_inv.
  cleanup_perm.
  rewrite (Nat.add_comm padr padm).
  cleanup_perm.
  rewrite compose_assoc, <- (compose_assoc _ _ (stack_perms _ _ f _)).
  cleanup_perm.
Qed.

Lemma expand_perm_id_mid_eq_of_perm_eq {padl padr f g} 
  (Hfg : perm_eq (padl + padr) f g) padm : 
  expand_perm_id_mid padl padm padr f = expand_perm_id_mid padl padm padr g.
Proof.
  unfold expand_perm_id_mid.
  do 2 f_equal.
  now apply stack_perms_proper_eq.
Qed.

Lemma expand_perm_id_mid_permutation {padl padr f} 
  (Hf : permutation (padl + padr) f) padm : 
  permutation (padl + padm + padr) (expand_perm_id_mid padl padm padr f).
Proof.
  unfold expand_perm_id_mid.
  rewrite <- Nat.add_assoc.
  apply permutation_compose; [|auto with perm_db].
  apply permutation_compose; [auto with perm_db|].
  replace (padl + (padm + padr)) with (padl + padr + padm) by lia.
  auto with perm_db.
Qed.

#[export] Hint Resolve expand_perm_id_mid_permutation : perm_db.



Lemma contract_expand_perm_perm_eq_inv padl padm padr f 
  (Hf : perm_bounded (padl + padr) f) :
  perm_eq (padl + padr)
    (contract_perm_id_mid padl padm padr 
      (expand_perm_id_mid padl padm padr f)) 
    f.
Proof.
  unfold contract_perm_id_mid, expand_perm_id_mid.
  rewrite !compose_assoc.
  cleanup_perm.
  rewrite (Nat.add_comm padr padm).
  rewrite <- !compose_assoc.
  cleanup_perm.
  rewrite (Nat.add_comm padr padm).
  cleanup_perm.
  intros k Hk.
  now rewrite stack_perms_left by easy.
Qed.


Lemma contract_perm_id_mid_compose {padl padm padr f}
  (Hf : perm_bounded (padl + padm + padr) f) g : 
  contract_perm_id_mid padl padm padr g ∘ contract_perm_id_mid padl padm padr f =
  contract_perm_id_mid padl padm padr (g ∘ f).
Proof.
  unfold contract_perm_id_mid.
  rewrite (compose_assoc _ (stack_perms _ _ idn (rotr _ padm))), 
    <- !(compose_assoc _ _ (stack_perms _ _ idn (rotr _ padm))).
  cleanup_perm.
Qed.

Lemma contract_perm_id_mid_permutation_big {padl padm padr f} 
  (Hf : permutation (padl + padm + padr) f) : 
  permutation (padl + padm + padr) (contract_perm_id_mid padl padm padr f).
Proof.
  unfold contract_perm_id_mid.
  rewrite <- Nat.add_assoc in *.
  auto with perm_db.
Qed.

Lemma contract_perm_id_mid_permutation {padl padm padr f}
  (Hf : permutation (padl + padm + padr) f) 
  (Hfid : perm_eq_id_mid padl padm f) : 
  permutation (padl + padr) (contract_perm_id_mid padl padm padr f).
Proof.
  apply (permutation_of_le_permutation_idn_above _ _ _
    (contract_perm_id_mid_permutation_big Hf));
  [lia|].
  intros k [].
  unfold contract_perm_id_mid.
  unfold compose at 1.
  rewrite stack_perms_right by lia.
  rewrite rotr_add_l_eq.
  do 2 simplify_bools_lia_one_kernel.
  unfold compose.
  rewrite (Nat.add_comm _ padl), Hfid by lia.
  rewrite stack_perms_right by lia.
  rewrite rotr_add_r_eq.
  bdestructΩ'.
Qed.

#[export] Hint Resolve contract_perm_id_mid_permutation_big
  contract_perm_id_mid_permutation : perm_db.


Lemma expand_contract_perm_perm_eq_idn_inv {padl padm padr f}
  (Hf : permutation (padl + padm + padr) f) 
  (Hfidn : perm_eq_id_mid padl padm f) :
  perm_eq (padl + padm + padr)
    ((expand_perm_id_mid padl padm padr 
      (contract_perm_id_mid padl padm padr f))) 
    f.
Proof.
  unfold contract_perm_id_mid, expand_perm_id_mid.
  intros k Hk.
  rewrite (stack_perms_idn_f _ _ (rotr _ padr)) at 2.
  unfold compose at 1.
  simplify_bools_lia_one_kernel.
  replace (if ¬ k <? padl then rotr (padm + padr) padr (k - padl) + padl else k)
  with (if ¬ k <? padl then if k <? padl + padm then k + padr else k - padm else k)
    by (rewrite rotr_add_r_eq; bdestructΩ').
  pose proof (inv_perm_eq_id_mid Hf Hfidn k).
  pose proof (Hfidn (k - padl)).
  bdestruct (k <? padl); simpl;
  [|bdestruct (k <? padl + padm); simpl].
  - unfold compose at 1.
    rewrite (@stack_perms_left (padl + padr)) by lia.
    unfold compose at 1.
    rewrite (stack_perms_left (k:=k)) by lia.
    unfold compose.
    rewrite (stack_perms_idn_f _ _ (rotr _ padr)).
    pose proof (permutation_is_bounded _ f Hf k ltac:(easy)).
    simplify_bools_lia_one_kernel.
    rewrite rotr_add_r_eq.
    bdestruct (f k <? padl);
    [simpl; now rewrite stack_perms_left by lia|].
    simpl.
    simplify_bools_lia_one_kernel.
    bdestructΩ'.
    rewrite stack_perms_right by lia.
    rewrite rotr_add_l_eq.
    bdestructΩ'.
  - unfold compose at 1.
    rewrite (@stack_perms_right (padl + padr)) by lia.
    rewrite stack_perms_right by lia.
    rewrite rotr_add_l_eq.
    replace (padl + (k - padl)) with k in * by lia.
    bdestructΩ'.
  - unfold compose at 1.
    rewrite (@stack_perms_left (padl + padr)) by lia.
    unfold compose at 1.
    rewrite (stack_perms_right (k:=k - padm)) by lia.
    rewrite rotr_add_l_eq.
    do 2 simplify_bools_lia_one_kernel.
    replace (k - padm - padl + padm + padl) with k by lia.
    unfold compose.
    rewrite (stack_perms_idn_f _ _ (rotr _ padr)).
    pose proof (permutation_is_bounded _ f Hf k ltac:(easy)).
    simplify_bools_lia_one_kernel.
    rewrite rotr_add_r_eq.
    bdestruct (f k <? padl);
    [simpl; now rewrite stack_perms_left by lia|].
    simpl.
    simplify_bools_lia_one_kernel.
    bdestructΩ'.
    rewrite stack_perms_right by lia.
    bdestructΩ'.
Qed.



(** Analogous to Nat.divmod for inhomogeneous division *)

Fixpoint Nsum_index (n : nat) (g : nat -> nat) (i : nat) : nat :=
  match n with 
  | 0 => 0
  | S n' => if big_sum g n' <=? i then n' else 
    Nsum_index n' g i
  end.

Definition Nsum_offset (n : nat) (g : nat -> nat) (i : nat) : nat :=
  i - big_sum g (Nsum_index n g i).

Add Parametric Morphism n : (Nsum_index n) with signature 
  perm_eq n ==> eq as Nsum_index_perm_eq_to_eq.
Proof.
  intros g g' Hg.
  apply functional_extensionality; intros k.
  induction n; [easy|].
  - cbn -[big_sum].
    assert (Hg' : perm_eq n g g') by (hnf in *; auto).
    rewrite IHn by auto.
    now rewrite (big_sum_eq_bounded _ _ _ Hg').
Qed.

Lemma Nsum_index_total_bounded n g i : 
  Nsum_index n g i <= n.
Proof.
  induction n; [cbn; lia|].
  simpl.
  bdestructΩ'.
Qed.

Lemma Nsum_index_bounded n g i : n <> 0 -> 
  Nsum_index n g i < n.
Proof.
  induction n; [cbn; lia|].
  simpl.
  destruct n; bdestructΩ'.
Qed.

Lemma Nsum_index_spec n g i (Hi : i < big_sum g n) : 
  big_sum g (Nsum_index n g i) <= i < big_sum g (S (Nsum_index n g i)).
Proof.
  induction n; [cbn in *; lia|].
  cbn.
  bdestruct_one.
  - cbn in *; lia.
  - apply IHn; easy.
Qed.

Lemma Nsum_index_spec_inv n g i k (Hk : k < n) : 
  big_sum g k <= i < big_sum g (S k) -> 
  Nsum_index n g i = k.
Proof.
  fill_differences.
  intros H.
  induction x.
  - rewrite Nat.add_0_r, Nat.add_comm.
    simpl.
    bdestructΩ'.
  - rewrite Nat.add_succ_r.
    simpl.
    rewrite (big_sum_split _ k) by lia.
    cbn in *.
    bdestructΩ'.
Qed.

Lemma Nsum_index_offset_spec n g i (Hi : i < big_sum g n) : 
  i = big_sum g (Nsum_index n g i) + Nsum_offset n g i
  /\ Nsum_offset n g i < g (Nsum_index n g i).
Proof.
  pose proof (Nsum_index_spec n g i Hi) as Hsum.
  simpl in Hsum.
  unfold Nsum_offset.
  split;
  lia.
Qed.

Lemma Nsum_index_add_big_sum_l n dims i k
  (Hi : i < dims k) (Hk : k < n) :
  Nsum_index n dims (big_sum dims k + i) = 
  k.
Proof.
  fill_differences.
  induction x; [
    rewrite <- Nat.add_assoc, Nat.add_comm;
    cbn; bdestructΩ'|].
  rewrite Nat.add_succ_r.
  cbn.
  rewrite (big_sum_split _ k _) by lia.
  cbn.
  simplify_bools_lia_one_kernel.
  easy.
Qed.

Lemma Nsum_offset_add_big_sum_l n dims i k
  (Hi : i < dims k) (Hk : k < n) :
  Nsum_offset n dims (big_sum dims k + i) = 
  i.
Proof.
  unfold Nsum_offset.
  rewrite Nsum_index_add_big_sum_l by auto.
  lia.
Qed.

Definition enlarge_permutation (n : nat) (f dims : nat -> nat)  :=
  fun k => if big_sum dims n <=? k then k else
  big_sum (dims ∘ f) 
    (perm_inv' n f (Nsum_index n dims k)) + 
    Nsum_offset n dims k.


Add Parametric Morphism n : (enlarge_permutation n) with signature
  on_predicate_relation_l 
    (fun f => perm_bounded n f)
    (perm_eq n) ==> perm_eq n ==> eq
    as enlarge_permutation_perm_eq_to_eq.
Proof.
  intros f f' [Hbdd Hf] dims dims' Hdims.
  apply functional_extensionality; intros k.
  unfold enlarge_permutation.
  rewrite (big_sum_eq_bounded _ _ n Hdims).
  bdestructΩ'.
  bdestruct (n =? 0); [subst; cbn in *; lia|].
  f_equal.
  - rewrite <- (perm_inv'_eq_of_perm_eq n f f' Hf).
    assert (Hrw : perm_eq n (dims ∘ f) (dims' ∘ f')) by 
      now rewrite Hdims, Hf.
    rewrite (Nsum_index_perm_eq_to_eq n _ _ Hdims).
    apply big_sum_eq_bounded.
    intros i Hi.
    apply Hrw.
    eapply Nat.lt_trans; [eassumption|].
    pose proof (Nsum_index_bounded n dims' k ltac:(auto)) as Hlt.
    auto with perm_bounded_db.
  - unfold Nsum_offset.
    rewrite (Nsum_index_perm_eq_to_eq n _ _ Hdims).
    f_equal.
    apply big_sum_eq_bounded.
    intros i Hi.
    apply Hdims.
    pose proof (Nsum_index_bounded n dims' k ltac:(auto)) as Hlt.
    lia.
Qed.


Add Parametric Morphism n : (enlarge_permutation n) with signature
  perm_eq n ==> eq ==> eq as enlarge_permutation_perm_eq_to_eq_to_eq.
Proof.
  intros f f' Hf dims.
  apply functional_extensionality; intros k.
  unfold enlarge_permutation.
  bdestructΩ'.
  bdestruct (n =? 0); [subst; cbn in *; lia|].
  f_equal.
  rewrite <- (perm_inv'_eq_of_perm_eq n f f' Hf).
  apply big_sum_eq_bounded.
  intros i Hi.
  unfold compose.
  f_equal.
  apply Hf.
  eapply Nat.lt_trans; [eassumption|].
  pose proof (Nsum_index_bounded n dims k ltac:(auto)) as Hlt.
  auto with perm_bounded_db.
Qed.

Lemma enlarge_permutation_add_big_sum_l n f dims i k
  (Hi : i < dims k) (Hk : k < n) :
  enlarge_permutation n f dims
    (big_sum dims k + i) = 
  big_sum (dims ∘ f) (perm_inv' n f k) + i.
Proof.
  unfold enlarge_permutation.
  rewrite (big_sum_split n k dims Hk).
  cbn.
  simplify_bools_lia_one_kernel.
  now rewrite Nsum_index_add_big_sum_l,
    Nsum_offset_add_big_sum_l by auto.
Qed.

Lemma enlarge_permutation_WF n f dims : 
  WF_Perm (big_sum dims n) (enlarge_permutation n f dims).
Proof.
  intros k Hk.
  unfold enlarge_permutation.
  bdestructΩ'.
Qed.

#[export] Hint Resolve enlarge_permutation_WF : WF_Perm_db.

Lemma enlarge_permutation_compose' n f g dims dims'
  (Hdims : perm_eq n (dims ∘ f) dims') 
  (Hf : permutation n f) (Hg : permutation n g) : 
  perm_eq (big_sum dims n) 
  (enlarge_permutation n g dims' ∘ enlarge_permutation n f dims)
  (enlarge_permutation n (f ∘ g) dims).
Proof.
  intros k Hk.
  rewrite <- Hdims.
  unfold compose at 1.
  unfold enlarge_permutation at 2.
  simplify_bools_lia_one_kernel.
  assert (Hn : n <> 0) by (intros ->; cbn in *; lia).
  pose proof (Nsum_index_bounded n dims k Hn).
  rewrite enlarge_permutation_add_big_sum_l.
  3: auto with perm_bounded_db.
  2: {
    pose proof (Nsum_index_offset_spec n dims k Hk).
    unfold compose.
    rewrite perm_inv'_eq by auto with perm_bounded_db.
    rewrite perm_inv_is_rinv_of_permutation by auto.
    lia.
  } 
  rewrite Combinators.compose_assoc.
  unfold enlarge_permutation.
  simplify_bools_lia_one_kernel.
  rewrite perm_inv'_compose by auto.
  easy.
Qed.

Lemma enlarge_permutation_bounded n f dims (Hf : permutation n f) : 
  perm_bounded (big_sum dims n) (enlarge_permutation n f dims).
Proof.
  intros k Hk.
  unfold enlarge_permutation.
  simplify_bools_lia_one_kernel.
  rewrite (Nsum_reorder n dims (f)) by auto with perm_db.
  pose proof (Nsum_index_offset_spec n dims k Hk).
  assert (Hn : n <> 0) by (intros ->; cbn in *; lia).
  pose proof (Nsum_index_bounded n dims k Hn) as Hidx.
  rewrite (big_sum_split n (perm_inv' n f (Nsum_index n dims k))) 
    by auto with perm_bounded_db.
  unfold compose at 3.
  rewrite perm_inv'_eq, perm_inv_is_rinv_of_permutation 
    by auto with perm_bounded_db.
  cbn. 
  lia.
Qed.

#[export] Hint Resolve enlarge_permutation_bounded : perm_bounded_db.

Lemma enlarge_permutation_defn n f dims : 
  perm_eq (big_sum dims n) 
    (enlarge_permutation n f dims) 
    (fun k => big_sum (dims ∘ f)
    (perm_inv' n f (Nsum_index n dims k)) +
    Nsum_offset n dims k).
Proof.
  intros k Hk.
  unfold enlarge_permutation.
  bdestructΩ'.
Qed.

Lemma enlarge_permutation_idn n dims : 
  enlarge_permutation n idn dims = idn.
Proof.
  eq_by_WF_perm_eq (big_sum dims n).
  rewrite enlarge_permutation_defn.
  intros k Hk.
  rewrite idn_inv', compose_idn_r.
  symmetry.
  now apply Nsum_index_offset_spec.
Qed.


Lemma enlarge_permutation_permutation n f dims (Hf : permutation n f) : 
  permutation (big_sum dims n) (enlarge_permutation n f dims).
Proof.
  rewrite permutation_defn.
  assert (Hfinv : permutation n (perm_inv' n f)) by auto with perm_db.
  exists (enlarge_permutation n (perm_inv' n f) (dims ∘ f)).
  repeat split.
  - auto with perm_bounded_db.
  - rewrite (Nsum_reorder n dims _ Hf).
    auto with perm_bounded_db perm_db.
  - rewrite (Nsum_reorder n dims _ Hf).
    rewrite enlarge_permutation_compose' by cleanup_perm_inv.
    rewrite perm_inv'_eq, perm_inv_linv_of_permutation by assumption.
    now rewrite enlarge_permutation_idn.
  - rewrite enlarge_permutation_compose' by cleanup_perm_inv.
    rewrite perm_inv'_eq, perm_inv_rinv_of_permutation by assumption.
    now rewrite enlarge_permutation_idn.
Qed.

#[export] Hint Resolve enlarge_permutation_permutation : perm_db.

Lemma enlarge_permutation_inv n f dims (Hf : permutation n f) : 
  perm_eq (big_sum dims n) 
    (perm_inv (big_sum dims n) (enlarge_permutation n f dims))
    (enlarge_permutation n (perm_inv n f) (dims ∘ f)).
Proof.
  perm_eq_by_inv_inj (enlarge_permutation n f dims) (big_sum dims n).
  rewrite enlarge_permutation_compose' by auto_perm.
  rewrite perm_inv_rinv_of_permutation by auto.
  now rewrite enlarge_permutation_idn.
Qed.

Lemma enlarge_permutation_inv' n f dims (Hf : permutation n f) : 
  perm_inv' (big_sum dims n) (enlarge_permutation n f dims) =
  enlarge_permutation n (perm_inv' n f) (dims ∘ f).
Proof.
  eq_by_WF_perm_eq (big_sum dims n);
  [rewrite (Nsum_reorder n dims f Hf); auto_perm..|].
  rewrite 2!perm_inv'_eq.
  now apply enlarge_permutation_inv.
Qed.


Definition swap_2_to_2_perm a b c d n := 
  fun k =>
  if n <=? k then k else
  if b =? c then (
    if k =? a then b else
    if k =? b then d else
    if k =? d then a else k
  ) else if a =? d then (
    if k =? a then c else
    if k =? c then b else
    if k =? b then a else k
  ) else (
    if k =? a then c else 
    if k =? b then d else
    if k =? c then a else
    if k =? d then b else k).

Lemma swap_2_to_2_perm_WF a b c d n :
  WF_Perm n (swap_2_to_2_perm a b c d n).
Proof.
  intros k Hk.
  unfold swap_2_to_2_perm; bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_WF : WF_Perm_db.

Lemma swap_2_to_2_perm_invol a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) 
  (Hab : a <> b) (Hbc : b <> c) (Hcd : c <> d) 
  (Had : a <> d) :
  swap_2_to_2_perm a b c d n ∘ swap_2_to_2_perm a b c d n = idn.
Proof.
  eq_by_WF_perm_eq n.
  intros k Hk.
  unfold swap_2_to_2_perm, compose.
  do 2 simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_invol : perm_inv_db.

Lemma swap_2_to_2_perm_bounded a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) : 
  perm_bounded n (swap_2_to_2_perm a b c d n).
Proof.
  intros k Hk.
  unfold swap_2_to_2_perm.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_2_to_2_perm_bounded : perm_bounded_db.

Lemma swap_2_to_2_perm_permutation a b c d n 
  (Ha : a < n) (Hb : b < n) (Hc : c < n) (Hd : d < n) 
  (Hab : a <> b) (Hcd : c <> d) : 
  permutation n (swap_2_to_2_perm a b c d n).
Proof.
  bdestruct (b =? c);
  [|bdestruct (a =? d)].
  - exists (swap_2_to_2_perm d b b a n).
    intros k Hk; repeat split;
    unfold swap_2_to_2_perm;
    do 2 simplify_bools_lia_one_kernel;
    bdestructΩ'.
  - exists (swap_2_to_2_perm a c b a n).
    intros k Hk; repeat split;
    unfold swap_2_to_2_perm;
    do 2 simplify_bools_lia_one_kernel;
    bdestructΩ'.
  - perm_by_inverse (swap_2_to_2_perm a b c d n).
Qed.

#[export] Hint Resolve swap_2_to_2_perm_permutation : perm_db.

Lemma swap_2_to_2_perm_first a b c d n (Ha : a < n) : 
  swap_2_to_2_perm a b c d n a = c.
Proof.
  unfold swap_2_to_2_perm; bdestructΩ'.
Qed.

Lemma swap_2_to_2_perm_second a b c d n (Ha : b < n) (Hab : a <> b) : 
  swap_2_to_2_perm a b c d n b = d.
Proof.
  unfold swap_2_to_2_perm.
  bdestructΩ'.
Qed.



Lemma perm_eq_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  perm_eq m f (stack_perms n (m - n) idn (fun k => f (k + n) - n)).
Proof.
  assert (Hfeqinv : forall k, k < m -> f k < n -> k < n). 1:{
    intros k Hk Hfk.
    enough (f k = k) by lia.
    apply (permutation_is_injective m f Hf); [lia..|].
    now apply Hfeq.
  }
  assert (Hfbig : forall k, n <= k < m -> n <= f k). 1: {
    intros k [].
    bdestructΩ (n <=? f k).
    specialize (Hfeqinv k); lia.
  }
  intros k Hk.
  bdestruct (k <? n).
  - rewrite stack_perms_left by lia.
    now apply Hfeq.
  - rewrite stack_perms_right by lia.
    rewrite (Nat.sub_add n k) by lia.
    specialize (Hfbig k).
    lia.
Qed.

Lemma perm_big_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  forall k, n <= k < m -> n <= f k.
Proof.
  assert (Hfeqinv : forall k, k < m -> f k < n -> k < n). 1:{
    intros k Hk Hfk.
    enough (f k = k) by lia.
    apply (permutation_is_injective m f Hf); [lia..|].
    now apply Hfeq.
  }
  intros k [].
  bdestructΩ (n <=? f k).
  specialize (Hfeqinv k); lia.
Qed.

Lemma perm_inv_perm_eq_idn_of_perm_eq_idn_up_to n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) :
  perm_eq n (perm_inv m f) idn.
Proof.
  intros k Hk.
  apply (permutation_is_injective m f Hf); [auto with perm_bounded_db..|].
  cleanup_perm.
  symmetry.
  now apply Hfeq.
Qed.

Lemma perm_shift_permutation_of_small_eq_idn n m f (Hm : n <= m) 
  (Hf : permutation m f) (Hfeq : perm_eq n f idn) : 
  permutation (m - n) (fun k => f (k + n) - n).
Proof.
  pose proof (perm_big_of_small_eq_idn n m f Hm Hf Hfeq) as Hfbig.
  pose proof (perm_big_of_small_eq_idn n m _ Hm (perm_inv_permutation m f Hf) 
    (perm_inv_perm_eq_idn_of_perm_eq_idn_up_to n m f Hm Hf Hfeq))
    as Hfinvbig.
  exists (fun k => (perm_inv m f (k + n) - n)).
  intros k Hk; repeat split.
  - pose proof (permutation_is_bounded m f Hf (k + n)).
    lia.
  - pose proof (perm_inv_bounded m f (k + n)).
    lia.
  - rewrite Nat.sub_add by (apply Hfbig; lia).
    cleanup_perm;
    lia.
  - rewrite Nat.sub_add by (apply Hfinvbig; lia).
    cleanup_perm;
    lia.
Qed.
  
#[export] Hint Resolve perm_shift_permutation_of_small_eq_idn : perm_db.