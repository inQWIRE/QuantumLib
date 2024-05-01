Require Import VectorStates.

(** Facts about permutations and matrices that implement them. *)

Local Open Scope nat_scope.

Create HintDb perm_db.
Create HintDb perm_bdd_db.
Create HintDb perm_inv_db.
Create HintDb WF_perm_db.

(** Permutations on (0, ..., n-1) *)
Definition permutation (n : nat) (f : nat -> nat) :=
  exists g, forall x, x < n -> (f x < n /\ g x < n /\ g (f x) = x /\ f (g x) = x).

Lemma permutation_is_injective : forall n f, 
  permutation n f -> 
  forall x y, x < n -> y < n -> f x = f y -> x = y.
Proof.
  intros n f [g Hbij] x y Hx Hy H.
  destruct (Hbij x Hx) as [_ [_ [H0 _]]].
  destruct (Hbij y Hy) as [_ [_ [H1 _]]].
  rewrite <- H0. 
  rewrite <- H1.
  rewrite H.
  reflexivity.
Qed.

Lemma permutation_is_surjective : forall n f,
  permutation n f ->
  forall k, k < n -> exists k', k' < n /\ f k' = k.
Proof.
  intros n f Hf k Hk.
  destruct Hf as [finv Hfinv].
  specialize (Hfinv k Hk).
  exists (finv k).
  intuition.
Qed.

Lemma permutation_compose : forall n f g,
  permutation n f ->
  permutation n g ->
  permutation n (f ∘ g)%prg.
Proof.
  intros n f g [finv Hfbij] [ginv Hgbij].
  exists (ginv ∘ finv)%prg.
  unfold compose.
  intros x Hx.
  destruct (Hgbij x) as [? [_ [? _]]]; auto.
  destruct (Hfbij (g x)) as [? [_ [Hinv1 _]]]; auto.
  destruct (Hfbij x) as [_ [? [_ ?]]]; auto.
  destruct (Hgbij (finv x)) as [_ [? [_ Hinv2]]]; auto.
  repeat split; auto.
  rewrite Hinv1. 
  assumption.
  rewrite Hinv2. 
  assumption.
Qed.

(** The identity permutation *)
Local Notation idn := (fun (k : nat) => k).

Lemma compose_idn_l : forall {T} (f : T -> nat), (idn ∘ f = f)%prg.
Proof.
  intros.
  unfold compose.
  apply functional_extensionality; easy.
Qed.

Lemma compose_idn_r : forall {T} (f : nat -> T), (f ∘ idn = f)%prg.
Proof.
  intros.
  unfold compose.
  apply functional_extensionality; easy.
Qed.

#[export] Hint Rewrite @compose_idn_r @compose_idn_l : perm_cleanup_db.

Lemma idn_permutation : forall n, permutation n idn.
Proof.
  intros. 
  exists idn.
  easy. 
Qed.

Global Hint Resolve idn_permutation : perm_db.

(** Notions of injectivity, boundedness, and surjectivity of f : nat -> nat 
  (interpreted as a function from [n]_0 to [n]_0) and their equivalences *)
Local Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Local Notation perm_bdd n f := (forall k, k < n -> f k < n).
Local Notation perm_inj n f := (forall k l, k < n -> l < n -> f k = f l -> k = l).

Lemma fswap_injective_if_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f -> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy Hinj k l Hk Hl.
  unfold fswap.
  bdestruct (k =? x); bdestruct (k =? y);
  bdestruct (l =? x); bdestruct (l =? y);
  subst; auto using Hinj.
  all: intros Heq;
    epose proof (Hinj _ _ _ _ Heq); 
    exfalso; lia.
  Unshelve.
  all: assumption.
Qed.

Lemma fswap_injective_iff_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f <-> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy.
  split.
  - apply fswap_injective_if_injective; easy.
  - intros Hinj.
    rewrite <- (fswap_involutive f x y).
    apply fswap_injective_if_injective; easy.
Qed.

Lemma fswap_surjective_if_surjective : forall n f x y, 
  x < n -> y < n -> 
  perm_surj n f -> perm_surj n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hsurj k Hk.
  destruct (Hsurj k Hk) as [k' [Hk' Hfk']].
  bdestruct (k' =? x); [|bdestruct (k' =? y)].
  - exists y.
    split; [assumption|].
    subst.
    rewrite fswap_simpl2.
    easy.
  - exists x.
    split; [assumption|].
    subst.
    rewrite fswap_simpl1.
    easy.
  - exists k'.
    split; [assumption|].
    rewrite fswap_neq; lia.
Qed.

Lemma fswap_surjective_iff_surjective : forall n f x y,
  x < n -> y < n ->
  perm_surj n f <-> perm_surj n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_surjective_if_surjective; easy.
  - intros Hsurj.
    rewrite <- (fswap_involutive f x y).
    apply fswap_surjective_if_surjective; easy.
Qed.

Lemma fswap_bounded_if_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bdd n f -> perm_bdd n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hbdd k Hk.
  unfold fswap.
  bdestruct_all;
  apply Hbdd; 
  easy.
Qed.

Lemma fswap_bounded_iff_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bdd n f <-> perm_bdd n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_bounded_if_bounded; easy.
  - intros Hbdd.
    rewrite <- (fswap_involutive f x y).
    apply fswap_bounded_if_bounded; easy.
Qed.

Lemma surjective_of_eq_boundary_shrink : forall n f,
  perm_surj (S n) f -> f n = n -> perm_surj n f.
Proof.
  intros n f Hsurj Hfn k Hk.
  assert (HkS : k < S n) by lia.
  destruct (Hsurj k HkS) as [k' [Hk' Hfk']].
  bdestruct (k' =? n).
  - exfalso; subst; lia.
  - exists k'.
    split; [lia | assumption].
Qed.

Lemma surjective_of_eq_boundary_grow : forall n f,
  perm_surj n f -> f n = n -> perm_surj (S n) f.
Proof.
  intros n f Hsurj Hfn k Hk.
  bdestruct (k =? n).
  - exists n; lia.
  - assert (H'k : k < n) by lia.
    destruct (Hsurj k H'k) as [k' [Hk' Hfk']].
    exists k'; lia.
Qed.

Lemma fswap_at_boundary_surjective : forall n f n',
  n' < S n -> perm_surj (S n) f -> f n' = n -> 
  perm_surj n (fswap f n' n).
Proof.
  intros n f n' Hn' Hsurj Hfn' k Hk.
  bdestruct (k =? f n).
  - exists n'.
    split.
    + assert (Hneq: n' <> n); [|lia].
      intros Hfalse.
      rewrite Hfalse in Hfn'.
      rewrite Hfn' in H.
      lia.
    + rewrite fswap_simpl1; easy.
  - assert (H'k : k < S n) by lia.
    destruct (Hsurj k H'k) as [k' [Hk' Hfk']].
    assert (Hk'n: k' <> n) by (intros Hfalse; subst; lia).
    assert (Hk'n': k' <> n') by (intros Hfalse; subst; lia).
    exists k'.
    split; [lia|].
    rewrite fswap_neq; lia.
Qed.

Lemma injective_monotone : forall {A} n (f : nat -> A) m, 
  m < n -> perm_inj n f -> perm_inj m f.
Proof.
  intros A n f m Hmn Hinj k l Hk Hl Hfkl.
  apply Hinj; auto; lia.
Qed.

Lemma injective_and_bounded_grow_of_boundary : forall n f,
  perm_inj n f /\ perm_bdd n f -> f n = n ->
  perm_inj (S n) f /\ perm_bdd (S n) f.
Proof.
  intros n f [Hinj Hbdd] Hfn.
  split.
  - intros k l Hk Hl Hfkl.
    bdestruct (k =? n).
    + subst.
      bdestruct (l =? n); [easy|].
      assert (H'l : l < n) by lia.
      specialize (Hbdd _ H'l).
      lia.
    + assert (H'k : k < n) by lia.
      bdestruct (l =? n).
      * specialize (Hbdd _ H'k). 
        subst. lia.
      * assert (H'l : l < n) by lia.
        apply Hinj; easy.
  - intros k Hk.
    bdestruct (k <? n).
    + specialize (Hbdd _ H). lia.
    + replace k with n by lia.
      lia.
Qed.

Lemma injective_and_bounded_of_surjective : forall n f,
  perm_surj n f -> perm_inj n f /\ perm_bdd n f.
Proof.
  intros n.
  induction n; [easy|].
  intros f Hsurj.
  assert (HnS : n < S n) by lia.
  destruct (Hsurj n HnS) as [n' [Hn' Hfn']].
  pose proof (fswap_at_boundary_surjective _ _ _ Hn' Hsurj Hfn') as Hswap_surj.
  specialize (IHn (fswap f n' n) Hswap_surj).
  rewrite (fswap_injective_iff_injective _ f n' n); [|easy|easy].
  rewrite (fswap_bounded_iff_bounded _ f n' n); [|easy|easy].
  apply injective_and_bounded_grow_of_boundary;
  [| rewrite fswap_simpl2; easy].
  easy.
Qed.

Lemma injective_and_bounded_shrink_of_boundary : forall n f,
  perm_inj (S n) f /\ perm_bdd (S n) f -> f n = n -> 
  perm_inj n f /\ perm_bdd n f.
Proof.
  intros n f [Hinj Hbdd] Hfn.
  split.
  - eapply injective_monotone, Hinj; lia.
  - intros k Hk.
    assert (H'k : k < S n) by lia.
    specialize (Hbdd k H'k).
    bdestruct (f k =? n).
    + rewrite <- Hfn in H.
      assert (HnS : n < S n) by lia.
      specialize (Hinj _ _ H'k HnS H).
      lia.
    + lia.
Qed.

(* Formalization of proof sketch of pigeonhole principle
   from https://math.stackexchange.com/a/910790 *)
Lemma exists_bounded_decidable : forall n P,
  (forall k, k < n -> {P k} + {~ P k}) ->
  {exists j, j < n /\ P j} + {~ exists j, j < n /\ P j}.
Proof.
  intros n P HPdec.
  induction n.
  - right; intros [x [Hlt0 _]]; inversion Hlt0.
  - destruct (HPdec n) as [HPn | HnPn]; [lia| |].
    + left. exists n; split; [lia | assumption].
    + destruct IHn as [Hex | Hnex].
      * intros k Hk; apply HPdec; lia.
      * left. 
        destruct Hex as [j [Hjn HPj]].
        exists j; split; [lia | assumption].
      * right.
        intros [j [Hjn HPj]].
        apply Hnex.
        bdestruct (j =? n).
        -- exfalso; apply HnPn; subst; easy.
        -- exists j; split; [lia | easy].
Qed.

Lemma has_preimage_decidable : forall n f, 
  forall k, k < n ->
  {exists j, j < n /\ f j = k} + {~exists j, j < n /\ f j = k}.
Proof.
  intros n f k Hk.
  apply exists_bounded_decidable.
  intros k' Hk'.
  bdestruct (f k' =? k).
  - left; easy.
  - right; easy.
Qed.

Lemma pigeonhole_S : forall n f, 
  (forall i, i < S n -> f i < n) ->
  exists i j, i < S n /\ j < i /\ f i = f j.
Proof.
  intros n.
  destruct n;
    [intros f Hbdd; specialize (Hbdd 0); lia|].
  induction n; intros f Hbdd.
  1: {
    exists 1, 0.
    pose (Hbdd 0).
    pose (Hbdd 1). 
    lia.
  }
  destruct (has_preimage_decidable (S (S n)) f (f (S (S n)))) as [Hex | Hnex].
  - apply Hbdd; lia.
  - destruct Hex as [j [Hj Hfj]].
    exists (S (S n)), j.
    repeat split; lia.
  - destruct (IHn (fun k => if f k <? f (S (S n)) then f k else f k - 1)) as
      [i [j [Hi [Hj Hgij]]]].
    + intros i Hi.
      bdestruct (f i <? f (S (S n))).
      * specialize (Hbdd (S (S n))).
        lia.
      * specialize (Hbdd i).
        lia.
    + exists i, j.
      repeat (split; [lia|]).
      assert (Hnex': forall k, k < S (S n) -> f k >= f (S (S n)) -> f k > f (S (S n))). 1:{
        intros k Hk Hge.
        bdestruct (f k =? f (S (S n))).
        - exfalso; apply Hnex; exists k; split; lia.
        - lia.
      }
      bdestruct (f i <? f (S (S n)));
      bdestruct (f j <? f (S (S n)));
      try easy.
      * specialize (Hnex' j); lia.
      * specialize (Hnex' i); lia.
      * pose (Hnex' j).
        pose (Hnex' i Hi H).
        lia.
Qed.

Lemma n_has_preimage_of_injective_and_bounded : forall n f,
  perm_inj (S n) f /\ perm_bdd (S n) f -> exists k, k < S n /\ f k = n.
Proof. 
  intros n f [Hinj Hbdd].
  destruct (has_preimage_decidable (S n) f n) as [Hex | Hnex]; 
    [lia | assumption |].
  (* Now, contradict injectivity using pigeonhole principle *)
  exfalso.
  assert (Hbdd': forall j, j < S n -> f j < n). 1:{
    intros j Hj.
    specialize (Hbdd j Hj).
    bdestruct (f j =? n).
    - exfalso; apply Hnex; exists j; easy.
    - lia.
  }
  destruct (pigeonhole_S n f Hbdd') as [i [j [Hi [Hj Heq]]]].
  absurd (i = j).
  - lia.
  - apply Hinj; lia.
Qed.

Lemma surjective_of_injective_and_bounded : forall n f,
  perm_inj n f /\ perm_bdd n f -> perm_surj n f.
Proof. 
  induction n; [easy|].
  intros f Hinj_bdd.
  destruct (n_has_preimage_of_injective_and_bounded n f Hinj_bdd) as [n' [Hn' Hfn']].
  rewrite (fswap_injective_iff_injective _ _ n n') in Hinj_bdd;
    [|lia|lia].
  rewrite (fswap_bounded_iff_bounded _ _ n n') in Hinj_bdd;
    [|lia|lia].
  rewrite (fswap_surjective_iff_surjective _ _ n n');
    [|lia|easy].
  intros k Hk.
  bdestruct (k =? n).
  - exists n.
    split; [lia|].
    rewrite fswap_simpl1; subst; easy.
  - pose proof (injective_and_bounded_shrink_of_boundary n _ Hinj_bdd) as Hinj_bdd'.
    rewrite fswap_simpl1 in Hinj_bdd'.
    specialize (Hinj_bdd' Hfn').
    destruct (IHn (fswap f n n') Hinj_bdd' k) as [k' [Hk' Hfk']]; [lia|].
    exists k'.
    split; [lia|assumption].
Qed.

(** Explicit inverse of a permutation *)
Fixpoint perm_inv n f k : nat :=
  match n with
  | 0 => 0%nat
  | S n' => if f n' =? k then n'%nat else perm_inv n' f k
  end.

Lemma perm_inv_bounded_S : forall n f k,
  perm_inv (S n) f k < S n.
Proof.
  intros n f k. 
  induction n; simpl.
  - bdestructΩ (f 0 =? k).
  - bdestruct (f (S n) =? k); [|transitivity (S n); [apply IHn|]]. 
  all: apply Nat.lt_succ_diag_r.
Qed.

Lemma perm_inv_bounded : forall n f,
  perm_bdd n (perm_inv n f).
Proof.
  induction n.
  - easy.
  - intros.
    apply perm_inv_bounded_S.
Qed.

#[export] Hint Resolve perm_inv_bounded_S perm_inv_bounded : perm_bdd_db.

Lemma perm_inv_is_linv_of_injective : forall n f, 
  perm_inj n f ->
  forall k, k < n -> perm_inv n f (f k) = k.
Proof.
  intros n f Hinj k Hk.
  induction n.
  - easy.
  - simpl.
    bdestruct (f n =? f k).
    + apply Hinj; lia.
    + assert (k <> n) by (intros Heq; subst; easy).
      apply IHn; [auto|].
      assert (k <> n) by (intros Heq; subst; easy).
      lia.
Qed.

Lemma perm_inv_is_rinv_of_surjective' : forall n f k,
  (exists l, l < n /\ f l = k) ->
  f (perm_inv n f k) = k.
Proof.
  intros n f k.
  induction n.
  - intros []; easy.
  - intros [l [Hl Hfl]].
    simpl.
    bdestruct (f n =? k); [easy|].
    apply IHn.
    exists l.
    split; [|easy].
    bdestruct (l =? n); [subst; easy|].
    lia.
Qed.

Lemma perm_inv_is_rinv_of_surjective : forall n f,
  perm_surj n f -> forall k, k < n -> 
  f (perm_inv n f k) = k.
Proof.
  intros n f Hsurj k Hk.
  apply perm_inv_is_rinv_of_surjective', Hsurj, Hk.
Qed.

Lemma perm_inv_is_linv_of_permutation : forall n f,
  permutation n f ->
  forall k, k < n -> perm_inv n f (f k) = k.
Proof.
  intros n f Hperm.
  apply perm_inv_is_linv_of_injective, permutation_is_injective, Hperm.
Qed.

Lemma perm_inv_is_rinv_of_permutation : forall n f,
  permutation n f ->
  forall k, k < n -> f (perm_inv n f k) = k.
Proof.
  intros n f Hperm k Hk.
  apply perm_inv_is_rinv_of_surjective', (permutation_is_surjective _ _ Hperm _ Hk).
Qed.

Lemma perm_inv_is_inv_of_surjective_injective_bounded : forall n f,
  perm_surj n f -> perm_inj n f -> perm_bdd n f ->
  (forall k, k < n -> 
    f k < n /\ perm_inv n f k < n /\ perm_inv n f (f k) = k /\ f (perm_inv n f k) = k).
Proof.
  intros n f Hsurj Hinj Hbdd.
  intros k Hk; repeat split.
  - apply Hbdd, Hk.
  - apply perm_inv_bounded, Hk.
  - rewrite perm_inv_is_linv_of_injective; easy.
  - rewrite perm_inv_is_rinv_of_surjective'; [easy|].
    apply Hsurj; easy.
Qed.

Lemma permutation_iff_surjective : forall n f, 
  permutation n f <-> perm_surj n f.
Proof.
  split.
  - apply permutation_is_surjective.
  - intros Hsurj.
    exists (perm_inv n f).
    pose proof (injective_and_bounded_of_surjective n f Hsurj).
    apply perm_inv_is_inv_of_surjective_injective_bounded; easy.
Qed.

Lemma perm_inv_permutation n f : permutation n f ->
  permutation n (perm_inv n f).
Proof.
  intros Hperm.
  exists f.
  intros k Hk; repeat split.
  - apply perm_inv_bounded, Hk.
  - destruct Hperm as [? H]; apply H, Hk.
  - rewrite perm_inv_is_rinv_of_permutation; easy.
  - rewrite perm_inv_is_linv_of_permutation; easy.
Qed.

#[export] Hint Resolve perm_inv_permutation : perm_db.

Lemma permutation_is_bounded n f : permutation n f ->
  perm_bdd n f.
Proof.
  intros [finv Hfinv] k Hk.
  destruct (Hfinv k Hk); easy.
Qed.

Lemma id_permutation : forall n,
  permutation n Datatypes.id.
Proof. intros.
       exists Datatypes.id.
       intros.
       unfold Datatypes.id.
       easy.
Qed.

Lemma fswap_permutation : forall n f x y,
  permutation n f ->
  (x < n)%nat -> 
  (y < n)%nat -> 
  permutation n (fswap f x y).
Proof. intros. 
       replace (fswap f x y) with (f ∘ (fswap (fun i => i) x y))%prg.
       apply permutation_compose; auto.
       exists (fswap (fun i => i) x y).
       intros. unfold fswap.
       bdestruct_all; subst; auto.
       apply functional_extensionality; intros.
       unfold compose, fswap.
       bdestruct_all; easy.
Qed.

Lemma fswap_at_boundary_permutation : forall n f x,
  permutation (S n) f ->
  (x < S n)%nat -> f x = n ->
  permutation n (fswap f x n).
Proof.
  intros n f x.
  rewrite 2!permutation_iff_surjective.
  intros HsurjSn Hx Hfx.
  apply fswap_at_boundary_surjective; easy.
Qed.

(** Well-foundedness of permutations; f k = k for k not in [n]_0 *)
Definition WF_Perm (n : nat) (f : nat -> nat) := 
  forall k, n <= k -> f k = k.

Lemma monotonic_WF_Perm n m f : WF_Perm n f -> n <= m ->
  WF_Perm m f.
Proof.
  intros HWF Hnm k Hk.
  apply HWF; lia.
Qed.

(* #[export] Hint Resolve monotonic_WF_perm : WF_perm_db. *)

Lemma compose_WF_Perm n f g : WF_Perm n f -> WF_Perm n g -> 
  WF_Perm n (f ∘ g)%prg.
Proof.
  unfold compose.
  intros Hf Hg k Hk.
  rewrite Hg, Hf; easy.
Qed.

(* #[export] Hint Resolve compose_WF_perm : WF_perm_db. *)

Lemma linv_WF_of_WF {n} {f finv}
    (HfWF : WF_Perm n f) (Hinv : (finv ∘ f = idn)%prg) :
    WF_Perm n finv.
Proof.
  intros k Hk.
  rewrite <- (HfWF k Hk).
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv.
  rewrite Hinv, (HfWF k Hk).
  easy.
Qed.

Lemma bdd_of_WF_linv {n} {f finv}  
  (HWF: WF_Perm n f) (Hinv : (finv ∘ f = idn)%prg) : 
  perm_bdd n f.
Proof.
  intros k Hk.
  pose proof (linv_WF_of_WF HWF Hinv) as HWFinv.
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv. 
  bdestruct (f k <? n); [easy|].
  specialize (HWFinv (f k) H).
  lia.
Qed.

Lemma rinv_bdd_of_WF {n} {f finv} (Hinv : (f ∘ finv = idn)%prg)
  (HWF : WF_Perm n f) :
  perm_bdd n finv.
Proof.
  intros k Hk.
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv.
  bdestruct (finv k <? n).
  - easy.
  - specialize (HWF _ H).
    lia.
Qed.

Lemma WF_permutation_inverse_injective (f : nat->nat) (n:nat) {finv finv'}
  (Hf: permutation n f) (HfWF : WF_Perm n f)
  (Hfinv : (finv ∘ f = idn)%prg) (Hfinv' : (finv' ∘ f = idn)%prg) :
  finv = finv'.
Proof.
    apply functional_extensionality; intros k.
    pose proof (linv_WF_of_WF HfWF Hfinv) as HfinvWF.
    pose proof (linv_WF_of_WF HfWF Hfinv') as Hfinv'WF.
    bdestruct (n <=? k).
    - rewrite HfinvWF, Hfinv'WF; easy.
    - destruct Hf as [fi Hfi].
      specialize (Hfi k H).
    unfold compose in Hfinv, Hfinv'.
      apply (f_equal_inv (fi k)) in Hfinv, Hfinv'. 
      replace (f (fi k)) with k in * by easy.
      rewrite Hfinv, Hfinv'.
      easy.
Qed.

Lemma permutation_monotonic_of_WF f m n : (m <= n)%nat -> 
  permutation m f -> WF_Perm m f -> 
  permutation n f.
Proof.
  intros Hmn [finv_m Hfinv_m] HWF.
  exists (fun k => if m <=? k then k else finv_m k).
  intros k Hk.
  bdestruct (m <=? k).
  - rewrite HWF; bdestruct_all; auto.
  - specialize (Hfinv_m _ H).
    repeat split; bdestruct_all; try easy; lia.
Qed.


Local Notation perm_eq n f g := (forall k, k < n -> f k = g k).

Lemma eq_of_WF_perm_eq n f g : WF_Perm n f -> WF_Perm n g ->
  perm_eq n f g -> f = g.
Proof.
  intros HfWF HgWF Heq.
  apply functional_extensionality; intros k.
  bdestruct (k <? n).
  - apply Heq, H.
  - rewrite HfWF, HgWF; easy.
Qed.

Lemma permutation_linv_iff_rinv_of_bounded n f finv :
  permutation n f -> perm_bdd n finv -> 
  perm_eq n (f ∘ finv)%prg idn <-> perm_eq n (finv ∘ f)%prg idn.
Proof.
  intros Hperm Hbdd.
  split; unfold compose.
  - intros Hrinv.
    intros k Hk.
    apply (permutation_is_injective n f Hperm); try easy.
    + apply Hbdd, permutation_is_bounded, Hk.
      apply Hperm.
    + rewrite Hrinv; [easy|].
      apply (permutation_is_bounded n f Hperm _ Hk).
  - intros Hlinv k Hk.
    destruct Hperm as [fi Hf].
    destruct (Hf k Hk) as [Hfk [Hfik [Hfifk Hffik]]].
    rewrite <- Hffik.
    rewrite Hlinv; easy.
Qed.

Local Notation is_perm_rinv n f finv := (perm_eq n (f ∘ finv)%prg idn).
Local Notation is_perm_linv n f finv := (perm_eq n (finv ∘ f)%prg idn).
Local Notation is_perm_inv n f finv := 
  (perm_eq n (f ∘ finv)%prg idn /\ perm_eq n (finv ∘ f)%prg idn).

Lemma perm_linv_injective_of_surjective n f finv finv' : 
  perm_surj n f -> is_perm_linv n f finv -> is_perm_linv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hsurj Hfinv Hfinv' k Hk.
  destruct (Hsurj k Hk) as [k' [Hk' Hfk']].
  rewrite <- Hfk'.
  unfold compose in *.
  rewrite Hfinv, Hfinv'; easy.
Qed.

Lemma perm_bounded_rinv_injective_of_injective n f finv finv' : 
  perm_inj n f -> perm_bdd n finv -> perm_bdd n finv' ->
  is_perm_rinv n f finv -> is_perm_rinv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hinj Hbdd Hbdd' Hfinv Hfinv' k Hk.
  apply Hinj; auto.
  unfold compose in *.
  rewrite Hfinv, Hfinv'; easy.
Qed.

Lemma permutation_inverse_injective n f finv finv' : permutation n f ->
  is_perm_inv n f finv -> is_perm_inv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hperm Hfinv Hfinv'.
  eapply perm_linv_injective_of_surjective.
  + apply permutation_is_surjective, Hperm.
  + destruct (Hfinv); auto.
  + destruct (Hfinv'); auto.
Qed.

Fixpoint for_all_nat_lt (f : nat -> bool) (k : nat) := 
  match k with
  | 0 => true
  | S k' => f k' && for_all_nat_lt f k'
  end.

Lemma forall_nat_lt_S (P : forall k : nat, Prop) (n : nat) : 
  (forall k, k < S n -> P k) <-> P n /\ (forall k, k < n -> P k).
Proof.
  split.
  - intros Hall.
    split; intros; apply Hall; lia.
  - intros [Hn Hall].
    intros k Hk.
    bdestruct (k=?n); [subst; easy | apply Hall; lia].
Qed.

Lemma for_all_nat_ltE {f : nat -> bool} {P : forall k : nat, Prop} 
  (ref : forall k, reflect (P k) (f k)) : 
  forall n, (forall k, k < n -> P k) <-> (for_all_nat_lt f n = true).
Proof.
  induction n.
  - easy.
  - rewrite forall_nat_lt_S.
    simpl.
    rewrite andb_true_iff.
    rewrite IHn.
    apply and_iff_compat_r.
    apply reflect_iff; easy.
Qed.

Definition perm_inv_is_inv_pred (f : nat -> nat) (n : nat) : Prop :=
  forall k, k < n ->
    f k < n /\ perm_inv n f k < n /\ 
    perm_inv n f (f k) = k /\ f (perm_inv n f k) = k.

Definition is_permutation (f : nat -> nat) (n : nat) :=
  for_all_nat_lt 
    (fun k => 
      (f k <? n) && (perm_inv n f k <? n)
      && (perm_inv n f (f k) =? k)
      && (f (perm_inv n f k) =? k)) n.

Lemma permutation_iff_perm_inv_is_inv (f : nat -> nat) (n : nat) : 
  permutation n f <-> perm_inv_is_inv_pred f n.
Proof.
  split.
  - intros Hperm.
    intros k Hk.
    repeat split.
    + destruct Hperm as [g Hg];
      apply (Hg k Hk).
    + apply perm_inv_bounded; easy.
    + apply perm_inv_is_linv_of_permutation; easy.
    + apply perm_inv_is_rinv_of_permutation; easy.
  - intros Hperminv.
    exists (perm_inv n f); easy.
Qed.

Lemma is_permutation_E (f : nat -> nat) (n : nat) : 
  perm_inv_is_inv_pred f n <-> is_permutation f n = true.
Proof.
  unfold perm_inv_is_inv_pred, is_permutation.
  apply for_all_nat_ltE.
  intros k.
  apply iff_reflect.
  rewrite 3!andb_true_iff.
  rewrite 2!Nat.ltb_lt, 2!Nat.eqb_eq, 2!and_assoc.
  easy.
Qed.

Lemma permutation_iff_is_permutation (f : nat -> nat) (n : nat) : 
  permutation n f <-> is_permutation f n = true.
Proof.
  rewrite permutation_iff_perm_inv_is_inv.
  apply is_permutation_E.
Qed.

Lemma permutationP (f : nat -> nat) (n : nat) :
  reflect (permutation n f) (is_permutation f n).
Proof.
  apply iff_reflect, permutation_iff_is_permutation.
Qed.

Definition permutation_dec (f : nat -> nat) (n : nat) :
  {permutation n f} + {~ permutation n f} :=
  reflect_dec _ _ (permutationP f n).


(** vsum terms can be arbitrarily reordered *)
Lemma vsum_reorder : forall {d} n (v : nat -> Vector d) f,
  permutation n f ->
  big_sum v n = big_sum (fun i => v (f i)) n.
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f [g Hg].
  destruct (Hg n) as [_ [H1 [_ H2]]]; try lia.
  rewrite (vsum_eq_up_to_fswap _ f _ (g n) n) by auto.
  repeat rewrite <- big_sum_extend_r.
  rewrite fswap_simpl2.
  rewrite H2.
  specialize (IHn (fswap f (g n) n)).
  rewrite <- IHn.
  reflexivity.
  apply fswap_at_boundary_permutation; auto.
  exists g. auto.
Qed.

(** showing every permutation is a sequence of fswaps *)

(* note the list acts on the left, for example, [s1,s2,...,sk] ⋅ f = s1 ⋅ ( ... ⋅ (sk ⋅ f)) *)
Fixpoint stack_fswaps (f : nat -> nat) (l : list (nat * nat)) :=
  match l with 
  | [] => f
  | p :: ps => (fswap (Datatypes.id) (fst p) (snd p) ∘ (stack_fswaps f ps))%prg 
  end.

Definition WF_fswap_stack n (l : list (nat * nat)) :=
  forall p, In p l -> (fst p < n /\ snd p < n). 

Lemma WF_fswap_stack_pop : forall n a l, 
  WF_fswap_stack n (a :: l) -> WF_fswap_stack n l.
Proof. intros.
       unfold WF_fswap_stack in *.
       intros.
       apply H.
       right; easy.
Qed.

Lemma WF_fswap_stack_cons : forall n a l, 
  fst a < n -> snd a < n -> WF_fswap_stack n l -> WF_fswap_stack n (a :: l).
Proof. intros.
       unfold WF_fswap_stack in *.
       intros.
       destruct H2; subst; auto.
Qed.

Lemma WF_fswap_miss : forall n l i,
  WF_fswap_stack n l ->
  n <= i -> 
  (stack_fswaps Datatypes.id l) i = i.
Proof. induction l. 
       intros; simpl; easy.
       intros; simpl.
       unfold compose.
       rewrite IHl; auto.
       unfold fswap, Datatypes.id; simpl.
       destruct (H a).
       left; auto.
       bdestruct_all; try lia.
       apply WF_fswap_stack_pop in H; auto.
Qed.

Lemma stack_fswaps_permutation : forall {n} (f : nat -> nat) (l : list (nat * nat)),
  WF_fswap_stack n l -> 
  permutation n f -> 
  permutation n (stack_fswaps f l).
Proof. induction l.
       - intros. easy.
       - intros. 
         simpl.
         apply permutation_compose.
         apply fswap_permutation.
         apply id_permutation.
         3 : apply IHl; auto.
         3 : apply WF_fswap_stack_pop in H; auto.
         all : apply H; left; easy.
Qed.

Lemma stack_fswaps_cons : forall (p : nat * nat) (l : list (nat * nat)),
  ((stack_fswaps Datatypes.id [p]) ∘ (stack_fswaps Datatypes.id l))%prg = 
  stack_fswaps Datatypes.id (p :: l).
Proof. intros. 
       simpl.
       rewrite compose_id_right.
       easy.
Qed.
 
(*
Theorem all_perms_are_fswap_stacks : forall {n} f,
  permutation n f -> 
  exists l, WF_fswap_stack n l /\ f = (stack_fswaps Datatypes.id l) /\ length l = n.
Proof. induction n. 
       - intros. 
         exists []; simpl.
*)     

Definition ordered_real_function n (f : nat -> R) :=
  forall i j, i < n -> j < n -> i <= j -> (f j <= f i)%R.

Lemma get_real_function_min : forall {n} (f : nat -> R),
  exists n0, (n0 < (S n))%nat /\ (forall i, (i < (S n))%nat -> (f n0 <= f i)%R).
Proof. induction n.
       - intros.
         exists O; intros.
         split; auto.
         intros. 
         destruct i; try lia.
         lra.
       - intros.  
         destruct (IHn f) as [n0 [H H0] ]. 
         destruct (Rlt_le_dec (f n0) (f (S n))). 
         + exists n0; intros. 
           split; try lia. 
           intros.
           bdestruct (i =? (S n))%nat; subst.
           lra.
           apply H0.
           bdestruct (n0 <? S n)%nat; bdestruct (i <? S n)%nat; try lia.
         + exists (S n).
           split.
           lia.
           intros.
           specialize (H0 i).
           unfold get_minor in H0.
           bdestruct (n0 <? S n)%nat; bdestruct (i <? S n)%nat; try lia.
           apply H0 in H3.
           lra.
           bdestruct (i =? S n)%nat; try lia; subst.
           lra.
Qed.

Lemma order_real_function : forall n (f : nat -> R), 
  exists l, WF_fswap_stack n l /\ 
         ordered_real_function n (f ∘ (stack_fswaps Datatypes.id l))%prg.
Proof. intros.
       generalize dependent f.
       induction n.
       - intros; exists [].
         split; auto.
         unfold WF_fswap_stack; intros.
         destruct H.
         simpl.
         unfold ordered_real_function; intros; lia.
       - intros. 
         destruct (@get_real_function_min n f) as [n0 [H H0]].
         destruct (IHn (f ∘ (stack_fswaps Datatypes.id [(n0, n)]))%prg) as [l [H1 H2]].
         exists ((n0, n) :: l).
         split. 
         apply WF_fswap_stack_cons; simpl; auto. 
         unfold WF_fswap_stack in *; intros. 
         apply H1 in H3.
         lia.
         rewrite compose_assoc, stack_fswaps_cons in H2.
         unfold ordered_real_function in *.
         intros.  
         bdestruct (j =? n); subst.
         simpl.
         rewrite <- compose_assoc.
         assert (H' : permutation (S n) 
                                  (fswap Datatypes.id n0 n ∘ stack_fswaps Datatypes.id l)%prg).
         { apply permutation_compose.
           apply fswap_permutation; auto.
           apply id_permutation.
           apply stack_fswaps_permutation.
           unfold WF_fswap_stack in *; intros. 
           apply H1 in H6.
           lia.
           apply id_permutation. }
         unfold compose in *.
         destruct H' as [g H6].  
         destruct (H6 i); auto.
         rewrite (WF_fswap_miss n); auto.
         replace (fswap Datatypes.id n0 n n) with n0.
         apply H0; easy. 
         unfold fswap, Datatypes.id.
         bdestruct_all; simpl; easy.
         bdestruct (j <? n); bdestruct (i <? n); try lia.
         apply H2; auto. 
Qed.

(** * Permutation matrices *)

Definition perm_mat n (p : nat -> nat) : Square n :=
  (fun x y => if (x =? p y) && (x <? n) && (y <? n) then C1 else C0).

Lemma perm_mat_WF : forall n p, WF_Matrix (perm_mat n p).
Proof.
  intros n p.
  unfold WF_Matrix, perm_mat. 
  intros x y [H | H].
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
  bdestruct (x =? p y); bdestruct (x <? n); bdestruct (y <? n); trivial; lia.
Qed. 
#[export] Hint Resolve perm_mat_WF : wf_db.

Lemma perm_mat_id : forall n,
  perm_mat n (Datatypes.id) = (I n).
Proof. intros. 
       unfold Datatypes.id, I, perm_mat.
       prep_matrix_equality.
       bdestruct_all; easy.
Qed.

Lemma perm_mat_unitary : forall n p, 
  permutation n p -> WF_Unitary (perm_mat n p).
Proof.
  intros n p [pinv Hp].
  split.
  apply perm_mat_WF.
  unfold Mmult, adjoint, perm_mat, I.
  prep_matrix_equality.
  destruct ((x =? y) && (x <? n)) eqn:H.
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  subst.
  apply big_sum_unique.
  exists (p y).
  destruct (Hp y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros.  
  bdestruct_all; simpl; lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite andb_true_r in H.
  apply Nat.eqb_neq in H.
  assert (pinv (p x) = pinv (p y)) by auto.
  destruct (Hp x) as [_ [_ [H5 _]]]; auto.
  destruct (Hp y) as [_ [_ [H6 _]]]; auto.
  contradict H.
  rewrite <- H5, <- H6.
  assumption.
Qed.

Lemma perm_mat_Mmult : forall n f g,
  permutation n g ->
  perm_mat n f × perm_mat n g = perm_mat n (f ∘ g)%prg.
Proof.
  intros n f g [ginv Hgbij].
  unfold perm_mat, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? f (g y)) && (x <? n) && (y <? n)) eqn:H.
  apply andb_prop in H as [H H3].
  apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1.
  apply Nat.ltb_lt in H2.
  apply Nat.ltb_lt in H3.
  subst.
  apply big_sum_unique.
  exists (g y).
  destruct (Hgbij y) as [? _]; auto.
  split; auto.
  split.
  bdestruct_all; simpl; lca.
  intros.
  bdestruct_all; simpl; lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  subst.
  rewrite 2 andb_true_r in H.
  apply Nat.eqb_neq in H.
  contradiction.
Qed.

Lemma perm_mat_I : forall n f,
  (forall x, x < n -> f x = x) ->
  perm_mat n f = I n.
Proof.
  intros n f Hinv.
  unfold perm_mat, I.
  prep_matrix_equality.
  bdestruct_all; simpl; try lca.
  rewrite Hinv in H1 by assumption.
  contradiction.
  rewrite Hinv in H1 by assumption.
  contradiction.
Qed.

Lemma perm_mat_col_swap_I : forall n f i j,
  (forall x, x < n -> f x = x) ->
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = col_swap (I n) i j.
Proof. intros. 
       unfold perm_mat, fswap, col_swap, I.
       prep_matrix_equality.
       rewrite 2 H; auto.
       bdestruct_all; simpl; try lia; auto.
       rewrite H in H4; auto; lia.
       rewrite H in H4; auto; lia.
Qed.

Lemma perm_mat_col_swap : forall n f i j,
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = col_swap (perm_mat n f) i j.
Proof. intros. 
       unfold perm_mat, fswap, col_swap, I.
       prep_matrix_equality.
       bdestruct_all; simpl; try lia; auto.
Qed. 

Lemma perm_mat_row_swap : forall n f i j,
  i < n -> j < n -> 
  perm_mat n (fswap f i j) = (row_swap (perm_mat n f)† i j)†.
Proof. intros. 
       unfold perm_mat, fswap, row_swap, I, adjoint.
       prep_matrix_equality.
       bdestruct_all; simpl; try lia; auto; lca.
Qed. 

Lemma perm_mat_e_i : forall n f i, 
  i < n ->
  permutation n f ->
  (perm_mat n f) × e_i i = e_i (f i).
Proof. intros. 
       apply mat_equiv_eq; auto with wf_db.
       unfold mat_equiv; intros.
       destruct j; try lia.
       unfold Mmult.
       apply big_sum_unique.
       exists i.
       split; auto.
       split. 
       unfold e_i, perm_mat. 
       bdestruct_all; simpl; lca.
       intros. 
       unfold e_i.
       bdestruct_all; simpl; lca.
Qed.

(* with get_entry_with_e_i this became soo much easier *)
Lemma perm_mat_conjugate : forall {n} (A : Square n) f (i j : nat), 
  WF_Matrix A -> 
  i < n -> j < n ->
  permutation n f ->
  ((perm_mat n f)† × A × ((perm_mat n f))) i j = A (f i) (f j). 
Proof. intros. 
       rewrite get_entry_with_e_i, (get_entry_with_e_i A); auto.
       rewrite <- 2 Mmult_assoc, <- Mmult_adjoint.
       rewrite perm_mat_e_i; auto.
       rewrite 3 Mmult_assoc.
       rewrite perm_mat_e_i; auto.
       all : destruct H2; apply H2; auto.
Qed.       

Lemma perm_mat_conjugate_nonsquare : forall {m n} (A : Matrix m n) f (i j : nat), 
  WF_Matrix A -> 
  i < m -> j < n ->
  permutation m f -> permutation n f ->
  ((perm_mat m f)† × A × ((perm_mat n f))) i j = A (f i) (f j). 
Proof. intros. 
       rewrite get_entry_with_e_i, (get_entry_with_e_i A); auto.
       rewrite <- 2 Mmult_assoc, <- Mmult_adjoint.
       rewrite perm_mat_e_i; auto.
       rewrite 3 Mmult_assoc.
       rewrite perm_mat_e_i; auto.
       all : destruct H2; destruct H3; try apply H2; try apply H3; auto.
Qed.      

(** Given a permutation p over n qubits, construct a permutation over 2^n indices. *)
Definition qubit_perm_to_nat_perm n (p : nat -> nat) :=
  fun x:nat => funbool_to_nat n ((nat_to_funbool n x) ∘ p)%prg.

Lemma qubit_perm_to_nat_perm_bij : forall n p,
  permutation n p -> permutation (2^n) (qubit_perm_to_nat_perm n p).
Proof.
  intros n p [pinv Hp].
  unfold qubit_perm_to_nat_perm.
  exists (fun x => funbool_to_nat n ((nat_to_funbool n x) ∘ pinv)%prg).
  intros x Hx.
  repeat split.
  apply funbool_to_nat_bound.
  apply funbool_to_nat_bound.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [_ H]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [_ [? _]]; auto. }
  rewrite nat_to_funbool_inverse; auto.
  unfold compose.
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. 
       rewrite funbool_to_nat_inverse. 
       destruct (Hp y) as [_ [_ [H _]]].
       assumption.
       rewrite H.
       reflexivity.
       destruct (Hp y) as [? _]; auto. }
  rewrite nat_to_funbool_inverse; auto.
Qed.  

(** Transform a (0,...,n-1) permutation into a 2^n by 2^n matrix. *)
Definition perm_to_matrix n p :=
  perm_mat (2 ^ n) (qubit_perm_to_nat_perm n p).
 
Lemma perm_to_matrix_permutes_qubits : forall n p f, 
  permutation n p ->
  perm_to_matrix n p × f_to_vec n f = f_to_vec n (fun x => f (p x)).
Proof.
  intros n p f [pinv Hp].
  rewrite 2 basis_f_to_vec.
  unfold perm_to_matrix, perm_mat, qubit_perm_to_nat_perm.
  unfold basis_vector, Mmult, compose.
  prep_matrix_equality.
  destruct ((x =? funbool_to_nat n (fun x0 : nat => f (p x0))) && (y =? 0)) eqn:H.
  apply andb_prop in H as [H1 H2].
  rewrite Nat.eqb_eq in H1.
  rewrite Nat.eqb_eq in H2.
  apply big_sum_unique.
  exists (funbool_to_nat n f).
  split.
  apply funbool_to_nat_bound.
  split.
  erewrite funbool_to_nat_eq.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  specialize (funbool_to_nat_bound n f) as ?.
  specialize (funbool_to_nat_bound n (fun x0 : nat => f (p x0))) as ?.
  bdestruct_all; lca.
  intros z Hz H3.
  bdestructΩ (z =? funbool_to_nat n f).
  lca.
  apply (@big_sum_0 C C_is_monoid).
  intros z.
  bdestruct_all; simpl; try lca.
  rewrite andb_true_r in H.
  apply Nat.eqb_neq in H.
  subst z.
  erewrite funbool_to_nat_eq in H2.
  2: { intros. rewrite funbool_to_nat_inverse. reflexivity.
  destruct (Hp x0) as [? _]; auto. }
  contradiction.
Qed.

Lemma perm_to_matrix_unitary : forall n p, 
  permutation n p ->
  WF_Unitary (perm_to_matrix n p).
Proof.
  intros.
  apply perm_mat_unitary.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma qubit_perm_to_nat_perm_compose : forall n f g,
  permutation n f ->
  (qubit_perm_to_nat_perm n f ∘ qubit_perm_to_nat_perm n g = 
    qubit_perm_to_nat_perm n (g ∘ f))%prg.
Proof.
  intros n f g [finv Hbij].
  unfold qubit_perm_to_nat_perm, compose.
  apply functional_extensionality.
  intro x.
  apply funbool_to_nat_eq.
  intros y Hy.
  rewrite funbool_to_nat_inverse.
  reflexivity.
  destruct (Hbij y) as [? _]; auto.
Qed.

Lemma perm_to_matrix_Mmult : forall n f g,
  permutation n f ->
  permutation n g ->
  perm_to_matrix n f × perm_to_matrix n g = perm_to_matrix n (g ∘ f)%prg.
Proof.
  intros. 
  unfold perm_to_matrix.
  rewrite perm_mat_Mmult.
  rewrite qubit_perm_to_nat_perm_compose by assumption.
  reflexivity.
  apply qubit_perm_to_nat_perm_bij.
  assumption.
Qed.

Lemma perm_to_matrix_I : forall n f,
  permutation n f ->
  (forall x, x < n -> f x = x) ->
  perm_to_matrix n f = I (2 ^ n).
Proof.
  intros n f g Hbij. 
  unfold perm_to_matrix.
  apply perm_mat_I.
  intros x Hx.
  unfold qubit_perm_to_nat_perm, compose. 
  erewrite funbool_to_nat_eq.
  2: { intros y Hy. rewrite Hbij by assumption. reflexivity. }
  apply nat_to_funbool_inverse.
  assumption.
Qed.

Lemma perm_to_matrix_WF : forall n p, WF_Matrix (perm_to_matrix n p).
Proof. intros. apply perm_mat_WF. Qed. 
#[export] Hint Resolve perm_to_matrix_WF : wf_db.

(* Stack and swap perms definitions *)

Definition stack_perms (n0 n1 : nat) (f g : nat -> nat) : nat -> nat :=
  fun n => 
  if (n <? n0) then f n else 
  if (n <? n0 + n1) then (g (n - n0) + n0)%nat else n.

Definition swap_2_perm : nat -> nat :=
  fun n => if 2 <=? n then n else match n with
    | 0 => 1%nat
    | 1 => 0%nat
    | other => other
  end.

Definition swap_perm a b n := 
  fun k => if n <=? k then k else 
  if k =? a then b else
  if k =? b then a else k.

Definition rotr n m : nat -> nat :=
	fun k => if n <=? k then k else (k + m) mod n.

Definition rotl n m : nat -> nat :=
	fun k => if n <=? k then k else (k + (n - (m mod n))) mod n.

Ltac bdestruct_one :=
  let fail_if_iffy H :=
    match H with
    | context[if _ then _ else _] => fail 1
    | _ => idtac
    end
  in
  match goal with
  | |- context [ ?a <? ?b ] => fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] => fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ ?a =? ?b ] => fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b)
  | |- context[if ?b then _ else _]
      => fail_if_iffy b; destruct b eqn:?
  end.

Ltac bdestructΩ' :=
  let tryeasylia := try easy; try lia in 
  repeat (bdestruct_one; subst; tryeasylia);
  tryeasylia.

Tactic Notation "cleanup_perm_inv" := 
  autorewrite with perm_inv_db.

Tactic Notation "cleanup_perm" :=
  autorewrite with perm_inv_db perm_cleanup_db.

Tactic Notation "cleanup_perm_of_zx" :=
  autounfold with zxperm_db;
  autorewrite with perm_of_zx_cleanup_db perm_inv_db perm_cleanup_db.

Lemma compose_id_of_compose_idn {f g : nat -> nat} 
  (H : (f ∘ g)%prg = (fun n => n)) {k : nat} : f (g k) = k.
Proof.
  apply (f_equal_inv k) in H.
  easy.
Qed.

Ltac perm_by_inverse finv :=
  let tryeasylia := try easy; try lia in 
  exists finv;
  intros k Hk; repeat split;
  only 3,4 : (try apply compose_id_of_compose_idn; cleanup_perm; tryeasylia) 
            || cleanup_perm; tryeasylia;
  only 1,2 : auto with perm_bdd_db; tryeasylia.

(* Section on swap_perm, swaps two elements *)

Lemma swap_perm_same a n :
  swap_perm a a n = idn.
Proof.
  unfold swap_perm.
  apply functional_extensionality; intros k.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_perm_same : perm_cleanup_db.

Lemma swap_perm_comm a b n :
  swap_perm a b n = swap_perm b a n.
Proof.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  bdestructΩ'.
Qed.

Lemma swap_WF_perm a b n : forall k, n <= k -> swap_perm a b n k = k.
Proof.
  intros.
  unfold swap_perm. 
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_WF_perm : WF_perm_db.

Lemma swap_perm_bdd a b n : a < n -> b < n ->
  forall k, k < n -> swap_perm a b n k < n.
Proof.
  intros Ha Hb k Hk.
  unfold swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Resolve swap_perm_bdd : perm_bdd_db.

Lemma swap_perm_inv a b n : a < n -> b < n -> 
  ((swap_perm a b n) ∘ (swap_perm a b n))%prg = idn.
Proof.
  intros Ha Hb.
  unfold compose.
  apply functional_extensionality; intros k.
  unfold swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite swap_perm_inv : perm_inv_db.

Lemma swap_perm_2_perm a b n : a < n -> b < n ->
  permutation n (swap_perm a b n).
Proof.
  intros Ha Hb.
  perm_by_inverse (swap_perm a b n).
Qed.

#[export] Hint Resolve swap_perm_2_perm : perm_db.

Lemma swap_perm_S_permutation a n (Ha : S a < n) :
  permutation n (swap_perm a (S a) n).
Proof.
  apply swap_perm_2_perm; lia.
Qed.

#[export] Hint Resolve swap_perm_S_permutation : perm_db.

Lemma compose_swap_perm a b c n : a < n -> b < n -> c < n -> 
  b <> c -> a <> c ->
  (swap_perm a b n ∘ swap_perm b c n ∘ swap_perm a b n)%prg = swap_perm a c n.
Proof.
  intros Ha Hb Hc Hbc Hac. 
  apply functional_extensionality; intros k.
  unfold compose, swap_perm.
  bdestructΩ'.
Qed.

#[export] Hint Rewrite compose_swap_perm : perm_cleanup_db.

(* Section for swap_2_perm *)
Lemma swap_2_perm_inv : 
  (swap_2_perm ∘ swap_2_perm)%prg = idn.
Proof.
  apply functional_extensionality; intros k.
  repeat first [easy | destruct k].
Qed.

#[export] Hint Rewrite swap_2_perm_inv : perm_inv_db.

Lemma swap_2_perm_bdd k :
  k < 2 -> swap_2_perm k < 2.
Proof.
  intros Hk.
  repeat first [easy | destruct k | cbn; lia].
Qed.

#[export] Hint Resolve swap_2_perm_bdd : perm_bdd_db.

Lemma swap_2_WF_perm k : 1 < k -> swap_2_perm k = k.
Proof.
  intros. 
  repeat first [easy | lia | destruct k].
Qed.

Global Hint Resolve swap_2_WF_perm : WF_perm_db.

Lemma swap_2_perm_permutation : permutation 2 swap_2_perm.
Proof. 
  perm_by_inverse swap_2_perm.
Qed.

Global Hint Resolve swap_2_perm_permutation : perm_db.

(* Section for stack_perms *)
Lemma mod_add_n_r : forall m n, 
	(m + n) mod n = m mod n.
Proof.
	intros m n.
	replace (m + n)%nat with (m + 1 * n)%nat by lia.
	destruct n.
	- cbn; easy.
	- rewrite Nat.mod_add;
		lia.
Qed.

Lemma mod_eq_sub : forall m n,
	m mod n = (m - n * (m / n))%nat.
Proof.
	intros m n.
	destruct n.
	- cbn; lia.
	- assert (H: (S n <> 0)%nat) by easy.
		pose proof (Nat.div_mod m (S n) H) as Heq.
		lia.
Qed.

Lemma mod_of_scale : forall m n q, 
	(n * q <= m < n * S q)%nat -> m mod n = (m - q * n)%nat.
Proof.
	intros m n q [Hmq HmSq].
	rewrite mod_eq_sub.
	replace (m/n)%nat with q; [lia|].
	apply Nat.le_antisymm.
	- apply Nat.div_le_lower_bound; lia. 
	- epose proof (Nat.div_lt_upper_bound m n (S q) _ _).
		lia.
		Unshelve.
		all: lia.
Qed.

Lemma mod_n_to_2n : forall m n, 
	(n <= m < 2 * n)%nat -> m mod n = (m - n)%nat.
Proof.
	intros.
	epose proof (mod_of_scale m n 1 _).
	lia.
	Unshelve.
	lia.
Qed.

Lemma mod_n_to_n_plus_n : forall m n, 
	(n <= m < n + n)%nat -> m mod n = (m - n)%nat.
Proof.
	intros.
	apply mod_n_to_2n; lia.
Qed.

Ltac simplify_mods_of a b :=
	first [
		rewrite (Nat.mod_small a b) in * by lia
	| rewrite (mod_n_to_2n a b) in * by lia
	].

Ltac solve_simple_mod_eqns :=
  let __fail_if_has_mods a :=
    match a with
    | context[_ mod _] => fail 1
    | _ => idtac
    end
  in
	match goal with
	| |- context[if _ then _ else _] => fail 1 "Cannot solve equation with if"
	| _ =>
		repeat first [
      easy
	  |	lia
		|	match goal with 
			| |- context[?a mod ?b] => __fail_if_has_mods a; __fail_if_has_mods b; 
					simplify_mods_of a b
			| H: context[?a mod ?b] |- _ => __fail_if_has_mods a; __fail_if_has_mods b; 
					simplify_mods_of a b
			end 
		| match goal with
			| |- context[?a mod ?b] => (* idtac a b; *) bdestruct (a <? b);
					[rewrite (Nat.mod_small a b) by lia 
					| try rewrite (mod_n_to_2n a b) by lia]
			end
		]
	end.

Ltac solve_modular_permutation_equalities :=
  first [cleanup_perm_of_zx | cleanup_perm_inv | cleanup_perm];
  unfold Basics.compose, rotr, rotl, stack_perms, swap_perm,
  (* TODO: remove *) swap_2_perm;
  apply functional_extensionality; let k := fresh "k" in intros k;
  bdestructΩ';
  solve_simple_mod_eqns.

Lemma stack_perms_WF_idn {n0 n1} {f} 
	(H : forall k, n0 <= k -> f k = k): 
	stack_perms n0 n1 f idn = f.
Proof.
	solve_modular_permutation_equalities;
	rewrite H; lia.
Qed.

Lemma stack_perms_WF {n0 n1} {f g} k :
  n0 + n1 <= k -> stack_perms n0 n1 f g k = k.
Proof.
  intros H.
  unfold stack_perms.
  bdestructΩ'.
Qed.

Global Hint Resolve stack_perms_WF : WF_perm_db.

Lemma stack_perms_bdd {n0 n1} {f g}
  (Hf : forall k, k < n0 -> f k < n0) (Hg : forall k, k < n1 -> g k < n1) :
  forall k, k < n0 + n1 -> stack_perms n0 n1 f g k < n0 + n1.
Proof.
  intros k Hk.
  unfold stack_perms.
  bdestruct (k <? n0).
  - specialize (Hf k H). lia.
  - bdestruct (k <? n0 + n1); [|easy].
    assert (Hkn0 : k - n0 < n1) by lia.
    specialize (Hg _ Hkn0). lia.
Qed. 

Global Hint Resolve stack_perms_bdd : perm_bdd_db.

Lemma stack_perms_rinv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  (stack_perms n0 n1 f g ∘ stack_perms n0 n1 finv ginv)%prg = idn.
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

#[export] Hint Rewrite is_inv_iff_inv_is : perm_inv_db.

Lemma stack_perms_linv {n0 n1} {f g} {finv ginv}
  (Hf: forall k, k < n0 -> (f k < n0 /\ finv k < n0 /\ finv (f k) = k /\ f (finv k) = k))
  (Hg: forall k, k < n1 -> (g k < n1 /\ ginv k < n1 /\ ginv (g k) = k /\ g (ginv k) = k)) : 
  (stack_perms n0 n1 finv ginv ∘ stack_perms n0 n1 f g)%prg = idn.
Proof.
  rewrite stack_perms_rinv.
  2,3: rewrite is_inv_iff_inv_is.
  all: easy.
Qed.

#[export] Hint Rewrite @stack_perms_rinv @stack_perms_linv : perm_inv_db.

Lemma stack_perms_permutation {n0 n1 f g} (Hf : permutation n0 f) (Hg: permutation n1 g) :
  permutation (n0 + n1) (stack_perms n0 n1 f g).
Proof.
  destruct Hf as [f' Hf'].
  destruct Hg as [g' Hg'].
  perm_by_inverse (stack_perms n0 n1 f' g').
  1,2: apply stack_perms_bdd; try easy; intros k' Hk'; 
       try specialize (Hf' _ Hk'); try specialize (Hg' _ Hk'); easy.
  1,2: rewrite is_inv_iff_inv_is; easy.
Qed.

Global Hint Resolve stack_perms_permutation : perm_db.

(* Section on insertion_sort_list *)
Fixpoint insertion_sort_list n f := 
  match n with 
  | 0 => []
  | S n' => let k := (perm_inv (S n') f n') in
      k :: insertion_sort_list n' (fswap f k n')
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

Lemma fswap_eq_compose_swap_perm {A} (f : nat -> A) n m o : n < o -> m < o ->
  fswap f n m = (f ∘ swap_perm n m o)%prg.
Proof.
  intros Hn Hm.
  apply functional_extensionality; intros k.
  unfold compose, fswap, swap_perm.
  bdestruct_all; easy.
Qed.

Lemma fswap_perm_inv_n_permutation f n : permutation (S n) f ->
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
    rewrite swap_WF_perm; easy.
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
    rewrite swap_WF_perm; [|easy].
    rewrite IHl; [easy|easy|lia].
Qed.

#[export] Hint Resolve perm_of_swap_list_WF invperm_of_swap_list_WF : WF_perm_db.

Lemma perm_of_swap_list_bounded l : swap_list_spec l = true ->
  perm_bdd (length l) (perm_of_swap_list l).
Proof. 
  induction l; [easy|].
  simpl.
  rewrite andb_true_iff.
  intros [Ha Hl].
  intros k Hk.
  unfold compose.
  rewrite Nat.ltb_lt in Ha.
  apply swap_perm_bdd; try lia.
  bdestruct (k =? length l).
  - subst; rewrite perm_of_swap_list_WF; try easy; lia.
  - transitivity (length l); [|lia].
    apply IHl; [easy | lia].
Qed.

Lemma invperm_of_swap_list_bounded l : swap_list_spec l = true ->
  perm_bdd (length l) (invperm_of_swap_list l).
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
    pose proof (swap_perm_bdd a (length l) (S (length l)) Ha (ltac:(lia)) k Hk).
    lia.
Qed.

#[export] Hint Resolve perm_of_swap_list_bounded invperm_of_swap_list_bounded : perm_bdd_db.

Lemma invperm_linv_perm_of_swap_list l : swap_list_spec l = true ->
  (invperm_of_swap_list l ∘ perm_of_swap_list l)%prg = idn.
Proof.
  induction l.
  - easy.
  - simpl. 
    rewrite andb_true_iff.
    intros [Ha Hl].
    rewrite Combinators.compose_assoc, 
    <- (Combinators.compose_assoc _ _ _ _ (perm_of_swap_list _)).
    rewrite swap_perm_inv, compose_idn_l.
    + apply (IHl Hl).
    + bdestructΩ (a <? S (length l)).
    + lia.
Qed.

Lemma invperm_rinv_perm_of_swap_list l : swap_list_spec l = true ->
  (perm_of_swap_list l ∘ invperm_of_swap_list l)%prg = idn.
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
    rewrite swap_perm_inv; [easy| |lia].
    bdestructΩ (a <? S (length l)).
Qed.

#[export] Hint Rewrite invperm_linv_perm_of_swap_list 
  invperm_rinv_perm_of_swap_list : perm_cleanup_db.

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

Lemma perm_of_insertion_sort_list_is_rinv n f : permutation n f ->
  forall k, k < n ->
  (f ∘ perm_of_swap_list (insertion_sort_list n f))%prg k = k.
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
      all: rewrite perm_inv_is_rinv_of_permutation; [easy|easy|lia].
    + rewrite <- Combinators.compose_assoc.
      rewrite <- fswap_eq_compose_swap_perm; [|apply perm_inv_bounded_S|lia].
      rewrite IHn; [easy| |lia].
      apply fswap_perm_inv_n_permutation, Hperm.
Qed.
Local Transparent perm_inv. 

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

#[export] Hint Resolve perm_of_insertion_sort_list_WF invperm_of_swap_list_WF : WF_perm_db.

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
  - auto with perm_bdd_db.
  - apply perm_of_insertion_sort_list_is_rinv, Hperm.
  - apply perm_inv_is_rinv_of_permutation, Hperm.
Qed.

Lemma perm_of_insertion_sort_list_eq_make_WF_perm_inv n f : permutation n f ->
  (perm_of_swap_list (insertion_sort_list n f)) = fun k => if n <=?k then k else perm_inv n f k.
Proof.
  intros Hperm.
  apply functional_extensionality; intros k.
  bdestruct (n <=? k).
  - rewrite perm_of_insertion_sort_list_WF; easy.
  - rewrite perm_of_insertion_sort_list_perm_eq_perm_inv; easy.
Qed.

Lemma perm_eq_linv_injective n f finv finv' : permutation n f ->
  is_perm_linv n f finv -> is_perm_linv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hperm Hfinv Hfinv' k Hk.
  destruct (permutation_is_surjective n f Hperm k Hk) as [k' [Hk' Hfk']].
  unfold compose in *.
  specialize (Hfinv k' Hk').
  specialize (Hfinv' k' Hk').
  rewrite Hfk' in *.
  rewrite Hfinv, Hfinv'.
  easy.
Qed.

Lemma perm_inv_eq_inv n f finv : 
  (forall x : nat, x < n -> f x < n /\ finv x < n /\ finv (f x) = x /\ f (finv x) = x)
  -> perm_eq n (perm_inv n f) finv.
Proof.
  intros Hfinv.
  assert (Hperm: permutation n f) by (exists finv; easy).
  apply (perm_eq_linv_injective n f); [easy| | ]; 
    unfold compose; intros k Hk.
  - rewrite perm_inv_is_linv_of_permutation; easy.
  - apply Hfinv, Hk.
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
  intros Hperm k Hk.
  unfold compose.
  rewrite (perm_inv_eq_inv n (perm_inv n f) f); try easy.
  apply perm_inv_is_inv, Hperm.
Qed.

Lemma perm_inv_eq_of_perm_eq' n m f g : perm_eq n f g -> m <= n ->
  perm_eq n (perm_inv m f) (perm_inv m g).
Proof.
  intros Heq Hm.
  induction m; [trivial|].
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

Lemma perm_inv_of_insertion_sort_list_eq n f : permutation n f ->
  perm_eq n f (perm_inv n (perm_of_swap_list (insertion_sort_list n f))).
Proof.
  intros Hperm k Hk.
  rewrite (perm_of_insertion_sort_list_eq_make_WF_perm_inv n f) by easy.
  rewrite (perm_inv_eq_of_perm_eq n _ (perm_inv n f)); [
    | intros; bdestructΩ' | easy].
  rewrite perm_inv_perm_inv; easy.
Qed.

Lemma perm_of_insertion_sort_list_of_perm_inv_eq n f : permutation n f ->
  perm_eq n f (perm_of_swap_list (insertion_sort_list n (perm_inv n f))).
Proof.
  intros Hperm.
  rewrite perm_of_insertion_sort_list_eq_make_WF_perm_inv by (auto with perm_db).
  intros; bdestructΩ'.
  rewrite perm_inv_perm_inv; easy.
Qed.

Lemma insertion_sort_list_S n f : 
  insertion_sort_list (S n) f = 
  (perm_inv (S n) f n) :: (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)).
Proof. easy. Qed.

Lemma perm_of_swap_list_cons a l :
  perm_of_swap_list (a :: l) = (swap_perm a (length l) (S (length l)) ∘ perm_of_swap_list l)%prg.
Proof. easy. Qed.

Lemma invperm_of_swap_list_cons a l :
  invperm_of_swap_list (a :: l) = (invperm_of_swap_list l ∘ swap_perm a (length l) (S (length l)))%prg.
Proof. easy. Qed.

Lemma perm_of_insertion_sort_list_S n f : 
  perm_of_swap_list (insertion_sort_list (S n) f) =
  (swap_perm (perm_inv (S n) f n) n (S n) ∘ 
    perm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n)))%prg.
Proof. 
  rewrite insertion_sort_list_S, perm_of_swap_list_cons.
  rewrite length_insertion_sort_list.
  easy.
Qed.

Lemma invperm_of_insertion_sort_list_S n f : 
  invperm_of_swap_list (insertion_sort_list (S n) f) =
  (invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n))%prg.
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
  - apply swap_perm_2_perm; [|lia].
    simpl in Hsw.
    bdestruct (a <? S (length l)); easy.
  - eapply permutation_monotonic_of_WF.
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
  - eapply permutation_monotonic_of_WF.
    2: apply IHl.
    1: lia.
    2: apply invperm_of_swap_list_WF.
    all: simpl in Hsw;
    rewrite andb_true_iff in Hsw; easy.
  - apply swap_perm_2_perm; [|lia].
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

#[export] Hint Resolve perm_of_insertion_sort_list_permutation
    invperm_of_insertion_sort_list_permutation : perm_db.

Lemma invperm_of_insertion_sort_list_eq n f : permutation n f ->
  perm_eq n f (invperm_of_swap_list (insertion_sort_list n f)).
Proof.
  intros Hperm.
  apply (perm_eq_linv_injective n (perm_of_swap_list (insertion_sort_list n f))).
  - auto with perm_db.
  - intros k Hk.
    rewrite perm_of_insertion_sort_list_is_rinv; easy.
  - intros k Hk.
    rewrite invperm_linv_perm_of_swap_list; [easy|].
    apply insertion_sort_list_is_swap_list.
Qed.
  
Lemma permutation_grow_l' n f : permutation (S n) f -> 
  perm_eq (S n) f (swap_perm (f n) n (S n) ∘ 
  perm_of_swap_list (insertion_sort_list n (fswap (perm_inv (S n) f) (f n) n)))%prg.
Proof.
  intros Hperm k Hk.
  rewrite (perm_of_insertion_sort_list_of_perm_inv_eq _ _ Hperm) at 1 by auto.
Local Opaque perm_inv.
  simpl.
Local Transparent perm_inv.
  rewrite length_insertion_sort_list, perm_inv_perm_inv by auto.
  easy.
Qed.

Lemma permutation_grow_r' n f : permutation (S n) f -> 
  perm_eq (S n) f ( 
  invperm_of_swap_list (insertion_sort_list n (fswap f (perm_inv (S n) f n) n))
  ∘ swap_perm (perm_inv (S n) f n) n (S n))%prg.
Proof.
  intros Hperm k Hk.
  rewrite (invperm_of_insertion_sort_list_eq _ _ Hperm) at 1 by auto.
Local Opaque perm_inv.
  simpl.
Local Transparent perm_inv.
  rewrite length_insertion_sort_list by auto.
  easy.
Qed.

Lemma permutation_grow_l n f : permutation (S n) f ->
  exists g k, k < S n /\ perm_eq (S n) f (swap_perm k n (S n) ∘ g)%prg /\ permutation n g.
Proof.
  intros Hperm.
  eexists.
  exists (f n).
  split; [apply permutation_is_bounded; [easy | lia] | split].
  pose proof (perm_of_insertion_sort_list_of_perm_inv_eq _ _ Hperm) as H.
  rewrite perm_of_insertion_sort_list_S in H.
  rewrite perm_inv_perm_inv in H by (easy || lia).
  exact H.
  auto with perm_db.
Qed.

Lemma permutation_grow_r n f : permutation (S n) f ->
  exists g k, k < S n /\ perm_eq (S n) f (g ∘ swap_perm k n (S n))%prg /\ permutation n g.
Proof.
  intros Hperm.
  eexists.
  exists (perm_inv (S n) f n).
  split; [apply permutation_is_bounded; [auto with perm_db | lia] | split].
  pose proof (invperm_of_insertion_sort_list_eq _ _ Hperm) as H.
  rewrite invperm_of_insertion_sort_list_S in H.
  exact H.
  auto with perm_db.
Qed.

(* Section on stack_perms *)
Ltac replace_bool_lia b0 b1 :=
  first [
    replace b0 with b1 by (bdestruct b0; lia || (destruct b1 eqn:?; lia)) |
    replace b0 with b1 by (bdestruct b1; lia || (destruct b0 eqn:?; lia)) |
    replace b0 with b1 by (bdestruct b0; bdestruct b1; lia)
  ].

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
	(Hf' : permutation n0 f') (Hg' : permutation n1 g') :
	(stack_perms n0 n1 f g ∘ stack_perms n0 n1 f' g'
	= stack_perms n0 n1 (f ∘ f') (g ∘ g'))%prg.
Proof.
	destruct Hf' as [Hf'inv Hf'].
	destruct Hg' as [Hg'inv Hg'].
	unfold compose.
	(* bdestruct_one. *)
  solve_modular_permutation_equalities.
	1,2: specialize (Hf' k H); lia.
	- f_equal; f_equal. lia.
	- assert (Hk: k - n0 < n1) by lia.
	  specialize (Hg' _ Hk); lia.
Qed.

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

(* Section on rotr / rotl *)
Lemma rotr_WF : 
	forall n k, WF_Perm n (rotr n k).
Proof. unfold WF_Perm. intros. unfold rotr. bdestruct_one; lia. Qed.

Lemma rotl_WF {n m} : 
	forall k, n <= k -> (rotl n m) k = k.
Proof. intros. unfold rotl. bdestruct_one; lia. Qed.

#[export] Hint Resolve rotr_WF rotl_WF : WF_perm_db.

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

#[export] Hint Resolve rotr_bdd rotl_bdd : perm_bdd_db.

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
	- rewrite Nat.add_mod_idemp_l; [|easy].
	  rewrite <- Nat.add_assoc.
	  replace (n - m mod n + m) with
	    (n - m mod n + (n * (m / n) + m mod n)) by
	    (rewrite <- (Nat.div_mod m n Hn0); easy).
	  pose proof (Nat.mod_upper_bound m n Hn0).
	  replace (n - m mod n + (n * (m / n) + m mod n)) with
	    (n * (1 + m / n)) by lia.
	  rewrite Nat.mul_comm, Nat.mod_add; [|easy].
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
	- rewrite Nat.add_mod_idemp_l; [|easy].
	  rewrite <- Nat.add_assoc.
	  replace (m + (n - m mod n)) with
	    ((n * (m / n) + m mod n) + (n - m mod n)) by
	    (rewrite <- (Nat.div_mod m n Hn0); easy).
	  pose proof (Nat.mod_upper_bound m n Hn0).
	  replace ((n * (m / n) + m mod n) + (n - m mod n)) with
	    (n * (1 + m / n)) by lia.
	  rewrite Nat.mul_comm, Nat.mod_add; [|easy].
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
	rewrite Nat.mod_0_l, Nat.sub_0_r; [|lia].
	replace (k + n) with (k + 1 * n) by lia.
	rewrite Nat.mod_add, Nat.mod_small; lia.
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
	bdestructΩ'; assert (Hn0 : n <> 0) by lia.
	- pose proof (Nat.mod_upper_bound (a + l) n Hn0); lia.
	- rewrite Nat.add_mod_idemp_l; [|easy].
	  f_equal; lia.
Qed.

Lemma rotl_rotl n k l :
	((rotl n k) ∘ (rotl n l) = rotl n (k + l))%prg.
Proof.
	apply (WF_permutation_inverse_injective (rotr n (k + l)) n).
	- apply rotr_perm.
	- apply rotr_WF.
	- rewrite Nat.add_comm, <- rotr_rotr, 
		<- Combinators.compose_assoc, (Combinators.compose_assoc _ _ _ _ (rotr n l)).
	  cleanup_perm; easy. (* rewrite rotl_rotr_inv, compose_idn_r, rotl_rotr_inv. *)
	- rewrite rotl_rotr_inv; easy.
Qed.

#[export] Hint Rewrite rotr_rotr rotl_rotl : perm_cleanup_db.

Lemma rotr_n n : rotr n n = idn.
Proof.
	apply functional_extensionality; intros a.
	unfold rotr.
	bdestructΩ'.
	replace (a + n) with (a + 1 * n) by lia.
	destruct n; [lia|].
	rewrite Nat.mod_add; [|easy].
	rewrite Nat.mod_small; easy.
Qed.

#[export] Hint Rewrite rotr_n : perm_cleanup_db.

Ltac perm_eq_by_WF_inv_inj f n :=
  let tryeasylia := try easy; try lia in 
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with WF_perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; tryeasylia.

Lemma rotr_eq_rotr_mod n k : rotr n k = rotr n (k mod n).
Proof.
  perm_eq_by_WF_inv_inj (rotl n k) n. 
  - unfold WF_Perm. 
    apply rotl_WF.
  - apply functional_extensionality.
    intros a.
    unfold Basics.compose, rotr.
    bdestruct (n <=? a).
    + rewrite (rotl_WF a) by easy.
      bdestruct_all; easy.
    + unfold rotl.
      pose proof (Nat.mod_upper_bound (a + (n-k mod n)) n ltac:(lia)).
      bdestruct_all; try lia.
      rewrite <- Nat.add_mod by lia.
      rewrite (Nat.div_mod k n) at 2 by lia.
      replace ((a + (n - k mod n) + (n * (k / n) + k mod n)))
      with ((a + ((n - k mod n) + k mod n + (n * (k / n))))) by lia.
      rewrite Nat.sub_add by (pose proof (Nat.mod_upper_bound k n); lia).
      rewrite Nat.add_assoc, Nat.mul_comm, Nat.mod_add by lia.
      rewrite mod_add_n_r, Nat.mod_small; lia.
Qed.

Lemma rotl_n n : rotl n n = idn.
Proof.
  perm_eq_by_WF_inv_inj (rotr n n) n.
Qed.

#[export] Hint Rewrite rotl_n : perm_cleanup_db.

Lemma rotl_eq_rotl_mod n k : rotl n k = rotl n (k mod n).
Proof. 
  perm_eq_by_WF_inv_inj (rotr n k) n.
  rewrite rotr_eq_rotr_mod, rotl_rotr_inv; easy.
Qed.

Lemma rotr_eq_rotl_sub n k : 
	rotr n k = rotl n (n - k mod n).
Proof.
	rewrite rotr_eq_rotr_mod.
  perm_eq_by_WF_inv_inj (rotl n (k mod n)) n.
  - unfold WF_Perm.
    apply rotr_WF.
  - cleanup_perm.
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
  perm_eq_by_WF_inv_inj (rotr n k) n.
	destruct n; [cbn; rewrite 2!rotr_0_l, compose_idn_l; easy|].
  rewrite (rotr_eq_rotr_mod _ k), rotr_rotr, <- (rotr_n (S n)).
  f_equal.
  assert (H' : S n <> 0) by easy.
  pose proof (Nat.mod_upper_bound k (S n) H').
  lia.
Qed.

