Require Import Bits.
Require Import Modulus.

(** Facts about permutations *)
Declare Scope perm_scope.
Local Open Scope perm_scope.
Local Open Scope nat_scope.

Create HintDb perm_db.
Create HintDb perm_bounded_db.
Create HintDb perm_inv_db.
Create HintDb WF_Perm_db.

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
Notation idn := (fun (k : nat) => k).

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
  interpreted as a function from [n]_0 to [n]_0) and their equivalences *)
Notation perm_surj n f := (forall k, k < n -> exists k', k' < n /\ f k' = k).
Notation perm_bounded n f := (forall k, k < n -> f k < n).
Notation perm_inj n f := (forall k l, k < n -> l < n -> f k = f l -> k = l).

Lemma fswap_injective_if_injective : forall {A} n (f:nat -> A) x y,
  x < n -> y < n ->
  perm_inj n f -> perm_inj n (fswap f x y).
Proof.
  intros A n f x y Hx Hy Hinj k l Hk Hl.
  unfold fswap.
  bdestruct (k =? x); bdestruct (k =? y);
  bdestruct (l =? x); bdestruct (l =? y);
  subst;
  intros Heq; 
  apply Hinj in Heq; lia. 
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
  perm_bounded n f -> perm_bounded n (fswap f x y).
Proof.
  intros n f x y Hx Hy Hbounded k Hk.
  unfold fswap.
  bdestruct_all;
  apply Hbounded; 
  easy.
Qed.

Lemma fswap_bounded_iff_bounded : forall n f x y,
  x < n -> y < n ->
  perm_bounded n f <-> perm_bounded n (fswap f x y).
Proof.
  intros n f x y Hx Hy.
  split.
  - apply fswap_bounded_if_bounded; easy.
  - intros Hbounded.
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
  perm_inj n f /\ perm_bounded n f -> f n = n ->
  perm_inj (S n) f /\ perm_bounded (S n) f.
Proof.
  intros n f [Hinj Hbounded] Hfn.
  split.
  - intros k l Hk Hl Hfkl.
    bdestruct (k =? n).
    + subst.
      bdestruct (l =? n); [easy|].
      assert (H'l : l < n) by lia.
      specialize (Hbounded _ H'l).
      lia.
    + assert (H'k : k < n) by lia.
      bdestruct (l =? n).
      * specialize (Hbounded _ H'k). 
        subst. lia.
      * assert (H'l : l < n) by lia.
        apply Hinj; easy.
  - intros k Hk.
    bdestruct (k <? n).
    + specialize (Hbounded _ H). lia.
    + replace k with n by lia.
      lia.
Qed.

Lemma injective_and_bounded_of_surjective : forall n f,
  perm_surj n f -> perm_inj n f /\ perm_bounded n f.
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
  perm_inj (S n) f /\ perm_bounded (S n) f -> f n = n -> 
  perm_inj n f /\ perm_bounded n f.
Proof.
  intros n f [Hinj Hbounded] Hfn.
  split.
  - eapply injective_monotone, Hinj; lia.
  - intros k Hk.
    assert (H'k : k < S n) by lia.
    specialize (Hbounded k H'k).
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
    [intros f Hbounded; specialize (Hbounded 0); lia|].
  induction n; intros f Hbounded.
  1: {
    exists 1, 0.
    pose (Hbounded 0).
    pose (Hbounded 1). 
    lia.
  }
  destruct (has_preimage_decidable (S (S n)) f (f (S (S n)))) as [Hex | Hnex].
  - apply Hbounded; lia.
  - destruct Hex as [j [Hj Hfj]].
    exists (S (S n)), j.
    repeat split; lia.
  - destruct (IHn (fun k => if f k <? f (S (S n)) then f k else f k - 1)) as
      [i [j [Hi [Hj Hgij]]]].
    + intros i Hi.
      bdestruct (f i <? f (S (S n))).
      * specialize (Hbounded (S (S n))).
        lia.
      * specialize (Hbounded i).
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
  perm_inj (S n) f /\ perm_bounded (S n) f -> exists k, k < S n /\ f k = n.
Proof. 
  intros n f [Hinj Hbounded].
  destruct (has_preimage_decidable (S n) f n) as [Hex | Hnex]; 
    [lia | assumption |].
  (* Now, contradict injectivity using pigeonhole principle *)
  exfalso.
  assert (Hbounded': forall j, j < S n -> f j < n). 1:{
    intros j Hj.
    specialize (Hbounded j Hj).
    bdestruct (f j =? n).
    - exfalso; apply Hnex; exists j; easy.
    - lia.
  }
  destruct (pigeonhole_S n f Hbounded') as [i [j [Hi [Hj Heq]]]].
  absurd (i = j).
  - lia.
  - apply Hinj; lia.
Qed.

Lemma surjective_of_injective_and_bounded : forall n f,
  perm_inj n f /\ perm_bounded n f -> perm_surj n f.
Proof. 
  induction n; [easy|].
  intros f Hinj_bounded.
  destruct (n_has_preimage_of_injective_and_bounded n f Hinj_bounded) as [n' [Hn' Hfn']].
  rewrite (fswap_injective_iff_injective _ _ n n') in Hinj_bounded;
    [|lia|lia].
  rewrite (fswap_bounded_iff_bounded _ _ n n') in Hinj_bounded;
    [|lia|lia].
  rewrite (fswap_surjective_iff_surjective _ _ n n');
    [|lia|easy].
  intros k Hk.
  bdestruct (k =? n).
  - exists n.
    split; [lia|].
    rewrite fswap_simpl1; subst; easy.
  - pose proof (injective_and_bounded_shrink_of_boundary n _ Hinj_bounded) as Hinj_bounded'.
    rewrite fswap_simpl1 in Hinj_bounded'.
    specialize (Hinj_bounded' Hfn').
    destruct (IHn (fswap f n n') Hinj_bounded' k) as [k' [Hk' Hfk']]; [lia|].
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
  perm_bounded n (perm_inv n f).
Proof.
  induction n.
  - easy.
  - intros.
    apply perm_inv_bounded_S.
Qed.

#[export] Hint Resolve perm_inv_bounded_S perm_inv_bounded : perm_bounded_db.

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
  perm_surj n f -> perm_inj n f -> perm_bounded n f ->
  (forall k, k < n -> 
    f k < n /\ perm_inv n f k < n /\ perm_inv n f (f k) = k /\ f (perm_inv n f k) = k).
Proof.
  intros n f Hsurj Hinj Hbounded.
  intros k Hk; repeat split.
  - apply Hbounded, Hk.
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
  perm_bounded n f.
Proof.
  intros [finv Hfinv] k Hk.
  destruct (Hfinv k Hk); easy.
Qed.

Lemma id_permutation : forall n,
  permutation n Datatypes.id.
Proof. 
  intros.
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
Proof. 
  intros. 
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

Lemma compose_WF_Perm n f g : WF_Perm n f -> WF_Perm n g -> 
  WF_Perm n (f ∘ g)%prg.
Proof.
  unfold compose.
  intros Hf Hg k Hk.
  rewrite Hg, Hf; easy.
Qed.

#[export] Hint Resolve compose_WF_Perm : WF_Perm_db.

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

Lemma bounded_of_WF_linv {n} {f finv}  
  (HWF: WF_Perm n f) (Hinv : (finv ∘ f = idn)%prg) : 
  perm_bounded n f.
Proof.
  intros k Hk.
  pose proof (linv_WF_of_WF HWF Hinv) as HWFinv.
  unfold compose in Hinv.
  apply (f_equal_inv k) in Hinv. 
  bdestruct (f k <? n); [easy|].
  specialize (HWFinv (f k) H).
  lia.
Qed.

Lemma rinv_bounded_of_WF {n} {f finv} (Hinv : (f ∘ finv = idn)%prg)
  (HWF : WF_Perm n f) :
  perm_bounded n finv.
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


Definition perm_eq (n : nat) (f g : nat -> nat) := 
  forall k, k < n -> f k = g k.

Lemma perm_eq_refl (n : nat) (f : nat -> nat) : 
  perm_eq n f f.
Proof.
  easy.
Qed.

Lemma perm_eq_sym {n} {f g : nat -> nat} : 
  perm_eq n f g -> perm_eq n g f.
Proof.
  intros H k Hk; symmetry; auto.
Qed.

Lemma perm_eq_trans {n} {f g h : nat -> nat} : 
  perm_eq n f g -> perm_eq n g h -> perm_eq n f h.
Proof.
  intros Hfg Hgh k Hk; 
  rewrite Hfg; auto.
Qed.

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
  permutation n f -> perm_bounded n finv -> 
  perm_eq n (f ∘ finv)%prg idn <-> perm_eq n (finv ∘ f)%prg idn.
Proof.
  intros Hperm Hbounded.
  split; unfold compose.
  - intros Hrinv.
    intros k Hk.
    apply (permutation_is_injective n f Hperm); try easy.
    + apply Hbounded, permutation_is_bounded, Hk.
      apply Hperm.
    + rewrite Hrinv; [easy|].
      apply (permutation_is_bounded n f Hperm _ Hk).
  - intros Hlinv k Hk.
    destruct Hperm as [fi Hf].
    destruct (Hf k Hk) as [Hfk [Hfik [Hfifk Hffik]]].
    rewrite <- Hffik.
    rewrite Hlinv; easy.
Qed.

Notation is_perm_rinv n f finv := (perm_eq n (f ∘ finv)%prg idn) (only parsing).
Notation is_perm_linv n f finv := (perm_eq n (finv ∘ f)%prg idn) (only parsing).
Notation is_perm_inv n f finv := 
  (perm_eq n (f ∘ finv)%prg idn /\ perm_eq n (finv ∘ f)%prg idn) (only parsing).

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
  perm_inj n f -> perm_bounded n finv -> perm_bounded n finv' ->
  is_perm_rinv n f finv -> is_perm_rinv n f finv' ->
  perm_eq n finv finv'.
Proof.
  intros Hinj Hbounded Hbounded' Hfinv Hfinv' k Hk.
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

Lemma perm_inv_perm_eq_injective (f : nat -> nat) (n : nat) 
  {finv finv' : nat -> nat} (Hf : permutation n f) : 
  perm_eq n (finv ∘ f)%prg idn -> 
  perm_eq n (finv' ∘ f)%prg idn -> 
  perm_eq n finv finv'.
Proof.
  apply perm_linv_injective_of_surjective.
  now apply permutation_is_surjective.
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

Lemma is_permutationE (f : nat -> nat) (n : nat) : 
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
  apply is_permutationE.
Qed.

Lemma permutationP (f : nat -> nat) (n : nat) :
  reflect (permutation n f) (is_permutation f n).
Proof.
  apply iff_reflect, permutation_iff_is_permutation.
Qed.

Definition permutation_dec (f : nat -> nat) (n : nat) :
  {permutation n f} + {~ permutation n f} :=
  reflect_dec _ _ (permutationP f n).


Lemma big_sum_eq_up_to_fswap {G} `{Comm_Group G} 
  n (v : nat -> G) f x y (Hx : x < n) (Hy : y < n) :
  big_sum (fun i => v (f i)) n = 
  big_sum (fun i => v (fswap f x y i)) n.
Proof.
  bdestruct (x =? y);
  [apply big_sum_eq_bounded; unfold fswap; intros;
    bdestructΩ'|].
  bdestruct (x <? y).
  - rewrite 2 (big_sum_split n y) by auto.
    rewrite 2 (big_sum_split y x) by auto.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_sum_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite <- !Gplus_assoc.
    apply f_equal_gen; try apply f_equal;
    [apply big_sum_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    rewrite Gplus_comm, (Gplus_comm _ (v (f y))), Gplus_assoc.
    do 2 f_equal.
    apply big_sum_eq_bounded; unfold fswap, shift; intros;
    bdestructΩ'.
  - rewrite 2 (big_sum_split n x) by auto.
    rewrite 2 (big_sum_split x y) by lia.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_sum_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite <- !Gplus_assoc.
    apply f_equal_gen; try apply f_equal;
    [apply big_sum_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    rewrite Gplus_comm, (Gplus_comm _ (v (f x))), Gplus_assoc.
    do 2 f_equal.
    apply big_sum_eq_bounded; unfold fswap, shift; intros;
    bdestructΩ'.
Qed.


Lemma big_sum_reorder {G} `{Comm_Group G} 
  n (v : nat -> G) f (Hf : permutation n f) :
  big_sum v n = big_sum (fun i => v (f i)) n.
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f [g Hg].
  destruct (Hg n) as [_ [H1' [_ H2']]]; try lia.
  symmetry.
  rewrite (big_sum_eq_up_to_fswap _ v _ (g n) n) by auto.
  repeat rewrite <- big_sum_extend_r.
  rewrite fswap_simpl2.
  rewrite H2'.
  specialize (IHn (fswap f (g n) n)).
  rewrite <- IHn; [easy|].
  apply fswap_at_boundary_permutation; auto.
  exists g. auto.
Qed.

(** vsum terms can be arbitrarily reordered *)
Lemma vsum_reorder : forall {d} n (v : nat -> Vector d) f,
  permutation n f ->
  big_sum v n = big_sum (fun i => v (f i)) n.
Proof.
  intros d n v f Hf.
  now apply big_sum_reorder.
Qed.

(** Some special cases for @big_sum nat nat_is_monoid, to which the 
  above cannot apply because addition is commutative but does not
  form a group. A class Comm_Monoid would generalize this. *)
Lemma Nsum_eq_up_to_fswap
  n (v : nat -> nat) f x y (Hx : x < n) (Hy : y < n) :
  big_sum (fun i => v (f i)) n = 
  big_sum (fun i => v (fswap f x y i)) n.
Proof.
  bdestruct (x =? y);
  [apply big_sum_eq_bounded; unfold fswap; intros;
    bdestructΩ'|].
  bdestruct (x <? y).
  - rewrite 2 (big_sum_split n y) by auto.
    rewrite 2 (big_sum_split y x) by auto.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_sum_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite <- !Gplus_assoc.
    apply f_equal_gen; try apply f_equal;
    [apply big_sum_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    cbn. 
    rewrite Nat.add_comm, (Nat.add_comm _ (v (f y))), Nat.add_assoc.
    do 2 f_equal.
    apply big_sum_eq_bounded; unfold fswap, shift; intros;
    bdestructΩ'.
  - rewrite 2 (big_sum_split n x) by auto.
    rewrite 2 (big_sum_split x y) by lia.
    rewrite fswap_simpl1, fswap_simpl2.
    apply f_equal_gen; try apply f_equal;
    [|apply big_sum_eq_bounded; unfold fswap, shift; intros;
      bdestructΩ'].
    rewrite <- !Gplus_assoc.
    apply f_equal_gen; try apply f_equal;
    [apply big_sum_eq_bounded; unfold fswap; intros;
      bdestructΩ'|].
    rewrite Nat.add_comm, (Nat.add_comm _ (v (f x))), Nat.add_assoc.
    do 2 f_equal.
    apply big_sum_eq_bounded; unfold fswap, shift; intros;
    bdestructΩ'.
Qed.

Lemma Nsum_reorder n (v : nat -> nat) f (Hf : permutation n f) :
  big_sum v n = big_sum (v ∘ f)%prg n.
Proof.
  intros.
  generalize dependent f.
  induction n.
  reflexivity.
  intros f Hf. 
  pose proof Hf as [g Hg].
  destruct (Hg n) as [_ [H1' [_ H2']]]; try lia.
  symmetry.
  rewrite (Nsum_eq_up_to_fswap _ _ _ (g n) n) by auto.
  repeat rewrite <- big_sum_extend_r.
  rewrite fswap_simpl2.
  unfold compose.

  rewrite H2'.
  specialize (IHn (fswap f (g n) n)).
  rewrite IHn by
    (apply fswap_at_boundary_permutation; auto).
  simpl.
  f_equal.
  apply big_sum_eq_bounded.
  intros k Hk.
  unfold compose, fswap.
  bdestructΩ'.
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

#[export] Hint Resolve stack_fswaps_permutation : perm_db.

Lemma stack_fswaps_cons : forall (p : nat * nat) (l : list (nat * nat)),
  ((stack_fswaps Datatypes.id [p]) ∘ (stack_fswaps Datatypes.id l))%prg = 
  stack_fswaps Datatypes.id (p :: l).
Proof. intros. 
       simpl.
       rewrite compose_id_right.
       easy.
Qed.

Lemma fswap_comm {A} (f : nat -> A) a b : 
  fswap f a b = fswap f b a.
Proof.
  apply functional_extensionality; intros k.
  unfold fswap.
  bdestruct_all; now subst.
Qed.

(*
Theorem all_perms_are_fswap_stacks : forall {n} f,
  permutation n f -> 
  exists l, WF_fswap_stack n l /\ 
    perm_eq n f (stack_fswaps Datatypes.id l) /\ length l = n.
Proof. 
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

Lemma get_real_function_min_constructive : forall {n} (f : nat -> R),
  {n0 : nat | (n0 < (S n))%nat /\ (forall i, (i < (S n))%nat -> (f n0 <= f i)%R)}.
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

Lemma order_real_function_constructive : forall n (f : nat -> R), 
  {l : list (nat * nat) | WF_fswap_stack n l /\ 
         ordered_real_function n (f ∘ (stack_fswaps Datatypes.id l))%prg}.
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
         destruct (@get_real_function_min_constructive n f) as [n0 [H H0]].
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

