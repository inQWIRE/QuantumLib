Require Import Bits.
Require Import Modulus.
Require Export PermutationsBase.

Local Open Scope perm_scope.
Local Open Scope nat_scope.

Create HintDb perm_unfold_db.
Create HintDb perm_cleanup_db.
Create HintDb proper_side_conditions_db.

Ltac auto_perm_to n := 
  auto n with perm_db perm_bounded_db WF_Perm_db perm_inv_db.

Ltac auto_perm := 
  auto 6 with perm_db perm_bounded_db WF_Perm_db perm_inv_db.

Tactic Notation "auto_perm" int_or_var(n) :=
  auto_perm_to n.

Tactic Notation "auto_perm" :=
  auto_perm 6.

#[export] Hint Resolve 
  permutation_is_bounded
  permutation_is_injective
  permutation_is_surjective : perm_db.

#[export] Hint Extern 0 (perm_inj ?n ?f) =>
  apply (permutation_is_injective n f) : perm_db.

#[export] Hint Resolve
  permutation_compose : perm_db.

#[export] Hint Resolve compose_WF_Perm : WF_Perm_db.
#[export] Hint Rewrite @compose_idn_r @compose_idn_l : perm_cleanup_db.

#[export] Hint Extern 100 (_ < _) =>
  show_moddy_lt : perm_bounded_db.

#[export] Hint Extern 0 (funbool_to_nat ?n ?f < ?b) =>
  apply (Nat.lt_le_trans (Bits.funbool_to_nat n f) (2^n) b);
  [apply (Bits.funbool_to_nat_bound n f) | show_pow2_le] : show_moddy_lt_db.

Ltac show_permutation :=
  repeat first [
    split
  | simpl; solve [auto with perm_db]
  | subst; solve [auto with perm_db]
  | solve [eauto using permutation_compose with perm_db]
  | easy
  | lia
  ].

Ltac cleanup_perm_inv := 
  auto with perm_inv_db perm_db perm_bounded_db WF_Perm_db;
  autorewrite with perm_inv_db; 
  auto with perm_inv_db perm_db perm_bounded_db WF_Perm_db.

Ltac cleanup_perm :=
  auto with perm_inv_db perm_cleanup_db perm_db perm_bounded_db WF_Perm_db;
  autorewrite with perm_inv_db perm_cleanup_db; 
  auto with perm_inv_db perm_cleanup_db perm_db perm_bounded_db WF_Perm_db.

 
Ltac solve_modular_permutation_equalities :=
  first [cleanup_perm_inv | cleanup_perm];
  autounfold with perm_unfold_db;
  apply functional_extensionality; let k := fresh "k" in intros k;
  bdestructΩ';
  solve_simple_mod_eqns.

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
  only 3,4 : 
    (solve [apply compose_id_of_compose_idn; cleanup_perm; tryeasylia]) 
    || cleanup_perm; tryeasylia;
  only 1,2 : auto with perm_bounded_db; tryeasylia.

Ltac permutation_eq_by_WF_inv_inj f n :=
  let tryeasylia := (try easy); (try lia) in
  apply (WF_permutation_inverse_injective f n); [
    tryeasylia; auto with perm_db |
    tryeasylia; auto with WF_Perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; 
    tryeasylia.

Ltac perm_eq_by_inv_inj f n :=
  let tryeasylia := (try easy); (try lia) in
  apply (perm_inv_perm_eq_injective f n); [
    tryeasylia; auto with perm_db |
    try solve [cleanup_perm; auto] |
    try solve [cleanup_perm; auto]]; 
    tryeasylia.

Ltac eq_by_WF_perm_eq n := 
  apply (eq_of_WF_perm_eq n); 
  auto with WF_Perm_db.


(* Extending setoid rewriting to work with side conditions *)
Import Setoid Morphisms.

(* Placeholder for irrelevant arguments *)
Definition true_rel {A} : relation A := 
	fun _ _ => True.

(* Add Parametric Relation A : A true_rel 
	reflexivity proved by ltac:(easy)
	symmetry proved by ltac:(easy)
	transitivity proved by ltac:(easy) 
	as true_rel_equivalence. *)

#[export] Hint Unfold true_rel : typeclass_instances.

#[export] Instance true_rel_superrel {A} (R : relation A) : 
  subrelation R true_rel | 10.
Proof.
  intros x y H.
  constructor.
Qed.

Definition on_predicate_relation_l {A} (P : A -> Prop) (R : relation A) 
  : relation A :=
  fun (x y : A) => P x /\ R x y. 

Definition on_predicate_relation_r {A} (P : A -> Prop) (R : relation A) 
  : relation A :=
  fun (x y : A) => P y /\ R x y. 

Lemma proper_proxy_on_predicate_l {A} (P : A -> Prop) (R : relation A) 
  (x : A) : 
  P x ->
  Morphisms.ProperProxy R x ->
  Morphisms.ProperProxy (on_predicate_relation_l P R) x.
Proof.
  easy.
Qed.

Lemma proper_proxy_on_predicate_r {A} (P : A -> Prop) (R : relation A) 
  (x : A) : 
  P x ->
  Morphisms.ProperProxy R x ->
  Morphisms.ProperProxy (on_predicate_relation_r P R) x.
Proof.
  easy.
Qed.

Lemma proper_proxy_flip_on_predicate_l {A} (P : A -> Prop) (R : relation A) 
  (x : A) : 
  P x ->
  Morphisms.ProperProxy R x ->
  Morphisms.ProperProxy (flip (on_predicate_relation_l P R)) x.
Proof.
  easy.
Qed.

Lemma proper_proxy_flip_on_predicate_r {A} (P : A -> Prop) (R : relation A) 
  (x : A) : 
  P x ->
  Morphisms.ProperProxy R x ->
  Morphisms.ProperProxy (flip (on_predicate_relation_r P R)) x.
Proof.
  easy.
Qed.

#[export] Hint Extern 0 
  (Morphisms.ProperProxy (on_predicate_relation_l ?P ?R) ?x) =>
  apply (proper_proxy_on_predicate_l P R x 
  ltac:(auto with proper_side_conditions_db)) : typeclass_instances.

#[export] Hint Extern 0 
  (Morphisms.ProperProxy (on_predicate_relation_r ?P ?R) ?x) =>
  apply (proper_proxy_on_predicate_r P R x 
  ltac:(auto with proper_side_conditions_db)) : typeclass_instances.

#[export] Hint Extern 0 
  (Morphisms.ProperProxy (flip (on_predicate_relation_l ?P ?R)) ?x) =>
  apply (proper_proxy_flip_on_predicate_l P R x 
  ltac:(auto with proper_side_conditions_db)) : typeclass_instances.

#[export] Hint Extern 0 
  (Morphisms.ProperProxy (flip (on_predicate_relation_r ?P ?R)) ?x) =>
  apply (proper_proxy_flip_on_predicate_r P R x 
  ltac:(auto with proper_side_conditions_db)) : typeclass_instances.

#[export] Hint Extern 10 => cbn beta : proper_side_conditions_db.

Add Parametric Relation n : (nat -> nat) (perm_eq n) 
  reflexivity proved by (perm_eq_refl n)
  symmetry proved by (@perm_eq_sym n)
  transitivity proved by (@perm_eq_trans n)
  as perm_eq_Setoid.

#[export] Hint Extern 0 (perm_bounded _ _) =>
  solve [auto with perm_bounded_db perm_db] : proper_side_conditions_db.

#[export] Hint Extern 0 (permutation _ _) =>
  solve [auto with perm_db] : proper_side_conditions_db.

#[export] Hint Extern 0 (WF_Perm _ _) =>
  solve [auto with WF_Perm_db] : proper_side_conditions_db.


#[export] Hint Resolve perm_eq_refl : perm_db perm_inv_db.

Section PermComposeLemmas.

Local Open Scope prg.

Lemma perm_eq_compose_rewrite_l {n} {f g h : nat -> nat}
  (H : perm_eq n (f ∘ g) (h)) : forall (i : nat -> nat), 
  perm_eq n (i ∘ f ∘ g) (i ∘ h). 
Proof.
  intros i k Hk.
  unfold compose in *.
  now rewrite H.
Qed.

Lemma perm_eq_compose_rewrite_l_to_2 {n} {f g h i : nat -> nat}
  (H : perm_eq n (f ∘ g) (h ∘ i)) : forall (j : nat -> nat), 
  perm_eq n (j ∘ f ∘ g) (j ∘ h ∘ i).
Proof.
  intros j k Hk.
  unfold compose in *.
  now rewrite H.
Qed.

Lemma perm_eq_compose_rewrite_l_to_Id {n} {f g : nat -> nat}
  (H : perm_eq n (f ∘ g) idn) : forall (h : nat -> nat), 
  perm_eq n (h ∘ f ∘ g) h.
Proof.
  intros h k Hk.
  unfold compose in *.
  now rewrite H.
Qed.

Lemma perm_eq_compose_rewrite_r {n} {f g h : nat -> nat}
  (H : perm_eq n (f ∘ g) h) : forall (i : nat -> nat), 
  perm_bounded n i ->
  perm_eq n (f ∘ (g ∘ i)) (h ∘ i).
Proof.
  intros i Hi k Hk.
  unfold compose in *.
  now rewrite H by auto.
Qed.

Lemma perm_eq_compose_rewrite_r_to_2 {n} {f g h i : nat -> nat}
  (H : perm_eq n (f ∘ g) (h ∘ i)) : forall (j : nat -> nat), 
  perm_bounded n j ->
  perm_eq n (f ∘ (g ∘ j)) (h ∘ (i ∘ j)).
Proof.
  intros j Hj k Hk.
  unfold compose in *.
  now rewrite H by auto.
Qed.

Lemma perm_eq_compose_rewrite_r_to_Id {n} {f g : nat -> nat}
  (H : perm_eq n (f ∘ g) idn) : forall (h : nat -> nat), 
  perm_bounded n h ->
  perm_eq n (f ∘ (g ∘ h)) h.
Proof.
  intros h Hh k Hk.
  unfold compose in *.
  now rewrite H by auto.
Qed.

End PermComposeLemmas.



Ltac make_perm_eq_compose_assoc_rewrite_l lem :=
  lazymatch type of lem with
  | perm_eq ?n (?F ∘ ?G)%prg idn => 
    constr:(perm_eq_compose_rewrite_l_to_Id lem)
  | perm_eq ?n (?F ∘ ?G)%prg (?F' ∘ ?G')%prg => 
    constr:(perm_eq_compose_rewrite_l_to_2 lem)
  | perm_eq ?n (?F ∘ ?G)%prg ?H => 
    constr:(perm_eq_compose_rewrite_l lem)
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_l (lem x) in 
      exact r))
  end.

Ltac make_perm_eq_compose_assoc_rewrite_l' lem :=
  lazymatch type of lem with
  | perm_eq ?n idn (?F ∘ ?G)%prg => 
    constr:(perm_eq_compose_rewrite_l_to_Id (perm_eq_sym lem))
  | perm_eq ?n (?F ∘ ?G)%prg (?F' ∘ ?G')%prg => 
    constr:(perm_eq_compose_rewrite_l_to_2 (perm_eq_sym lem))
  | perm_eq ?n ?H (?F ∘ ?G)%prg => 
    constr:(perm_eq_compose_rewrite_l (perm_eq_sym lem))
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_l' (lem x) in 
      exact r))
  end.

Ltac rewrite_perm_eq_compose_assoc_l lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_l lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_perm_eq_compose_assoc_l' lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_l' lem in
  rewrite lem' || rewrite <- lem.

Ltac make_perm_eq_compose_assoc_rewrite_r lem :=
  lazymatch type of lem with
  | perm_eq ?n (?F ∘ ?G)%prg idn => 
    constr:(perm_eq_compose_rewrite_r_to_Id lem)
  | perm_eq ?n (?F ∘ ?G)%prg (?F' ∘ ?G')%prg => 
    constr:(perm_eq_compose_rewrite_r_to_2 lem)
  | perm_eq ?n (?F ∘ ?G)%prg ?H => 
    constr:(perm_eq_compose_rewrite_r lem)
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_r (lem x) in 
      exact r))
  end.

Ltac make_perm_eq_compose_assoc_rewrite_r' lem :=
  lazymatch type of lem with
  | perm_eq ?n idn (?F ∘ ?G)%prg => 
    constr:(perm_eq_compose_rewrite_r_to_Id (perm_eq_sym lem))
  | perm_eq ?n (?F ∘ ?G)%prg (?F' ∘ ?G')%prg => 
    constr:(perm_eq_compose_rewrite_r_to_2 (perm_eq_sym lem))
  | perm_eq ?n ?H (?F ∘ ?G)%prg => 
    constr:(perm_eq_compose_rewrite_r (perm_eq_sym lem))
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_perm_eq_compose_assoc_rewrite_r' (lem x) in 
      exact r))
  end.

Ltac rewrite_perm_eq_compose_assoc_r lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_r lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_perm_eq_compose_assoc_r' lem :=
  let lem' := make_perm_eq_compose_assoc_rewrite_r' lem in
  rewrite lem' || rewrite <- lem.

Notation "'###perm_l' '->' lem" :=
  (ltac:(let r := make_perm_eq_compose_assoc_rewrite_l lem in exact r)) 
  (at level 0, lem at level 15, only parsing).

Notation "'###perm_r' '->' lem" :=
  (ltac:(let r := make_perm_eq_compose_assoc_rewrite_r lem in exact r)) 
  (at level 0, lem at level 15, only parsing).

Notation "'###perm_l' '<-' lem" :=
  (ltac:(let r := make_perm_eq_compose_assoc_rewrite_l' lem in exact r)) 
  (at level 0, lem at level 15, only parsing).

Notation "'###perm_r' '<-' lem" :=
  (ltac:(let r := make_perm_eq_compose_assoc_rewrite_r' lem in exact r)) 
  (at level 0, lem at level 15, only parsing).


Section ComposeLemmas.

Local Open Scope prg.

(* Helpers for rewriting with compose and perm_eq *)
Lemma compose_rewrite_l {f g h : nat -> nat}
  (H : f ∘ g = h) : forall (i : nat -> nat), 
  i ∘ f ∘ g = i ∘ h.
Proof.
  intros; 
  now rewrite compose_assoc, H.
Qed.

Lemma compose_rewrite_l_to_2 {f g h i : nat -> nat}
  (H : f ∘ g = h ∘ i) : forall (j : nat -> nat), 
  j ∘ f ∘ g = j ∘ h ∘ i.
Proof.
  intros; 
  now rewrite !compose_assoc, H.
Qed.

Lemma compose_rewrite_l_to_Id {f g : nat -> nat}
  (H : f ∘ g = idn) : forall (h : nat -> nat), 
  h ∘ f ∘ g = h.
Proof.
  intros; 
  now rewrite compose_assoc, H, compose_idn_r.
Qed.

Lemma compose_rewrite_r {f g h : nat -> nat}
  (H : f ∘ g = h) : forall (i : nat -> nat), 
  f ∘ (g ∘ i) = h ∘ i.
Proof.
  intros; 
  now rewrite <- compose_assoc, H.
Qed.

Lemma compose_rewrite_r_to_2 {f g h i : nat -> nat}
  (H : f ∘ g = h ∘ i) : forall (j : nat -> nat), 
  f ∘ (g ∘ j) = h ∘ (i ∘ j).
Proof.
  intros; 
  now rewrite <- !compose_assoc, H.
Qed.

Lemma compose_rewrite_r_to_Id {f g : nat -> nat}
  (H : f ∘ g = idn) : forall (h : nat -> nat), 
  f ∘ (g ∘ h) = h.
Proof.
  intros; 
  now rewrite <- compose_assoc, H, compose_idn_l.
Qed.

End ComposeLemmas.

Ltac make_compose_assoc_rewrite_l lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_compose_assoc_rewrite_l (lem x) in 
      exact r))
  | (?F ∘ ?G)%prg = idn => 
    constr:(compose_rewrite_l_to_Id lem)
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_l_to_2 lem)
  | (?F ∘ ?G)%prg = ?H => 
    constr:(compose_rewrite_l lem)
  end.

Ltac make_compose_assoc_rewrite_l' lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_compose_assoc_rewrite_l' (lem x) in 
      exact r))
  | idn = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_l_to_Id (eq_sym lem))
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_l_to_2 (eq_sym lem))
  | ?H = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_l (eq_sym lem))
  end.

Ltac rewrite_compose_assoc_l lem :=
  let lem' := make_compose_assoc_rewrite_l lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_compose_assoc_l' lem :=
  let lem' := make_compose_assoc_rewrite_l' lem in
  rewrite lem' || rewrite <- lem.

Ltac make_compose_assoc_rewrite_r lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_compose_assoc_rewrite_r (lem x) in 
      exact r))
  | (?F ∘ ?G)%prg = idn => 
    constr:(compose_rewrite_r_to_Id lem)
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_r_to_2 lem)
  | (?F ∘ ?G)%prg = ?H => 
    constr:(compose_rewrite_r lem)
  end.

Ltac make_compose_assoc_rewrite_r' lem :=
  lazymatch type of lem with
  | forall a : ?A, @?f a => 
    let x := fresh a in 
    constr:(fun x : A => ltac:(
      let r := make_compose_assoc_rewrite_r' (lem x) in 
      exact r))
  | idn = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_r_to_Id (eq_sym lem))
  | (?F ∘ ?G)%prg = (?F' ∘ ?G')%prg => 
    constr:(compose_rewrite_r_to_2 (eq_sym lem))
  | ?H = (?F ∘ ?G)%prg => 
    constr:(compose_rewrite_r (eq_sym lem))
  end.

Ltac rewrite_compose_assoc_r lem :=
  let lem' := make_compose_assoc_rewrite_r lem in
  rewrite lem' || rewrite lem.

Ltac rewrite_compose_assoc_r' lem :=
  let lem' := make_compose_assoc_rewrite_r' lem in
  rewrite lem' || rewrite <- lem.

Notation "'###comp_l' '->' lem" :=
  (ltac:(let r := make_compose_assoc_rewrite_l lem in exact r)) 
  (at level 0, lem at level 15, only parsing).

Notation "'###comp_r' '->' lem" :=
  (ltac:(let r := make_compose_assoc_rewrite_r lem in exact r)) 
  (at level 0, lem at level 15, only parsing).

Notation "'###comp_l' '<-' lem" :=
  (ltac:(let r := make_compose_assoc_rewrite_l' lem in exact r)) 
  (at level 0, lem at level 15, only parsing).

Notation "'###comp_r' '<-' lem" :=
  (ltac:(let r := make_compose_assoc_rewrite_r' lem in exact r)) 
  (at level 0, lem at level 15, only parsing).