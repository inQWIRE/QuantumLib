Require Import Bits.
Require Import VectorStates.
Require Import Modulus.
Require Import Permutations.

Local Open Scope perm_scope.
Local Open Scope nat_scope.

Create HintDb perm_unfold_db.
Create HintDb perm_cleanup_db.
Create HintDb proper_side_conditions_db.

#[export] Hint Resolve 
  permutation_is_bounded
  permutation_is_injective
  permutation_is_surjective : perm_db.

#[export] Hint Resolve
  permutation_compose
  qubit_perm_to_nat_perm_bij : perm_db.

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

#[export] Hint Extern 0 
  (Morphisms.ProperProxy (on_predicate_relation_l ?P ?R) ?x) =>
  apply (proper_proxy_on_predicate_l P R x 
  ltac:(auto with proper_side_conditions_db)) : typeclass_instances.

#[export] Hint Extern 0 
  (Morphisms.ProperProxy (on_predicate_relation_r ?P ?R) ?x) =>
  apply (proper_proxy_on_predicate_r P R x 
  ltac:(auto with proper_side_conditions_db)) : typeclass_instances.


Add Parametric Relation n : (nat -> nat) (perm_eq n) 
  reflexivity proved by (perm_eq_refl n)
  symmetry proved by (@perm_eq_sym n)
  transitivity proved by (@perm_eq_trans n)
  as perm_eq_Setoid.

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
  intros f f' Hf g g' [Hgbdd <-] k Hk.
  unfold compose.
  auto.
Qed.

#[export] Hint Extern 0 (perm_bounded _ _) =>
  solve [auto with perm_bounded_db perm_db] : proper_side_conditions_db.