Require Export Matrix.
Require Import RowColOps.
Import Complex.
Require Import Modulus.

Local Open Scope nat_scope.
Local Open Scope C_scope.

Lemma kron_I_r {n m p} (A : Matrix n m) :
  mat_equiv (A ⊗ I p)
  (fun i j => if i mod p =? j mod p then A (i / p)%nat (j / p)%nat else C0).
Proof.
  intros i j Hi Hj.
  unfold kron, I.
  pose proof (Nat.mod_upper_bound i p ltac:(lia)).
  bdestructΩ'; lca.
Qed.

Lemma kron_I_l {n m p} (A : Matrix n m) :
  mat_equiv (I p ⊗ A)
  (fun i j => if i / n =? j / m then A (i mod n) (j mod m) else C0).
Proof.
  intros i j Hi Hj.
  unfold kron, I.
  rewrite Nat.mul_comm in Hi.
  pose proof (Nat.Div0.div_lt_upper_bound _ _ _ Hi).
  bdestructΩ'; lca.
Qed.

Lemma kron_I_l_eq {n m} (A : Matrix n m) p : WF_Matrix A ->
  I p ⊗ A = 
  (fun i j : nat =>
   if ((i / n =? j / m) && (i <? p * n))%nat
   then A (i mod n) (j mod m)
   else C0).
Proof.
  intros HA.
  apply mat_equiv_eq.
  - auto_wf.
  - intros i j []; bdestructΩ'.
    bdestruct (m =? 0); [subst; now rewrite Nat.mod_0_r, HA by lia|].
    pose proof (Nat.div_le_lower_bound j m p).
    pose proof (Nat.Div0.div_lt_upper_bound i n p).
    lia.
  - autounfold with U_db.
    intros i j Hi Hj.
    simplify_bools_lia_one_kernel.
    simplify_bools_moddy_lia_one_kernel.
    bdestructΩ'; lca.
Qed.

Lemma kron_I_r_eq {n m} (A : Matrix n m) p : WF_Matrix A ->
  A ⊗ I p = 
  (fun i j : nat =>
	 if (i mod p =? j mod p) && (i <? n * p) then 
   A (i / p)%nat (j / p)%nat else C0).
Proof.
  intros HA.
  apply mat_equiv_eq.
  - auto_wf.
  - bdestruct (p =? 0); [subst; intros i j _; bdestructΩ'|].
    intros i j []; (rewrite HA; [bdestructΩ'|]); [left | right];
    apply Nat.div_le_lower_bound; lia.
  - autounfold with U_db.
    intros i j Hi Hj.
    simplify_bools_lia_one_kernel.
    simplify_bools_moddy_lia_one_kernel.
    bdestructΩ'; lca.
Qed.

Ltac bdestructΩ'simp := 
  bdestructΩ'_with 
    ltac:(subst; simpl_bools; simpl; try easy; try lca; try lia).

Definition kron_comm p q : Matrix (p*q) (q*p):=
  @make_WF (p*q) (q*p) (fun s t => 
  (* have blocks H_ij, p by q of them, and each is q by p *)
  let i := (s / q)%nat in let j := (t / p)%nat in 
  let k := (s mod q)%nat in let l := (t mod p) in
  if (i =? l) && (j =? k) then C1 else C0
).

Lemma WF_kron_comm p q : WF_Matrix (kron_comm p q).
Proof. unfold kron_comm; 
  rewrite Nat.mul_comm;
  trivial with wf_db. Qed.
#[export] Hint Resolve WF_kron_comm : wf_db.


Lemma kron_comm_transpose_mat_equiv : forall p q, 
  (kron_comm p q) ⊤ ≡ kron_comm q p.
Proof.
  intros p q.
  intros i j Hi Hj.
  unfold kron_comm, transpose, make_WF.
  rewrite andb_comm, Nat.mul_comm.
  rewrite (andb_comm (_ =? _)).
  easy.
Qed.

Lemma kron_comm_transpose : forall p q, 
  (kron_comm p q) ⊤ = kron_comm q p.
Proof.
  intros p q.
  apply mat_equiv_eq; auto with wf_db.
  apply kron_comm_transpose_mat_equiv.
Qed.

Lemma kron_comm_adjoint : forall p q,
  (kron_comm p q) † = kron_comm q p.
Proof.
  intros p q.
  apply mat_equiv_eq; [auto with wf_db..|].
  unfold adjoint.
  intros i j Hi Hj.
  change (kron_comm p q j i) with ((kron_comm p q) ⊤ i j).
  rewrite kron_comm_transpose_mat_equiv by easy.
  unfold kron_comm, make_WF.
  rewrite !(@if_dist C C).
  bdestructΩ'; lca.
Qed.

Lemma kron_comm_1_r_mat_equiv : forall p, 
  (kron_comm p 1) ≡ Matrix.I p.
Proof.
  intros p.
  intros s t Hs Ht.
  unfold kron_comm.
  unfold make_WF.
  unfold Matrix.I.
  rewrite Nat.mul_1_r, Nat.div_1_r, Nat.mod_1_r, Nat.div_small, Nat.mod_small by lia. 
  bdestructΩ'.
Qed.

Lemma kron_comm_1_r : forall p, 
  (kron_comm p 1) = Matrix.I p.
Proof.
  intros p.
  apply mat_equiv_eq; [|rewrite Nat.mul_1_l, Nat.mul_1_r|]; auto with wf_db.
  apply kron_comm_1_r_mat_equiv.
Qed.

Lemma kron_comm_1_l_mat_equiv : forall p, 
  (kron_comm 1 p) ≡ Matrix.I p.
Proof.
  intros p.
  intros s t Hs Ht.
  unfold kron_comm.
  unfold make_WF.
  unfold Matrix.I.
  rewrite Nat.mul_1_l, Nat.div_1_r, Nat.mod_1_r, Nat.div_small, Nat.mod_small by lia. 
  bdestructΩ'.
Qed.

Lemma kron_comm_1_l : forall p, 
  (kron_comm 1 p) = Matrix.I p.
Proof.
  intros p.
  apply mat_equiv_eq; [|rewrite Nat.mul_1_l, Nat.mul_1_r|]; auto with wf_db.
  apply kron_comm_1_l_mat_equiv.
Qed.

Definition mx_to_vec {n m} (A : Matrix n m) : Vector (m * n) :=
  make_WF (fun i j => A (i mod n)%nat (i / n)%nat
  (* Note: goes columnwise. Rowwise would be:
  make_WF (fun i j => A (i / m)%nat (i mod n)%nat
  *)
).

Lemma WF_mx_to_vec {n m} (A : Matrix n m) : WF_Matrix (mx_to_vec A).
Proof. unfold mx_to_vec; auto with wf_db. Qed.
#[export] Hint Resolve WF_mx_to_vec : wf_db.

(* Compute vec_to_list (mx_to_vec (Matrix.I 2)). *)
From Coq Require Import ZArith.
Ltac Zify.zify_post_hook ::= PreOmega.Z.div_mod_to_equations.

Lemma kron_comm_mx_to_vec_helper : forall i p q, (i < p * q)%nat ->
  (p * (i mod q) + i / q < p * q)%nat.
Proof.
  intros i p q Hi.
  show_moddy_lt.
Qed.

Lemma mx_to_vec_additive_mat_equiv {n m} (A B : Matrix n m) :
  mx_to_vec (A .+ B) ≡ mx_to_vec A .+ mx_to_vec B.
Proof.
  intros i j Hi Hj.
  replace j with O by lia; clear dependent j.
  unfold mx_to_vec, make_WF, Mplus.
  bdestructΩ'.
Qed.

Lemma mx_to_vec_additive {n m} (A B : Matrix n m) :
  mx_to_vec (A .+ B) = mx_to_vec A .+ mx_to_vec B.
Proof.
  apply mat_equiv_eq; auto with wf_db.
  apply mx_to_vec_additive_mat_equiv.
Qed.

Lemma if_mult_dist_r (b : bool) (z : C) :
  (if b then C1 else C0) * z = 
  if b then z else C0.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_dist_l (b : bool) (z : C) :
  z * (if b then C1 else C0) = 
  if b then z else C0.
Proof.
  destruct b; lca.
Qed.

Lemma if_mult_and (b c : bool) :
  (if b then C1 else C0) * (if c then C1 else C0) =
  if (b && c) then C1 else C0.
Proof.
  destruct b; destruct c; lca.
Qed.

Lemma kron_comm_mx_to_vec_mat_equiv : forall p q (A : Matrix p q),
  kron_comm p q × mx_to_vec A ≡ mx_to_vec (A ⊤).
Proof.
  intros p q A.
  intros i j Hi Hj.
  replace j with O by lia; clear dependent j.
  unfold transpose, mx_to_vec, kron_comm, make_WF, Mmult.
  rewrite (Nat.mul_comm q p). 
  replace_bool_lia (i <? p * q) true.
  replace_bool_lia (0 <? 1) true.
  simpl.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite andb_true_r, <- andb_if.
  replace_bool_lia (k <? p * q) true.
  simpl.
  rewrite if_mult_dist_r.
  replace ((i / q =? k mod p) && (k / p =? i mod q)) with 
    (k =? p * (i mod q) + (i/q));
  [reflexivity|]. (* Set this as our new Σ body; NTS the equality we claimed*)
  rewrite eq_iff_eq_true.
  rewrite andb_true_iff, 3!Nat.eqb_eq.
  split.
  - intros ->.
    destruct p; [lia|].
    destruct q; [lia|].
    split.
    + rewrite Nat.add_comm, Nat.mul_comm.
      rewrite Nat.Div0.mod_add by easy.
      rewrite Nat.mod_small; [lia|].
      show_moddy_lt.
    + rewrite Nat.mul_comm, Nat.div_add_l by easy.
      rewrite Nat.div_small; [lia|].
      show_moddy_lt.
  - intros [Hmodp Hdivp].
    rewrite (Nat.div_mod_eq k p).
    lia.
  }
  apply big_sum_unique.
  exists (p * (i mod q) + i / q)%nat; repeat split;
  [apply kron_comm_mx_to_vec_helper; easy | rewrite Nat.eqb_refl | intros; 
  bdestructΩ'simp].
  destruct p; [lia|];
  destruct q; [lia|].
  f_equal.
  - rewrite Nat.add_comm, Nat.mul_comm, Nat.Div0.mod_add, Nat.mod_small; try easy.
    show_moddy_lt.
  - rewrite Nat.mul_comm, Nat.div_add_l by easy. 
    rewrite Nat.div_small; [lia|].
    show_moddy_lt.
Qed.

Lemma kron_comm_mx_to_vec : forall p q (A : Matrix p q),
  kron_comm p q × mx_to_vec A = mx_to_vec (A ⊤).
Proof.
  intros p q A.
  apply mat_equiv_eq; auto with wf_db.
  apply kron_comm_mx_to_vec_mat_equiv.
Qed.

Lemma kron_comm_ei_kron_ei_sum_mat_equiv : forall p q, 
  kron_comm p q ≡
  big_sum (G:=Matrix (p*q) (q*p)) 
  (fun i => big_sum (fun j =>
    (@e_i p i ⊗ @e_i q j) × ((@e_i q j ⊗ @e_i p i) ⊤))
    q) p.
Proof.
  intros p q.
  intros i j Hi Hj.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros l Hl.
  unfold Mmult, kron, transpose, e_i.
  erewrite big_sum_eq_bounded.
  2: {
  intros m Hm.
  (* replace m with O by lia. *)
  rewrite Nat.div_1_r, Nat.mod_1_r.
  replace_bool_lia (m =? 0) true; rewrite 4!andb_true_r.
  rewrite 3!if_mult_and.
  match goal with 
  |- context[if ?b then _ else _] => 
    replace b with ((i =? k * q + l) && (j =? l * p + k))
  end.
  1: reflexivity. (* set our new function *)
  clear dependent m.
  rewrite eq_iff_eq_true, 8!andb_true_iff, 
    6!Nat.eqb_eq, 4!Nat.ltb_lt.
  split.
  - intros [Hieq Hjeq].
    subst i j.
    rewrite 2!Nat.div_add_l, Nat.div_small, Nat.add_0_r by lia.
    rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small, 
    Nat.div_small, Nat.add_0_r by lia.
    rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small by lia.
    easy.
  - intros [[[] []] [[] []]].
    split.
    + rewrite (Nat.div_mod_eq i q) by lia; lia.
    + rewrite (Nat.div_mod_eq j p) by lia; lia.
  }
  simpl; rewrite Cplus_0_l.
  reflexivity.
  }
  apply big_sum_unique.
  exists (i mod q).
  split; [|split].
  - apply Nat.mod_upper_bound; lia.
  - reflexivity.
  - intros l Hl Hnmod.
    bdestructΩ'simp.
    exfalso; apply Hnmod.
    rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small by lia; lia.
  }
  symmetry.
  apply big_sum_unique.
  exists (j mod p).
  repeat split.
  - apply Nat.mod_upper_bound; lia.
  - unfold kron_comm, make_WF.
    replace_bool_lia (i <? p * q) true.
    replace_bool_lia (j <? q * p) true.
    simpl.
    apply f_equal_if; [|easy..].
    rewrite eq_iff_eq_true, 2!andb_true_iff, 4!Nat.eqb_eq.
    split.
    + intros [Hieq Hjeq].
      split; [rewrite Hieq | rewrite Hjeq];
      rewrite Hieq, Nat.div_add_l by lia;
      (rewrite Nat.div_small; [lia|]);
      apply Nat.mod_upper_bound; lia.
    + intros [Hidiv Hjdiv].
      rewrite (Nat.div_mod_eq i q) at 1 by lia.
      rewrite (Nat.div_mod_eq j p) at 2 by lia.
      lia.
  - intros k Hk Hkmod.
    bdestructΩ'simp.
    exfalso; apply Hkmod.
    rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small by lia; lia.
Qed.

Lemma kron_comm_ei_kron_ei_sum : forall p q, 
  kron_comm p q = 
  big_sum (fun i => big_sum (fun j =>
  (@e_i p i ⊗ @e_i q j) × ((@e_i q j ⊗ @e_i p i) ⊤))
   q) p.
Proof.
  intros p q.
  apply mat_equiv_eq; auto 10 with wf_db.
  apply kron_comm_ei_kron_ei_sum_mat_equiv.
Qed.

Lemma kron_comm_ei_kron_ei_sum'_mat_equiv : forall p q, 
  kron_comm p q ≡ 
  big_sum (fun ij =>
  let i := (ij / q)%nat in let j := (ij mod q) in
  ((@e_i p i ⊗ @e_i q j) × ((@e_i q j ⊗ @e_i p i) ⊤))) (p*q).
Proof.
  intros p q.
  rewrite kron_comm_ei_kron_ei_sum, big_sum_double_sum, Nat.mul_comm.
  reflexivity.
Qed.

(* TODO: put somewhere sensible *)
Lemma big_sum_mat_equiv_bounded : forall {o p} (f g : nat -> Matrix o p) (n : nat),
  (forall x : nat, (x < n)%nat -> f x ≡ g x) -> big_sum f n ≡ big_sum g n.
Proof.
  intros.
  induction n.
  - easy.
  - simpl.
    rewrite IHn, H; [easy|lia|auto].
Qed.

Lemma kron_comm_Hij_sum_mat_equiv : forall p q,
  kron_comm p q ≡
  big_sum (fun i => big_sum (fun j =>
  @kron p q q p (@e_i p i × ((@e_i q j) ⊤)) 
  ((@Mmult p 1 q (@e_i p i) (((@e_i q j) ⊤))) ⊤)) q) p.
Proof.
  intros p q.
  rewrite kron_comm_ei_kron_ei_sum_mat_equiv.
  apply big_sum_mat_equiv_bounded; intros i Hi.
  apply big_sum_mat_equiv_bounded; intros j Hj.
  rewrite kron_transpose, kron_mixed_product.
  rewrite Mmult_transpose, transpose_involutive.
  easy.
Qed.

Lemma kron_comm_Hij_sum : forall p q,
  kron_comm p q =
  big_sum (fun i => big_sum (fun j =>
    e_i i × (e_i j) ⊤ ⊗
    (e_i i × (e_i j) ⊤) ⊤) q) p.
Proof.
  intros p q.
  apply mat_equiv_eq; [auto 10 with wf_db.. | ].
  apply kron_comm_Hij_sum_mat_equiv.
Qed.


Lemma kron_comm_ei_kron_ei_sum' : forall p q, 
  kron_comm p q = 
  big_sum (fun ij =>
  let i := (ij / q)%nat in let j := (ij mod q) in
  ((e_i i ⊗ e_i j) × ((e_i j ⊗ e_i i) ⊤))) (p*q).
Proof.
  intros p q.
  rewrite kron_comm_ei_kron_ei_sum, big_sum_double_sum, Nat.mul_comm.
  reflexivity.
Qed.

Local Notation H := (fun i j => e_i i × (e_i j)⊤).

Lemma kron_comm_Hij_sum'_mat_equiv : forall p q,
  kron_comm p q ≡
  big_sum ( fun ij =>
    let i := (ij / q)%nat in let j := (ij mod q) in
    H i j ⊗ (H i j) ⊤) (p*q).
Proof.
  intros p q.
  rewrite kron_comm_Hij_sum_mat_equiv, big_sum_double_sum, Nat.mul_comm.
  easy.
Qed.

Lemma kron_comm_Hij_sum' : forall p q,
  kron_comm p q =
  big_sum (fun ij =>
  let i := (ij / q)%nat in let j := (ij mod q) in
  H i j ⊗ (H i j) ⊤) (p*q).
Proof.
  intros p q.
  rewrite kron_comm_Hij_sum, big_sum_double_sum, Nat.mul_comm.
  easy.
Qed.


Lemma div_eq_iff : forall a b c, b <> O ->
  (a / b)%nat = c <-> (b * c <= a /\ a < b * (S c))%nat.
Proof.
  intros a b c Hb.
  split.
  intros Hadivb.
  split;
  subst c.
  - rewrite (Nat.div_mod_eq a b) at 2; lia.
  - now apply Nat.mul_succ_div_gt.
  - intros [Hge Hlt].
    symmetry.
    apply (Nat.div_unique _ _ _ (a - b*c)); lia.
Qed.

Lemma div_eqb_iff : forall a b c, b <> O ->
  (a / b)%nat =? c = ((b * c <=? a) && (a <? b * (S c))).
Proof.
  intros a b c Hb.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, Nat.leb_le, Nat.ltb_lt, Nat.eqb_eq.
  now apply div_eq_iff.
Qed.


Lemma kron_e_i_transpose_l : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k)⊤ ⊗ A = (fun i j =>
  if (i <? m) && (j / o =? k) then A i (j - k * o)%nat else C0).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_r.
  bdestruct (i <? m).
  - rewrite (Nat.div_small i m),
    (Nat.mod_small i m), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
    replace ((j / o =? k) && (j / o <? n)) with (j / o =? k) by bdestructΩ'simp.
    bdestruct_one; [|easy].
    rewrite mod_eq_sub; f_equal;
    lia.
  - bdestructΩ'simp.
    rewrite Nat.div_small_iff in *; lia.
Qed.

Lemma kron_e_i_transpose_l_mat_equiv : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k)⊤ ⊗ A ≡ (fun i j =>
  if (i <? m) && (j / o =? k) then A i (j - k * o)%nat else 0%R).
Proof.
  intros.
  rewrite kron_e_i_transpose_l; easy.
Qed.

Lemma kron_e_i_transpose_l_mat_equiv' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (@e_i n k)⊤ ⊗ A ≡ (fun i j =>
  if (i <? m) && (j / o =? k) then A i (j - k * o)%nat else 0%R).
Proof.
  intros.
  destruct m; [|destruct o];
  try (intros i j Hi Hj; lia).
  rewrite kron_e_i_transpose_l; easy.
Qed.

Lemma kron_e_i_l : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A = (fun i j =>
  if (j <? o) && (i / m =? k) then A (i - k * m)%nat j else 0%R).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_r.
  bdestruct (j <? o).
  - rewrite (Nat.div_small j o),
    (Nat.mod_small j o), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
    replace ((i / m =? k) && (i / m <? n)) with (i / m =? k) by bdestructΩ'.
    bdestruct_one; [|easy].
    rewrite mod_eq_sub; f_equal;
    lia.
  - bdestructΩ'simp.
    rewrite Nat.div_small_iff in *; lia.
Qed.

Lemma kron_e_i_l_mat_equiv : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A ≡ (fun i j =>
  if (j <? o) && (i / m =? k) then A (i - k * m)%nat j else 0%R).
Proof.
  intros.
  rewrite kron_e_i_l; easy.
Qed.

Lemma kron_e_i_l_mat_equiv' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (@e_i n k) ⊗ A ≡ (fun i j =>
  if (j <? o) && (i / m =? k) then A (i - k * m)%nat j else 0%R).
Proof.
  intros.
  destruct m; [|destruct o];
  try (intros i j Hi Hj; lia).
  rewrite kron_e_i_l; easy.
Qed.

Lemma kron_e_i_transpose_l' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k)⊤ ⊗ A = (fun i j =>
  if (i <? m) && (k * o <=? j) && (j <? (S k) * o) then A i (j - k * o)%nat else 0%R).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_r.
  bdestruct (i <? m).
  - rewrite (Nat.div_small i m), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
  rewrite Nat.mod_small by easy.
  replace ((j / o =? k) && (j / o <? n)) with ((k * o <=? j) && (j <? S k * o)).
  + do 2 bdestruct_one_old; simpl; try easy.
    destruct o; [lia|].
    f_equal.
    rewrite mod_eq_sub, Nat.mul_comm.
    do 2 f_equal.
    rewrite div_eq_iff; lia.
  + rewrite eq_iff_eq_true, 2!andb_true_iff, Nat.eqb_eq, 2!Nat.ltb_lt, Nat.leb_le.
    assert (Hrw: ((j / o)%nat = k /\ (j / o < n)%nat) <-> ((j/o)%nat=k)) by lia;
    rewrite Hrw; clear Hrw.
    symmetry.
    rewrite div_eq_iff by lia.
    lia.
  - replace (i / m =? 0) with false.
  rewrite andb_false_r; easy.
  symmetry.
  rewrite Nat.eqb_neq.
  rewrite Nat.div_small_iff; lia.
Qed.

Lemma kron_e_i_transpose_l'_mat_equiv : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k)⊤ ⊗ A ≡ (fun i j =>
  if (i <? m) && (k * o <=? j) && (j <? (S k) * o) then A i (j - k * o)%nat else 0%R).
Proof.
  intros.
  rewrite kron_e_i_transpose_l'; easy.
Qed.

Lemma kron_e_i_transpose_l'_mat_equiv' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (@e_i n k)⊤ ⊗ A ≡ (fun i j =>
  if (i <? m) && (k * o <=? j) && (j <? (S k) * o) then A i (j - k * o)%nat else 0%R).
Proof.
  intros.
  destruct m; [|destruct o];
  try (intros i j Hi Hj; lia).
  rewrite kron_e_i_transpose_l'; easy.
Qed.

Lemma kron_e_i_l' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A = (fun i j =>
  if (j <? o) && (k * m <=? i) && (i <? (S k) * m) then A (i - k * m)%nat j else 0%R).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, e_i.
  rewrite if_mult_dist_r.
  bdestruct (j <? o).
  - rewrite (Nat.div_small j o), Nat.eqb_refl, andb_true_r, andb_true_l by easy.
  rewrite (Nat.mod_small j o) by easy.
  replace ((i / m =? k) && (i / m <? n)) with ((k * m <=? i) && (i <? S k * m)).
  + do 2 bdestruct_one_old; simpl; try easy.
    destruct m; [lia|].
    f_equal.
    rewrite mod_eq_sub, Nat.mul_comm.
    do 2 f_equal.
    rewrite div_eq_iff; lia.
  + rewrite eq_iff_eq_true, 2!andb_true_iff, Nat.eqb_eq, 2!Nat.ltb_lt, Nat.leb_le.
    assert (Hrw: ((i/m)%nat=k/\(i/m<n)%nat) <-> ((i/m)%nat=k)) by lia;
    rewrite Hrw; clear Hrw.
    symmetry.
    rewrite div_eq_iff by lia.
    lia.
  - replace (j / o =? 0) with false.
  rewrite andb_false_r; easy.
  symmetry.
  rewrite Nat.eqb_neq.
  rewrite Nat.div_small_iff; lia.
Qed.

Lemma kron_e_i_l'_mat_equiv : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A ≡ (fun i j =>
  if (j <? o) && (k * m <=? i) && (i <? (S k) * m) then A (i - k * m)%nat j else 0%R).
Proof.
  intros.
  rewrite kron_e_i_l'; easy.
Qed.

Lemma kron_e_i_l'_mat_equiv' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  (@e_i n k) ⊗ A ≡ (fun i j =>
  if (j <? o) && (k * m <=? i) && (i <? (S k) * m) then A (i - k * m)%nat j else 0%R).
Proof.
  intros.
  destruct m; [|destruct o];
  try (intros i j Hi Hj; lia).
  rewrite kron_e_i_l'; easy.
Qed.  

Lemma kron_e_i_r : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  A ⊗ (@e_i n k) = (fun i j =>
  if (i mod n =? k) then A (i / n)%nat j else 0%R).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, e_i.
  rewrite if_mult_dist_l, Nat.div_1_r.
  rewrite Nat.mod_1_r, Nat.eqb_refl, andb_true_r.
  replace (i mod n <? n) with true;
  [rewrite andb_true_r; easy |].
  symmetry; rewrite Nat.ltb_lt.
  apply Nat.mod_upper_bound; lia.
Qed.

Lemma kron_e_i_r_mat_equiv : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  A ⊗ (@e_i n k) ≡ (fun i j =>
  if (i mod n =? k) then A (i / n)%nat j else 0%R).
Proof.
  intros.
  rewrite kron_e_i_r; easy.
Qed.

Lemma kron_e_i_r_mat_equiv' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  A ⊗ (@e_i n k) ≡ (fun i j =>
  if (i mod n =? k) then A (i / n)%nat j else 0%R).
Proof.
  intros.
  destruct m; [|destruct o];
  try (intros i j Hi Hj; lia).
  rewrite kron_e_i_r; easy.
Qed.

Lemma kron_e_i_transpose_r : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  A ⊗ (@e_i n k) ⊤ = (fun i j =>
  if (j mod n =? k) then A i (j / n)%nat else 0%R).
Proof.
  intros k n m o A Hk Ho Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  unfold kron, transpose, e_i.
  rewrite if_mult_dist_l, Nat.div_1_r.
  rewrite Nat.mod_1_r, Nat.eqb_refl, andb_true_r.
  replace (j mod n <? n) with true;
  [rewrite andb_true_r; easy |].
  symmetry; rewrite Nat.ltb_lt.
  apply Nat.mod_upper_bound; lia.
Qed.

Lemma kron_e_i_transpose_r_mat_equiv : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  (o <> O) -> (m <> O) ->
  A ⊗ (@e_i n k) ⊤ ≡ (fun i j =>
  if (j mod n =? k) then A i (j / n)%nat else 0%R).
Proof.
  intros.
  rewrite kron_e_i_transpose_r; easy.
Qed.

Lemma kron_e_i_transpose_r_mat_equiv' : forall k n m o (A : Matrix m o), (k < n)%nat -> 
  A ⊗ (@e_i n k) ⊤ ≡ (fun i j =>
  if (j mod n =? k) then A i (j / n)%nat else 0%R).
Proof.
  intros.
  destruct m; [|destruct o];
  try (intros i j Hi Hj; lia).
  rewrite kron_e_i_transpose_r; easy.
Qed.

Lemma ei_kron_I_kron_ei : forall m n k, (k < n)%nat -> m <> O ->
  (@e_i n k) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n k) =
  (fun i j => if (i mod n =? k) && (j / m =? k)%nat 
  && (i / n =? j - k * m) && (i / n <? m)
  then 1%R else 0%R).
Proof.
  intros m n k Hk Hm.
  apply functional_extensionality; intros i;
  apply functional_extensionality; intros j.
  rewrite kron_e_i_transpose_l by easy.
  rewrite kron_e_i_r; try lia;
  [| rewrite Nat.mul_eq_0; lia].
  unfold Matrix.I.
  rewrite <- 2!andb_if.
  bdestruct_one_old; [
  rewrite 2!andb_true_r, andb_true_l | rewrite 4!andb_false_r; easy
  ].
  easy.
Qed.

Lemma ei_kron_I_kron_ei_mat_equiv : forall m n k, (k < n)%nat -> m <> O ->
  (@e_i n k) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n k) ≡
  (fun i j => if (i mod n =? k) && (j / m =? k)%nat 
  && (i / n =? j - k * m) && (i / n <? m)
  then 1%R else 0%R).
Proof.
  intros.
  rewrite ei_kron_I_kron_ei; easy.
Qed.

Lemma ei_kron_I_kron_ei_mat_equiv' : forall m n k, (k < n)%nat ->
  (@e_i n k) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n k) ≡
  (fun i j => if (i mod n =? k) && (j / m =? k)%nat 
  && (i / n =? j - k * m) && (i / n <? m)
  then 1%R else 0%R).
Proof.
  intros.
  destruct m; try (intros i j Hi Hj; lia).
  rewrite ei_kron_I_kron_ei; easy.
Qed.

Lemma kron_comm_kron_form_sum_mat_equiv : forall m n,
  kron_comm m n ≡ big_sum (fun j =>
  (@e_i n j) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n j)) n.
Proof.
  intros m n.
  intros i j Hi Hj.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros ij Hij.
  rewrite ei_kron_I_kron_ei by lia.
  reflexivity.
  }
  unfold kron_comm, make_WF.
  do 2 simplify_bools_lia_one_kernel.
  replace (i / n <? m) with true by show_moddy_lt.
  bdestruct_one; [bdestruct_one|]; simpl; symmetry; [
  apply big_sum_unique;
  exists (j / m)%nat;
  split; [ apply Nat.Div0.div_lt_upper_bound; lia | ];
  split; [rewrite (Nat.mul_comm (j / m) m), <- mod_eq_sub by lia; bdestructΩ'|];
  intros k Hk Hkne; bdestructΩ'simp
  | |];
  (rewrite big_sum_0; [easy|]; intros k; bdestructΩ'simp).
  pose proof (mod_eq_sub j m); lia.
Qed.

Lemma kron_comm_kron_form_sum : forall m n,
  kron_comm m n = big_sum 
    (fun j => (@e_i n j) ⊤ ⊗ (Matrix.I m) ⊗ (@e_i n j)) n.
Proof.
  intros m n.
  apply mat_equiv_eq; 
  [|eapply WF_Matrix_dim_change; [lia..|]|];
  [auto with wf_db..|].
  apply kron_comm_kron_form_sum_mat_equiv; easy.
Qed.

Lemma kron_comm_kron_form_sum' : forall m n,
  kron_comm m n = big_sum (fun i =>
  (@e_i m i) ⊗ (Matrix.I n) ⊗ (@e_i m i)⊤) m.
Proof.
  intros.
  rewrite <- (kron_comm_transpose n m).
  rewrite (kron_comm_kron_form_sum n m).
  replace (n * m)%nat with (1 * n * m)%nat by lia.
  replace (m * n)%nat with (m * n * 1)%nat by lia.
  rewrite (Nat.mul_1_r (m * n * 1)).
  etransitivity;
  [apply Msum_transpose|].
  apply big_sum_eq_bounded.
  intros k Hk.
  restore_dims.
  rewrite !kron_transpose.
  now rewrite id_transpose_eq, transpose_involutive.
Qed.

Lemma kron_comm_kron_form_sum'_mat_equiv : forall m n,
  kron_comm m n ≡ big_sum (fun i =>
  (@e_i m i) ⊗ (Matrix.I n) ⊗ (@e_i m i)⊤) m.
Proof.
  intros.
  rewrite kron_comm_kron_form_sum'; easy.
Qed.

Lemma e_i_dot_is_component_mat_equiv : forall p k (x : Vector p),
  (k < p)%nat -> 
  (@e_i p k) ⊤ × x ≡ x k O .* Matrix.I 1.
Proof.
  intros p k x Hk.
  intros i j Hi Hj;
  replace i with O by lia;
  replace j with O by lia;
  clear i Hi;
  clear j Hj.
  unfold Mmult, transpose, scale, e_i, Matrix.I.
  simpl_bools.
  rewrite Cmult_1_r.
  apply big_sum_unique.
  exists k.
  split; [easy|].
  bdestructΩ'simp.
  rewrite Cmult_1_l.
  split; [easy|].
  intros l Hl Hkl.
  bdestructΩ'simp.
Qed.

Lemma e_i_dot_is_component : forall p k (x : Vector p),
  (k < p)%nat -> WF_Matrix x ->
  (@e_i p k) ⊤ × x = x k O .* Matrix.I 1.
Proof.
  intros p k x Hk HWF.
  apply mat_equiv_eq; auto with wf_db.
  apply e_i_dot_is_component_mat_equiv; easy.
Qed.

Lemma kron_e_i_e_i : forall p q k l,
  (k < p)%nat -> (l < q)%nat -> 
  @e_i q l ⊗ @e_i p k = @e_i (p*q) (l*p + k).
Proof.
  intros p q k l Hk Hl.
  apply functional_extensionality; intro i.
  apply functional_extensionality; intro j.
  unfold kron, e_i.
  rewrite Nat.mod_1_r, Nat.div_1_r.
  rewrite if_mult_and.
  apply f_equal_if; [|easy..].
  rewrite Nat.eqb_refl, andb_true_r.
  destruct (j =? 0); [|rewrite 2!andb_false_r; easy].
  rewrite 2!andb_true_r.
  rewrite eq_iff_eq_true, 4!andb_true_iff, 3!Nat.eqb_eq, 3!Nat.ltb_lt.
  split.
  - intros [[] []].
  rewrite (Nat.div_mod_eq i p).
  split; nia.
  - intros [].
  subst i.
  rewrite Nat.div_add_l, Nat.div_small, Nat.add_0_r,
  Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small by lia.
  easy.
Qed.

Lemma kron_e_i_e_i_mat_equiv : forall p q k l,
  (k < p)%nat -> (l < q)%nat -> 
  @e_i q l ⊗ @e_i p k ≡ @e_i (p*q) (l*p + k).
Proof.
  intros p q k l; intros.
  rewrite (kron_e_i_e_i p q); easy.
Qed.

Lemma kron_e_i_e_i_split : forall p q k, (k < p * q)%nat ->
  @e_i (p*q) k = @e_i q (k / p) ⊗ @e_i p (k mod p).
Proof.
  intros p q k Hk.
  rewrite (kron_e_i_e_i p q) by show_moddy_lt.
  rewrite (Nat.div_mod_eq k p) at 1.
  f_equal; lia.
Qed.

Lemma kron_eq_sum_mat_equiv : forall p q (x : Vector q) (y : Vector p),
  y ⊗ x ≡ big_sum (fun ij =>
  let i := (ij / q)%nat in let j := ij mod q in
  (x j O * y i O) .* (@e_i p i ⊗ @e_i q j)) (p * q).
Proof.
  intros p q x y.
  erewrite big_sum_eq_bounded.
  2: {
  intros ij Hij.
  simpl.
  rewrite (@kron_e_i_e_i q p) by 
    (try apply Nat.mod_upper_bound; try apply Nat.Div0.div_lt_upper_bound; lia).
  rewrite (Nat.mul_comm (ij / q) q).
  rewrite <- (Nat.div_mod_eq ij q).
  reflexivity.
  }
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  simpl.
  rewrite Msum_Csum.
  symmetry.
  apply big_sum_unique.
  exists i.
  split; [lia|].
  unfold e_i; split.
  - unfold scale, kron; bdestructΩ'simp.
  - intros j Hj Hij.
    unfold scale, kron; bdestructΩ'simp.
Qed.

Lemma kron_eq_sum : forall p q (x : Vector q) (y : Vector p),
  WF_Matrix x -> WF_Matrix y ->
  y ⊗ x = big_sum (fun ij =>
  let i := (ij / q)%nat in let j := ij mod q in
  (x j O * y i O) .* (@e_i p i ⊗ @e_i q j)) (p * q).
Proof.
  intros p q x y Hwfx Hwfy.
  apply mat_equiv_eq; [| |]; auto with wf_db.
  apply kron_eq_sum_mat_equiv.
Qed.

Lemma kron_comm_commutes_vectors_l_mat_equiv : forall p q (x : Vector q) (y : Vector p),
  kron_comm p q × (x ⊗ y) ≡ (y ⊗ x).
Proof.
  intros p q x y.
  rewrite kron_comm_ei_kron_ei_sum'_mat_equiv, Mmult_Msum_distr_r.

  rewrite (big_sum_mat_equiv_bounded _ 
  (fun k => x (k mod q) 0 * y (k / q) 0 .* (e_i (k / q) ⊗ e_i (k mod q)))%nat);
  [rewrite <- kron_eq_sum_mat_equiv; easy|].
  intros k Hk.
  simpl.
  rewrite Mmult_assoc.
  change 1%nat with (1 * 1)%nat.
  restore_dims.
  rewrite (kron_transpose' (@e_i q (k mod q)) (@e_i p (k / q))). 
  rewrite kron_mixed_product.
  rewrite 2!(e_i_dot_is_component_mat_equiv) by show_moddy_lt.
  rewrite Mscale_kron_dist_l, Mscale_kron_dist_r, Mscale_assoc.
  rewrite kron_1_l, Mscale_mult_dist_r, Mmult_1_r by auto with wf_db.
  reflexivity.
Qed.

Lemma kron_comm_commutes_vectors_l : forall p q (x : Vector q) (y : Vector p),
  WF_Matrix x -> WF_Matrix y ->
  kron_comm p q × (x ⊗ y) = (y ⊗ x).
Proof.
  intros p q x y Hwfx Hwfy.
  apply mat_equiv_eq; auto with wf_db.
  apply kron_comm_commutes_vectors_l_mat_equiv.
Qed.

(* Lemma kron_basis_vector_basis_vector : forall p q k l,
  (k < p)%nat -> (l < q)%nat -> 
  basis_vector q l ⊗ basis_vector p k = basis_vector (p*q) (l*p + k).
Proof.
  intros p q k l Hk Hl.
  apply functional_extensionality; intros i.
  apply functional_extensionality; intros j.
  unfold kron, basis_vector.
  rewrite Nat.mod_1_r, Nat.div_1_r, Nat.eqb_refl, andb_true_r, if_mult_and.
  pose proof (Nat.div_mod_eq i p).
  bdestructΩ'simp.
  rewrite Nat.div_add_l, Nat.div_small in * by lia.
  lia.
Qed.

Lemma kron_basis_vector_basis_vector_mat_equiv : forall p q k l,
  (k < p)%nat -> (l < q)%nat -> 
  basis_vector q l ⊗ basis_vector p k ≡ basis_vector (p*q) (l*p + k).
Proof.
  intros.
  rewrite (kron_basis_vector_basis_vector p q); easy.
Qed. *)

Lemma kron_extensionality_mat_equiv : forall n m s t (A B : Matrix (n*m) (s*t)),
  (forall (x : Vector s) (y :Vector t), 
  A × (x ⊗ y) ≡ B × (x ⊗ y)) ->
  A ≡ B.
Proof.
  intros n m s t A B Hext.
  apply mat_equiv_of_equiv_on_ei.
  intros i Hi.
  
  pose proof (Nat.Div0.div_lt_upper_bound i t s ltac:(lia)).
  pose proof (Nat.mod_upper_bound i s ltac:(lia)).
  pose proof (Nat.mod_upper_bound i t ltac:(lia)).

  specialize (Hext (@e_i s (i / t)) (@e_i t (i mod t))).
  rewrite (kron_e_i_e_i_mat_equiv t s) in Hext by lia.
  rewrite (Nat.mul_comm (i/t) t), <- (Nat.div_mod_eq i t) in Hext.
  rewrite (Nat.mul_comm t s) in Hext. easy.
Qed.

Lemma kron_extensionality : forall n m s t (A B : Matrix (n*m) (s*t)),
  WF_Matrix A -> WF_Matrix B ->
  (forall (x : Vector s) (y :Vector t), 
  WF_Matrix x -> WF_Matrix y ->
  A × (x ⊗ y) = B × (x ⊗ y)) ->
  A = B.
Proof.
  intros n m s t A B HwfA HwfB Hext.
  apply mat_equiv_eq; [auto with wf_db..|].
  apply mat_equiv_of_equiv_on_ei.
  intros k Hk.
  rewrite (Nat.mul_comm s t).
  rewrite (kron_e_i_e_i_split t s) by lia.
  rewrite mat_equiv_eq_iff by 
    auto using WF_Matrix_dim_change with wf_db zarith.
  restore_dims.
  apply Hext; auto with wf_db.
Qed.

Lemma kron_comm_commutes_mat_equiv : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  kron_comm m n × (A ⊗ B) × (kron_comm s t) ≡ (B ⊗ A).
Proof.
  intros n s m t A B.
  apply kron_extensionality_mat_equiv.
  intros x y.
  rewrite (Mmult_assoc (_ × _)).
  rewrite kron_comm_commutes_vectors_l_mat_equiv.
  rewrite Mmult_assoc, kron_mixed_product.
  rewrite kron_comm_commutes_vectors_l_mat_equiv.
  rewrite <- kron_mixed_product.
  easy.
Qed.

Lemma kron_comm_commutes : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  kron_comm m n × (A ⊗ B) × (kron_comm s t) = (B ⊗ A).
Proof.
  intros n s m t A B HwfA HwfB.
  apply kron_extensionality; 
  auto with wf_db. 
  intros x y Hwfx Hwfy.
  rewrite (Mmult_assoc (_ × _)).
  rewrite kron_comm_commutes_vectors_l by easy.
  rewrite Mmult_assoc, kron_mixed_product.
  rewrite kron_comm_commutes_vectors_l by auto with wf_db.
  rewrite <- kron_mixed_product.
  easy.
Qed.

Lemma commute_kron_mat_equiv : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  (A ⊗ B) ≡ kron_comm n m × (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B.
  now rewrite kron_comm_commutes_mat_equiv. 
Qed.

Lemma commute_kron : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  (A ⊗ B) = kron_comm n m × (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B HA HB. 
  now rewrite kron_comm_commutes.
Qed.

Lemma kron_comm_mul_inv_mat_equiv : forall p q,
  kron_comm p q × kron_comm q p ≡ Matrix.I (p * q).
Proof.
  intros p q.
  unfold kron_comm.
  rewrite 2!make_WF_equiv.
  intros i j Hi Hj.
  unfold Mmult.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    rewrite Nat.eqb_sym.
    rewrite Cmult_if_if_1_l.
    replace ((k mod p =? i / q) && (k / p =? i mod q) &&
      ((k / p =? j mod q) && (j / q =? k mod p))) with 
      ((k mod p =? i / q) && (k / p =? i mod q) &&
      ((i mod q =? j mod q) && (i / q =? j / q))) by bdestructΩ'.
    rewrite <- eqb_iff_div_mod_eqb.
    rewrite andb_comm, andb_if.
    reflexivity.
  }
  unfold I.
  simplify_bools_lia_one_kernel.
  bdestructΩ'.
  - apply big_sum_unique.
    exists (j / q + j mod q * p)%nat.
    split; [show_moddy_lt|].
    rewrite Nat.Div0.mod_add, Nat.div_add, (Nat.div_small (_/_)), Nat.add_0_l,
      Nat.mod_small, 2!Nat.eqb_refl
      by lia + show_moddy_lt.
    simpl_bools.
    split; [easy|].
    intros k Hk.
    rewrite <- Nat.eqb_neq.
    rewrite (eqb_iff_div_mod_eqb p).
    rewrite Nat.Div0.mod_add, Nat.div_add, (Nat.div_small (_/_)), Nat.add_0_l,
      Nat.mod_small
      by lia + show_moddy_lt.
    bdestructΩ'.
  - now apply (@big_sum_0 C).
Qed.

Lemma kron_comm_mul_inv : forall p q,
  kron_comm p q × kron_comm q p = Matrix.I _.
Proof.
  intros p q.
  apply mat_equiv_eq; auto with wf_db.
  rewrite kron_comm_mul_inv_mat_equiv; easy.
Qed.

Lemma kron_comm_mul_transpose_r_mat_equiv : forall p q,
  kron_comm p q × (kron_comm p q) ⊤ ≡ Matrix.I _.
Proof.
  intros p q.
  rewrite (kron_comm_transpose p q).
  apply kron_comm_mul_inv_mat_equiv.
Qed.

Lemma kron_comm_mul_transpose_r : forall p q,
  kron_comm p q × (kron_comm p q) ⊤ = Matrix.I _.
Proof.
  intros p q.
  rewrite (kron_comm_transpose p q).
  apply kron_comm_mul_inv.
Qed.

Lemma kron_comm_mul_transpose_l_mat_equiv : forall p q,
  (kron_comm p q) ⊤ × kron_comm p q ≡ Matrix.I _.
Proof.
  intros p q.
  rewrite <- (kron_comm_transpose q p).
  rewrite (transpose_involutive _ _ (kron_comm q p)).
  apply kron_comm_mul_transpose_r_mat_equiv.
Qed.

Lemma kron_comm_mul_transpose_l : forall p q,
  (kron_comm p q) ⊤ × kron_comm p q = Matrix.I _.
Proof.
  intros p q.
  rewrite <- (kron_comm_transpose q p).
  rewrite (transpose_involutive _ _ (kron_comm q p)).
  apply kron_comm_mul_transpose_r.
Qed.

Lemma kron_comm_commutes_l_mat_equiv : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  kron_comm m n × (A ⊗ B) ≡ (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B.
  match goal with |- ?A ≡ ?B =>
    rewrite <- (Mmult_1_r_mat_eq _ _ A), <- (Mmult_1_r_mat_eq _ _ B) 
  end.
  rewrite (Nat.mul_comm t s).
  rewrite <- (kron_comm_mul_transpose_r), <- 2!Mmult_assoc.
  rewrite (kron_comm_commutes_mat_equiv n s m t).
  apply Mmult_simplify_mat_equiv; [|easy].
  rewrite Mmult_assoc.
  restore_dims.
  rewrite (kron_comm_mul_inv_mat_equiv t s), Mmult_1_r_mat_eq.
  easy.
Qed.

Lemma kron_comm_commutes_l : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  kron_comm m n × (A ⊗ B) = (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B HwfA HwfB.
  apply mat_equiv_eq; auto with wf_db.
  apply kron_comm_commutes_l_mat_equiv.
Qed.

Lemma kron_comm_commutes_r_mat_equiv : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  (A ⊗ B) × kron_comm s t ≡ (kron_comm n m) × (B ⊗ A).
Proof.
  intros.
  rewrite kron_comm_commutes_l_mat_equiv; easy.
Qed.

Lemma kron_comm_commutes_r : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  (A ⊗ B) × kron_comm s t = (kron_comm n m) × (B ⊗ A).
Proof.
  intros n s m t A B HA HB.
  rewrite kron_comm_commutes_l; easy.
Qed.
  


(* Lemma kron_comm_commutes_r : forall n s m t 
  (A : Matrix n s) (B : Matrix m t),
  WF_Matrix A -> WF_Matrix B ->
  kron_comm m n × (A ⊗ B) = (B ⊗ A) × (kron_comm t s).
Proof.
  intros n s m t A B HwfA HwfB.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_r _ _ A), <- (Mmult_1_r _ _ B)  ; auto with wf_db
  end.
  rewrite (Nat.mul_comm t s).
  rewrite <- (kron_comm_mul_transpose_r), <- 2!Mmult_assoc.
  rewrite (kron_comm_commutes n s m t) by easy.
  apply Mmult_simplify; [|easy].
  rewrite Mmult_assoc.
  rewrite (Nat.mul_comm s t), (kron_comm_mul_inv t s), Mmult_1_r by auto with wf_db.
  easy.
Qed. *)


Lemma vector_eq_basis_comb_mat_equiv : forall n (y : Vector n),
  y ≡ big_sum (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y.
  intros i j Hi Hj.
  replace j with O by lia; clear j Hj.
  symmetry.
  rewrite Msum_Csum.
  apply big_sum_unique.
  exists i.
  repeat split; try easy.
  - unfold ".*", e_i; bdestructΩ'simp.
  - intros l Hl Hnk.
    unfold ".*", e_i; bdestructΩ'simp.
Qed.


Lemma vector_eq_basis_comb : forall n (y : Vector n),
  WF_Matrix y -> 
  y = big_sum (G:=Vector n) (fun i => y i O .* @e_i n i) n.
Proof.
  intros n y Hwfy.
  apply mat_equiv_eq; auto with wf_db.
  apply vector_eq_basis_comb_mat_equiv.
Qed.

(* Lemma kron_vecT_matrix_vec : forall m n o p
  (P : Matrix m o) (y : Vector n) (z : Vector p),
  WF_Matrix y -> WF_Matrix z -> WF_Matrix P ->
  (z⊤) ⊗ P ⊗ y = @Mmult (m*n) (m*n) (o*p) (kron_comm m n) ((y × (z⊤)) ⊗ P).
Proof.
  intros m n o p P y z Hwfy Hwfz HwfP.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_l _ _ A) ; auto with wf_db
  end.
  rewrite Nat.mul_1_l.
  rewrite <- (kron_comm_mul_transpose_r), Mmult_assoc at 1.
  rewrite Nat.mul_1_r, (Nat.mul_comm o p).
  apply Mmult_simplify; [easy|].
  rewrite kron_comm_kron_form_sum.
  rewrite Msum_transpose.
  rewrite Mmult_Msum_distr_r.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  pose proof (kron_transpose _ _ _ _ ((@e_i n k) ⊤ ⊗ Matrix.I m) (@e_i n k)) as H;
  rewrite Nat.mul_1_l, Nat.mul_1_r, (Nat.mul_comm m n) in *;
  rewrite H; clear H.
  pose proof (kron_transpose _ _ _ _ ((@e_i n k) ⊤) (Matrix.I m)) as H;
  rewrite Nat.mul_1_l in *;
  rewrite H; clear H.
  restore_dims.
  rewrite 2!kron_mixed_product.
  rewrite id_transpose_eq, Mmult_1_l by easy.
  rewrite e_i_dot_is_component, transpose_involutive by easy.
  (* rewrite <- Mmult_transpose. *)
  rewrite Mscale_kron_dist_r, <- 2!Mscale_kron_dist_l.
  rewrite kron_1_r.
  rewrite <- Mscale_mult_dist_l.
  reflexivity.
  }
  rewrite <- (kron_Msum_distr_r n _ P).
  rewrite <- (Mmult_Msum_distr_r).
  rewrite <- vector_eq_basis_comb by easy.
  easy.
Qed. 
*)

Lemma kron_vecT_matrix_vec_mat_equiv : forall m n o p
  (P : Matrix m o) (y : Vector n) (z : Vector p),
  (z⊤) ⊗ P ⊗ y ≡ kron_comm m n × ((y × (z⊤)) ⊗ P).
Proof.
  intros m n o p P y z.
  match goal with |- ?A ≡ ?B =>
  rewrite <- (Mmult_1_l_mat_eq _ _ A)
  end.
  rewrite Nat.mul_1_l.
  rewrite <- (kron_comm_mul_transpose_r_mat_equiv), Mmult_assoc at 1.
  rewrite Nat.mul_1_r. 
  apply Mmult_simplify_mat_equiv; [easy|].
  rewrite kron_comm_kron_form_sum_mat_equiv.
  replace (m * n)%nat with (1 * m * n)%nat by lia.
  replace (n * m)%nat with (n * m * 1)%nat by lia.
  rewrite (Msum_transpose (1*m*n) (n*m*1) n).
  restore_dims.
  rewrite Mmult_Msum_distr_r.
  replace (n * m * 1)%nat with (1 * m * n)%nat by lia.
  replace (p * o)%nat with (p * o * 1)%nat by lia.
  rewrite (Nat.mul_1_r (p * o * 1)).
  erewrite (big_sum_mat_equiv_bounded _ _ n).
  2: {
    intros k Hk.
    unshelve (instantiate (1:=_)).
    refine (fun k : nat => y k 0%nat .* e_i k × (z) ⊤ ⊗ P); exact n.
    pose proof (kron_transpose _ _ _ _ ((@e_i n k) ⊤ ⊗ Matrix.I m) (@e_i n k)) as H;
    rewrite Nat.mul_1_l, Nat.mul_1_r, (Nat.mul_comm m n) in *;
    rewrite H; clear H.
    pose proof (kron_transpose _ _ _ _ ((@e_i n k) ⊤) (Matrix.I m)) as H;
    rewrite Nat.mul_1_l in *;
    rewrite H; clear H.
    restore_dims.
    rewrite 2!kron_mixed_product.
    rewrite (id_transpose_eq m).
    rewrite Mscale_mult_dist_l, transpose_involutive.
    rewrite <- (kron_1_r _ _ P) at 2.
    rewrite Mscale_kron_dist_l, <- !Mscale_kron_dist_r.
    rewrite kron_assoc_mat_equiv.
    restore_dims.
    apply kron_simplify_mat_equiv; [easy|].
    rewrite <- Mscale_kron_dist_r.
    rewrite Mmult_1_l_mat_eq.
    apply kron_simplify_mat_equiv; [easy|].
    rewrite (e_i_dot_is_component_mat_equiv); easy.
  }
  rewrite <- (kron_Msum_distr_r n _ P).
  rewrite <- (Mmult_Msum_distr_r).
  replace (1*m*n)%nat with (n*m)%nat by lia.
  replace (p*o*1)%nat with (p*o)%nat by lia.
  apply kron_simplify_mat_equiv; [|easy].
  apply Mmult_simplify_mat_equiv; [|easy].
  symmetry. 
  apply vector_eq_basis_comb_mat_equiv.
Qed.

Lemma kron_vecT_matrix_vec : forall m n o p
  (P : Matrix m o) (y : Vector n) (z : Vector p),
  WF_Matrix y -> WF_Matrix z -> WF_Matrix P ->
  (z⊤) ⊗ P ⊗ y = kron_comm m n × ((y × (z⊤)) ⊗ P).
Proof.
  intros m n o p P y z Hwfy Hwfz HwfP.
  apply mat_equiv_eq; 
  [|rewrite ?Nat.mul_1_l, ?Nat.mul_1_r; apply WF_mult|]; 
  auto with wf_db.
  apply kron_vecT_matrix_vec_mat_equiv.
Qed.

Lemma kron_vec_matrix_vecT : forall m n o p
  (Q : Matrix n o) (x : Vector m) (z : Vector p),
  WF_Matrix x -> WF_Matrix z -> WF_Matrix Q ->
  x ⊗ Q ⊗ (z⊤) = kron_comm m n × (Q ⊗ (x × z⊤)).
Proof.
  intros m n o p Q x z Hwfx Hwfz HwfQ.
  match goal with |- ?A = ?B =>
  rewrite <- (Mmult_1_l _ _ A) ; auto with wf_db
  end.
  rewrite Nat.mul_1_r.
  rewrite <- (kron_comm_mul_transpose_r), Mmult_assoc at 1.
  rewrite Nat.mul_1_l.
  apply Mmult_simplify; [easy|].
  rewrite kron_comm_kron_form_sum'.
  rewrite (Msum_transpose (m*n) (n*m) m).
  restore_dims.
  rewrite Mmult_Msum_distr_r.
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    restore_dims.
    replace (@transpose (m*n) (n*m)) with
      (@transpose (m*n*1) (1*n*m)) by (f_equal; lia). 
    rewrite kron_transpose.
    rewrite kron_transpose, transpose_involutive.
    restore_dims.
    rewrite 2!kron_mixed_product.
    rewrite id_transpose_eq, Mmult_1_l by easy.
    rewrite e_i_dot_is_component, transpose_involutive by easy.
    rewrite 2!Mscale_kron_dist_l, kron_1_l, <-Mscale_kron_dist_r by easy.
    rewrite <- Mscale_mult_dist_l.
    restore_dims.
    reflexivity.
  }
  erewrite big_sum_eq_bounded.
  2: {
    intros k Hk.
    rewrite transpose_involutive.
    reflexivity.
  }
  rewrite <- (kron_Msum_distr_l m _ Q).
  rewrite <- (Mmult_Msum_distr_r).
  rewrite <- vector_eq_basis_comb by easy.
  easy.
Qed.

Lemma kron_vec_matrix_vecT_mat_equiv : forall m n o p
  (Q : Matrix n o) (x : Vector m) (z : Vector p),
  x ⊗ Q ⊗ (z⊤) ≡ kron_comm m n × (Q ⊗ (x × z⊤)).
Proof.
  intros m n o p Q x z.
  match goal with |- ?A ≡ ?B =>
  rewrite <- (Mmult_1_l_mat_eq _ _ A)
  end.
  rewrite Nat.mul_1_r.
  rewrite <- (kron_comm_mul_transpose_r_mat_equiv), Mmult_assoc at 1.
  rewrite Nat.mul_1_l.
  apply Mmult_simplify_mat_equiv; [easy|].
  rewrite kron_comm_kron_form_sum'.
  replace (@transpose (m*n) (n*m)) with
    (@transpose (m*n*1) (1*n*m)) by (f_equal; lia). 
  rewrite (Msum_transpose (m*n*1) (1*n*m) m).
  restore_dims.
  rewrite Mmult_Msum_distr_r.
  replace (@mat_equiv (n*m) (o*p))
    with (@mat_equiv (m*n*1) (1*o*p)) by (f_equal; lia).
  erewrite (big_sum_mat_equiv_bounded).
  2: {
    intros k Hk.
    unshelve (instantiate (1:=(fun k : nat =>
    @kron n o m p Q
      (@Mmult m 1 p (@scale m 1 (x k 0%nat) (@e_i m k))
          (@transpose p 1 z))))).
    rewrite 2!kron_transpose.
    restore_dims.
    rewrite 2!kron_mixed_product.
    rewrite id_transpose_eq, transpose_involutive.
    rewrite Mscale_mult_dist_l, Mscale_kron_dist_r, <- Mscale_kron_dist_l.
    replace (m*n*1)%nat with (1*n*m)%nat by lia.
    replace (@kron n o m p) with (@kron (1*n) (1*o) m p) by (f_equal; lia).
    apply kron_simplify_mat_equiv; [|easy].
    intros i j Hi Hj.
    unfold kron.
    rewrite (Mmult_1_l_mat_eq _ _ Q) by (apply Nat.mod_upper_bound; lia).
    (* revert i j Hi Hj. *)
    rewrite (e_i_dot_is_component_mat_equiv m k x Hk) by (apply Nat.Div0.div_lt_upper_bound; lia).
    set (a:= (@kron 1 1 n o ((x k 0%nat .* Matrix.I 1)) Q) i j).
    match goal with 
    |- ?A = _ => change A with a
    end.
    unfold a.
    clear a.
    rewrite Mscale_kron_dist_l.
    unfold scale.
    rewrite kron_1_l_mat_equiv by lia.
    easy.
  }
  rewrite <- (kron_Msum_distr_l m _ Q).
  rewrite <- (Mmult_Msum_distr_r).
  rewrite (Nat.mul_comm m n).
  rewrite Nat.mul_1_r, Nat.mul_1_l.
  rewrite <- vector_eq_basis_comb_mat_equiv.
  easy.
Qed.

Lemma kron_comm_triple_cycle_mat : forall m n s t p q (A : Matrix m n)
  (B : Matrix s t) (C : Matrix p q), 
  A ⊗ B ⊗ C ≡ (kron_comm (m*s) p) × (C ⊗ A ⊗ B) × (kron_comm q (t*n)).
Proof.
  intros m n s t p q A B C.
  rewrite (commute_kron_mat_equiv _ _ _ _ (A ⊗ B) C) by auto with wf_db.
  rewrite (Nat.mul_comm n t), (Nat.mul_comm q (t*n)).
  apply Mmult_simplify_mat_equiv; [|easy].
  apply Mmult_simplify_mat_equiv; [easy|].
  rewrite (Nat.mul_comm t n).
  intros i j Hi Hj;
  rewrite <- (kron_assoc_mat_equiv C A B);
  [easy|lia|lia].
Qed.

Lemma kron_comm_triple_cycle : forall m n s t p q (A : Matrix m n)
  (B : Matrix s t) (C : Matrix p q), WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  A ⊗ B ⊗ C = (kron_comm (m*s) p) × (C ⊗ A ⊗ B) × (kron_comm q (t*n)).
Proof.
  intros m n s t p q A B C HA HB HC.
  rewrite (commute_kron _ _ _ _ (A ⊗ B) C) by auto with wf_db.
  rewrite kron_assoc by easy.
  f_equal; try lia; f_equal; lia.
Qed.

Lemma kron_comm_triple_cycle2_mat_equiv : forall m n s t p q (A : Matrix m n)
  (B : Matrix s t) (C : Matrix p q),
  A ⊗ (B ⊗ C) ≡ (kron_comm m (s*p)) × (B ⊗ C ⊗ A) × (kron_comm (q*t) n).
Proof.
  intros m n s t p q A B C.
  rewrite kron_assoc_mat_equiv.
  intros i j Hi Hj.
  rewrite (commute_kron_mat_equiv _ _ _ _ A (B ⊗ C)) by lia.
  rewrite (Nat.mul_comm t q).
  apply Mmult_simplify_mat_equiv; [|easy + lia..].
  apply Mmult_simplify_mat_equiv; [easy|].
  rewrite (Nat.mul_comm q t).
  apply kron_assoc_mat_equiv.
Qed.

Lemma kron_comm_triple_cycle2 : forall m n s t p q (A : Matrix m n)
  (B : Matrix s t) (C : Matrix p q), WF_Matrix A -> WF_Matrix B -> WF_Matrix C ->
  A ⊗ (B ⊗ C) = (kron_comm m (s*p)) × (B ⊗ C ⊗ A) × (kron_comm (q*t) n).
Proof.
  intros m n s t p q A B C HA HB HC.
  apply mat_equiv_eq; [auto using WF_Matrix_dim_change with wf_db zarith..|].
  apply kron_comm_triple_cycle2_mat_equiv.
Qed.






  
Lemma id_eq_sum_kron_e_is_mat_equiv : forall n, 
  Matrix.I n ≡ big_sum (G:=Square n) (fun i => @e_i n i ⊗ (@e_i n i) ⊤) n.
Proof.
  intros n.
  symmetry.
  intros i j Hi Hj.
  rewrite Msum_Csum.
  erewrite big_sum_eq_bounded.
  2: {
  intros k Hk.
  rewrite kron_e_i_l by lia.
  unfold transpose, e_i.
  rewrite <- andb_if.
  replace_bool_lia (j <? n) true.
  rewrite Nat.div_1_r.
  simpl.
  replace ((i =? k) && ((j =? k) && true && (i - k * 1 =? 0)))%nat 
    with ((i =? k) && (j =? k)) by bdestructΩ'.
  reflexivity.
  }
  unfold Matrix.I.
  replace_bool_lia (i <? n) true.
  rewrite andb_true_r.
  bdestruct (i =? j).
  - subst.
  apply big_sum_unique.
  exists j; repeat split; intros; bdestructΩ'.
  - rewrite big_sum_0; [easy|].
  intros k; bdestructΩ'.
Qed.  

Lemma id_eq_sum_kron_e_is : forall n, 
  Matrix.I n = big_sum (G:=Square n) (fun i => @e_i n i ⊗ (@e_i n i) ⊤) n.
Proof.
  intros n.
  apply mat_equiv_eq; auto with wf_db.
  apply id_eq_sum_kron_e_is_mat_equiv.
Qed.

Lemma kron_comm_cycle_indices : forall t s n,
  kron_comm (t*s) n = @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) 
  (kron_comm s (n*t)) (kron_comm t (s*n)).
Proof.
  intros t s n.
  rewrite kron_comm_kron_form_sum.
  erewrite big_sum_eq_bounded.
  2: {
  intros j Hj.
  rewrite (Nat.mul_comm t s), <- id_kron, <- kron_assoc by auto with wf_db.
  restore_dims.
  rewrite kron_assoc by auto with wf_db.
  (* rewrite (kron_assoc ((@e_i n j)⊤ ⊗ Matrix.I t) (Matrix.I s) (@e_i n j)) by auto with wf_db. *)
  lazymatch goal with
  |- ?A ⊗ ?B = _ => rewrite (commute_kron _ _ _ _ A B) by auto with wf_db
  end.
  (* restore_dims. *)
  reflexivity.
  }
  (* rewrite ?Nat.mul_1_r, ?Nat.mul_1_l. *)
  (* rewrite <- Mmult_Msum_distr_r. *)

  rewrite <- (Mmult_Msum_distr_r n _ (kron_comm (t*1) (n*s))).
  rewrite <- Mmult_Msum_distr_l.
  erewrite big_sum_eq_bounded.
  2: {
  intros j Hj.
  rewrite <- kron_assoc, (kron_assoc (Matrix.I t)) by auto with wf_db.
  restore_dims.
  reflexivity.
  } 
  (* rewrite Nat.mul_1_l *)
  rewrite <- (kron_Msum_distr_r n _ (Matrix.I s)).
  rewrite <- (kron_Msum_distr_l n _ (Matrix.I t)).
  rewrite 2!Nat.mul_1_r, 2!Nat.mul_1_l.
  rewrite <- (id_eq_sum_kron_e_is n).
  rewrite 2!id_kron.
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite (Nat.mul_comm t n), (Nat.mul_comm n s).
  easy.
Qed.

Lemma kron_comm_cycle_indices_mat_equiv : forall t s n,
  (kron_comm (t*s) n ≡ @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n))).
Proof.
  intros t s n.
  rewrite kron_comm_cycle_indices; easy.
Qed.

Lemma kron_comm_cycle_indices_rev : forall t s n,
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n)) = kron_comm (t*s) n.
Proof.
  intros. 
  rewrite <- kron_comm_cycle_indices.
  easy.
Qed.

Lemma kron_comm_cycle_indices_rev_mat_equiv : forall t s n,
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n)) ≡ kron_comm (t*s) n.
Proof.
  intros. 
  rewrite <- kron_comm_cycle_indices.
  easy.
Qed.

Lemma kron_comm_triple_id : forall t s n, 
  (kron_comm (t*s) n) × (kron_comm (s*n) t) × (kron_comm (n*t) s) = Matrix.I (t*s*n).
Proof.
  intros t s n.
  rewrite kron_comm_cycle_indices.
  restore_dims.
  rewrite (Mmult_assoc (kron_comm s (n*t))).
  restore_dims.
  rewrite (kron_comm_mul_inv t (s*n)).
  restore_dims.
  rewrite Mmult_1_r by auto with wf_db.
  rewrite (kron_comm_mul_inv).
  f_equal; lia.
Qed.

Lemma kron_comm_triple_id_mat_equiv : forall t s n, 
  (kron_comm (t*s) n) × (kron_comm (s*n) t) × (kron_comm (n*t) s) ≡ Matrix.I (t*s*n).
Proof.
  intros t s n.
  setoid_rewrite kron_comm_triple_id; easy.
Qed.

Lemma kron_comm_triple_id' : forall n t s, 
  (kron_comm n (t*s)) × (kron_comm t (s*n)) × (kron_comm s (n*t)) = Matrix.I (t*s*n).
Proof.
  intros n t s.
  apply transpose_matrices.
  rewrite 2!Mmult_transpose.
  rewrite (kron_comm_transpose s (n*t)).
  rewrite (kron_comm_transpose n (t*s)).
  restore_dims.
  rewrite (Nat.mul_assoc s n t), <- (Nat.mul_assoc t s n).

  rewrite (kron_comm_transpose t (s*n)).
  rewrite Nat.mul_assoc. 
  replace (t*(s*n))%nat with (n*t*s)%nat by lia.
  rewrite id_transpose_eq.
  replace (n*t*s)%nat with (t*n*s)%nat by lia.
  rewrite <- (kron_comm_triple_id t n s).
  rewrite Mmult_assoc.
  restore_dims.
  replace (s*(t*n))%nat with (s*(n*t))%nat by lia.
  replace (n*(t*s))%nat with (n*(s*t))%nat by lia.
  replace (n*t*s)%nat with (t*n*s)%nat by lia.
  apply Mmult_simplify; [f_equal; lia|].
  repeat (f_equal; try lia).
Qed.

Lemma kron_comm_triple_id'_mat_equiv : forall t s n, 
  (kron_comm n (t*s)) × (kron_comm t (s*n)) × (kron_comm s (n*t)) = Matrix.I (t*s*n).
Proof.
  intros t s n.
  rewrite (kron_comm_triple_id' n t s).
  easy.
Qed.

Lemma kron_comm_triple_id'C : forall n t s, 
  (kron_comm n (s*t)) × (kron_comm t (n*s)) × (kron_comm s (t*n)) = Matrix.I (t*s*n).
Proof.
  intros n t s.
  rewrite <- (kron_comm_triple_id' n t s).
  rewrite (Nat.mul_comm s t), (Nat.mul_comm n s), 
    (Nat.mul_comm t n).
  easy.
Qed.

Lemma kron_comm_triple_id'C_mat_equiv : forall n t s, 
  (kron_comm n (s*t)) × (kron_comm t (n*s)) × (kron_comm s (t*n)) ≡ Matrix.I (t*s*n).
Proof.
  intros n t s.
  rewrite <- (kron_comm_triple_id'C n t s).
  easy.
Qed.

Lemma kron_comm_triple_indices_collapse_mat_equiv : forall s n t, 
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n))
   ≡ (kron_comm (t*s) n).
Proof.
  intros s n t.
  rewrite <- (Mmult_1_r_mat_eq _ _ (_ × _)).
  (* replace (t*(s*n))%nat with (n*(t*s))%nat by lia. *)
  rewrite <- (kron_comm_mul_inv_mat_equiv).
  rewrite <- Mmult_assoc.
  (* restore_dims. *)
  pose proof (kron_comm_triple_id'C s t n) as Hrw.
  apply (f_equal (fun A => A × kron_comm (t*s) n)) in Hrw.
  replace (t*n*s)%nat with (t*s*n)%nat in Hrw by lia.
  restore_dims in Hrw.
  rewrite (Mmult_1_l _ _ (kron_comm (t*s) n)) in Hrw by auto with wf_db.
  rewrite <- Hrw.
  rewrite !Mmult_assoc.
  restore_dims.
  replace (n*(t*s))%nat with (t*(s*n))%nat by lia.
  apply Mmult_simplify_mat_equiv; [easy|].
  replace (n*t*s)%nat with (t*(s*n))%nat by lia.
  apply Mmult_simplify_mat_equiv; [easy|].
  restore_dims.
  rewrite 2!kron_comm_mul_inv.
  now replace (t*(s*n))%nat with (n*(t*s))%nat by lia.
Qed.

Lemma kron_comm_triple_indices_collapse : forall s n t, 
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n))
   = (kron_comm (t*s) n).
Proof.
  intros s n t.
  apply mat_equiv_eq; 
  [restore_dims; apply WF_Matrix_dim_change; [lia..|]..|];
  auto 10 using WF_Matrix_dim_change with wf_db zarith.
  apply kron_comm_triple_indices_collapse_mat_equiv.
Qed.

Lemma kron_comm_triple_indices_collapse_mat_equivC : forall s n t, 
  @Mmult (s*(t*n)) (s*(t*n)) (t*(n*s)) (kron_comm s (t*n)) (kron_comm t (n*s))
   ≡ (kron_comm (t*s) n).
Proof.
  intros s n t.
  rewrite (Nat.mul_comm t n), (Nat.mul_comm n s).
  rewrite kron_comm_triple_indices_collapse_mat_equiv.
  easy.
Qed.

Lemma kron_comm_triple_indices_collapseC : forall s n t, 
  @Mmult (s*(t*n)) (s*(t*n)) (t*(n*s)) (kron_comm s (t*n)) (kron_comm t (n*s))
   = (kron_comm (t*s) n).
Proof.
  intros s n t.
  apply mat_equiv_eq; 
  [restore_dims; apply WF_Matrix_dim_change; [lia..|]..|];
  auto 10 using WF_Matrix_dim_change with wf_db zarith.
  apply kron_comm_triple_indices_collapse_mat_equivC.
Qed.

(* 
Not sure what this is, or if it's true:
Lemma kron_comm_triple_indices_commute : forall t s n,
  @Mmult (s*t*n) (s*t*n) (t*(s*n)) (kron_comm (s*t) n) (kron_comm t (s*n)) = 
  @Mmult (t*(s*n)) (t*(s*n)) (s*t*n) (kron_comm t (s*n)) (kron_comm (s*t) n). *)
Lemma kron_comm_triple_indices_commute_mat_equiv : forall t s n,
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n)) ≡
  @Mmult (t*(s*n)) (t*(s*n)) (s*(n*t)) (kron_comm t (s*n)) (kron_comm s (n*t)).
Proof.
  intros t s n.
  rewrite kron_comm_triple_indices_collapse_mat_equiv.
  rewrite (Nat.mul_comm t s).
  rewrite <- (kron_comm_triple_indices_collapseC t n s).
  easy.
Qed.

Lemma kron_comm_triple_indices_commute : forall t s n,
  @Mmult (s*(n*t)) (s*(n*t)) (t*(s*n)) (kron_comm s (n*t)) (kron_comm t (s*n)) =
  @Mmult (t*(s*n)) (t*(s*n)) (s*(n*t)) (kron_comm t (s*n)) (kron_comm s (n*t)).
Proof.
  intros t s n.
  apply mat_equiv_eq; 
  [restore_dims; apply WF_Matrix_dim_change; [lia..|]..|];
  auto 10 using WF_Matrix_dim_change with wf_db zarith.
  apply kron_comm_triple_indices_commute_mat_equiv.
Qed.

Lemma kron_comm_triple_indices_commute_mat_equivC : forall t s n,
  @Mmult (s*(t*n)) (s*(t*n)) (t*(n*s)) (kron_comm s (t*n)) (kron_comm t (n*s)) ≡
  @Mmult (t*(s*n)) (t*(s*n)) (s*(n*t)) (kron_comm t (s*n)) (kron_comm s (n*t)).
Proof.
  intros t s n.
  rewrite (Nat.mul_comm t n), (Nat.mul_comm n s).
  apply kron_comm_triple_indices_commute_mat_equiv.
Qed.

Lemma kron_comm_triple_indices_commuteC : forall t s n,
  @Mmult (s*(t*n)) (s*(t*n)) (t*(n*s)) (kron_comm s (t*n)) (kron_comm t (n*s)) =
  @Mmult (t*(s*n)) (t*(s*n)) (s*(n*t)) (kron_comm t (s*n)) (kron_comm s (n*t)).
Proof.
  intros t s n.
  rewrite (Nat.mul_comm t n), (Nat.mul_comm n s).
  apply kron_comm_triple_indices_commute.
Qed.

Lemma kron_comm_kron_of_mult_commute1_mat_equiv : forall m n p q s t
  (A : Matrix m n) (B : Matrix p q) (C : Matrix q s) (D : Matrix n t),
  @mat_equiv (m*p) (s*t) ((kron_comm m p) × ((B × C) ⊗ (A × D))) 
  ((A ⊗ B) × kron_comm n q × (C ⊗ D)).
Proof.
  intros m n p q s t A B C D.
  rewrite <- kron_mixed_product.
  rewrite (Nat.mul_comm p m), <- Mmult_assoc.
  rewrite kron_comm_commutes_r_mat_equiv.
  match goal with (* TODO: Make a lemma *)
  |- ?A ≡ ?B => enough (H : A = B) by (rewrite H; easy)
  end.
  repeat (f_equal; try lia).
Qed.

Lemma kron_comm_kron_of_mult_commute2_mat_equiv : forall m n p q s t
  (A : Matrix m n) (B : Matrix p q) (C : Matrix q s) (D : Matrix n t),
  ((A ⊗ B) × kron_comm n q × (C ⊗ D)) ≡ (A × D ⊗ (B × C)) × kron_comm t s.
Proof.
  intros m n p q s t A B C D.
  rewrite Mmult_assoc, kron_comm_commutes_l_mat_equiv, <-Mmult_assoc,
  <- kron_mixed_product.
  easy.
Qed.

Lemma kron_comm_kron_of_mult_commute3_mat_equiv : forall m n p q s t
  (A : Matrix m n) (B : Matrix p q) (C : Matrix q s) (D : Matrix n t),
  (A × D ⊗ (B × C)) × kron_comm t s ≡ 
  (Matrix.I m) ⊗ (B × C) × kron_comm m s × (Matrix.I s ⊗ (A × D)).
Proof.
  intros m n p q s t A B C D.
  rewrite <- 2!kron_comm_commutes_l_mat_equiv, Mmult_assoc.
  restore_dims.
  rewrite kron_mixed_product. 
  rewrite Mmult_1_r_mat_eq, Mmult_1_l_mat_eq.
  easy.
Qed.

Lemma kron_comm_kron_of_mult_commute4_mat_equiv : forall m n p q s t
  (A : Matrix m n) (B : Matrix p q) (C : Matrix q s) (D : Matrix n t),
  @mat_equiv (m*p) (s*t) 
  ((Matrix.I m) ⊗ (B × C) × kron_comm m s × (Matrix.I s ⊗ (A × D)))
  ((A × D) ⊗ (Matrix.I p) × kron_comm t p × ((B × C) ⊗ Matrix.I t)).
Proof.
  intros m n p q s t A B C D.
  rewrite <- 2!kron_comm_commutes_l_mat_equiv, 2!Mmult_assoc.
  restore_dims.
  rewrite 2!kron_mixed_product. 
  rewrite (Nat.mul_comm m p), 2!Mmult_1_r_mat_eq.
  rewrite 2!Mmult_1_l_mat_eq.
  easy.
Qed.