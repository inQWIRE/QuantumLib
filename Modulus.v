(** Some lemmas about nats, especially about div and mod *)

Require Import Prelim.

(** * Automation extending that in Prelim *)

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

Ltac replace_bool_lia b0 b1 :=
  first [
    replace b0 with b1 by (bdestruct b0; lia || (destruct b1 eqn:?; lia)) |
    replace b0 with b1 by (bdestruct b1; lia || (destruct b0 eqn:?; lia)) |
    replace b0 with b1 by (bdestruct b0; bdestruct b1; lia)
  ].

Ltac simpl_bools :=
  repeat (cbn [andb orb negb xorb]; 
  rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r). 

Ltac simplify_bools_lia_one_free :=
  let act_T b := ((replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := ((replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_one_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_many_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_lia b true || replace_bool_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_lia b false || replace_bool_lia b true); simpl) in 
  multimatch goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; simpl negb
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools.

Ltac simplify_bools_lia_one :=
  simplify_bools_lia_one_kernel || simplify_bools_lia_one_free.

Ltac simplify_bools_lia :=
  repeat simplify_bools_lia_one.

Ltac bdestruct_one_old := 
  let fail_if_iffy H :=
  match H with
  | context [ if _ then _ else _ ] => fail 1
  | _ => idtac
  end
  in
  match goal with
  | |- context [ ?a <? ?b ] =>
      fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ ?a =? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b)
  | |- context [ if ?b then _ else _ ] => fail_if_iffy b; destruct b eqn:?
  end.

Ltac bdestruct_one_new :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_booley H := 
    fail_if_iffy H;
    match H with
    | context [ ?a <? ?b   ] => fail 1
    | context [ ?a <=? ?b  ] => fail 1
    | context [ ?a =? ?b   ] => fail 1
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | context [ negb ?a    ] => fail 1
    | context [ xorb ?a ?b ] => fail 1
    | _ => idtac
    end
  in 
  let rec destruct_kernel H :=
    match H with
    | context [ if ?b then _ else _ ] => destruct_kernel b
    | context [ ?a <? ?b   ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a <? b)
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a <=? ?b  ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a <=? b)
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a =? ?b   ] => 
      tryif fail_if_booley a then 
      (tryif fail_if_booley b then bdestruct (a =? b); try subst
       else destruct_kernel b) else (destruct_kernel a)
    | context [ ?a && ?b   ] => 
      destruct_kernel a || destruct_kernel b
    | context [ ?a || ?b   ] => 
      destruct_kernel a || destruct_kernel b
    | context [ xorb ?a ?b ] => 
      destruct_kernel a || destruct_kernel b
    | context [ negb ?a    ] =>
      destruct_kernel a
    | _ => idtac
    end
  in 
  simpl_bools;
  match goal with
  | |- context [ ?a =? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a =? b); try subst
  | |- context [ ?a <? ?b ] =>
      fail_if_iffy a; fail_if_iffy b; bdestruct (a <? b)
  | |- context [ ?a <=? ?b ] =>
        fail_if_iffy a; fail_if_iffy b; bdestruct (a <=? b)
  | |- context [ if ?b then _ else _ ] => fail_if_iffy b; destruct b eqn:?
  end;
  simpl_bools.

Ltac bdestruct_one' := bdestruct_one_new || bdestruct_one_old.

Ltac bdestructΩ'_with tac :=
  tac;
  repeat (bdestruct_one'; subst; simpl_bools; tac); 
  tac.

(* Ltac bdestructΩ'simp :=
  bdestructΩ'_with ltac:(try easy + lca + lia). *)




Lemma pow2_nonzero n : 2 ^ n <> 0.
Proof.
  apply Nat.pow_nonzero; lia.
Qed.

Ltac show_term_nonzero term :=
  match term with
  | 2 ^ ?a => exact (pow2_nonzero a)
  | ?a ^ ?b => exact (Nat.pow_nonzero a b ltac:(show_term_nonzero a))
  | ?a * ?b => 
    (assert (a <> 0) by (show_term_nonzero a);
    assert (b <> 0) by (show_term_nonzero b);
    lia)
  | ?a + ?b => 
    ((assert (a <> 0) by (show_term_nonzero a) ||
    assert (b <> 0) by (show_term_nonzero b));
    lia)
  | _ => lia
  | _ => nia
  end.

Ltac show_nonzero :=
  match goal with
  | |- ?t <> 0 => show_term_nonzero t
  | |- 0 <> ?t => symmetry; show_term_nonzero t
  | |- 0 < ?t => assert (t <> 0) by (show_term_nonzero t); lia
  | |- ?t > 0 => assert (t <> 0) by (show_term_nonzero t); lia
  | _ => lia
  end.

Ltac get_div_by_pow_2 t pwr :=
  match t with
  | 2 ^ pwr => constr:(1)
  | 2 ^ pwr * ?a => constr:(a)
  | ?a * 2 ^ pwr => constr:(a)
  | ?a * ?b => let ra := get_div_by_pow_2 a pwr in constr:(ra * b)
  | ?a * ?b => let rb := get_div_by_pow_2 b pwr in constr:(a * rb)
  | 2 ^ (?a + ?b) => 
    let val := constr:(2 ^ a * 2 ^ b) in 
    get_div_by_pow_2 val pwr
  | ?a + ?b => 
    let ra := get_div_by_pow_2 a pwr in 
    let rb := get_div_by_pow_2 b pwr in 
    constr:(ra + rb)
  | ?a - 1 => 
    let ra := get_div_by_pow_2 a pwr in 
    constr:(ra - 1)
  end.

Lemma div_mul_l a b : a <> 0 -> 
  (a * b) / a = b.
Proof.
  rewrite Nat.mul_comm;
  apply Nat.div_mul.
Qed.


Ltac show_div_by_pow2_ge t pwr :=
  (* Shows t / 2 ^ pwr <= get_div_by_pwr t pwr *)
  match t with
  | 2 ^ pwr => (* constr:(1) *)
    rewrite (Nat.div_same (2^pwr) (pow2_nonzero pwr));
    apply Nat.le_refl
  | 2 ^ pwr * ?a => (* constr:(a) *)
    rewrite (div_mul_l (2^pwr) a (pow2_nonzero pwr));
    apply Nat.le_refl
  | ?a * 2 ^ pwr => (* constr:(a) *)
    rewrite (Nat.div_mul a (2^pwr) (pow2_nonzero pwr));
    apply Nat.le_refl
  | ?a * (?b * ?c) => 
    let rval := constr:(a * b * c) in 
    show_div_by_pow2_ge rval pwr
  | ?a * ?b => (* b is not right, so... *)
    let rval := constr:(b * a) in 
    show_div_by_pow2_ge rval pwr
  | ?a + ?b => 
    let ra := get_div_by_pow_2 a pwr in 
    let rb := get_div_by_pow_2 b pwr in 
    constr:(ra + rb)
  | ?a - 1 => 
    fail 1 "Case not supported"
  | 2 ^ (?a + ?b) => 
    let val := constr:(2 ^ a * 2 ^ b) in 
    rewrite (Nat.pow_add_r 2 a b);
    show_div_by_pow2_ge val pwr
  
  end.


Ltac get_div_by t val :=
  match t with
  | val => constr:(1)
  | val * ?a => constr:(a)
  | ?a * val => constr:(a)
  | ?a * ?b => let ra := get_div_by a val in constr:(ra * b)
  | ?a * ?b => let rb := get_div_by b val in constr:(a * rb)
  | 2 ^ (?a + ?b) => 
    let val' := constr:(2 ^ a * 2 ^ b) in 
    get_div_by val' val
  | ?a + ?b => 
    let ra := get_div_by a val in 
    let rb := get_div_by b val in 
    constr:(ra + rb)
  | ?a - 1 => 
    let ra := get_div_by a val in 
    constr:(ra - 1)
  end.

Ltac show_div_by_ge t val :=
  (* Shows t / val <= get_div_by t val *)
  match t with
  | val => (* constr:(1) *)
    rewrite (Nat.div_same val ltac:(show_term_nonzero val));
    apply Nat.le_refl
  | val * ?a => (* constr:(a) *)
    rewrite (div_mul_l val a ltac:(show_term_nonzero val));
    apply Nat.le_refl
  | ?a * val => (* constr:(a) *)
    rewrite (Nat.div_mul a val ltac:(show_term_nonzero val));
    apply Nat.le_refl
  | ?a * (?b * ?c) => 
    let rval := constr:(a * b * c) in 
    show_div_by_ge rval val
  | ?a * ?b => (* b is not right, so... *)
    let rval := constr:(b * a) in 
    show_div_by_ge rval val
  | ?a + ?b => 
    let ra := get_div_by a val in 
    let rb := get_div_by b val in 
    constr:(ra + rb)
  | ?a - 1 => 
    nia ||
    fail 1 "Case not supported"
  end.

Ltac get_strict_upper_bound term :=
  match term with
  | ?k mod 0 => let r := get_strict_upper_bound k in constr:(r)
  | ?k mod (2 ^ ?a) => constr:(Nat.pow 2 a)
  | ?k mod (?a ^ ?b) => constr:(Nat.pow a b)
  | ?k mod ?a => 
    let _ := match goal with |- _ => assert (H: a <> 0) by show_nonzero end in
    constr:(a)
  | ?k mod ?a => 
    let _ := match goal with |- _ => assert (H: a = 0) by lia end in
    constr:(k + 1)
  
  | 2 ^ ?a * ?t => let r := get_strict_upper_bound t in 
    constr:(Nat.mul (Nat.pow 2 a) r)
  | ?t * 2 ^ ?a => let r := get_strict_upper_bound t in 
    constr:(Nat.mul r (Nat.pow 2 a))
  | ?a ^ ?b => constr:(Nat.pow a b + 1)

  | ?a + ?b => 
      let ra := get_strict_upper_bound a in 
      let rb := get_strict_upper_bound b in 
      constr:(ra + rb + 1)
  | ?a * ?b => 
      let ra := get_strict_upper_bound a in 
      let rb := get_strict_upper_bound b in 
      constr:(ra * rb + 1)
  | ?a / (?b * (?c * ?d)) => let rval := constr:(a / (b * c * d)) in
    let r := get_strict_upper_bound rval in constr:(r)
  | ?a / (?b * ?c) => let rval := constr:(a / b / c) in
    let r := get_strict_upper_bound rval in constr:(r)
  | ?a / (2 ^ ?b) => 
    let ra := get_strict_upper_bound a in 
    let rr := get_div_by_pow_2 ra b in constr:(rr)

  | ?t => match goal with
    | H : t < ?a |- _ => constr:(a)
    | H : t <= ?a |- _ => constr:(a + 1)
    | _ => constr:(t + 1)
    end
  end.

Ltac get_upper_bound term :=
  match term with
  | ?k mod 0 => let r := get_upper_bound k in constr:(r)
  | ?k mod (2 ^ ?a) => constr:(Nat.sub (Nat.pow 2 a) 1)
  | ?k mod (?a ^ ?b) => constr:(Nat.sub (Nat.pow a b) 1)
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a <> 0) by show_nonzero; clear H end in
    constr:(a - 1)
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a = 0) by lia; clear H end in
    let rk := get_upper_bound k in
    constr:(rk)
  
  | 2 ^ ?a * ?t => let r := get_upper_bound t in 
    constr:(Nat.mul (Nat.pow 2 a) r)
  | ?t * 2 ^ ?a => let r := get_upper_bound t in 
    constr:(Nat.mul r (Nat.pow 2 a))
  | ?a ^ ?b => constr:(Nat.pow a b)

  | ?a + ?b => 
      let ra := get_upper_bound a in 
      let rb := get_upper_bound b in 
      constr:(ra + rb)
  | ?a * ?b => 
      let ra := get_upper_bound a in 
      let rb := get_upper_bound b in 
      constr:(ra * rb)
  | ?a / (?b * (?c * ?d)) => let rval := constr:(a / (b * c * d)) in
    let r := get_upper_bound rval in constr:(r)
  | ?a / (?b * ?c) => let rval := constr:(a / b / c) in
    let r := get_upper_bound rval in constr:(r)
  | ?a / (2 ^ ?b) => 
    let ra := get_strict_upper_bound a in 
    let rr := get_div_by_pow_2 ra b in constr:(rr - 1)

  | ?a / ?b =>
    let ra := get_strict_upper_bound a in 
    let rr := get_div_by ra b in constr:(rr - 1)

  | ?t => match goal with
    | H : t < ?a |- _ => constr:(a - 1)
    | H : t <= ?a |- _ => constr:(a)
    | _ => t
    end
  end.

Lemma mul_ge_l_of_nonzero p q : q <> 0 ->
  p <= p * q.
Proof.
  nia.
Qed.

Lemma mul_ge_r_of_nonzero p q : p <> 0 ->
  q <= p * q.
Proof.
  nia.
Qed.

Ltac show_pow2_le :=
  rewrite ?Nat.pow_add_r, 
  ?Nat.mul_add_distr_r, ?Nat.mul_add_distr_l,
  ?Nat.mul_sub_distr_r, ?Nat.mul_sub_distr_l,
  ?Nat.mul_1_r, ?Nat.mul_1_l;
  repeat match goal with
  |- context [2 ^ ?a] => 
    tryif assert (2 ^ a <> 0) by assumption 
    then fail 
    else pose proof (pow2_nonzero a)
  end;
  nia || (
  repeat match goal with
  | |- context [?p * ?q] => 
    tryif assert (p <> 0) by assumption 
    then 
      (tryif assert (q <> 0) by assumption 
      then fail 
      else assert (q <> 0) by nia)
    else assert (p <> 0) by nia;
      (tryif assert (q <> 0) by assumption 
      then idtac else assert (q <> 0) by nia)
  end;
  repeat match goal with
  | |- context [?p * ?q] => 
    tryif assert (p <= p * q) by assumption 
    then 
      (tryif assert (q <= p * q) by assumption 
      then fail 
      else pose proof (mul_ge_r_of_nonzero p q ltac:(assumption)))
    else pose proof (mul_ge_l_of_nonzero p q ltac:(assumption));
      (tryif assert (q <= p * q) by assumption 
      then idtac
      else pose proof (mul_ge_r_of_nonzero p q ltac:(assumption)))
  end;
  nia).


Lemma lt_of_le_sub_1 a b : 
  b <> 0 -> a <= b - 1 -> a < b.
Proof. lia. Qed.

Lemma le_sub_1_of_lt a b : 
  a < b -> a <= b - 1.
Proof. lia. Qed.

(* FIXME: TODO: Remove in favor of Nat.Div0.div_le_mono when we upgrade past Coq ~8.16*)
Lemma div0_div_le_mono : forall a b c : nat, a <= b -> a / c <= b / c.
Proof.
  intros a b []; [easy|].
  apply Nat.div_le_mono; easy.
Qed.

Lemma div0_div_lt_upper_bound : forall a b c : nat, a < b * c -> 
  a / b < c.
Proof.
  intros a b c H; apply Nat.div_lt_upper_bound; lia.
Qed.

Lemma div0_div_div : forall a b c, a / b / c = a / (b * c).
Proof.
  intros a [] []; [rewrite ?Nat.mul_0_r; easy..|].
  now apply Nat.div_div.
Qed.

Lemma nat_mod_0_r : forall a, a mod 0 = a.
Proof. easy. Qed.

Lemma div0_mod_0_l : forall a, 0 mod a = 0.
Proof.
  intros []; [easy|];
  now apply Nat.mod_0_l.
Qed.

Lemma div0_mod_add : forall a b c, (a + b * c) mod c = a mod c.
Proof.
  intros a b []; [f_equal; lia|];
  now apply Nat.mod_add.
Qed.

Lemma div0_mod_mul_r : forall a b c, 
  a mod (b * c) = a mod b + b * ((a / b) mod c).
Proof. 
  intros a [] []; rewrite ?Nat.mul_0_r, ?Nat.mul_0_l, 
    ?nat_mod_0_r; [lia..| pose proof (Nat.div_mod_eq a (S n)); lia |].
  now apply Nat.mod_mul_r.
Qed.

Lemma div0_mod_mod : forall a n, (a mod n) mod n = a mod n.
Proof.
  intros a []; [easy|]; now apply Nat.mod_mod.
Qed.

Lemma div0_mod_mul : forall a b, (a * b) mod b = 0.
Proof.
  intros a []; [cbn;lia|];
  now apply Nat.mod_mul.
Qed.

Lemma div0_add_mod_idemp_l : forall a b n : nat, 
  (a mod n + b) mod n = (a + b) mod n.
Proof.
  intros a b []; [easy|]; now apply Nat.add_mod_idemp_l.
Qed.

Lemma div0_add_mod : forall a b n, 
  (a + b) mod n = (a mod n + b mod n) mod n.
Proof.
  intros a b []; [easy|];
  now apply Nat.add_mod.
Qed.

Lemma div0_mod_same : forall n, 
  n mod n = 0.
Proof.
  intros []; [easy|]; now apply Nat.mod_same.
Qed.

Lemma div0_div_0_l : forall n, 0 / n = 0.
Proof. intros []; easy. Qed.

Notation "Nat.Div0.div_le_mono" := div0_div_le_mono.
Notation "Nat.Div0.div_lt_upper_bound" := div0_div_lt_upper_bound.
Notation "Nat.Div0.div_div" := div0_div_div.
Notation "Nat.mod_0_r" := nat_mod_0_r.
Notation "Nat.Div0.div_0_l" := div0_div_0_l.
Notation "Nat.Div0.mod_0_l" := div0_mod_0_l.
Notation "Nat.Div0.mod_add" := div0_mod_add.
Notation "Nat.Div0.mod_same" := div0_mod_same.
Notation "Nat.Div0.mod_mul_r" := div0_mod_mul_r.
Notation "Nat.Div0.mod_mod" := div0_mod_mod.
Notation "Nat.Div0.mod_mul" := div0_mod_mul.
Notation "Nat.Div0.add_mod" := div0_add_mod.
Notation "Nat.Div0.add_mod_idemp_l" := div0_add_mod_idemp_l.


Ltac show_le_upper_bound term :=
  lazymatch term with
  | ?k mod 0 => 
    rewrite (Nat.mod_0_r k);
    show_le_upper_bound k
  | ?k mod (2 ^ ?a) => 
    exact (le_sub_1_of_lt (k mod (2^a)) (2^a)
      (Nat.mod_upper_bound k (2^a) (pow2_nonzero a)))
  | ?k mod (?a ^ ?b) => 
    exact (le_sub_1_of_lt (k mod (2^a)) (a^b)
      (Nat.mod_upper_bound k (a^b) 
      (Nat.pow_nonzero a b ltac:(show_term_nonzero a))))
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a <> 0) by show_nonzero end in
    exact (le_sub_1_of_lt _ _ (Nat.mod_upper_bound k a H))
  | ?k mod ?a => 
    let H := fresh in 
    let _ := match goal with |- _ => 
      assert (H: a = 0) by lia end in
    rewrite H;
    show_le_upper_bound k
  
  | 2 ^ ?a * ?t => let r := get_upper_bound t in 
    apply (Nat.mul_le_mono_l t _ (2^a));
    show_le_upper_bound t
  | ?t * 2 ^ ?a => let r := get_upper_bound t in 
    apply (Nat.mul_le_mono_r t _ (2^a));
    show_le_upper_bound t
  | ?a ^ ?b => 
    apply Nat.le_refl

  | ?a + ?b => 
    apply Nat.add_le_mono;
    [
     (* match goal with |- ?G => idtac G "should be about" a end;  *)
     show_le_upper_bound a | 
     show_le_upper_bound b]
  | ?a * ?b => 
    apply Nat.mul_le_mono;
    [
     (* match goal with |- ?G => idtac G "should be about" a end;  *)
     show_le_upper_bound a | 
     show_le_upper_bound b]
  | ?a / (?b * (?c * ?d)) => 
    let H := fresh in 
    pose proof (f_equal (fun x => a / x) (Nat.mul_assoc b c d) :
      a / (b * (c * d)) = a / (b * c * d)) as H;
    rewrite H;
    clear H;
    let rval := constr:(a / (b * c * d)) in
    show_le_upper_bound rval
  | ?a / (?b * ?c) => 
    let H := fresh in 
    pose proof (eq_sym (Nat.Div0.div_div a b c) :
      a / (b * c) = a / b / c) as H;
    rewrite H;
    clear H;
    let rval := constr:(a / b / c) in
    show_le_upper_bound rval
  | ?a / (2 ^ ?b) => 
    let ra := get_upper_bound a in
    apply (Nat.le_trans (a / (2^b)) (ra / (2^b)) _);
    [apply Nat.Div0.div_le_mono;
     show_le_upper_bound a | 
     tryif show_div_by_pow2_ge ra b then idtac 
     else 
     match goal with
     | |- (?val - 1) / 2 ^ ?pwr <= ?rhs - 1 =>
      apply le_sub_1_of_lt, Nat.Div0.div_lt_upper_bound;
      tryif nia || show_pow2_le then idtac 
      else fail 20 "nia failed" "on (" val "- 1) / 2 ^" pwr "<=" rhs "- 1"
     | |- ?G =>
      tryif nia then idtac else 
     fail 40 "show div failed for" a "/ (2^" b "), ra =" ra 
      "; full goal:" G 
     end]
  | ?a / ?b =>
    let ra := get_upper_bound a in
    apply (Nat.le_trans (a / b) (ra / b) _);
    [apply Nat.Div0.div_le_mono;
     show_le_upper_bound a | 
     tryif show_div_by_ge ra b then idtac 
     else 
     match goal with
     | |- (?val - 1) / ?den <= ?rhs - 1 =>
      apply le_sub_1_of_lt, Nat.Div0.div_lt_upper_bound;
      tryif nia || show_pow2_le then idtac 
      else fail 20 "nia failed" "on (" val "- 1) / " den "<=" rhs "- 1"
     | |- ?G =>
      tryif nia then idtac else 
     fail 40 "show div failed for" a "/ (" b "), ra =" ra 
      "; full goal:" G 
     end]
  | ?t => match goal with
    | _ => nia
    end
  end.

Create HintDb show_moddy_lt_db.

Ltac show_moddy_lt :=
  try trivial with show_moddy_lt_db;
  lazymatch goal with
  | |- Nat.b2n ?b < ?a =>
    apply (Nat.le_lt_trans (Nat.b2n b) (2^1) a);
    [destruct b; simpl; lia | show_pow2_le]
  | |- ?a < ?b =>
    let r := get_upper_bound a in
    apply (Nat.le_lt_trans a r b);
    [show_le_upper_bound a | show_pow2_le]
  | |- ?a <= ?b => (* Likely not to work *)
    let r := get_upper_bound a in
    apply (Nat.le_trans a r b);
    [show_le_upper_bound a | show_pow2_le]
  | |- ?a > ?b => 
    change (b < a); show_moddy_lt
  | |- ?a >= ?b => 
    change (b <= a); show_moddy_lt
  | |- (?a <? ?b) = true =>
    apply (proj2 (Nat.ltb_lt a b));
    show_moddy_lt
  | |- true = (?a <? ?b) =>
    symmetry;
    apply (proj2 (Nat.ltb_lt a b));
    show_moddy_lt
  | |- (?a <=? ?b) = false =>
    apply (proj2 (Nat.leb_gt a b));
    show_moddy_lt
  | |- false = (?a <=? ?b) =>
    symmetry;
    apply (proj2 (Nat.leb_gt a b));
    show_moddy_lt
  end.

Ltac try_show_moddy_lt := 
  try trivial with show_moddy_lt_db;
  lazymatch goal with
  | |- Nat.b2n ?b < ?a =>
    apply (Nat.le_lt_trans (Nat.b2n b) (2^1) a);
    [destruct b; simpl; lia | try show_pow2_le]
  | |- ?a < ?b =>
    let r := get_upper_bound a in
    apply (Nat.le_lt_trans a r b);
    [try show_le_upper_bound a | try show_pow2_le]
  | |- ?a <= ?b => (* Likely not to work *)
    let r := get_upper_bound a in
    apply (Nat.le_trans a r b);
    [try show_le_upper_bound a | try show_pow2_le]
  | |- ?a > ?b => 
    change (b < a); try_show_moddy_lt
  | |- ?a >= ?b => 
    change (b <= a); try_show_moddy_lt
  | |- (?a <? ?b) = true =>
    apply (proj2 (Nat.ltb_lt a b));
    try_show_moddy_lt
  | |- true = (?a <? ?b) =>
    symmetry;
    apply (proj2 (Nat.ltb_lt a b));
    try_show_moddy_lt
  | |- (?a <=? ?b) = false =>
    apply (proj2 (Nat.leb_gt a b));
    try_show_moddy_lt
  | |- false = (?a <=? ?b) =>
    symmetry;
    apply (proj2 (Nat.leb_gt a b));
    try_show_moddy_lt
  end.

Ltac replace_bool_moddy_lia b0 b1 :=
  first
    [ replace b0 with b1
      by (show_moddy_lt || bdestruct b0; show_moddy_lt + lia 
        || (destruct b1 eqn:?; lia))
    | replace b0 with b1
      by (bdestruct b1; lia || (destruct b0 eqn:?; lia))
    | replace b0 with b1
      by (bdestruct b0; bdestruct b1; lia) ].

Ltac simpl_bools_nosimpl :=
  repeat (rewrite ?andb_true_r, ?andb_false_r, ?orb_true_r, ?orb_false_r,
    ?andb_true_l, ?andb_false_l, ?orb_true_l, ?orb_false_l).

Ltac simplify_bools_moddy_lia_one_kernel :=
  let fail_if_iffy H :=
    match H with
    | context [ if _ then _ else _ ] => fail 1
    | _ => idtac
    end
  in
  let fail_if_compound H := 
    fail_if_iffy H;
    match H with
    | context [ ?a && ?b   ] => fail 1
    | context [ ?a || ?b   ] => fail 1
    | _ => idtac
    end
  in 
  let act_T b := (fail_if_compound b; 
    (replace_bool_moddy_lia b true 
    || replace_bool_moddy_lia b false); simpl) in 
  let act_F b := (fail_if_compound b; 
    (replace_bool_moddy_lia b false 
    || replace_bool_moddy_lia b true); simpl) in 
  match goal with
  | |- context[?b && _] => act_F b; rewrite ?andb_true_l, ?andb_false_l
  | |- context[_ && ?b] => act_F b; rewrite ?andb_true_r, ?andb_false_r
  | |- context[?b || _] => act_T b; rewrite ?orb_true_l, ?orb_false_l
  | |- context[_ || ?b] => act_T b; rewrite ?orb_true_r, ?orb_false_r
  | |- context[negb ?b] => act_T b; cbn [negb]
  | |- context[if ?b then _ else _] => act_T b
  end; simpl_bools_nosimpl.

(** * Some general nat facts *)

Section nat_lemmas.

Import Nat.

Local Open Scope nat.

Lemma add_sub' n m : m + n - m = n.
Proof.
  lia.
Qed.

Lemma add_leb_mono_l n m d : 
  (n + m <=? n + d) = (m <=? d).
Proof.
  bdestructΩ'.
Qed.

Lemma add_ltb_mono_l n m d : 
  (n + m <? n + d) = (m <? d).
Proof.
  bdestructΩ'.
Qed.

Lemma geb_0 n : 0 <=? n = true.
Proof.
  bdestructΩ'.
Qed.

Lemma add_le_cancel_l_iff n m d : 
  n + m <= n + d <-> m <= d.
Proof. lia. Qed.

Lemma add_lt_cancel_l_iff n m d : 
  n + m < n + d <-> m < d.
Proof. lia. Qed.

Lemma add_ge_cancel_l_iff n m d : 
  n + m >= n + d <-> m >= d.
Proof. lia. Qed.

Lemma add_gt_cancel_l_iff n m d : 
  n + m > n + d <-> m > d.
Proof. lia. Qed.

Lemma sub_lt_iff n m p (Hp : 0 <> p) : 
  n - m < p <-> n < m + p.
Proof.
  split; lia.
Qed.

Lemma sub_eq_iff {a b m} : b <= a ->
  a - b = m <-> a = b + m.
Proof.
  lia.
Qed.

Lemma n_le_pow_2_n (n : nat) : n <= 2 ^ n.
Proof. 
  induction n; simpl; [lia|].
  pose proof (pow_positive 2 n).
  lia.
Qed.

Lemma div_mul_not_exact a b : b <> 0 -> 
  (a / b) * b = a - (a mod b).
Proof.
  intros Hb.
  rewrite (Nat.div_mod a b Hb) at 1 2.
  rewrite Nat.add_sub.
  rewrite (Nat.mul_comm b (a/b)), Nat.add_comm, Nat.div_add by easy.
  rewrite Nat.div_small by (apply Nat.mod_upper_bound; easy).
  easy.
Qed.

Lemma diff_divs_lower_bound a b k n : 
  (a < n -> b < n -> a / k <> b / k -> k < n)%nat.
Proof.
  intros Ha Hb Hne.
  bdestructΩ (k <? n).
  exfalso; apply Hne.
  now rewrite 2!Nat.div_small by lia.
Qed.

Lemma mod_div a b : a mod b / b = 0.
Proof.
  destruct b; [easy|].
  apply Nat.div_small, Nat.mod_upper_bound; easy.
Qed.

Lemma div_mod : forall (x y z : nat), (x / y) mod z = (x mod (y * z)) / y.
Proof.
  intros. 
  bdestruct (y =? 0); [subst; simpl; now rewrite Nat.Div0.mod_0_l|].
  rewrite Nat.Div0.mod_mul_r, Nat.mul_comm, Nat.div_add by easy.
  now rewrite mod_div.
Qed.

Lemma sub_mul_mod : forall x y z,
  y * z <= x ->
  (x - y * z) mod z = x mod z.
Proof.
  intros. 
  replace (x mod z) with ((x - y * z + y * z) mod z) by (f_equal; lia).
  now rewrite Nat.Div0.mod_add.
Qed.

Lemma mod_product : forall x y z, x mod (y * z) mod z = x mod z.
Proof.
  intros.
  rewrite Nat.mul_comm, Nat.Div0.mod_mul_r, Nat.mul_comm.
  now rewrite Nat.Div0.mod_add, Nat.Div0.mod_mod.
Qed.

Lemma mod_add_l a b c : (a * b + c) mod b = c mod b.
Proof.
  rewrite Nat.add_comm.
  apply Nat.Div0.mod_add.
Qed.

Lemma div_eq a b : a / b = (a - a mod b) / b.
Proof.
  rewrite (Nat.div_mod_eq a b) at 2.
  rewrite Nat.add_sub.
  bdestruct (b =? 0).
  - now subst.
  - now rewrite Nat.mul_comm, Nat.div_mul by easy.
Qed.

Lemma sub_mod_le n m : m <= n ->
  (n - m mod n) mod n = (n - m) mod n.
Proof.
  intros Hm.
  bdestruct (m =? n).
  - subst.
    now rewrite Nat.Div0.mod_same, Nat.sub_0_r, Nat.sub_diag,
      Nat.Div0.mod_same, Nat.Div0.mod_0_l.
  - now rewrite (Nat.mod_small m) by lia.
Qed.

Lemma mod_mul_sub_le a b c : c <> 0 -> a <= b * c -> 
  (b * c - a) mod c = 
  c * Nat.b2n (¬ a mod c =? 0) - a mod c.
Proof.
  intros Hc Ha.
  bdestruct (a =? b * c).
  - subst.
    rewrite Nat.sub_diag, Nat.Div0.mod_mul, Nat.Div0.mod_0_l.
    cbn; lia.
  - rewrite (Nat.div_mod_eq a c) at 1.
    assert (a < b * c) by lia.
    assert (a / c < b) by (apply Nat.Div0.div_lt_upper_bound; lia).
    assert (a mod c < c) by show_moddy_lt.
    replace (b * c - (c * (a / c) + a mod c)) with 
      ((b - a / c - 1) * c + (c - a mod c)) by nia.
    rewrite mod_add_l.
    bdestruct (a mod c =? 0).
    + replace -> (a mod c).
      rewrite Nat.sub_0_r, Nat.Div0.mod_same.
      cbn; lia.
    + rewrite Nat.mod_small by lia.
      cbn; lia.
Qed. 

Lemma div_sub a b c : c <> 0 -> 
  (b * c - a) / c = b - a / c - Nat.b2n (¬ a mod c =? 0).
Proof.
  intros Hc.
  bdestruct (a <? b * c); cycle 1.
  - replace (b * c - a) with 0 by lia.
    rewrite Nat.Div0.div_0_l.
    pose proof (Nat.div_le_lower_bound a c b); lia.
  - assert (a / c < b) by show_moddy_lt.
    apply (Nat.mul_cancel_r _ _ c Hc).
    rewrite div_mul_not_exact by easy.
    rewrite 2!Nat.mul_sub_distr_r.
    rewrite div_mul_not_exact by easy.
    pose proof (Nat.mod_le (b * c - a) c Hc).
    pose proof (Nat.mod_le a c Hc).
    enough (a + (b * c - a) mod c = 
      (a + c * Nat.b2n (¬ a mod c =? 0) - a mod c))
      by lia.
    rewrite <- Nat.add_sub_assoc by 
      (pose proof (Nat.mod_upper_bound a c Hc);
      bdestructΩ'; cbn; lia).
    f_equal.
    apply mod_mul_sub_le; lia.
Qed.

Lemma min_ltb n m : min n m = if n <? m then n else m.
Proof.
  bdestructΩ'.
Qed.

Lemma eqb_iff_div_mod_eqb a i j : 
  i =? j =
  (i mod a =? j mod a) && (i / a =? j / a).
Proof.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; [intros ->; easy|].
  intros.
  rewrite (Nat.div_mod_eq i a), (Nat.div_mod_eq j a).
  lia.
Qed.

Lemma eqb_comb_iff_div_mod_eqb a i x y (Hy : y < a) :
  i =? x * a + y =
  (i mod a =? y) && (i / a =? x).
Proof.
  rewrite (eqb_iff_div_mod_eqb a). 
  rewrite mod_add_l, Nat.div_add_l, 
    (Nat.mod_small y), (Nat.div_small y) by lia.
  now rewrite Nat.add_0_r.
Qed.

Lemma eqb_div_mod_pow_2_iff a i j k l : 
  i mod 2 ^ a + 2 ^ a * j =? k mod 2 ^ a + 2 ^ a * l  =
  ((i mod 2 ^ a =? k mod 2 ^ a) && 
  (j =? l)).
Proof.
  apply eq_iff_eq_true.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split; try lia.
  rewrite 2!(Nat.mul_comm (2^a)).
  intros H.
  generalize (f_equal (fun x => x mod 2^a) H).
  rewrite 2!Nat.Div0.mod_add, !Nat.Div0.mod_mod.
  intros; split; [easy|].
  generalize (f_equal (fun x => x / 2^a) H).
  now rewrite 2!Nat.div_add, !Nat.div_small by 
    (try apply Nat.mod_upper_bound; try apply pow_nonzero; lia).
Qed.

Lemma succ_even_lt_even a b : Nat.even a = true -> 
  Nat.even b = true ->
  a < b -> S a < b.
Proof.
  intros Ha Hb Hab.
  enough (S a <> b) by lia.
  intros Hf.
  apply (f_equal Nat.even) in Hf.
  rewrite Nat.even_succ in Hf.
  rewrite <- Nat.negb_even in Hf.
  rewrite Ha, Hb in Hf.
  easy.
Qed.

Lemma succ_odd_lt_odd a b : Nat.odd a = true -> 
  Nat.odd b = true ->
  a < b -> S a < b.
Proof.
  intros Ha Hb Hab.
  enough (S a <> b) by lia.
  intros Hf.
  apply (f_equal Nat.even) in Hf.
  rewrite Nat.even_succ in Hf.
  rewrite <- Nat.negb_odd in Hf.
  rewrite Ha, Hb in Hf.
  easy.
Qed.

Lemma even_add_same n : Nat.even (n + n) = true.
Proof.
  now rewrite Nat.even_add, eqb_reflx.
Qed.

Lemma even_succ_false n : 
  Nat.even (S n) = false <-> Nat.even n = true.
Proof.
  rewrite Nat.even_succ, <- Nat.negb_even. 
  now destruct (Nat.even n).
Qed.

Lemma even_succ_add_same n : Nat.even (S (n + n)) = false.
Proof.
  now rewrite even_succ_false, even_add_same.
Qed.

Lemma odd_succ_false n : 
  Nat.odd (S n) = false <-> Nat.odd n = true.
Proof.
  rewrite Nat.odd_succ, <- Nat.negb_odd. 
  now destruct (Nat.odd n).
Qed.

Lemma even_le_even_of_le_succ m n 
  (Hm : Nat.even m = true) (Hn : Nat.even n = true) : 
  (n <= S m -> n <= m)%nat.
Proof.
  intros Hnm.
  bdestructΩ (n =? S m).
  replace -> n in Hn.
  rewrite Nat.even_succ, <- Nat.negb_even in Hn.
  now rewrite Hm in Hn.
Qed.

Lemma even_eqb n : Nat.even n = (n mod 2 =? 0).
Proof.
  rewrite (Nat.div_mod_eq n 2) at 1.
  rewrite Nat.even_add, Nat.even_mul.
  cbn [Nat.even orb].
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)).
  now destruct ((ltac:(lia) : n mod 2 = O \/ n mod 2 = 1%nat)) as
    [-> | ->].
Qed.

Lemma mod_2_succ n : (S n) mod 2 = 1 - (n mod 2).
Proof.
  pose proof (Nat.mod_upper_bound (S n) 2 ltac:(lia)).
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)).
  enough (~ (S n mod 2 = 0) <-> n mod 2 = 0) by lia.
  rewrite <- Nat.eqb_neq, <- Nat.eqb_eq.
  rewrite <- 2!even_eqb.
  apply even_succ_false.
Qed.

Lemma double_add n m : n + m + (n + m) = n + n + (m + m).
Proof.
  lia.
Qed.

Lemma sub_leb_eq n m p : 
  n - m <=? p = (n <=? m + p).
Proof.
  bdestructΩ'.
Qed.

Lemma sub_ltb_eq_nonzero n m p : p <> 0 ->
  n - m <? p = (n <? m + p).
Proof.
  intros.
  bdestructΩ'.
Qed.

Lemma sub_ltb_eq_le n m p : m <= n ->
  n - m <? p = (n <? m + p).
Proof.
  intros.
  bdestructΩ'.
Qed.

Lemma sum_ne_pows_2_lt_pow_2_S n k l : 
  k < n -> l < n -> k <> l -> 
  2^k + 2^l < 2 ^ n.
Proof.
  intros.
  bdestruct (2^k + 2^l <? 2^n); [easy|].
  destruct n; [easy|].
  simpl in *; rewrite Nat.add_0_r in *.
  pose proof (Nat.pow_le_mono_r 2 k n).
  pose proof (Nat.pow_le_mono_r 2 l n).
  assert (Heq: 2^k = 2^l) by lia.
  apply (f_equal Nat.log2) in Heq.
  rewrite 2!Nat.log2_pow2 in Heq; lia.
Qed.

Lemma sub_S_sub_S n k : k < n -> 
  n - S (n - S k) = k.
Proof.
  lia.
Qed.


Lemma div_mod_inj {a b} (c :nat) : c > 0 ->
  (a mod c) = (b mod c) /\ (a / c) = (b / c) -> a = b.
Proof.
  intros Hc.
  intros [Hmod Hdiv].
  rewrite (Nat.div_mod_eq a c).
  rewrite (Nat.div_mod_eq b c).
  rewrite Hmod, Hdiv.
  easy.
Qed.

Lemma mod_add_n_r : forall m n, 
  (m + n) mod n = m mod n.
Proof.
  intros m n.
  replace (m + n)%nat with (m + 1 * n)%nat by lia.
  destruct n.
  - cbn; easy.
  - now rewrite Nat.Div0.mod_add.
Qed.

Lemma mod_eq_sub : forall m n,
  m mod n = (m - n * (m / n))%nat.
Proof.
  intros m n.
  destruct n.
  - cbn; lia.
  - pose proof (Nat.div_mod m (S n)).
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
  - pose proof (Nat.Div0.div_lt_upper_bound m n (S q)).
    lia.
Qed.

Lemma mod_n_to_2n : forall m n, 
  (n <= m < 2 * n)%nat -> m mod n = (m - n)%nat.
Proof.
  intros.
  pose proof (mod_of_scale m n 1).
  lia.
Qed.

Lemma mod_n_to_n_plus_n : forall m n, 
  (n <= m < n + n)%nat -> m mod n = (m - n)%nat.
Proof.
  intros.
  apply mod_n_to_2n; lia.
Qed.

(** Lemmas about Nat.testbit *)

Lemma testbit_add_pow2_small (i j s n : nat) (Hs : s < n) : 
  Nat.testbit (i + 2^n * j) s = Nat.testbit i s.
Proof.
  rewrite 2!Nat.testbit_eqb.
  replace n with (s + (n - s)) by lia.
  rewrite Nat.pow_add_r, <- Nat.mul_assoc, Nat.mul_comm, Nat.div_add by
    (apply Nat.pow_nonzero; lia).
  destruct (n - s) eqn:e; [lia|].
  cbn [Nat.pow].
  rewrite <- Nat.mul_assoc, Nat.mul_comm, Nat.Div0.mod_add by lia.
  easy.
Qed.

Lemma testbit_add_pow2_large (i j s n : nat) (Hs : n <= s) (Hi : i < 2^n) : 
  Nat.testbit (i + 2^n * j) s = Nat.testbit j (s - n).
Proof.
  replace s with (s-n + n) at 1 by lia.
  generalize (s - n) as d.
  intros d.
  rewrite 2!Nat.testbit_eqb.
  do 2 f_equal.
  rewrite Nat.pow_add_r, (Nat.mul_comm _ (2^_)), Nat.mul_comm,
    <- Nat.Div0.div_div, Nat.div_add by
    (apply Nat.pow_nonzero; lia).
  rewrite (Nat.div_small i) by easy.
  easy.
Qed.

Lemma testbit_add_pow2_split i j n (Hi : i < 2^n) : 
  forall s, 
  Nat.testbit (j * 2 ^ n + i) s =
  if s <? n then Nat.testbit i s else Nat.testbit j (s - n).
Proof.
  intros.
  rewrite Nat.add_comm, Nat.mul_comm.
  bdestruct (s <? n).
  - apply testbit_add_pow2_small; easy.
  - apply testbit_add_pow2_large; easy.
Qed.

Lemma mod_2_pow_S i n : 
  i mod 2^(S n) = 2^n * (Nat.b2n (Nat.testbit i n)) + (i mod (2^n)).
Proof.
  enough (Hmod : i mod 2^(S n) = 
    (2^n * (Nat.b2n (Nat.testbit i n)) + (i mod (2^n))) mod 2^(S n)).
  - rewrite (Nat.mod_small (_ + _)) in Hmod; [easy|].
    simpl.
    pose proof (Nat.mod_upper_bound i (2^n) 
      ltac:(apply Nat.pow_nonzero; lia)).
    destruct (Nat.testbit i n); simpl; lia.
  - rewrite Nat.pow_succ_r by lia.
    symmetry.
    rewrite (Nat.mul_comm 2 (2^n)).
    rewrite 2!Nat.Div0.mod_mul_r.
    rewrite Nat.mul_comm, (Nat.add_comm (_ * _)).
    pose proof (Nat.pow_nonzero 2 n ltac:(lia)).
    rewrite Nat.Div0.mod_add, Nat.Div0.mod_mod, Nat.div_add by easy.
    rewrite Nat.div_small by (now apply Nat.mod_upper_bound).
    do 2 f_equal.
    rewrite Nat.testbit_eqb.
    bdestructΩ'; simpl Nat.b2n.
    simpl Nat.add.
    rewrite Nat.Div0.mod_0_l.
    pose proof (Nat.mod_upper_bound (i / 2 ^ n) 2 ltac:(lia)).
    lia.
Qed.

Lemma mod_pow2_eq_closed_down i j n m : n <= m -> 
  i mod 2^m = j mod 2^m -> i mod 2^n = j mod 2^n.
Proof.
  intros Hnm Heq.
  replace m with (n + (m - n)) in * by lia.
  generalize dependent (m - n).
  intros k _.
  rewrite Nat.pow_add_r, 2!Nat.Div0.mod_mul_r.
  intros H.
  apply (f_equal (fun k => k mod 2^n)) in H.
  revert H.
  rewrite 2!(Nat.mul_comm (2^n)).
  rewrite 2!Nat.Div0.mod_add, 2!Nat.Div0.mod_mod.
  easy.
Qed.

Lemma bits_inj_upto i j n : 
  (forall s, s < n -> Nat.testbit i s = Nat.testbit j s) <->
  i mod 2^n = j mod 2^n.
Proof.
  split.
  - intros Heq.
    induction n;
    [now rewrite 2!Nat.mod_1_r|].
    rewrite 2!mod_2_pow_S.
    f_equal; [|apply IHn; intros k Hk; apply Heq; lia].
    rewrite Heq by lia.
    easy.
  - intros Heq s Hs.
    rewrite 2!Nat.testbit_eqb.
    rewrite (Nat.div_mod i (2^(S s)) ltac:(apply Nat.pow_nonzero; lia)).
    rewrite (Nat.div_mod j (2^(S s)) ltac:(apply Nat.pow_nonzero; lia)).
    rewrite (mod_pow2_eq_closed_down i j (S s) n ltac:(lia) Heq).
    rewrite 2!(Nat.mul_comm (2^ S s)), 2!(Nat.add_comm (_*_)).
    rewrite Nat.pow_succ_r by lia.
    rewrite 2!Nat.mul_assoc.
    rewrite 2!Nat.div_add by (apply Nat.pow_nonzero; lia).
    rewrite 2!Nat.Div0.mod_add.
    easy.
Qed.

Lemma lt_pow2_S_log2 i : i < 2 ^ S (Nat.log2 i).
Proof.
  destruct i; [cbn; lia|].
  apply Nat.log2_spec; lia.
Qed.

Lemma bits_inj_upto_small i j n (Hi : i < 2^n) (Hj : j < 2^n) : 
  (forall s, s < n -> Nat.testbit i s = Nat.testbit j s) <->
  i = j.
Proof.
  split; [|intros ->; easy].
  intros H; apply bits_inj_upto in H.
  assert (H2n : 2^n <> 0) by (apply Nat.pow_nonzero; lia).
  rewrite (Nat.div_mod i (2^n) H2n), (Nat.div_mod j (2^n) H2n).
  rewrite 2!Nat.div_small, Nat.mul_0_r by lia.
  easy.
Qed.

Lemma bits_inj i j : 
  (forall s, Nat.testbit i s = Nat.testbit j s) <-> i = j.
Proof.
  split; [|intros ->; easy].
  set (ub := 2^ max (S (Nat.log2 i)) (S (Nat.log2 j))).
  assert (Hi : i < ub) by 
    (enough (i < 2 ^ (S (Nat.log2 i))) by
    (pose proof (Nat.pow_le_mono_r 2 (S (Nat.log2 i)) _ 
      ltac:(easy) (Nat.le_max_l _ (S (Nat.log2 j)))); lia);
    apply lt_pow2_S_log2).
  assert (Hj : j < ub) by 
    (enough (j < 2 ^ (S (Nat.log2 j))) by
    (pose proof (Nat.pow_le_mono_r 2 (S (Nat.log2 j)) _ 
      ltac:(easy) (Nat.le_max_r (S (Nat.log2 i)) _)); lia);
    apply lt_pow2_S_log2).
  intros s.
  apply (bits_inj_upto_small i j _ Hi Hj).
  intros; easy.
Qed.

Lemma testbit_make_gap i m k s : 
  Nat.testbit (i mod 2^m + (i/2^m) * 2^k * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  if s <? k + m then false else
  Nat.testbit i (s - k).
Proof.
  rewrite Nat.add_comm.
  rewrite testbit_add_pow2_split by 
    (apply Nat.mod_upper_bound, Nat.pow_nonzero; easy).
  bdestructΩ'.
  - apply (proj2 (bits_inj_upto _ _ m) (Nat.Div0.mod_mod i _) s H).
  - rewrite Nat.testbit_eqb.
    replace k with ((k - (s-m) - 1 + 1) + (s-m)) by lia.
    rewrite 2!Nat.pow_add_r, Nat.mul_assoc, Nat.div_mul by
      (now apply Nat.pow_nonzero).
    change (2^1) with 2.
    now rewrite Nat.mul_assoc, Nat.Div0.mod_mul.
  - replace (s - m) with (s - m - k + k) by lia.
    rewrite Nat.mul_pow2_bits_add, Nat.div_pow2_bits.
    f_equal; lia.
Qed.

Lemma testbit_make_2_gap i m s : 
  Nat.testbit (i mod 2^m + (i/2^m) * 4 * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  if s <? 2 + m then false else
  Nat.testbit i (s - 2).
Proof.
  change 4 with (2^2); apply testbit_make_gap.
Qed.

Lemma testbit_make_2_gap' i m s : 
  Nat.testbit ((i/2^m) * 4 * (2^m) + i mod 2^m) s =
  if s <? m then Nat.testbit i s else 
  if s <? 2 + m then false else
  Nat.testbit i (s - 2).
Proof.
  rewrite Nat.add_comm; apply testbit_make_2_gap.
Qed.

Lemma testbit_mod_pow2 i n m : 
  Nat.testbit (i mod 2^n) m = 
  if m <? n then Nat.testbit i m else false.
Proof.
  pose proof (Nat.pow_nonzero) as Hnz.
  bdestruct (m <? n).
  - rewrite Nat.mod_pow2_bits_low; easy.
  - rewrite Nat.mod_pow2_bits_high; easy.
Qed.

Lemma testbit_div_pow2 i n m : 
  Nat.testbit (i / 2^n) m = 
  Nat.testbit i (n + m).
Proof.
  rewrite Nat.add_comm.
  apply Nat.div_pow2_bits.
Qed.

Lemma testbit_mul_pow2 i n m : 
  Nat.testbit (i * 2^n) m = 
  if m <? n then false else
  Nat.testbit i (m - n).
Proof.
  bdestructΩ'.
  - now rewrite Nat.mul_pow2_bits_low.
  - now rewrite Nat.mul_pow2_bits_high.
Qed.

Lemma testbit_remove_gap i m k s : 
  Nat.testbit (i mod 2^m + (i/2^m / 2^k) * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  Nat.testbit i (s + k).
Proof.
  rewrite Nat.add_comm.
  rewrite testbit_add_pow2_split by
  (apply Nat.mod_upper_bound, Nat.pow_nonzero; lia).
  bdestruct (s <? m).
  - rewrite testbit_mod_pow2; bdestructΩ'.
  - rewrite !testbit_div_pow2.
    bdestructΩ'; f_equal; lia.
Qed.

Lemma testbit_remove_2_gap i m s : 
  Nat.testbit (i mod 2^m + (i/2^m / 4) * (2^m)) s =
  if s <? m then Nat.testbit i s else 
  Nat.testbit i (s + 2).
Proof.
  change 4 with (2^2).
  apply testbit_remove_gap.
Qed.

Lemma testbit_remove_2_gap' i m s : 
  Nat.testbit ((i/2^m / 4) * (2^m) + i mod 2^m) s =
  if s <? m then Nat.testbit i s else
  Nat.testbit i (s + 2).
Proof.
  rewrite Nat.add_comm; apply testbit_remove_2_gap.
Qed.

Lemma div_add' n m p : 
  (n + m) / p = 
  n / p + m / p + (n mod p + m mod p) / p.
Proof.
  rewrite (Nat.div_mod_eq n p) at 1.
  rewrite (Nat.div_mod_eq m p) at 1.
  bdestruct (p =? 0); [now subst|].
  symmetry.
  rewrite Nat.add_comm.
  rewrite <- Nat.div_add by easy.
  f_equal.
  lia.
Qed.

Lemma sum_eq_lxor_of_bits_disj_l n m : 
  (forall k, Nat.testbit n k = true -> Nat.testbit m k = false) ->
  n + m = Nat.lxor n m.
Proof.
  intros Hnm.
  apply bits_inj.
  intros s.
  rewrite lxor_spec.
  revert n m Hnm.
  induction s; 
  intros n m Hnm;
  [apply Nat.odd_add|].
  simpl.
  rewrite !div2_div.
  rewrite div_add'.
  rewrite <- !bit0_mod.
  rewrite (div_small (_ + _)), Nat.add_0_r by 
    (generalize (Hnm 0); 
    destruct (testbit n 0), (testbit m 0); 
    simpl; lia).
  apply IHs.
  intros k.
  rewrite 2!div2_bits; auto.
Qed.

Lemma testbit_add_disjoint_pow2_l k n : 
  Nat.testbit n k = false ->
  forall i,
  Nat.testbit (2^k + n) i = (i =? k) || testbit n i.
Proof.
  intros Hn i.
  rewrite sum_eq_lxor_of_bits_disj_l, lxor_spec, pow2_bits_eqb, eqb_sym.
  - bdestruct (i =? k). 
    + subst. 
      now rewrite Hn. 
    + now destruct (testbit n i).
  - intros s.
    rewrite pow2_bits_eqb.
    bdestructΩ'.
Qed.

Lemma testbit_sum_pows_2_ne k l : k <> l -> forall i, 
  Nat.testbit (2 ^ k + 2 ^ l) i = (i =? k) || (i =? l).
Proof.
  intros Hkl i.
  rewrite testbit_add_disjoint_pow2_l;
  rewrite pow2_bits_eqb; bdestructΩ'.
Qed.

Lemma testbit_add_disjoint m n : 
  (forall k, Nat.testbit n k = true -> Nat.testbit m k = false) ->
  forall i,
  Nat.testbit (n + m) i = testbit n i || testbit m i.
Proof.
  intros Hn i.
  rewrite sum_eq_lxor_of_bits_disj_l, lxor_spec by easy.
  generalize (Hn i).
  destruct (testbit n i), (testbit m i); lia + auto.
Qed.

Lemma testbit_b2n b k : 
  testbit (b2n b) k = b && (k =? 0).
Proof.
  destruct b, k; easy + apply Nat.bits_0.
Qed.

Lemma testbit_decomp n k : 
  n = (n / 2 ^ (S k)) * 2 ^ (S k) + 
    b2n (testbit n k) * 2 ^ k + (n mod 2^k).
Proof.
  apply bits_inj.
  intros s.
  rewrite Nat.pow_succ_r, Nat.mul_assoc, <- Nat.mul_add_distr_r by lia.
  rewrite testbit_add_pow2_split by show_moddy_lt.
  change 2 with (2^1) at 4.
  rewrite testbit_add_pow2_split by (destruct (testbit n k); simpl; lia).
  rewrite testbit_b2n.
  rewrite <- Nat.pow_succ_r by lia.
  rewrite testbit_div_pow2, testbit_mod_pow2.
  bdestructΩ'; rewrite ?andb_true_r; f_equal; lia.
Qed.

End nat_lemmas.

Ltac simplify_mods_of a b :=
  first [
    rewrite (Nat.mod_small a b) in * by lia
  | rewrite (mod_n_to_2n a b) in * by lia].

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
    | lia
    | match goal with 
      | |- context[?a mod ?b] => 
          __fail_if_has_mods a; __fail_if_has_mods b; 
          simplify_mods_of a b
      | H: context[?a mod ?b] |- _ => 
          __fail_if_has_mods a; __fail_if_has_mods b; 
          simplify_mods_of a b
      end 
    | match goal with
      | |- context[?a mod ?b] => (* idtac a b; *) 
          bdestruct (a <? b);
          [rewrite (Nat.mod_small a b) by lia 
          | try rewrite (mod_n_to_2n a b) by lia]
      end
    ]
  end.




(** * Some useful lemmas **)
Section Assorted_lemmas.

Lemma if_sumbool {A P Q} (x y : A) (c : {P} + {Q}) : 
  (if c then x else y) = if RMicromega.sumboolb c then x else y.
Proof.
  destruct c; reflexivity.
Qed.

Lemma if_true {A} b (u v : A) : 
  b = true ->
  (if b then u else v) = u.
Proof.
  bdestructΩ'.
Qed.

Lemma if_false {A} b (u v : A) : 
  b = false ->
  (if b then u else v) = v.
Proof.
  bdestructΩ'.
Qed.

Lemma if_dist' {A B} (f : A -> B) (b : bool) (x y : A) : 
  f (if b then x else y) = if b then f x else f y.
Proof.
  now destruct b.
Qed.

Lemma orb_if {A} b c (v v' : A) : 
  (if (b || c) then v else v') =
  if b then v else if c then v else v'.
Proof.
  bdestructΩ'.
Qed.

Lemma f_equal_if {A} (b c : bool) (u v x y : A) : 
  b = c -> u = v -> x = y ->
  (if b then u else x) = (if c then v else y).
Proof.
  intros; subst; easy.
Qed.

Lemma f_equal_if_precedent {A} b c (v1 v2 u1 u2 : A) : 
  b = c -> 
  (b = true -> c = true -> v1 = v2) ->
  (b = false -> c = false -> u1 = u2) ->
  (if b then v1 else u1) = (if c then v2 else u2).
Proof.
  intros ->.
  destruct c; auto.
Qed.

Lemma f_equal_if_precedent_same {A} b (v1 v2 u1 u2 : A) : 
  (b = true -> v1 = v2) ->
  (b = false -> u1 = u2) ->
  (if b then v1 else u1) = (if b then v2 else u2).
Proof.
  intros.
  apply f_equal_if_precedent; auto.
Qed.

Lemma and_same (P : Prop) : P /\ P <-> P.
Proof. split; try intros []; auto. Qed.

Local Open Scope nat_scope.

Lemma and_andb {P P'} {b b'} : 
  reflect P b -> reflect P' b' -> 
  reflect (P /\ P') (b && b').
Proof.
  intros H H'; apply reflect_iff in H, H'.
  apply iff_reflect.
  rewrite andb_true_iff.
  now rewrite H, H'.
Qed.

Lemma forall_iff {A} (f g : A -> Prop) : 
  (forall a, (f a <-> g a)) ->
  ((forall a, f a) <-> (forall a, g a)).
Proof.
  intros ?; split; intros; apply H; auto.
Qed.

Lemma impl_iff (P Q Q' : Prop) : 
  ((P -> Q) <-> (P -> Q')) <->
  (P -> (Q <-> Q')).
Proof.
  split;
  intros ?; split; intros; apply H; auto.
Qed.

Import Setoid.

Lemma Forall_forallb {A} (f : A -> bool) (P : A -> Prop)
  (Hf : forall a, P a <-> f a = true) : 
  forall l, Forall P l <-> forallb f l = true.
Proof.
  intros l.
  induction l; [repeat constructor|].
  simpl.
  rewrite andb_true_iff.
  rewrite Forall_cons_iff.
  apply Morphisms_Prop.and_iff_morphism; easy.
Qed.

Lemma eq_eqb_iff (b c : bool) : 
  b = c <-> eqb b c = true.
Proof.
  destruct b, c ; easy.
Qed.

Lemma eqb_true_l b : eqb true b = b.
Proof. now destruct b. Qed.

Lemma eqb_true_r b : eqb b true = b.
Proof. now destruct b. Qed.

Lemma Forall_seq {start len : nat} f : 
  Forall f (seq start len) <-> forall k, k < len -> f (start + k).
Proof.
  revert start;
  induction len; intros start;
  [split; constructor + lia|].
  simpl.
  rewrite Forall_cons_iff.
  split.
  - intros [Hfk H].
    rewrite IHlen in H.
    intros k Hk.
    destruct k.
    + rewrite Nat.add_0_r; easy.
    + specialize (H k).
      rewrite Nat.add_succ_r.
      apply H. 
      lia.
  - intros H.
    rewrite IHlen; split. 
    + specialize (H 0).
      rewrite Nat.add_0_r in H.
      apply H; lia.
    + intros k Hk; specialize (H (S k)).
      rewrite Nat.add_succ_r in H.
      apply H.
      lia.
Qed.

Lemma Forall_seq0 {len : nat} f : 
  Forall f (seq 0 len) <-> forall k, k < len -> f k.
Proof.
  apply (@Forall_seq 0 len f).
Qed.

Lemma forallb_seq (f : nat -> bool) n m : 
  forallb f (seq m n) = true <->
  (forall s, s < n -> f (s + m) = true).
Proof.
  revert m;
  induction n; intros m; [easy|].
  simpl.
  rewrite andb_true_iff, IHn.
  split.
  - intros [Hm Hlt].
    intros s.
    destruct s; [easy|].
    setoid_rewrite Nat.add_succ_r in Hlt.
    intros.
    apply Hlt; lia.
  - intros Hlt; split.
    + apply (Hlt 0 ltac:(lia)).
    + intros s Hs. 
      rewrite Nat.add_succ_r.
      apply (Hlt (S s)).
      lia.
Qed.

Lemma forallb_seq0 (f : nat -> bool) n : 
  forallb f (seq 0 n) = true <->
  (forall s, s < n -> f s = true).
Proof.
  rewrite forallb_seq.
  now setoid_rewrite Nat.add_0_r.
Qed.

Lemma forall_lt_sum_split n m (P : nat -> Prop) : 
  (forall k, k < n + m -> P k) <->
  (forall k, k < n -> P k) /\ (forall k, k < m -> P (n + k)).
Proof.
  split; [intros H; split; intros; apply H; lia|].
  intros [Hlow Hhigh].
  intros.
  bdestruct (k <? n);
  [now apply Hlow|].
  generalize (Hhigh (k - n) ltac:(lia)).
  rewrite Nat.add_sub_assoc, add_sub' by lia.
  easy.
Qed.

Lemma and_True_l P : True /\ P <-> P.
Proof. tauto. Qed.

Lemma and_True_r P : P /\ True <-> P.
Proof. tauto. Qed.

Lemma and_iff_distr_l (P Q R : Prop) :
  (P -> (Q <-> R)) <-> (P /\ Q <-> P /\ R).
Proof. tauto. Qed.

Lemma and_iff_distr_r (P Q R : Prop) :
  (P -> (Q <-> R)) <-> (Q /\ P <-> R /\ P).
Proof. rewrite and_iff_distr_l. now rewrite 2!(and_comm P). Qed.

End Assorted_lemmas.