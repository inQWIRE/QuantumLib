Require Import Prelim.

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
