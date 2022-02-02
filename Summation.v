Require Import List.
Require Import Prelim.



Declare Scope group_scope.
Open Scope group_scope.

(* try reserved notation *)
Class Group G :=
  { id : G
  ; op : G -> G -> G
  }.

Infix "+" := op : group_scope.

Class Group_Laws G `{Group G} :=
  { G_id_l : forall g, id + g = g
  ; G_id_r : forall g, g + id = g
  ; G_inv_l : forall g, exists h, h + g = id
  ; G_inv_r : forall g, exists h, g + h = id                                
  ; G_assoc : forall g h i, (g + h) + i = g + (h + i) 
  }.

Class Ring R `{Group_Laws R} :=
  { one : R
  ; mul : R -> R -> R
  }.

Infix "*" := mul : group_scope.

Class Ring_Laws R `{Ring R} :=                    
  { R_plus_comm : forall a b, a + b = b + a
  ; R_mul_1_l : forall a, one * a = a
  ; R_mul_comm : forall a b, a * b = b * a
  ; R_mul_plus_distr_l : forall a b c, a * (b + c) = (a * b) + (a * c)
  }.

Class Field F `{Ring F} :=
  { F_inv : forall f, f <> id -> exists g, f * g = one }.

Class Vector_Space V F `{Group_Laws V} `{Field F} :=
  { scale : F -> V -> V }.

Infix "⋅" := scale (at level 40) : group_scope.

Class Vector_Space_Laws V F `{Vector_Space V F} :=
  { V_plus_comm : forall u v, u + v = v + u
  ; V_scale_dist : forall a u v, a ⋅ (u + v) = a ⋅ u + a ⋅ v
  ; V_scale_assoc : forall a b v, a ⋅ (b ⋅ v) = (a * b) ⋅ v
  }.  


(* some lemmas about these objects *)
Lemma scale_zero : forall {V F} `{Vector_Space_Laws V F} (c : F),
  c ⋅ id = id.
Proof. intros. 
       inversion H0; inversion H6.
       assert (H' : c ⋅ id = c ⋅ id + c ⋅ id).
       { rewrite <- V_scale_dist0, G_id_l0; easy. }
       Admitted.


Lemma mul_zero : forall {R} `{Ring_Laws R} (r : R),
  id * r = id.
Proof. Admitted.



(* sum to n exclusive *)
Fixpoint big_sum {G : Type} `{Group_Laws G} (f : nat -> G) (n : nat) : G := 
  match n with
  | 0 => id
  | S n' => (big_sum f n') + (f n')
  end.


Lemma big_sum_0 : forall {G} `{Group_Laws G} f n,
    (forall x, f x = id) -> big_sum f n = id. 
Proof.
  intros.
  inversion H; inversion H0; subst. 
  induction n.
  - reflexivity.
  - simpl.
    rewrite H1, IHn, G_id_r0; easy. 
Qed.

Lemma big_sum_eq : forall {G} `{Group_Laws G} f g n, f = g -> big_sum f n = big_sum g n.
Proof. intros; subst; reflexivity. Qed.

Lemma big_sum_0_bounded : forall {G} `{Group_Laws G} f n, 
    (forall x, (x < n)%nat -> f x = id) -> big_sum f n = id. 
Proof.
  intros.
  inversion H; inversion H0; subst. 
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, G_id_l0.   
    apply H1; lia. 
    intros.
    apply H1; lia.
Qed.

Lemma big_sum_eq_bounded : forall {G} `{Group_Laws G} f g n, 
    (forall x, (x < n)%nat -> f x = g x) -> big_sum f n = big_sum g n.
Proof. 
  intros G H0 H1 f g n H. 
  inversion H0; inversion H1; subst. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma big_sum_plus : forall {G} `{Ring_Laws G} f g n, 
    big_sum (fun x => f x + g x) n = big_sum f n + big_sum g n.
Proof.
  intros.
  inversion H0; inversion H2; subst. 
  induction n; simpl. 
  + rewrite G_id_l0; easy.
  + rewrite IHn.
    repeat rewrite G_assoc0.
    apply f_equal_gen; try easy. 
    rewrite R_plus_comm0.  
    repeat rewrite G_assoc0.
    apply f_equal_gen; try easy.
Qed.

Lemma big_sum_scale_l : forall {G} {V} `{Vector_Space_Laws G V} c f n, 
    c ⋅ big_sum f n = big_sum (fun x => c ⋅ f x) n.
Proof.
  intros.
  induction n; simpl. 
  + apply scale_zero.
  + rewrite <- IHn.
    inversion H6.
    rewrite V_scale_dist0.
    reflexivity.
Qed.

Lemma big_sum_func_distr : forall {G} `{Group_Laws G} f g n, 
    (forall a b, g (a + b) = g a + g b) -> g (big_sum f n) = big_sum (fun x => g (f x)) n.
Proof. 
  intros.
  induction n; simpl. 
  + Admitted. 
    
Lemma big_sum_extend_r : forall {G} `{Group_Laws G} n f, 
    big_sum f n + f n = big_sum f (S n).
Proof. reflexivity. Qed.

Lemma big_sum_extend_l : forall {G} `{Group_Laws G} n f, 
    f O + big_sum (fun x => f (S x)) n = big_sum f (S n).
Proof.
  intros.
  inversion H0; subst. 
  induction n; simpl.   
  + rewrite G_id_l0, G_id_r0; easy. 
  + rewrite <- G_assoc0, IHn.
    simpl; reflexivity.
Qed.

Lemma big_sum_unique : forall {G} `{Group_Laws G} k (f : nat -> G) n, 
  (exists x, (x < n)%nat /\ f x = k /\ (forall x', x <> x' -> f x' = id)) ->
  big_sum f n = k.
Proof. Admitted.

Lemma big_sum_sum : forall {G} `{Group_Laws G} m n f, 
  big_sum f (m + n) = big_sum f m + big_sum (fun x => f (m + x)%nat) n. 
Proof.
  intros.
  inversion H0; subst.
  induction m.
  + simpl. rewrite G_id_l0. reflexivity. 
  + simpl.
    rewrite IHm.
    repeat rewrite G_assoc0.
    remember (fun y => f (m + y)%nat) as g.
    replace (f m) with (g O) by (subst; rewrite plus_0_r; reflexivity).
    replace (f (m + n)%nat) with (g n) by (subst; reflexivity).
    replace (big_sum (fun x : nat => f (S (m + x))) n) with
            (big_sum (fun x : nat => g (S x)) n).
    2:{ apply big_sum_eq. subst. apply functional_extensionality.
    intros; rewrite <- plus_n_Sm. reflexivity. }
    rewrite big_sum_extend_l.
    rewrite big_sum_extend_r.
    reflexivity.
Qed.

Lemma Csum_product : forall {G} `{Ring_Laws G} m n f g, 
  n <> O ->
  big_sum f m * big_sum g n = big_sum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
Proof.
  intros.
  inversion H2.
  induction m; simpl. 
  + rewrite mul_zero; reflexivity. 
  + Admitted.

(* rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite Csum_mult_l.    
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (Csum (fun x : nat => f m * g x) n) with
            (Csum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply Csum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- Csum_sum.
    rewrite plus_comm.
    reflexivity.
Qed. *)

(*
Lemma Csum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> 0 <= fst (Csum f n).
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.

Lemma Csum_gt_0 : forall f n, (forall x, 0 <= fst (f x)) -> 
                              (exists y : nat, (y < n)%nat /\ 0 < fst (f y)) ->
                              0 < fst (Csum f n).
Proof.
  intros f n H [y [H0 H1]].
  induction n.
  - simpl. lia. 
  - simpl in *.
    bdestruct (y <? n)%nat; bdestruct (y =? n)%nat; try lia. 
    + assert (H' : 0 <= fst (f n)). { apply H. } 
      apply IHn in H2. lra. 
    + apply (Csum_ge_0 f n) in H.
      rewrite H3 in H1.
      lra. 
Qed.
*)

(*

Instance nat_is_group : Group C :=
  { id := C0
  ; op := Cplus
  }.


Instance C_is_group_law : Group_Laws C.
Proof. split; intros; simpl; try lca. 
       all : exists (-g); lca.








(* sum to n exclusive *)
Fixpoint big_sum {G : Type} (id : G) (plus : G -> G -> G) (f : nat -> G) (n : nat) : G := 
  match n with
  | 0 => id
  | S n' => plus (big_sum id plus f n') (f n')
  end.

Inductive cmtv_grp (G : Type) (id : G) (plus : G -> G -> G) : Prop :=
| is_cmtv_grp : (forall g : G, plus id g = g) ->
                (forall g1 g2 : G, plus g1 g2 = plus g2 g1) ->
                (forall g1 g2 g3 : G, plus (plus g1 g2) g3 = plus g1 (plus g2 g3)) ->
                cmtv_grp G id plus.

Inductive cmtv_scl_grp (G S : Type) (id : G)
          (plus : G -> G -> G) (scale : S -> G -> G) : Prop :=
| is_cmtv_scl_grp : 


*)













(*

Program Instance C_is_group : Group C := 
  { id := C0
  ; op := Cplus
  }.
Next Obligation.
Proof. lca. Qed.
Next Obligation.
Proof. lca. Qed.
Next Obligation.
Proof. exists (-g); lca. Qed.
Next Obligation.
Proof. exists (-g); lca. Qed.
Next Obligation.
Proof. lca. Qed.

Program Instance C_is_ring : Ring C :=
  { one := C1
  ; mul := Cmult
  }.
Next Obligation.
Proof. lca. Qed.
Next Obligation.
Proof. lca. Qed.
Next Obligation.
Proof. lca. Qed.

Lemma C_is_field : Field C.
Proof. split; intros; simpl in *. 
       exists (/f).
       rewrite Cinv_r; easy.
Qed.





Instance C_is_group_law : Group_Laws C.
Proof. split; intros; simpl; try lca. 
       all : exists (-g); lca.
Qed.

*)

(*
Declare Scope group_scope.
Infix "+" := op : group_scope.

Open Scope group_scope.

Class Group_Laws G `{Group G} :=
  { G_id_l : forall g, id + g = g
  ; G_id_r : forall g, g + id = g
  ; G_inv_l : forall g, exists h, h + g = id
  ; G_inv_r : forall g, exists h, g + h = id                                
  ; G_assoc : forall g h i, (g + h) + i = g + (h + i) 
  }.


Class Ring R `{Group_Laws R} :=
  {
    one : R;
    mul : R -> R -> R
  }.

Infix "*" := mul : group_scope.

Class Ring_Laws R `{Ring R} :=
  { R_mul_1_l : forall a, one * a = a
  ; R_mul_comm : forall a b, a * b = b * a
  ; R_mul_plus_distr_l : forall a b c, a * (b + c) = a * b + a * c
  }.



Class Field_Laws F `{Ring F} :=
  { F_inv : forall f, f <> id -> exists g, f * g = one }.



Class Vector_Space V `{Group_Laws V} :=
  { F : Type;
    F_group : `{ Group F}; 
    F_group_law : `{ Group_Laws F};  
    F_ring : `{ Ring F}; 
    F_ring_law : `{ Ring_Laws F}; 
    F_field_law : `{ Field_Laws F};
    scale : F -> V -> V
  }.  


Class Vector_Space_Laws V `{Vector_Space V} :=
  { V_plus_comm : forall u v, u + v = v + u
  ; V_scale_comm : forall a u v, scale a (u + v) = scale a u + scale a v
  ; V_scale_assoc : forall a b v, scale a (scale b v) = scale (a * b) v
  }.

*)



(*
Class Ring R `{Group R} :=
  { one : R
  ; mul : R -> R -> R
  ; R_mul_1_l : forall a, mul one a = a
  ; R_mul_comm : forall a b, mul a b = mul b a
  ; R_mul_plus_distr_l : forall a b c, mul a (b + c) = mul a b + mul a c
  }.

Infix "*" := mul : group_scope.


Class Field F `{Ring F} :=
  { F_inv : forall f, f <> id -> exists g, f * g = one }.



Class Vector_Space V F `{Group V} `{Field F} :=
  { scale : F -> V -> V
  ; V_plus_comm : forall u v, u + v = v + u
  ; V_scale_comm : forall a u v, scale a (u + v) = scale a u + scale a v
  ; V_scale_assoc : forall a b v, scale a (scale b v) = scale (a * b) v
  }.  
*)
