Require Import List.
Require Import Prelim.



Declare Scope group_scope.
Delimit Scope group_scope with G.

Open Scope group_scope.


(* TODO: try reserved notation *)
Class Monoid G :=
  { Gzero : G
  ; Gplus : G -> G -> G
  ; Gplus_0_l : forall g, Gplus Gzero g = g
  ; Gplus_0_r : forall g, Gplus g Gzero = g                              
  ; Gplus_assoc : forall g h i, Gplus g (Gplus h i) = Gplus (Gplus g h) i
  }.

Infix "+" := Gplus : group_scope.
Notation "0" := Gzero : group_scope.

      
Class Group G `{Monoid G} :=
  { Gopp : G -> G
  ; Gopp_l : forall g, (Gopp g) + g = 0
  ; Gopp_r : forall g, g + (Gopp g) = 0             
  }.

Class Comm_Group G `{Group G} :=
  { Gplus_comm : forall a b, Gplus a b = Gplus b a }.

Definition Gminus {G} `{Group G} (g1 g2 : G) := g1 + (Gopp g2).

Notation "- x" := (Gopp x) : group_scope.
Infix "-" := Gminus : group_scope.

Class Ring R `{Comm_Group R} :=
  { Gone : R
  ; Gmult : R -> R -> R                 
  ; Gmult_1_l : forall a, Gmult Gone a = a
  ; Gmult_1_r : forall a, Gmult a Gone = a
  ; Gmult_assoc : forall a b c, Gmult a (Gmult b c) = Gmult (Gmult a b) c 
  ; Gmult_plus_distr_l : forall a b c, Gmult c (a + b) = (Gmult c a) + (Gmult c b)
  ; Gmult_plus_distr_r : forall a b c, Gmult (a + b) c = (Gmult a c) + (Gmult b c)
  }.

Class Comm_Ring R `{Ring R} :=
  { Gmult_comm : forall a b, Gmult a b = Gmult b a }.

Infix "*" := Gmult : group_scope.
Notation "1" := Gone : group_scope.

Class Field F `{Comm_Ring F} :=
  { Ginv : F -> F
  ; G1_neq_0 : 1 <> 0
  ; Ginv_r : forall f, f <> 0 -> f * (Ginv f) = 1 }.

Definition Gdiv {G} `{Field G} (g1 g2 : G) := Gmult g1 (Ginv g2).

Notation "/ x" := (Ginv x) : group_scope.
Infix "/" := Gdiv : group_scope.

Class Vector_Space V F `{Comm_Group V} `{Field F} :=
  { Vscale : F -> V -> V 
  ; Vscale_1 : forall v, Vscale 1 v = v
  ; Vscale_dist : forall a u v, Vscale a (u + v) = Vscale a u + Vscale a v
  ; Vscale_assoc : forall a b v, Vscale a (Vscale b v) = Vscale (a * b) v
  }.  

Infix "⋅" := Vscale (at level 40) : group_scope.


(* showing that our notation of comm_ring and field is the same as coqs ring and field tactics *)

Lemma G_ring_theory : forall {R} `{Comm_Ring R}, ring_theory 0 1 Gplus Gmult Gminus Gopp eq.
Proof. intros. 
       constructor.
       exact Gplus_0_l.
       exact Gplus_comm.
       exact Gplus_assoc.
       exact Gmult_1_l.
       exact Gmult_comm.
       exact Gmult_assoc.
       exact Gmult_plus_distr_r.
       easy.
       exact Gopp_r.
Qed.

Lemma G_field_theory : forall {F} `{Field F}, field_theory 0 1 Gplus Gmult Gminus Gopp Gdiv Ginv eq.
Proof. intros. 
       constructor.
       apply G_ring_theory.
       exact G1_neq_0.
       easy.
       intros; rewrite Gmult_comm, Ginv_r; easy. 
Qed.

(*
Add Field C_field_field : C_field_theory.
*)

(* some lemmas about these objects *)
Lemma Gplus_cancel_l : forall {G} `{Group G} (g h a : G),
  a + g = a + h -> g = h.
Proof. intros. 
       rewrite <- Gplus_0_l, <- (Gplus_0_l g), 
         <- (Gopp_l a), <- Gplus_assoc, H1, Gplus_assoc; easy. 
Qed.

Lemma Gplus_cancel_r : forall {G} `{Group G} (g h a : G),
  g + a = h + a -> g = h.
Proof. intros.
       rewrite <- Gplus_0_r, <- (Gplus_0_r g), 
         <- (Gopp_r a), Gplus_assoc, H1, Gplus_assoc; easy. 
Qed.
  
Lemma Vscale_zero : forall {V F} `{Vector_Space V F} (c : F),
  c ⋅ 0 = 0.
Proof. intros.
       apply (Gplus_cancel_l _ _ (c ⋅ 0)).
       rewrite Gplus_0_r, <- Vscale_dist, Gplus_0_l; easy. 
Qed.                              
  
Lemma Gmult_0_l : forall {R} `{Ring R} (r : R),
  0 * r = 0.
Proof. intros.  
       apply (Gplus_cancel_l _ _ (0 * r)).
       rewrite Gplus_0_r, <- Gmult_plus_distr_r, Gplus_0_r; easy. 
Qed.

Lemma Gmult_0_r : forall {R} `{Ring R} (r : R),
  r * 0 = 0.
Proof. intros.
       apply (Gplus_cancel_l _ _ (r * 0)).
       rewrite Gplus_0_r, <- Gmult_plus_distr_l, Gplus_0_r; easy. 
Qed. 

Lemma Ginv_l : forall {F} `{Field F} (f : F), f <> 0 -> (Ginv f) * f = 1.
Proof. intros; rewrite Gmult_comm; apply Ginv_r; easy. Qed.

Lemma Gmult_cancel_l : forall {F} `{Field F} (g h a : F), 
  a <> 0 -> a * g = a * h -> g = h.
Proof. intros. 
       rewrite <- Gmult_1_l, <- (Gmult_1_l g), 
         <- (Ginv_l a), <- Gmult_assoc, H6, Gmult_assoc; easy. 
Qed.

Lemma Gmult_cancel_r : forall {F} `{Field F} (g h a : F), 
  a <> 0 -> g * a = h * a -> g = h.
Proof. intros. 
       rewrite <- Gmult_1_r, <- (Gmult_1_r g), 
         <- (Ginv_r a), Gmult_assoc, H6, <- Gmult_assoc; easy. 
Qed.

Lemma Gmult_neq_0 : forall {F} `{Field F} (a b : F), a <> 0 -> b <> 0 -> a * b <> 0.
Proof. intros.
       unfold not; intros. 
       apply H6.
       rewrite <- (Gmult_1_l b), <- (Ginv_l a), 
         <- Gmult_assoc, H7, Gmult_0_r; auto.
Qed.       

Lemma Ginv_mult_distr : forall {F} `{Field F} (a b : F),
    a <> 0 -> b <> 0 ->
    / (a * b) = / a * / b.
Proof. intros. 
       apply (Gmult_cancel_r _ _ (a * b)).
       apply Gmult_neq_0; easy. 
       rewrite Ginv_l; try apply Gmult_neq_0; auto.
       rewrite <- Gmult_assoc, (Gmult_assoc _ a), (Gmult_comm _ a), <- (Gmult_assoc a).
       rewrite Ginv_l, Gmult_1_r, Ginv_l; easy.
Qed.



(* showing that nat is a monoid *)

Program Instance nat_is_monoid : Monoid nat := 
  { Gzero := 0
  ; Gplus := plus
  }.
Solve All Obligations with program_simpl; try lia.





(*************************)
(** Summation functions *)
(*************************)




Fixpoint times_n {G} `{Monoid G} (g : G) (n : nat) :=
  match n with
  | 0 => 0
  | S n' => g + times_n g n'
  end.
      
Fixpoint G_big_plus {G} `{Monoid G} (gs : list G) : G := 
  match gs with
  | nil => 0 
  | g :: gs' => g + (G_big_plus gs')
  end. 

Fixpoint G_big_mult {R} `{Ring R} (rs : list R) : R := 
  match rs with
  | nil => 1 
  | r :: rs' => r * (G_big_mult rs')
  end. 


(** sum to n exclusive *)
Fixpoint big_sum {G : Type} `{Monoid G} (f : nat -> G) (n : nat) : G := 
  match n with
  | 0 => 0
  | S n' => (big_sum f n') + (f n')
  end.


Lemma big_sum_0 : forall {G} `{Monoid G} f n,
    (forall x, f x = 0) -> big_sum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite H0, IHn, Gplus_0_r; easy. 
Qed.

Lemma big_sum_eq : forall {G} `{Monoid G} f g n, f = g -> big_sum f n = big_sum g n.
Proof. intros; subst; reflexivity. Qed.

Lemma big_sum_0_bounded : forall {G} `{Monoid G} f n, 
    (forall x, (x < n)%nat -> f x = 0) -> big_sum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, Gplus_0_l.   
    apply H0; lia. 
    intros.
    apply H0; lia.
Qed.

Lemma big_sum_eq_bounded : forall {G} `{Monoid G} f g n, 
    (forall x, (x < n)%nat -> f x = g x) -> big_sum f n = big_sum g n.
Proof. 
  intros. 
  induction n.
  + simpl; reflexivity.
  + simpl. 
    rewrite H0 by lia.
    rewrite IHn by (intros; apply H0; lia).
    reflexivity.
Qed.

Lemma big_sum_shift : forall {G} `{Monoid G} n (f : nat -> G),
  big_sum f (S n) = f O + big_sum (fun x => f (S x)) n.
Proof.
  intros; simpl.
  induction n; simpl.
  rewrite Gplus_0_l, Gplus_0_r; easy.
  rewrite IHn.
  rewrite Gplus_assoc; easy.
Qed.

Lemma big_sum_constant : forall {G} `{Monoid G} g n,
  big_sum (fun _ => g) n = times_n g n.
Proof. induction n; try easy. 
       rewrite big_sum_shift. 
       rewrite IHn; simpl.
       easy. 
Qed.

Lemma big_sum_plus : forall {G} `{Comm_Group G} f g n, 
    big_sum (fun x => f x + g x) n = big_sum f n + big_sum g n.
Proof.
  intros.
  induction n; simpl. 
  + rewrite Gplus_0_l; easy.
  + rewrite IHn.
    repeat rewrite <- Gplus_assoc.
    apply f_equal_gen; try easy. 
    rewrite Gplus_comm.  
    repeat rewrite <- Gplus_assoc.
    apply f_equal_gen; try easy.
    rewrite Gplus_comm; easy.
Qed.

Lemma big_sum_scale_l : forall {G} {V} `{Vector_Space G V} c f n, 
    c ⋅ big_sum f n = big_sum (fun x => c ⋅ f x) n.
Proof.
  intros.
  induction n; simpl. 
  + apply Vscale_zero.
  + rewrite <- IHn.
    rewrite Vscale_dist.
    reflexivity.
Qed.

(* there is a bit of akwardness in that these are very similar and sometimes 
    encapsulate the same fact as big_sum_scale_l *)
Lemma big_sum_mult_l : forall {R} `{Ring R} c f n, 
    c * big_sum f n = big_sum (fun x => c * f x) n.
Proof.
  intros.
  induction n.
  + simpl; apply Gmult_0_r.
  + simpl.
    rewrite Gmult_plus_distr_l. 
    rewrite IHn.
    reflexivity.
Qed.

Lemma big_sum_mult_r : forall {R} `{Ring R} c f n, 
    big_sum f n * c = big_sum (fun x => f x * c) n.
Proof.
  intros.
  induction n.
  + simpl; apply Gmult_0_l.
  + simpl.
    rewrite Gmult_plus_distr_r. 
    rewrite IHn.
    reflexivity.
Qed.

Lemma big_sum_func_distr : forall {G1 G2} `{Group G1} `{Group G2} f (g : G1 -> G2) n, 
    (forall a b, g (a + b) = g a + g b) -> g (big_sum f n) = big_sum (fun x => g (f x)) n.
Proof. 
  intros.
  induction n; simpl. 
  + apply (Gplus_cancel_l _ _ (g 0)).
    rewrite <- H3, Gplus_0_l, Gplus_0_r; easy. 
  + rewrite H3, IHn; easy. 
Qed.

Lemma big_sum_prop_distr : forall {G} `{Monoid G} f (p : G -> Prop) n,
    (forall a b, p a -> p b -> p (a + b)) -> p 0 -> (forall i, i < n -> p (f i)) ->
    p (big_sum f n).
Proof. induction n as [| n'].
       - intros; easy.
       - intros. 
         apply H0.
         apply IHn'; try easy. 
         intros; apply H2; lia. 
         apply H2; lia. 
Qed.

Lemma big_sum_extend_r : forall {G} `{Monoid G} n f, 
    big_sum f n + f n = big_sum f (S n).
Proof. reflexivity. Qed.

Lemma big_sum_extend_l : forall {G} `{Monoid G} n f, 
    f O + big_sum (fun x => f (S x)) n = big_sum f (S n).
Proof.
  intros.
  induction n; simpl.   
  + rewrite Gplus_0_l, Gplus_0_r; easy. 
  + rewrite Gplus_assoc, IHn.
    simpl; reflexivity.
Qed.

Lemma big_sum_unique : forall {G} `{Monoid G} k (f : nat -> G) n, 
  (exists x, (x < n)%nat /\ f x = k /\ (forall x', x' < n -> x <> x' -> f x' = 0)) ->
  big_sum f n = k.
Proof.                    
  intros G H k f n [x [L [Eq Unique]]].
  induction n; try lia.
  rewrite <- big_sum_extend_r.
  destruct (Nat.eq_dec x n).
  - subst. 
    rewrite big_sum_0_bounded.
    rewrite Gplus_0_l; easy. 
    intros.
    apply Unique;
    lia.
  - rewrite Unique; try easy; try lia. 
    rewrite Gplus_0_r. 
    apply IHn.
    lia.
    intros.
    apply Unique; try easy; lia.
Qed.  

Lemma big_sum_sum : forall {G} `{Monoid G} m n f, 
  big_sum f (m + n) = big_sum f m + big_sum (fun x => f (m + x)%nat) n. 
Proof.
  intros.
  induction m.
  + simpl; rewrite Gplus_0_l. reflexivity. 
  + simpl.
    rewrite IHm.
    repeat rewrite <- Gplus_assoc.
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

Lemma big_sum_twice : forall {G} `{Monoid G} n f,
  big_sum f (2 * n) = big_sum f n + big_sum (fun x => f (n + x)%nat) n.
Proof.
  intros. replace (2 * n)%nat with (n + n)%nat by lia. apply big_sum_sum.
Qed.

Lemma big_sum_product : forall {G} `{Ring G} m n f g, 
  n <> O ->
  big_sum f m * big_sum g n = big_sum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
Proof.
  intros.
  induction m; simpl. 
  + rewrite Gmult_0_l; reflexivity. 
  + rewrite Gmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite big_sum_mult_l.    
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (big_sum (fun x : nat => f m * g x) n) with
            (big_sum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply big_sum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- big_sum_sum.
    rewrite plus_comm.
    reflexivity.
Qed. 

Local Open Scope nat_scope.

Lemma big_sum_double_sum : forall {G} `{Monoid G} (f : nat -> nat -> G) (n m : nat),
    big_sum (fun x => (big_sum (fun y => f x y) n)) m = big_sum (fun z => f (z / n) (z mod n)) (n * m).
Proof. induction m as [| m'].
       - rewrite Nat.mul_0_r.
         easy.
       - rewrite Nat.mul_succ_r.
         rewrite <- big_sum_extend_r.
         rewrite big_sum_sum.
         apply f_equal_gen; try (apply f_equal_gen; easy).
         apply big_sum_eq_bounded; intros.
         rewrite mult_comm.
         rewrite Nat.div_add_l; try lia. 
         rewrite (plus_comm (m' * n)).
         rewrite Nat.mod_add; try lia.
         destruct (Nat.mod_small_iff x n) as [_ HD]; try lia.
         destruct (Nat.div_small_iff x n) as [_ HA]; try lia.
         rewrite HD, HA; try lia.
         rewrite Nat.add_0_r.
         easy.
Qed.

Local Close Scope nat_scope.

Lemma big_sum_extend_double : forall {G} `{Ring G} (f : nat -> nat -> G) (n m : nat),
  big_sum (fun i => big_sum (fun j => f i j) (S m)) (S n) = 
  (big_sum (fun i => big_sum (fun j => f i j) m) n) + (big_sum (fun j => f n j) m) + 
                      (big_sum (fun i => f i m) n) + f n m.
Proof. intros. 
       rewrite <- big_sum_extend_r.
       assert (H' : forall a b c d : G, a + b + c + d = (a + c) + (b + d)). 
       { intros. 
         repeat rewrite <- Gplus_assoc.
         apply f_equal_gen; try easy. 
         repeat rewrite Gplus_assoc.
         apply f_equal_gen; try easy. 
         rewrite Gplus_comm; easy. }
       rewrite H'.
       apply f_equal_gen; try easy.
       apply f_equal_gen; try easy.
       rewrite <- big_sum_plus.
       apply big_sum_eq_bounded; intros. 
       easy.
Qed.

Lemma nested_big_sum : forall {G} `{Monoid G} m n f,
  big_sum f (2 ^ (m + n))
    = big_sum (fun x => big_sum (fun y => f (x * 2 ^ n + y)%nat) (2 ^ n)) (2 ^ m).
Proof.
  intros G H m n.
  replace (2 ^ (m + n))%nat with (2 ^ n * 2 ^ m)%nat by (rewrite Nat.pow_add_r; lia).
  induction m; intros.
  simpl.
  rewrite Nat.mul_1_r, Gplus_0_l.  
  reflexivity.
  replace (2 ^ n * 2 ^ S m)%nat with (2 * (2 ^ n * 2 ^ m))%nat by (simpl; lia).
  replace (2 ^ S m)%nat with (2 * 2 ^ m)%nat by (simpl; lia).
  rewrite 2 big_sum_twice.
  rewrite 2 IHm.
  apply f_equal2; try reflexivity.
  apply big_sum_eq.
  apply functional_extensionality; intros. 
  apply big_sum_eq.
  apply functional_extensionality; intros. 
  apply f_equal.
  lia.
Qed.



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
  { 0 := C0
  ; op := Cplus
  }.


Instance C_is_group_law : Group_Laws C.
Proof. split; intros; simpl; try lca. 
       all : exists (-g); lca.








(* sum to n exclusive *)
Fixpoint big_sum {G : Type} (id : G) (plus : G -> G -> G) (f : nat -> G) (n : nat) : G := 
  match n with
  | 0 => 0
  | S n' => plus (big_sum 0 plus f n') (f n')
  end.

Inductive cmtv_grp (G : Type) (id : G) (plus : G -> G -> G) : Prop :=
| is_cmtv_grp : (forall g : G, plus 0 g = g) ->
                (forall g1 g2 : G, plus g1 g2 = plus g2 g1) ->
                (forall g1 g2 g3 : G, plus (plus g1 g2) g3 = plus g1 (plus g2 g3)) ->
                cmtv_grp G 0 plus.

Inductive cmtv_scl_grp (G S : Type) (id : G)
          (plus : G -> G -> G) (scale : S -> G -> G) : Prop :=
| is_cmtv_scl_grp : 


*)













(*

Program Instance C_is_group : Group C := 
  { 0 := C0
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
  { G_id_l : forall g, 0 + g = g
  ; G_id_r : forall g, g + 0 = g
  ; G_inv_l : forall g, exists h, h + g = 0
  ; G_inv_r : forall g, exists h, g + h = 0                                
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
  { F_inv : forall f, f <> 0 -> exists g, f * g = one }.



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
  { F_inv : forall f, f <> 0 -> exists g, f * g = one }.



Class Vector_Space V F `{Group V} `{Field F} :=
  { scale : F -> V -> V
  ; V_plus_comm : forall u v, u + v = v + u
  ; V_scale_comm : forall a u v, scale a (u + v) = scale a u + scale a v
  ; V_scale_assoc : forall a b v, scale a (scale b v) = scale (a * b) v
  }.  
*)



(*



(******************************)
(** Proofs about finite sums **)
(******************************)

Local Close Scope nat_scope.

Lemma big_sum_0 : forall f n, (forall x, f x = C0) -> big_sum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    lca.
Qed.

Lemma big_sum_1 : forall f n, (forall x, f x = C1) -> big_sum f n = INR n. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    destruct n; lca.    
Qed.

Lemma big_sum_constant : forall c n, big_sum (fun x => c) n = INR n * c.
Proof.
  intros c n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite IHn.
    destruct n; lca.
Qed.

Lemma big_sum_eq : forall f g n, f = g -> big_sum f n = big_sum g n.
Proof. intros f g n H. subst. reflexivity. Qed.

Lemma big_sum_0_bounded : forall f n, (forall x, (x < n)%nat -> f x = C0) -> big_sum f n = 0. 
Proof.
  intros.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn, H. 
    lca.
    lia.
    intros.
    apply H.
    lia.
Qed.

Lemma big_sum_eq_bounded : forall f g n, (forall x, (x < n)%nat -> f x = g x) -> big_sum f n = big_sum g n.
Proof. 
  intros f g n H. 
  induction n.
  + simpl. reflexivity.
  + simpl. 
    rewrite H by lia.
    rewrite IHn by (intros; apply H; lia).
    reflexivity.
Qed.

Lemma big_sum_plus : forall f g n, big_sum (fun x => f x + g x) n = big_sum f n + big_sum g n.
Proof.
  intros f g n.
  induction n.
  + simpl. lca.
  + simpl. rewrite IHn. lca.
Qed.

Lemma big_sum_mult_l : forall c f n, c * big_sum f n = big_sum (fun x => c * f x) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_l.
    rewrite IHn.
    reflexivity.
Qed.

Lemma big_sum_mult_r : forall c f n, big_sum f n * c = big_sum (fun x => f x * c) n.
Proof.
  intros c f n.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cmult_plus_distr_r.
    rewrite IHn.
    reflexivity.
Qed.

Lemma big_sum_conj_distr : forall f n, (big_sum f n) ^* = big_sum (fun x => (f x)^* (* *)  ) n.
Proof. 
  intros f n.
  induction n.
  + simpl; lca.
  + simpl. 
    rewrite Cconj_plus_distr.
    rewrite IHn.
    reflexivity.
Qed.
    
Lemma big_sum_extend_r : forall n f, big_sum f n + f n = big_sum f (S n).
Proof. reflexivity. Qed.

Lemma big_sum_extend_l : forall n f, f O + big_sum (fun x => f (S x)) n = big_sum f (S n).
Proof.
  intros n f.
  induction n.
  + simpl; lca.
  + simpl.
    rewrite Cplus_assoc.
    rewrite IHn.
    simpl.
    reflexivity.
Qed.

Lemma big_sum_unique : forall k (f : nat -> C) n, 
  (exists x, (x < n)%nat /\ f x = k /\ (forall x', x <> x' -> f x' = 0)) ->
  big_sum f n = k.
Proof.                    
  intros k f n [x [L [Eq Unique]]].
  induction n; try lia.
  rewrite <- big_sum_extend_r.
  destruct (Nat.eq_dec x n).
  - subst. 
    rewrite big_sum_0_bounded.
    lca.
    intros.
    apply Unique.
    lia.
  - rewrite Unique by easy.
    Csimpl.
    apply IHn.
    lia.
Qed.    

Lemma big_sum_sum : forall m n f, big_sum f (m + n) = 
                          big_sum f m + big_sum (fun x => f (m + x)%nat) n. 
Proof.    
  intros m n f.
  induction m.
  + simpl. rewrite Cplus_0_l. reflexivity. 
  + simpl.
    rewrite IHm.
    repeat rewrite <- Cplus_assoc.
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

Lemma big_sum_product : forall m n f g, n <> O ->
                              big_sum f m * big_sum g n = 
                              big_sum (fun x => f (x / n)%nat * g (x mod n)%nat) (m * n). 
Proof.
  intros.
  induction m.
  + simpl; lca.
  + simpl.      
    rewrite Cmult_plus_distr_r.
    rewrite IHm. clear IHm.
    rewrite big_sum_mult_l.    
    remember ((fun x : nat => f (x / n)%nat * g (x mod n)%nat)) as h.
    replace (big_sum (fun x : nat => f m * g x) n) with
            (big_sum (fun x : nat => h ((m * n) + x)%nat) n). 
    2:{
      subst.
      apply big_sum_eq_bounded.
      intros x Hx.
      rewrite Nat.div_add_l by assumption.
      rewrite Nat.div_small; trivial.
      rewrite plus_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite plus_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- big_sum_sum.
    rewrite plus_comm.
    reflexivity.
Qed.

Lemma big_sum_ge_0 : forall f n, (forall x, 0 <= fst (f x)) -> 0 <= fst (big_sum f n).
Proof.
  intros f n H.
  induction n.
  - simpl. lra. 
  - simpl in *.
    rewrite <- Rplus_0_r at 1.
    apply Rplus_le_compat; easy.
Qed.

Lemma big_sum_gt_0 : forall f n, (forall x, 0 <= fst (f x)) -> 
                              (exists y : nat, (y < n)%nat /\ 0 < fst (f y)) ->
                              0 < fst (big_sum f n).
Proof.
  intros f n H [y [H0 H1]].
  induction n.
  - simpl. lia. 
  - simpl in *.
    bdestruct (y <? n)%nat; bdestruct (y =? n)%nat; try lia. 
    + assert (H' : 0 <= fst (f n)). { apply H. } 
      apply IHn in H2. lra. 
    + apply (big_sum_ge_0 f n) in H.
      rewrite H3 in H1.
      lra. 
Qed.

Lemma big_sum_member_le : forall (f : nat -> C) (n : nat), (forall x, 0 <= fst (f x)) ->
                      (forall x, (x < n)%nat -> fst (f x) <= fst (big_sum f n)).
Proof.
  intros f.
  induction n.
  - intros H x Lt. inversion Lt.
  - intros H x Lt.
    bdestruct (Nat.ltb x n).
    + simpl.
      rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat.
      apply IHn; easy.
      apply H.
    + assert (E: x = n) by lia.
      rewrite E.
      simpl.
      rewrite <- Rplus_0_l at 1.
      apply Rplus_le_compat.
      apply big_sum_ge_0; easy.
      lra.
Qed.  

Lemma big_sum_squeeze : forall (f : nat -> C) (n : nat), 
  (forall x, (0 <= fst (f x)))%R -> big_sum f n = C0 ->
  (forall x, (x < n)%nat -> fst (f x) = fst C0).
Proof. intros. 
       assert (H2 : (forall x, (x < n)%nat -> (fst (f x) <= 0)%R)).
       { intros. 
         replace 0%R with (fst (C0)) by easy.
         rewrite <- H0.
         apply big_sum_member_le; try easy. }
       assert (H3 : forall r : R, (r <= 0 -> 0 <= r -> r = 0)%R). 
       intros. lra. 
       simpl. 
       apply H3.
       apply H2; easy.
       apply H.
Qed.

Lemma big_sum_snd_0 : forall n f, (forall x, snd (f x) = 0) -> snd (big_sum f n) = 0.       
Proof. intros. induction n.
       - reflexivity.
       - rewrite <- big_sum_extend_r.
         unfold Cplus. simpl. rewrite H, IHn.
         lra.
Qed.

Lemma big_sum_comm : forall f g n, 
    (forall c1 c2 : C, g (c1 + c2) = g c1 + g c2) ->
    big_sum (fun x => g (f x)) n = g (big_sum f n).
Proof. intros. induction n as [| n'].
       - simpl.
         assert (H0 : g 0 - g 0 = g 0 + g 0 - g 0). 
         { rewrite <- H. rewrite Cplus_0_r. easy. }
         unfold Cminus in H0. 
         rewrite <- Cplus_assoc in H0.
         rewrite Cplus_opp_r in H0.
         rewrite Cplus_0_r in H0. 
         apply H0. 
       - do 2 (rewrite <- big_sum_extend_r).
         rewrite IHn'.
         rewrite H.
         reflexivity.
Qed.

Local Open Scope nat_scope.

Lemma big_sum_double_sum : forall (f : nat -> nat -> C) (n m : nat),
    big_sum (fun x => (big_sum (fun y => f x y) n)) m = big_sum (fun z => f (z / n) (z mod n)) (n * m).
Proof. induction m as [| m'].
       - rewrite Nat.mul_0_r.
         easy.
       - rewrite Nat.mul_succ_r.
         rewrite <- big_sum_extend_r.
         rewrite big_sum_sum.
         apply Cplus_simplify; try easy.
         apply big_sum_eq_bounded; intros.
         rewrite mult_comm.
         rewrite Nat.div_add_l; try lia. 
         rewrite (plus_comm (m' * n)).
         rewrite Nat.mod_add; try lia.
         destruct (Nat.mod_small_iff x n) as [_ HD]; try lia.
         destruct (Nat.div_small_iff x n) as [_ HA]; try lia.
         rewrite HD, HA; try lia.
         rewrite Nat.add_0_r.
         easy.
Qed.

Lemma big_sum_extend_double : forall (n m : nat) (f : nat -> nat -> C),
  (big_sum (fun i => big_sum (fun j => f i j) (S m)) (S n)) = 
  ((big_sum (fun i => big_sum (fun j => f i j) m) n) + (big_sum (fun j => f n j) m) + 
                      (big_sum (fun i => f i m) n) + f n m)%C.
Proof. intros. 
       rewrite <- big_sum_extend_r.
       assert (H' : forall a b c d, (a + b + c + d = (a + c) + (b + d))%C). 
       { intros. lca. }
       rewrite H'.
       apply Cplus_simplify; try easy.
       rewrite <- big_sum_plus.
       apply big_sum_eq_bounded; intros. 
       easy.
Qed.

Lemma big_sum_rearrange : forall (n : nat) (f g : nat -> nat -> C),
  (forall x y, x <= y -> f x y = -C1 * g (S y) x)%C ->
  (forall x y, y <= x -> f (S x) y = -C1 * g y x)%C ->
  big_sum (fun i => big_sum (fun j => f i j) n) (S n) = 
  (-C1 * (big_sum (fun i => big_sum (fun j => g i j) n) (S n)))%C.
Proof. induction n as [| n'].
       - intros. lca. 
       - intros. 
         do 2 rewrite big_sum_extend_double.
         rewrite (IHn' f g); try easy.
         repeat rewrite Cmult_plus_distr_l.
         repeat rewrite <- Cplus_assoc.
         apply Cplus_simplify; try easy.
         assert (H' : forall a b c, (a + (b + c) = (a + c) + b)%C). 
         intros. lca. 
         do 2 rewrite H'.
         rewrite <- Cmult_plus_distr_l.
         do 2 rewrite big_sum_extend_r. 
         do 2 rewrite big_sum_mult_l.
         rewrite Cplus_comm.
         apply Cplus_simplify.
         all : apply big_sum_eq_bounded; intros. 
         apply H; lia. 
         apply H0; lia. 
Qed.

Lemma Rsum_big_sum : forall n (f : nat -> R),
  fst (big_sum f n) = Rsum n f.
Proof.
  intros. induction n.
  - easy.
  - simpl. rewrite IHn.
    destruct n.
    + simpl. lra.
    + rewrite tech5. simpl. easy.
Qed.


*)




(******************)
(* Sum Over Reals *)
(******************)

(*

Definition Rsum (n : nat) (f : nat -> R) : R :=
  match n with
  | O => 0
  | S n => sum_f_R0 f n
  end.

Lemma Rsum_eq :
  forall n f1 f2,
    (forall i, f1 i = f2 i) -> Rsum n f1 = Rsum n f2.
Proof.
  intros. induction n.
  - easy.
  - simpl. destruct n.
    + simpl. apply H.
    + simpl. simpl in IHn. rewrite IHn. rewrite H. easy.
Qed.

Lemma Rsum_eq_bounded :
  forall n f1 f2,
    (forall i, (i < n)%nat -> f1 i = f2 i) -> Rsum n f1 = Rsum n f2.
Proof.
  intros. 
  induction n; simpl.
  reflexivity.
  destruct n; simpl.
  apply H. lia.
  simpl in IHn. rewrite IHn. 
  rewrite H by lia. easy.
  intros. apply H; lia.
Qed.

Lemma Rsum_extend : forall n (f : nat -> R),
  Rsum (S n) f = (f n + Rsum n f)%R.
Proof. intros. destruct n; simpl; lra. Qed.

Lemma Rsum_shift : forall n (f : nat -> R),
  Rsum (S n) f = (f O + Rsum n (fun x => f (S x)))%R.
Proof.
  intros n f. 
  simpl.
  induction n; simpl.
  lra.
  rewrite IHn.
  destruct n; simpl; lra.
Qed.

Lemma Rsum_plus_range : forall m n f,
  Rsum (m + n) f = (Rsum m f + Rsum n (fun x => f (x + m)%nat))%R.
Proof.
  intros m n f.
  induction n.
  simpl. 
  rewrite Nat.add_0_r. 
  lra.
  replace (m + S n)%nat with (S (m + n)) by lia. 
  rewrite 2 Rsum_extend.
  rewrite IHn.
  rewrite Nat.add_comm.
  lra.
Qed.

Lemma Rsum_twice : forall n f,
  Rsum (2 * n) f = (Rsum n f + Rsum n (fun x => f (x + n)%nat))%R.
Proof.
  intros n f. replace (2 * n)%nat with (n + n)%nat by lia. apply Rsum_plus_range.
Qed.

Lemma Rsum_plus: forall n f g,
  Rsum n (fun x => (f x + g x)%R) = ((Rsum n f) + (Rsum n g))%R.
Proof.
  intros n f g.
  induction n.
  simpl. lra.
  repeat rewrite Rsum_extend.
  rewrite IHn. lra.
Qed.

Lemma nested_Rsum : forall m n f,
  Rsum (2 ^ (m + n)) f 
    = Rsum (2 ^ m) (fun x => Rsum (2 ^ n) (fun y => f (x * 2 ^ n + y)%nat)).
Proof.
  intros m n.
  replace (2 ^ (m + n))%nat with (2 ^ n * 2 ^ m)%nat by (rewrite Nat.pow_add_r; lia).
  induction m; intro f.
  simpl.
  rewrite Nat.mul_1_r.
  reflexivity.
  replace (2 ^ n * 2 ^ S m)%nat with (2 * (2 ^ n * 2 ^ m))%nat by (simpl; lia).
  replace (2 ^ S m)%nat with (2 * 2 ^ m)%nat by (simpl; lia).
  rewrite 2 Rsum_twice.
  rewrite 2 IHm.
  apply f_equal2; try reflexivity.
  apply Rsum_eq.
  intro x.
  apply Rsum_eq.
  intro y.
  apply f_equal.
  lia.
Qed.

Lemma Rsum_scale : forall n f r,
  (r * Rsum n f = Rsum n (fun x => r * f x))%R.
Proof.
  intros n f r.
  induction n.
  simpl. lra.
  rewrite 2 Rsum_extend.
  rewrite <- IHn. lra.
Qed.

Lemma Rsum_0 : forall f n, (forall x : nat, f x = 0) -> Rsum n f = 0.
Proof.
  intros f n Hf. 
  induction n. reflexivity. 
  rewrite Rsum_extend, IHn, Hf. lra.
Qed.


*)
