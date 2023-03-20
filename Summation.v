Require Import List.
Require Export Prelim.
 
 
  
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



(* TODO: 

Lemma test : forall x1 x2 x3 x4 x5, 1 + x1 * x2 + x3 + x4 = 2 + x2 + x4... 
could use free ring and then call ring tactic 

Look in qwire's monoid file for an example 

*)



(* Geq_dec could be in Monoid, but then lists and matrices wont be monoids *)
Class Ring R `{Comm_Group R} :=
  { Gone : R
  ; Gmult : R -> R -> R                 
  ; Gmult_1_l : forall a, Gmult Gone a = a
  ; Gmult_1_r : forall a, Gmult a Gone = a
  ; Gmult_assoc : forall a b c, Gmult a (Gmult b c) = Gmult (Gmult a b) c 
  ; Gmult_plus_distr_l : forall a b c, Gmult c (a + b) = (Gmult c a) + (Gmult c b)
  ; Gmult_plus_distr_r : forall a b c, Gmult (a + b) c = (Gmult a c) + (Gmult b c)
  ; Geq_dec : forall a b : R, { a = b } + { a <> b }             
  }.

Class Comm_Ring R `{Ring R} :=
  { Gmult_comm : forall a b, Gmult a b = Gmult b a }.

(* I also add 1 <> 0 here, since it is helpful in VecSet *)
Class Domain R `{Ring R} :=
  { Gmult_neq_0 : forall a b, a <> 0 -> b <> 0 -> Gmult a b <> 0 
  ; G1_neq_0' : Gone <> Gzero }.


Infix "*" := Gmult : group_scope.
Notation "1" := Gone : group_scope.


Class Field F `{Comm_Ring F} :=
  { Ginv : F -> F
  ; G1_neq_0 : 1 <> 0
  ; Ginv_r : forall f, f <> 0 -> f * (Ginv f) = 1 }.

Definition Gdiv {G} `{Field G} (g1 g2 : G) := Gmult g1 (Ginv g2).

Notation "/ x" := (Ginv x) : group_scope.
Infix "/" := Gdiv : group_scope.


Class Module_Space V F `{Comm_Group V} `{Comm_Ring F} :=
  { Vscale : F -> V -> V 
  ; Vscale_1 : forall v, Vscale 1 v = v
  ; Vscale_dist : forall a u v, Vscale a (u + v) = Vscale a u + Vscale a v
  ; Vscale_assoc : forall a b v, Vscale a (Vscale b v) = Vscale (a * b) v
  }.  

Infix "⋅" := Vscale (at level 40) : group_scope.

Class Vector_Space (V F : Type) `{Comm_Group V} `{Field F} {H : Module_Space V F}.


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
  
Lemma Gopp_unique_l : forall {G} `{Group G} (g h : G),
  h + g = 0 -> h = Gopp g.
Proof. intros.
       rewrite <- (Gopp_l g) in H1.
       apply Gplus_cancel_r in H1.
       easy.
Qed.

Lemma Gopp_unique_r : forall {G} `{Group G} (g h : G),
  g + h = 0 -> h = - g.
Proof. intros.
       rewrite <- (Gopp_r g) in H1.
       apply Gplus_cancel_l in H1.
       easy.
Qed.

Lemma Gopp_involutive : forall {G} `{Group G} (g : G),
  - (- g) = g.
Proof. intros. 
       rewrite <- (Gopp_unique_r (- g) g); auto.
       apply Gopp_l.
Qed. 


Lemma Gopp_plus_distr : forall {G} `{Group G} (g h : G),
  - (g + h) = - h + - g.
Proof. intros. 
       rewrite (Gopp_unique_r (g + h) (- h + - g)); auto.
       rewrite Gplus_assoc, <- (Gplus_assoc g), Gopp_r, Gplus_0_r, Gopp_r.
       easy. 
Qed.


Lemma Gopp_eq_0 : forall {G} `{Group G} (g : G),
  - g = 0 -> g = 0.
Proof. intros. 
       apply (f_equal Gopp) in H1. 
       rewrite Gopp_involutive in H1; subst.
       symmetry. 
       apply Gopp_unique_l.
       rewrite Gplus_0_r.
       easy.
Qed.

Lemma Vscale_zero : forall {V F} `{Module_Space V F} (c : F),
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


Lemma Gopp_neg_1 : forall {R} `{Ring R} (r : R), -1%G * r = -r.
Proof. intros.
       apply (Gplus_cancel_l _ _ r).
       rewrite Gopp_r.
       replace (Gplus r) with (Gplus (1 * r)) by (rewrite Gmult_1_l; easy).
       rewrite <- Gmult_plus_distr_r, Gopp_r, Gmult_0_l; easy.
Qed.       

Lemma Gopp_neg_1_r : forall {R} `{Ring R} (r : R), r * -1%G = -r.
Proof. intros.
       apply (Gplus_cancel_r _ _ r).
       rewrite Gopp_l.
       replace (r * - (1) + r) with (r * - (1) + r * 1) by (rewrite Gmult_1_r; easy).
       rewrite <- Gmult_plus_distr_l, Gopp_l, Gmult_0_r; easy.
Qed.  

Lemma Gopp_mult_distr_l : forall {R} `{Ring R} (r1 r2 : R), - (r1 * r2) = -r1 * r2.
Proof. intros.
       rewrite <- Gopp_neg_1, <- (Gopp_neg_1 r1), Gmult_assoc; easy.
Qed.

Lemma Gopp_mult_distr_r : forall {R} `{Ring R} (r1 r2 : R), - (r1 * r2) = r1 * -r2.
Proof. intros.
       rewrite <- Gopp_neg_1_r, <- (Gopp_neg_1_r r2), Gmult_assoc; easy.
Qed.

Lemma Gmult_integral : forall {R} `{Domain R} (a b : R), a * b = 0 -> a = 0 \/ b = 0.
Proof. intros.
       destruct (Geq_dec a 0); destruct (Geq_dec b 0); auto.
       apply (Gmult_neq_0 a b) in n; auto.
       easy.
Qed.

Lemma Ginv_l : forall {F} `{Field F} (f : F), f <> 0 -> (Ginv f) * f = 1.
Proof. intros; rewrite Gmult_comm; apply Ginv_r; easy. Qed.

Lemma Gmult_cancel_l : forall {R} `{Domain R} (g h a : R), 
  a <> 0 -> a * g = a * h -> g = h.
Proof. intros. 
       apply (f_equal_gen Gplus Gplus) in H5; auto.
       apply (f_equal_inv (a * - g)) in H5. 
       rewrite <- 2 Gmult_plus_distr_l, Gopp_r, Gmult_0_r in H5.
       symmetry in H5.
       apply Gmult_integral in H5.
       destruct H5; try easy.
       rewrite <- (Gplus_0_l g), <- H5, <- Gplus_assoc, Gopp_l, Gplus_0_r.
       easy.
Qed.

Lemma Gmult_cancel_r : forall {R} `{Domain R} (g h a : R), 
  a <> 0 -> g * a = h * a -> g = h.
Proof. intros. 
       apply (f_equal_gen Gplus Gplus) in H5; auto.
       apply (f_equal_inv ((- g) * a)) in H5. 
       rewrite <- 2 Gmult_plus_distr_r, Gopp_r, Gmult_0_l in H5.
       symmetry in H5.
       apply Gmult_integral in H5.
       destruct H5; try easy.
       rewrite <- (Gplus_0_l g), <- H5, <- Gplus_assoc, Gopp_l, Gplus_0_r.
       easy.
Qed.


(* this is the best setup I found for conveying the fact that a field is a domain *)
Lemma field_is_domain : forall {F} `{Field F} a b, a <> 0 -> b <> 0 -> a * b <> 0.
Proof. intros. 
       unfold not; intros. 
       apply H6.
       rewrite <- (Gmult_1_l b), <- (Ginv_l a), 
         <- Gmult_assoc, H7, Gmult_0_r; auto.
Qed.

Global Program Instance Field_is_Domain : forall (F : Type) `{Field F}, Domain F.                      
Next Obligation.
  apply field_is_domain; auto.
Qed.       
Next Obligation.
  apply G1_neq_0.
Qed.       


Lemma Field_is_Domain' : forall {F} `{Field F}, Domain F.
Proof. intros.
       apply Field_is_Domain in H4.
       easy.
Qed.

Lemma Ginv_mult_distr : forall {F} `{Field F} (a b : F),
    a <> 0 -> b <> 0 ->
    / (a * b) = / a * / b.
Proof. intros.        
       apply (Gmult_cancel_r _ _ (a * b)).
       apply field_is_domain; auto.
       rewrite Ginv_l; try apply Gmult_neq_0; auto.
       rewrite <- Gmult_assoc, (Gmult_assoc _ a), (Gmult_comm _ a), <- (Gmult_assoc a).
       rewrite Ginv_l, Gmult_1_r, Ginv_l; easy.
Qed.




(* showing that nat is a monoid *)

Global Program Instance nat_is_monoid : Monoid nat := 
  { Gzero := 0
  ; Gplus := plus
  }.
Solve All Obligations with program_simpl; try lia.



(*************************)
(** Summation functions *)
(*************************)



(* multiplication by nats *)
Fixpoint times_n {G} `{Monoid G} (g : G) (n : nat) :=
  match n with
  | 0 => 0
  | S n' => g + times_n g n'
  end.
      
(* multiplication by positives *)
Fixpoint times_pos {R : Type} `{Monoid R} (r : R) (p : positive) : R :=
  match p with 
  | xH => r
  | xO p' => (times_pos r p') + (times_pos r p')
  | xI p' => r + (times_pos r p') + (times_pos r p')
  end.             

(* now multiplication by an integer *)
Definition times_z {R : Type} `{Group R} (r : R) (z : Z) : R :=
  match z with
    | Z0 => 0
    | Zpos p => times_pos r p
    | Zneg p => - times_pos r p
  end.

Fixpoint G_big_plus {G} `{Monoid G} (gs : list G) : G := 
  match gs with
  | nil => 0 
  | g :: gs' => g + (G_big_plus gs')
  end. 


(* ring mult could also be seen as a monoid, but I think its better to have 
   separate functions for plus and mult so its more clear what is going on *)

(* exponentiation *)
Fixpoint Gpow {R} `{Ring R} (r : R) (n : nat) : R :=  
  match n with
  | 0%nat => 1
  | S n' => Gmult r (Gpow r n')
  end.

Infix "^" := Gpow : group_scope.

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


(** * Gpow Lemmas *)

Lemma Gpow_add_r : forall {R} `{Ring R} (r : R) (n m : nat), (r ^ (n + m) = r^n * r^m).
Proof.
  intros. induction n. simpl. rewrite Gmult_1_l; easy. 
  simpl. rewrite IHn. rewrite Gmult_assoc; easy. 
Qed.

Lemma Gpow_mult_r : forall {R} `{Ring R} (r : R) (n m : nat), (r ^ (n * m) = (r ^ n) ^ m).
Proof.
  intros. induction m. rewrite Nat.mul_0_r. easy.
  replace (n * (S m))%nat with (n * m + n)%nat by lia.
  replace (S m) with (m + 1)%nat by lia.
  do 2 rewrite Gpow_add_r. 
  rewrite IHm. simpl. 
  rewrite Gmult_1_r. 
  easy. 
Qed.

Lemma Gpow_mult_l : forall {R} `{Ring R} (r1 r2 : R) (n : nat), 
  r1 * r2 = r2 * r1 ->
  (r1 * r2) ^ n = r1 ^ n * r2 ^ n.
Proof. induction n as [| n']; intros. 
       - simpl; rewrite Gmult_1_l; auto.
       - simpl; rewrite IHn'; auto.
         rewrite Gmult_assoc, <- (Gmult_assoc r1).
         assert (H' : forall m, r2 * r1 ^ m = r1 ^ m * r2).
         { intros. 
           induction m; simpl.
           rewrite Gmult_1_r, Gmult_1_l; auto.
           rewrite Gmult_assoc, <- H3, <- Gmult_assoc, IHm, Gmult_assoc; auto. }
         rewrite H', 2 Gmult_assoc; auto.
Qed.         

Lemma Gpow_nonzero : forall {R} `{Domain R} (r : R) (n : nat), r <> 0 -> r ^ n <> 0.
Proof.
  intros.
  induction n.
  - simpl; apply G1_neq_0'.
  - simpl. 
    apply Gmult_neq_0; easy.
Qed.



(** * Big sum lemmas *)

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

(* this is just big_sum_extend_l *)
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

Lemma big_plus_constant : forall {G} `{Monoid G} (l : list G) (g : G),
  (forall h, In h l -> h = g) -> G_big_plus l = (times_n g (length l))%nat.
Proof. induction l; try easy.
       intros; simpl. 
       rewrite (IHl g), (H0 a); auto.
       left; easy.
       intros. 
       apply H0; right; easy.
Qed.

Lemma big_plus_app : forall {G} `{Monoid G} (l1 l2 : list G),
  G_big_plus l1 + G_big_plus l2 = G_big_plus (l1 ++ l2).
Proof. intros. 
       induction l1; simpl.
       - apply Gplus_0_l.
       - rewrite <- IHl1, Gplus_assoc; easy.
Qed.

Lemma big_plus_inv : forall {G} `{Group G} (l : list G),
  - (G_big_plus l) = G_big_plus (map Gopp (rev l)).
Proof. induction l; simpl.
       rewrite <- (Gopp_unique_l 0 0); auto.
       rewrite Gplus_0_r; easy. 
       rewrite Gopp_plus_distr, map_app, <- big_plus_app, <- IHl; simpl. 
       rewrite Gplus_0_r; easy. 
Qed.

(* could be generalized to semi-rings... *)
Lemma times_n_nat : forall n k,
  times_n k n = (k * n)%nat.
Proof. induction n; try easy.
       intros; simpl.
       rewrite IHn. 
       lia.
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

Lemma big_sum_scale_l : forall {G} {V} `{Module_Space G V} c f n, 
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
 
Lemma big_sum_unique2 : forall {G} `{Monoid G} k (f : nat -> G) n, 
  (exists x y, (x < y)%nat /\ (y < n)%nat /\ (f x) + (f y) = k /\
                 (forall x', x' < n -> x <> x' -> y <> x' -> f x' = 0)) ->
  big_sum f n = k.
Proof.                    
  intros G H k f n [x [y [L1 [L2 [Eq Unique]]]]].
  induction n; try lia.
  rewrite <- big_sum_extend_r.
  destruct (Nat.eq_dec y n).
  - subst. 
    apply f_equal_gen; auto; apply f_equal.
    apply big_sum_unique.
    exists x; split; auto; split; auto.
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
    replace (f m) with (g O) by (subst; rewrite Nat.add_0_r; reflexivity).
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
      rewrite Nat.add_0_r.
      rewrite Nat.add_mod by assumption.
      rewrite Nat.mod_mul by assumption.
      rewrite Nat.add_0_l.
      repeat rewrite Nat.mod_small; trivial. }
    rewrite <- big_sum_sum.
    rewrite Nat.add_comm.
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
         rewrite Nat.mul_comm.
         rewrite Nat.div_add_l; try lia.  
         rewrite (Nat.add_comm (m' * n)).
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

(* this is basically big_sum_assoc *)
Lemma big_sum_swap_order : forall {G} `{Comm_Group G} (f : nat -> nat -> G) m n,
  big_sum (fun j => big_sum (fun i => f j i) m) n = 
    big_sum (fun i => big_sum (fun j => f j i) n) m.
Proof.
  intros.
  induction n; simpl.
  rewrite big_sum_0 by auto. reflexivity.
  rewrite IHn. rewrite <- big_sum_plus. reflexivity.
Qed.

Lemma big_sum_diagonal : forall {G} `{Monoid G} (f : nat -> nat -> G) n,
    (forall i j, (i < n)%nat -> (j < n)%nat -> (i <> j)%nat -> f i j = 0) ->
    big_sum (fun i => big_sum (fun j => f i j) n) n = big_sum (fun i => f i i) n.
Proof.
  intros. apply big_sum_eq_bounded. intros.
  apply big_sum_unique. 
  exists x; split; simpl; auto.
Qed.



Local Open Scope nat_scope. 

(* TODO: these should all probably have better names *)
Lemma big_sum_rearrange : forall {G} `{Ring G} (n : nat) (f g : nat -> nat -> G),
  (forall x y, x <= y -> f x y = (-1%G) * (g (S y) x))%G ->
  (forall x y, y <= x -> f (S x) y = (-1%G) * (g y x))%G ->
  big_sum (fun i => big_sum (fun j => f i j) n) (S n) = 
  (-1%G * (big_sum (fun i => big_sum (fun j => g i j) n) (S n)))%G.
Proof. induction n as [| n'].
       - intros; simpl. 
         rewrite Gplus_0_r, Gmult_0_r; easy.
       - intros. 
         do 2 rewrite big_sum_extend_double.
         rewrite (IHn' f g); try easy.
         repeat rewrite Gmult_plus_distr_l.
         repeat rewrite <- Gplus_assoc.
         apply f_equal_gen; try apply f_equal; try easy.
         assert (H' : forall a b c, (a + (b + c) = (a + c) + b)%G). 
         intros. 
         rewrite (Gplus_comm b), Gplus_assoc; easy.
         do 2 rewrite H'.
         rewrite <- Gmult_plus_distr_l.
         do 2 rewrite (@big_sum_extend_r G H). 
         do 2 rewrite (@big_sum_mult_l G _ _ _ H2).  
         rewrite Gplus_comm.
         apply f_equal_gen; try apply f_equal.
         all : apply big_sum_eq_bounded; intros. 
         apply H3; lia. 
         apply H4; lia. 
Qed.

Lemma big_sum_rearrange_cancel : forall {G} `{Ring G} (n : nat) (f : nat -> nat -> G),
  (forall x y, x <= y -> f x y = (-1%G) * (f (S y) x))%G ->
  (forall x y, y <= x -> f (S x) y = (-1%G) * (f y x))%G ->
  big_sum (fun i => big_sum (fun j => f i j) n) (S n) = 0%G.
Proof. induction n as [| n'].
       - intros; simpl. 
         rewrite Gplus_0_r; easy.
       - intros. 
         rewrite big_sum_extend_double.
         rewrite (IHn' f); try easy.
         rewrite Gplus_0_l.
         rewrite <- big_sum_extend_r.
         repeat rewrite <- Gplus_assoc.
         rewrite H3; auto.
         replace (- (1) * f (S n') n' + f (S n') n')%G with 0%G. 
         rewrite Gplus_0_r, <- big_sum_plus.
         rewrite big_sum_0_bounded; auto; intros. 
         rewrite H4; try lia.
         all : rewrite Gopp_neg_1, Gopp_l; easy.
Qed.


Local Close Scope nat_scope.


(* Lemma specifically for sums over nats
   TODO: can we generalize to other data types with comparison ops?
         (see Rsum_le in RealAux.v) *)
Lemma Nsum_le : forall n f g,
  (forall x, x < n -> f x <= g x)%nat ->
  (big_sum f n <= big_sum g n)%nat.
Proof.
  intros. induction n. simpl. easy.
  simpl.
  assert (f n <= g n)%nat.
  { apply H. lia. }
  assert (big_sum f n <= big_sum g n)%nat.
  { apply IHn. intros. apply H. lia. }
  lia.
Qed.
 







(*
 *
 *
 *)



(** * developing l_a tactics for all these new typeclasses *)


(** solve monoid tactic *)

Inductive mexp {G} : Type :=
| mIdent : mexp
| mVar : G -> mexp
| mOp : mexp -> mexp -> mexp.


(* turns mexp into g *)
Fixpoint mdenote {G} `{Monoid G} (me : mexp) : G :=
  match me with
  | mIdent => 0
  | mVar v => v
  | mOp me1 me2 => mdenote me1 + mdenote me2
  end.

(* we also want something that takes list G to G, this is done by G_big_plus *)

(* turns mexp into list G *)
Fixpoint flatten {G} `{Monoid G} (me : mexp) : list G :=
  match me with
  | mIdent => nil
  | mVar x => x :: nil
  | mOp me1 me2 => flatten me1 ++ flatten me2
  end.

Theorem flatten_correct : forall {G} `{Monoid G} me, 
  mdenote me = G_big_plus (flatten me).
Proof. 
  induction me; simpl; auto.
  rewrite Gplus_0_r; easy.
  rewrite <- big_plus_app, IHme1, IHme2.  
  easy. 
Qed.

Theorem monoid_reflect : forall {G} `{Monoid G} me1 me2,
  G_big_plus (flatten me1) = G_big_plus (flatten me2) -> 
  mdenote me1 = mdenote me2.
Proof.
  intros; repeat rewrite flatten_correct; assumption.
Qed.

(*
(* Simplify parts of an expression, but not the whole thing *)
Ltac simpl_arg e := let e' := fresh "e" in
                    set (e' := e);
                    simpl in e';
                    unfold e';
                    clear e'. 

Ltac simpl_args :=
  match goal with
  | [ |- ?e1 = ?e2 ] => simpl_arg e1; simpl_arg e2
  end. 
*)

Ltac reify_mon G me :=
  match me with
  | 0 => constr:(@mIdent G)
  | ?me1 + ?me2 =>
      let r1 := reify_mon G me1 in
      let r2 := reify_mon G me2 in
      constr:(mOp r1 r2)
  | _ => constr:(mVar me)
  end.

Ltac solve_monoid :=
  match goal with
  | [ |- @eq ?G ?me1 ?me2 ] =>
      let r1 := reify_mon G me1 in
      let r2 := reify_mon G me2 in
      change (mdenote r1 = mdenote r2);
      apply monoid_reflect;
      simpl; try easy
  end.

 
Lemma sm_test0 : forall {G} `{Monoid G}, 0 = 0.
Proof. intros. 
       solve_monoid.
Qed.

Lemma sm_test1 : forall {G} `{Monoid G} a b c d, a + b + c + d = a + (b + c) + d + 0 + 0.
Proof. intros. 
       solve_monoid.
Qed.

Lemma sm_test2 : forall {G} `{Monoid G}, 0 = 0 + 0.
Proof. intros. 
       solve_monoid.
Qed.


(** solve_group tactic *)

(* there is a lot of repeated code here, perhaps could simplify things *)
Inductive gexp {G} : Type :=
| gIdent : gexp
| gVar : G -> gexp
| gOp : gexp -> gexp -> gexp
| gInv : gexp -> gexp.

Fixpoint gdenote {G} `{Group G} (ge : gexp) : G :=
  match ge with
  | gIdent => 0
  | gVar v => v
  | gOp ge1 ge2 => gdenote ge1 + gdenote ge2
  | gInv v => - gdenote v
  end.

Fixpoint gflatten {G} `{Group G} (ge : gexp) : list G :=
  match ge with
  | gIdent => nil
  | gVar x => x :: nil
  | gOp ge1 ge2 => gflatten ge1 ++ gflatten ge2
  | gInv ge' => map Gopp (rev (gflatten ge'))
  end.

Theorem gflatten_correct : forall {G} `{Group G} ge, 
    gdenote ge = G_big_plus (gflatten ge).
Proof. 
  induction ge; simpl; auto.
  rewrite Gplus_0_r; easy.
  rewrite <- big_plus_app, IHge1, IHge2.  
  easy. 
  rewrite IHge, big_plus_inv. 
  easy.
Qed.
  

Theorem group_reflect : forall {G} `{Group G} ge1 ge2,
  G_big_plus (gflatten ge1) = G_big_plus (gflatten ge2) -> 
  gdenote ge1 = gdenote ge2.
Proof.
  intros; repeat rewrite gflatten_correct; assumption.
Qed.

Lemma big_plus_reduce : forall {G} `{Group G} a l,
  G_big_plus (a :: l) = a + G_big_plus l.
Proof. intros. easy. Qed.
  
Lemma big_plus_inv_r : forall {G} `{Group G} a l,
  G_big_plus (a :: -a :: l) = G_big_plus l.
Proof. 
  intros; simpl. 
  rewrite Gplus_assoc, Gopp_r, Gplus_0_l; easy.
Qed.

Lemma big_plus_inv_l : forall {G} `{Group G} a l,
  G_big_plus (-a :: a :: l) = G_big_plus l.
Proof. 
  intros; simpl. 
  rewrite Gplus_assoc, Gopp_l, Gplus_0_l; easy.
Qed.


Ltac reify_grp G ge :=
  match ge with
  | 0 => constr:(@gIdent G)
  | ?ge1 + ?ge2 =>
      let r1 := reify_grp G ge1 in
      let r2 := reify_grp G ge2 in
      constr:(gOp r1 r2)
  | ?ge1 - ?ge2 =>
      let r1 := reify_grp G ge1 in
      let r2 := reify_grp G ge2 in
      constr:(gOp r1 (gInv r2))             
  | -?ge => 
      let r := reify_grp G ge in
      constr:(gInv r)
  | _ => constr:(gVar ge)
  end.

Ltac solve_group :=
  unfold Gminus;
  match goal with
  | [ |- @eq ?G ?me1 ?me2 ] =>
      let r1 := reify_grp G me1 in
      let r2 := reify_grp G me2 in
      (* replace me1 with (gdenote r1) by easy;
         replace me2 with (gdenote r2) by easy; *)
      change (@eq ?G ?me1 ?me2) with (gdenote r1 = gdenote r2); 
      apply group_reflect; simpl gflatten;
      repeat (rewrite Gopp_involutive);
      repeat (try (rewrite big_plus_inv_r); 
              try (rewrite big_plus_inv_l); 
              try rewrite big_plus_reduce); simpl; try easy;
      repeat (rewrite Gplus_0_l); 
      repeat (rewrite Gplus_0_r);
      repeat (rewrite Gplus_assoc); try easy
  end.

Lemma test2 : forall {G} `{Group G} a b c d, a + b + c + d + 0 - d = a + (b + c) + d - d.
Proof. intros. solve_group. Qed.
 
Lemma test3 : forall {G} `{Group G} a b c, - (a + b + c) + a  = 0 - c - b.
Proof. intros. solve_group. Qed.

Lemma test4 : forall {G} `{Group G} a, 0 = a + -a.
Proof. intros. solve_group. Qed.

Lemma test5 : forall {G} `{Group G} a, -a + a + a = a.
Proof. intros. solve_group. Qed.

Lemma test6 : forall {G} `{Group G} a, a = -a + (a + a).
Proof. intros. solve_group. Qed.

Lemma test7 : forall {G} `{Group G}, 0 = -0.
Proof.  intros. solve_group. Qed.
               



(** * multiplication by integers *)


(** times_n lemmas *) 
Lemma times_n_add_r : forall {G} `{Monoid G} (g : G) (n1 n2 : nat), 
  times_n g (n1 + n2) = times_n g n1 + times_n g n2.
Proof. intros. 
       rewrite <- 3 big_sum_constant, big_sum_sum; easy.
Qed.

Lemma times_n_add_l : forall {G} `{Monoid G} (g1 g2 : G) (n : nat), 
  g1 + g2 = g2 + g1 ->
  times_n g1 n + times_n g2 n = times_n (g1 + g2) n. 
Proof. intros. 
       induction n; simpl.
       - rewrite Gplus_0_l; easy.
       - rewrite Gplus_assoc, <- (Gplus_assoc g1).
         assert (H' : forall m, times_n g1 m + g2 = g2 + times_n g1 m).
         { induction m; simpl. 
           - rewrite Gplus_0_l, Gplus_0_r; auto.
           - rewrite <- Gplus_assoc, IHm, 2 Gplus_assoc, H0; auto. }
         rewrite H', <- IHn.
         repeat rewrite Gplus_assoc; easy.
Qed.

Lemma times_n_mult : forall {G} `{Ring G} (g1 g2 : G) (n1 n2 : nat), 
  times_n (g1 * g2) (n1 * n2) = times_n g1 n1 * times_n g2 n2.
Proof. induction n1.
       - intros; simpl. 
         rewrite Gmult_0_l; easy.
       - intros; simpl.
         rewrite times_n_add_r, Gmult_plus_distr_r, IHn1. 
         apply f_equal_gen; try apply f_equal; auto. 
         rewrite <- 2 big_sum_constant, big_sum_mult_l; easy. 
Qed.

Lemma times_n_mult_r : forall {G} `{Monoid G} (g : G) (n1 n2 : nat), 
  times_n g (n1 * n2) = times_n (times_n g n1) n2.
Proof. induction n1; simpl; intros. 
       - rewrite <- big_sum_constant, big_sum_0_bounded; auto.
       - rewrite times_n_add_r, <- times_n_add_l.
         rewrite IHn1; easy.
         destruct n1.
         simpl; solve_monoid. 
         replace (g + times_n g (S n1)) with (g + times_n g n1 + g). 
         rewrite <- 2 big_sum_constant, <- big_sum_extend_l; auto.
         rewrite <- 2 big_sum_constant, <- big_sum_extend_r, Gplus_assoc; auto.
Qed.

(** times_pos lemmas *)
Lemma times_pos_to_nat : forall {R : Type} `{Monoid R} (r : R) (p : positive),
  times_pos r p = times_n r (Pos.to_nat p).
Proof. intros. 
       induction p.
       - rewrite Pos2Nat.inj_xI; simpl.  
         rewrite IHp, Nat.add_0_r, times_n_add_r, Gplus_assoc. 
         easy.
       - rewrite Pos2Nat.inj_xO; simpl. 
         rewrite IHp, Nat.add_0_r, times_n_add_r. 
         easy.
       - simpl. 
         rewrite Gplus_0_r.
         easy. 
Qed.

Lemma times_pos_add_l : forall {R : Type} `{Monoid R} (p : positive) (r1 r2 : R),
  r1 + r2 = r2 + r1 ->
  times_pos (r1 + r2) p = times_pos r1 p + times_pos r2 p.
Proof. intros. 
       rewrite 3 times_pos_to_nat, times_n_add_l; auto.
Qed.

Lemma times_pos_add_r : forall {R : Type} `{Monoid R} (r : R) (p1 p2 : positive),
  times_pos r (p1 + p2) = times_pos r p1 + times_pos r p2.
Proof. intros.
       rewrite 3 times_pos_to_nat, Pos2Nat.inj_add, times_n_add_r.
       easy. 
Qed.

Lemma times_pos_mult_r : forall {R : Type} `{Monoid R} (r : R) (p1 p2 : positive),
  times_pos r (p1 * p2) = times_pos (times_pos r p1) p2.
Proof. intros. 
       do 3 rewrite times_pos_to_nat.
       rewrite Pos2Nat.inj_mul, times_n_mult_r.
       easy.
Qed.

Lemma times_pos_mult : forall {R : Type} `{Ring R} (r1 r2 : R) (p1 p2 : positive),
  times_pos (r1 * r2) (p1 * p2) = times_pos r1 p1 * times_pos r2 p2.
Proof. intros. 
       rewrite 3 times_pos_to_nat, Pos2Nat.inj_mul, <- times_n_mult.
       easy. 
Qed.

Lemma times_pos_comm1 : forall {R : Type} `{Monoid R} (r : R) (p : positive),
  r + times_pos r p = times_pos r p + r.
Proof. induction p; simpl; auto.
       - rewrite <- 3 Gplus_assoc, <- IHp, (Gplus_assoc r (times_pos r p)), 
           IHp, 2 Gplus_assoc, <- IHp, 2 Gplus_assoc; auto. 
       - rewrite <- Gplus_assoc, <- IHp, 2 Gplus_assoc, IHp; auto.
Qed.   

Lemma times_pos_comm2 : forall {R : Type} `{Group R} (r : R) (p : positive),
  (-r) + times_pos r p = times_pos r p + (-r).
Proof. intros. 
       rewrite <- Gplus_0_l.
       replace 0 with (-r + r). 
       rewrite Gplus_assoc, <- (Gplus_assoc (-r)), times_pos_comm1, 
         <- 2 Gplus_assoc, Gopp_r, Gplus_0_r; auto.
       rewrite Gopp_l; easy.
Qed.
    
Lemma times_pos_succ : forall {R : Type} `{Monoid R} (r : R) (p : positive),
  times_pos r (Pos.succ p) = r + times_pos r p.
Proof. intros.
       induction p; simpl; try (solve_monoid; easy).
       - rewrite IHp, <- Gplus_assoc, (Gplus_assoc _ r), <- times_pos_comm1; solve_monoid.
Qed.

Lemma times_pos_pred_double : forall {R : Type} `{Group R} (r : R) (p : positive),
  times_pos r (Pos.pred_double p) = (- r) + (times_pos r p + times_pos r p).
Proof. intros.
       induction p; simpl; try solve_group.
       - do 4 (apply f_equal_gen; auto).
         rewrite times_pos_comm1, <- Gplus_assoc, times_pos_comm1; solve_group.
       - rewrite IHp; solve_group.
         do 4 (apply f_equal_gen; auto).
         rewrite times_pos_comm2, <- 2 Gplus_assoc, <- times_pos_comm2; solve_group.
Qed.

Lemma times_pos_opp : forall {R : Type} `{Group R} (r : R) (p : positive),
  times_pos (- r) p = - (times_pos r p). 
Proof. intros. 
       induction p; simpl.
       - rewrite IHp.
         rewrite times_pos_comm1, <- 2 Gplus_assoc, times_pos_comm1; solve_group.
       - rewrite IHp.
         solve_group.
       - easy.
Qed.

Lemma times_pos_0 : forall {R : Type} `{Monoid R} (p : positive),
  times_pos 0 p = 0.
Proof. intros.
       induction p; simpl.
       - rewrite IHp, 2 Gplus_0_l; auto. 
       - rewrite IHp, Gplus_0_l; auto. 
       - auto. 
Qed. 



(** times_z lemmas *)

Lemma times_z_add_1 : forall {R : Type} `{Group R} (r : R) (z : Z), 
  times_z r (1 + z) = r + times_z r z.
Proof. intros.
       destruct z. 
       - simpl; rewrite Gplus_0_r; easy.
       - destruct p; simpl; auto.
         rewrite times_pos_succ, 3 Gplus_assoc.
         do 2 (apply f_equal_gen; auto).
         rewrite <- Gplus_assoc, <- times_pos_comm1; solve_group.
         solve_group.
       - destruct p; simpl.
         + rewrite times_pos_comm1, <- Gplus_assoc, times_pos_comm1.
           solve_group.
         + rewrite times_pos_pred_double.
           rewrite Gplus_assoc, times_pos_comm2, <- Gplus_assoc, times_pos_comm2.
           solve_group.
         + rewrite Gopp_r; auto.
Qed.

Lemma times_z_minus_1 : forall {R : Type} `{Group R} (r : R) (z : Z), 
  times_z r ((-1) + z) = (- r) + times_z r z.
Proof. intros.
       destruct z.
       - simpl; rewrite Gplus_0_r; easy.
       - destruct p; simpl.
         + rewrite 2 Gplus_assoc, Gopp_l, Gplus_0_l. 
           easy.
         + rewrite times_pos_pred_double; auto.
         + rewrite Gopp_l; easy.
       - destruct p; simpl.
         + rewrite times_pos_succ, times_pos_comm1. 
           solve_group.
         + rewrite times_pos_comm1, <- Gplus_assoc, times_pos_comm1.
           solve_group.
         + solve_group.
Qed.

Lemma times_z_add_nat : forall {R : Type} `{Group R} (r : R) (n : nat) (z : Z), 
  times_z r (Z.of_nat n + z) = times_z r (Z.of_nat n) + times_z r z.
Proof. intros.
       induction n. 
       - solve_group.
       - replace (S n + z)%Z with (1 + (n + z))%Z by lia.
         replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.       
         repeat rewrite times_z_add_1; auto.
         rewrite IHn; solve_group.
Qed.

Lemma times_z_minus_nat : forall {R : Type} `{Group R} (r : R) (n : nat) (z : Z), 
  times_z r (- Z.of_nat n + z) = times_z r (- Z.of_nat n) + times_z r z.
Proof. intros. 
       induction n.
       - solve_group.
       - replace (- S n + z)%Z with (- 1 + (- n + z))%Z by lia.
         replace (- (S n))%Z with (- 1 + - n)%Z by lia.       
         repeat rewrite times_z_minus_1; auto.
         rewrite IHn; solve_group.
Qed.

(* this could be Group, but would be annoying *)
Lemma times_z_add_l : forall {R : Type} `{Comm_Group R} (z : Z) (r1 r2 : R),
  times_z (r1 + r2) z = times_z r1 z + times_z r2 z.
Proof. intros. 
       destruct z; simpl; auto; solve_group.
       all : rewrite times_pos_add_l; auto.
       apply Gplus_comm.
       rewrite Gopp_plus_distr.
       all : apply Gplus_comm.
Qed.     

Theorem times_z_add_r : forall {R : Type} `{Group R} (r : R) (z1 z2 : Z), 
  times_z r (z1 + z2) = times_z r z1 + times_z r z2.
Proof. intros.
       destruct (Z_plusminus_nat z1) as [n [H1 | H1]].
       - rewrite H1, times_z_add_nat; easy.
       - rewrite H1, times_z_minus_nat; easy.
Qed.

Theorem times_z_mult_r : forall {R : Type} `{Group R} (r : R) (z1 z2 : Z), 
  times_z r (z1 * z2) = times_z (times_z r z1) z2. 
Proof. intros. 
       destruct z1; destruct z2; try (solve_group; easy); simpl.
       all : try rewrite times_pos_0; auto. 
       apply Gopp_unique_l; rewrite Gplus_0_l; auto.
       all : rewrite times_pos_mult_r; try solve_group. 
       all : rewrite times_pos_opp; auto. 
       rewrite Gopp_involutive; auto.
Qed.

Theorem times_z_mult : forall {R : Type} `{Ring R} (r1 r2 : R) (z1 z2 : Z), 
  times_z (r1 * r2) (z1 * z2) = times_z r1 z1 * times_z r2 z2.
Proof. intros.
       destruct z1; destruct z2; simpl.
       all : try rewrite Gmult_0_l; auto.
       all : try rewrite Gmult_0_r; auto.
       all : rewrite times_pos_mult; auto.
       rewrite Gopp_mult_distr_r; auto.
       rewrite Gopp_mult_distr_l; auto.
       rewrite <- Gopp_mult_distr_l, <- Gopp_mult_distr_r, Gopp_involutive; auto.
Qed.       

Lemma times_z_0 : forall {G} `{Group G} (z : Z),
  times_z 0 z = 0.
Proof. intros. 
       destruct z; simpl; auto. 
       all : rewrite times_pos_0; auto.
       symmetry. 
       apply Gopp_unique_l.
       rewrite Gplus_0_l; auto.
Qed.       




(** solve_commgroup tactic *)

(* this time, we use nats to track vars since they are easily ordered *)
 Inductive cgexp : Type :=
  | cgIdent : cgexp
  | cgVar : nat -> cgexp 
  | cgOp : cgexp -> cgexp -> cgexp
  | cgInv : cgexp -> cgexp.

(*
Inductive cgexp_normal : Type :=
  | cgnIdent : cgexp_normal
  | cgnInj : nat -> cgexp_normal -> cgexp_normal
  | cgnX : Z -> cgexp_normal -> cgexp_normal.
*)

Definition cgexp_normal : Type := list Z.

Fixpoint WF_cgen (gen : cgexp_normal) : Prop := 
  match gen with
  | [] => True
  | [z] => match z with 
          | Z0 => False
          | _ => True
          end
  | z :: l => WF_cgen l
  end.

Definition V0 : cgexp_normal := [1%Z].

Definition Vi (i : nat) : cgexp_normal := repeat Z0 i ++ [1%Z].

Lemma nth_Vi : forall (i : nat) (z : Z), nth i (Vi i) z = 1%Z.
Proof. intros.
       unfold Vi.
       rewrite app_nth2. 
       all : rewrite repeat_length; try lia.
       replace (i - i)%nat with O by lia; easy.
Qed.

Lemma nth_Vi_miss : forall (i j : nat), i <> j -> nth i (Vi j) 0%Z = 0%Z.
Proof. intros.
       unfold Vi.
       bdestruct (i <? j)%nat; bdestruct (j <? i)%nat; bdestruct (i =? j)%nat; try lia. 
       - rewrite app_nth1. 
         rewrite nth_repeat; auto.
         rewrite repeat_length; auto. 
       - rewrite app_nth2. 
         all : rewrite repeat_length; auto.
         destruct (i - j)%nat as [|n] eqn:E; try lia; simpl.
         destruct n; auto.
Qed.


Lemma succ_Vi : forall (i : nat),
  Vi (S i) = Z0 :: Vi i.
Proof. easy. Qed.

(*
Lemma WF_cons : forall (z : Z) (l : cgexp_normal),
  l <> [] ->
  WF_cgen l ->
  WF_cgen (z :: l).
Proof. intros. 
       destruct l; easy.
Qed.

Lemma WF_cons_conv : forall (z : Z) (l : cgexp_normal),
  WF_cgen (z :: l) ->
  WF_cgen l.
Proof. intros. 
       destruct l; easy.
Qed.

Lemma WF_cgen_last : forall (l : cgexp_normal) (z : Z),
  z <> Z0 ->
  WF_cgen (l ++ [z]).
Proof. intros. 
       induction l. 
       - destruct z; try easy.
       - rewrite <- app_comm_cons. 
         destruct (l ++ [z]) eqn:E; try easy.
         apply (@f_equal (list Z) nat (@length Z)) in E.
         rewrite app_length in E; simpl in E; lia.
Qed.         

Lemma WF_Vi : forall (i : nat), WF_cgen (Vi i).
Proof. intros. 
       unfold Vi.  
       apply WF_cgen_last.
       lia.
Qed.
*)

Fixpoint cgenOp (gen1 gen2 : cgexp_normal) : cgexp_normal :=
  match gen1, gen2 with 
  | [], _ => gen2
  | _, [] => gen1
  | z1 :: gen1', z2 :: gen2' => (z1 + z2)%Z :: cgenOp gen1' gen2'
  end.

(* 
Fixpoint cgenOp (gen1 gen2 : cgexp_normal') : cgexp_normal' :=
  match gen1, gen2 with 
  | [], _ => gen2
  | _, [] => gen1
  |[z1], [z2] => 
     match (z1 + z2)%Z with
     | Z0 => []
     | _ => [(z1 + z2)%Z]
     end
  | z1 :: gen1', z2 :: gen2' => 
      match cgenOp gen1' gen2' with
      | [] => cgenOp [z1] [z2]
      | _ => (z1 + z2)%Z :: cgenOp gen1' gen2'
      end
  end.
*) 


Definition cgenInv (gen : cgexp_normal) : cgexp_normal :=
  map Z.opp gen. 

Fixpoint cgexp_to_normal (ge : cgexp) : cgexp_normal :=
  match ge with 
  | cgIdent => []
  | cgVar i => Vi i
  | cgOp ge1 ge2 => cgenOp (cgexp_to_normal ge1) (cgexp_to_normal ge2)
  | cgInv ge' => cgenInv (cgexp_to_normal ge')
  end.

(* here, nth l i 0 gives the mapping between actual group elems and cgVar i *) 
Fixpoint cgdenote {G} `{Group G} (l : list G) (ge : cgexp) : G :=
  match ge with
  | cgIdent => 0
  | cgVar i => nth i l 0
  | cgOp ge1 ge2 => cgdenote l ge1 + cgdenote l ge2
  | cgInv ge' => - cgdenote l ge'
  end.

(*
Fixpoint jump' {X} (l : list X) (n : nat) : list X :=
  match n with 
  | O => l
  | S n' => jump' (tail l) n'
  end.
*)

Definition cgendenote {G} `{Group G} (l : list G) (gen : cgexp_normal) : G :=
  big_sum (fun i => times_z (nth i l 0) (nth i gen 0%Z)) (length l).

Fixpoint cgendenote' {G} `{Group G} (l : list G) (gen : cgexp_normal) : G :=
  match gen, l with 
  | [], _ => 0
  | _, [] => 0
  | z :: gen', g :: l' => times_z g z + cgendenote' l' gen'
  end.

Lemma cgendenote_same : forall {G} `{Group G} (l : list G) (gen : cgexp_normal),
  cgendenote l gen = cgendenote' l gen.
Proof. induction l.
       - intros. 
         destruct gen; auto.
       - intros. 
         destruct gen; simpl.
         unfold cgendenote.
         rewrite big_sum_0_bounded; auto.
         intros. 
         destruct x; easy. 
         rewrite <- IHl.
         unfold cgendenote.
         simpl length. 
         rewrite <- big_sum_extend_l.
         apply f_equal_gen; try apply f_equal; auto.
Qed.

Lemma test_cgendenote : forall {G} `{Group G} (a b c : G), 
  cgendenote [a; b; c] [1; -1; 2]%Z = a - b + c + c.
Proof. intros. 
       unfold cgendenote; simpl. 
       solve_group. 
Qed.

Lemma cgendenote_Vi : forall {G} `{Group G} (n : nat) (l : list G),
  cgendenote l (Vi n) = nth n l 0.
Proof. intros. 
       unfold cgendenote.
       bdestruct (n <? length l)%nat.
       - rewrite (big_sum_unique (nth n l 0)); auto.
         exists n.
         split; auto.
         split. 
         rewrite nth_Vi; simpl; auto.
         intros.
         rewrite nth_Vi_miss.
         easy.
         auto.
       - rewrite big_sum_0_bounded.
         rewrite nth_overflow; auto.
         intros. 
         rewrite nth_Vi_miss; try lia.
         easy.
Qed.

Lemma cgendenote_grab_scale : forall {G} `{Group G} (i : nat) (l : list G) (gen : cgexp_normal),
  (forall j, j <> i -> nth j gen 0%Z = 0%Z) ->
  cgendenote l gen = times_z (nth i l 0) (nth i gen 0%Z) .
Proof. intros.          
       unfold cgendenote.
       bdestruct (i <? length l)%nat.
       - erewrite big_sum_unique.
         easy.
         exists i. 
         split; auto.
         split. easy.
         intros. 
         rewrite H1; auto.
       - rewrite nth_overflow; try lia.  
         rewrite times_z_0.
         rewrite big_sum_0_bounded; auto.
         intros. 
         rewrite H1; simpl; try lia.
         easy.
Qed.

Lemma cgenOp_nth : forall {G} `{Comm_Group G} (i : nat) (gen1 gen2 : cgexp_normal),
  nth i (cgenOp gen1 gen2) 0%Z = ((nth i gen1 0) + (nth i gen2 0))%Z.
Proof. induction i; intros. 
       - destruct gen1; destruct gen2; auto. 
         simpl; lia.
       - destruct gen1; destruct gen2; auto; simpl.
         lia.
         rewrite IHi; auto.
Qed.




(* we don't even use Comm_Group until here! *)
Lemma cgexp_to_normal_correct' : forall {G} `{Comm_Group G} (l : list G) (ge : cgexp),
  cgdenote l ge = cgendenote l (cgexp_to_normal ge).
Proof. induction ge; simpl.
       - rewrite cgendenote_same. 
         destruct l; try easy.
       - rewrite cgendenote_Vi; auto.
       - rewrite IHge1, IHge2.
         unfold cgendenote.
         rewrite <- big_sum_plus. 
         apply big_sum_eq_bounded; intros.
         rewrite cgenOp_nth.
         rewrite times_z_add_r; auto. 
       - rewrite IHge.
         unfold cgendenote.
         rewrite (big_sum_func_distr _ Gopp).
         apply big_sum_eq_bounded; intros. 
         symmetry.
         apply Gopp_unique_l.
         rewrite <- times_z_add_r.


unfold cgenInv.
         unfold cgendenote.

distr.

       rewrite <- H1.


Lemma cgexp_to_normal_correct : forall {G} `{Group G} (l : list G) 
                                  (ge : cgexp) (gen : cgexp_normal),
  cgexp_to_normal ge = gen ->
  cgdenote l ge = cgendenote l gen.
Proof. intros.  
       rewrite <- H1.


induction ge.
       - intros. 

(*
Lemma cgenOp_cons : forall (gen1 gen2 : cgexp_normal') (z1 z2 : Z),
  (z1 + z2)%Z <> Z0 ->
  cgenOp (z1 :: gen1) (z2 :: gen2) = (z1 + z2)%Z :: (cgenOp gen1 gen2).
Proof. intros.
       destruct gen1; destruct gen2.
       all : simpl; try easy. 
       destruct (z1 + z2)%Z; try easy.
Qed.

Lemma cgenOp_consconsl : forall (gen1 gen2 : cgexp_normal') (z1 z2 z3 : Z),
  cgenOp (z1 :: z2 :: gen1) (z3 :: gen2) = (z1 + z3)%Z :: (cgenOp (z2 :: gen1) gen2).
Proof. intros.
       simpl; easy. 
Qed.

Lemma cgenOp_consconsr : forall (gen1 gen2 : cgexp_normal') (z1 z2 z3 : Z),
  cgenOp (z1 :: gen1) (z2 :: z3 :: gen2) = (z1 + z2)%Z :: (cgenOp gen1 (z3 :: gen2)).
Proof. intros.
       destruct gen1; try easy.
Qed.

Lemma WF_cgenOp : forall (gen1 gen2 : cgexp_normal'),
  WF_cgen gen1 -> WF_cgen gen2 ->
  WF_cgen (cgenOp gen1 gen2).
Proof. induction gen1.
       - easy.
       - intros. 
         destruct gen2; try easy.
         destruct gen1; easy.
         destruct gen1; destruct gen2.
         + simpl.
           destruct (a + z)%Z; try easy.
         + rewrite cgenOp_consconsr. 
           replace (cgenOp [] (z0 :: gen2)) with (z0 :: gen2) by easy.
           apply WF_cons_conv in H0.
           apply WF_cons; try easy.
         + rewrite cgenOp_consconsl. 
           replace (cgenOp (z0 :: gen1) []) with (z0 :: gen1).  
           apply WF_cons_conv in H0.
           apply WF_cons; try easy.
           destruct gen1; try easy.
         + rewrite cgenOp_consconsl. 
           apply WF_cons.

           apply WF_cons.
           *)_

(*
Definition svar i := 
  match i with 
  | xH => cgnX 1 cgnIdent
  | xO j => cgnInj (Pos.to_pos (S n') 
  | xI j => 
  end.
*)

(*
Definition mkcgnInj (n : nat) (gen : cgexp_normal) :=
  match n with
  | O => gen
  | S n' => 
    (match gen with
     | cgnIdent => cgnIdent
     | cgnInj n1 gen1 => cgnInj (n + n1) gen1
     | cgnX _ _ => cgnInj n gen 
    end)
  end.
*)


(*
Definition cgenOp_Inj (gen : cgexp_normal) (n1 : nat) (gen1 : cgexp_normal) 
                    (op : cgexp_normal -> cgexp_normal -> cgexp_normal) : cgexp_normal :=
  match gen with 
  | cgnIdent => cgnInj n1 gen1
  | cgnInj n' gen' => if (n' =? n1)%nat then cgnInj n' (op gen' gen1) 
                     else if (n' <? n1)%nat 
                          then mkcgnInj n' (op gen' (mkcgnInj (n1 - n') gen1))
                          else mkcgnInj n1 (op (mkcgnInj (n' - n1) gen') gen1)
  | cgnX z' gen' => cgnIdent
  end.

Definition cgenOp_X (gen : cgexp_normal) (z1 : Z) (gen1 : cgexp_normal) 
           (op : cgexp_normal -> cgexp_normal -> cgexp_normal) : cgexp_normal :=
  match gen with 
  | cgnIdent => cgnX z1 gen1
  | cgnInj n' gen' => cgnIdent
  | cgnX z' gen' => cgnIdent
  end.
*)

(*
Fixpoint testnat (n1 n2 : nat) : nat :=
  match n1, n2 with 
  | O, O => O
  | O, S n2' => S O
  | S n1', O => S (S O)
  | S n1', S n2' => testnat n1' n2'
  end.


Fixpoint cgenOp (gen1 gen2 : cgexp_normal) : cgexp_normal :=
  match gen1, gen2 with 
  | cgnIdent, _ => gen2
  | _, cgnIdent => gen1
  | cgnInj n1 gen1', cgnInj n2 gen2' => 
      if (n1 =? n2)%nat then mkcgnInj n1 (cgenOp gen1' gen2') 
                     else if (n1 <? n2)%nat 
                          then mkcgnInj n1 (cgenOp gen1' (mkcgnInj (n2 - n1) gen2'))
                          else mkcgnInj n2 (cgenOp (mkcgnInj (n1 - n2) gen1') gen2')
  | _, _ => cgnIdent
  end.

  | cgnInj n2 gen2' => 
    match gen



cgenOp_Inj gen1 n2 gen2' cgenOp
  | cgnX z2 gen2' => cgenOp_X gen1 z2 gen2' cgenOp
  end.

Fixpoint cgenInv (gen : cgexp_normal) : cgexp_normal :=
  match gen with
  | cgnIdent => cgnIdent
  | cgnInj n gen' => cgnInj n (cgenInv gen')
  | cgnX z gen' => cgnX (-z) (cgenInv gen')
  end.
*)









   






(** exponentiation by integers *)

(* exponentiation by positives *)
Fixpoint Gpow_pos {R} `{Ring R} (r : R) (p : positive) : R :=
  match p with 
  | xH => r
  | xO p' => (Gpow_pos r p') * (Gpow_pos r p')
  | xI p' => r * (Gpow_pos r p') * (Gpow_pos r p')
  end.             


Lemma Gpow_pos_to_nat : forall {R} `{Ring R} (r : R) (p : positive),
  Gpow_pos r p = r ^ (Pos.to_nat p).
Proof. intros. 
       induction p.
       - rewrite Pos2Nat.inj_xI, Nat.mul_comm; simpl. 
         rewrite Gpow_mult_r, IHp; simpl. 
         rewrite Gmult_1_r, Gmult_assoc.
         easy.
       - rewrite Pos2Nat.inj_xO, Nat.mul_comm; simpl. 
         rewrite Gpow_mult_r, IHp; simpl. 
         rewrite Gmult_1_r.
         easy.
       - simpl.
         rewrite Gmult_1_r; easy.
Qed.

Lemma Gpow_pos_nonzero : forall {R} `{Domain R} (r : R) (p : positive),
  r <> 0 -> Gpow_pos r p <> 0. 
Proof. intros.
       rewrite Gpow_pos_to_nat.
       apply Gpow_nonzero.  
       easy.
Qed.

Lemma Gpow_pos_add_r : forall {R} `{Ring R} (r : R) (p1 p2 : positive), 
  Gpow_pos r (p1 + p2) = (Gpow_pos r p1) * (Gpow_pos r p2).
Proof. intros.
       do 3 rewrite Gpow_pos_to_nat.
       rewrite Pos2Nat.inj_add, Gpow_add_r.
       easy.
Qed.

Lemma Gpow_pos_mult_r : forall {R} `{Ring R} (r : R) (p1 p2 : positive), 
  Gpow_pos r (p1 * p2) = Gpow_pos (Gpow_pos r p1) p2.
Proof. intros. 
       do 3 rewrite Gpow_pos_to_nat.
       rewrite Pos2Nat.inj_mul, Gpow_mult_r.
       easy.
Qed.

Lemma Gpow_pos_mult_l : forall {R} `{Ring R} (r1 r2 : R) (p : positive), 
  r1 * r2 = r2 * r1 ->
  Gpow_pos (r1 * r2) p = (Gpow_pos r1 p) * (Gpow_pos r2 p). 
Proof. intros. 
       do 3 rewrite Gpow_pos_to_nat.
       rewrite Gpow_mult_l;
       easy.
Qed.

Lemma Gpow_pos_comm1 : forall {R} `{Ring R} (r : R) (p : positive),
  r * Gpow_pos r p = Gpow_pos r p * r.
Proof. induction p; simpl; auto.
       - rewrite <- 3 Gmult_assoc, <- IHp, (Gmult_assoc r (Gpow_pos r p)), 
           IHp, 2 Gmult_assoc, <- IHp, 2 Gmult_assoc; auto. 
       - rewrite <- Gmult_assoc, <- IHp, 2 Gmult_assoc, IHp; auto.
Qed.   

Lemma Gpow_pos_comm2 : forall {R} `{Field R} (r : R) (p : positive),
  (/ r) * Gpow_pos r p = Gpow_pos r p * (/ r).
Proof. intros. 
       rewrite Gmult_comm; auto.
Qed.

Lemma Gpow_pos_succ: forall {R} `{Field R} (r : R) (p : positive), 
  Gpow_pos r (Pos.succ p) = r * Gpow_pos r p.
Proof. intros.
       induction p; simpl; auto.
       - rewrite IHp, <- 2 Gmult_assoc.
         apply f_equal_gen; auto.
       - lca.
Qed.

Lemma Cpow_pos_pred_double : forall (c : C) (p : positive), 
  c <> 0 -> 
  Cpow_pos c (Pos.pred_double p) = (/ c) * (Cpow_pos c p * Cpow_pos c p).
Proof. intros.
       induction p; simpl; auto.
       - repeat rewrite Cmult_assoc.
         rewrite Cinv_l; try lca; auto.
       - rewrite IHp.
         repeat rewrite Cmult_assoc.
         rewrite Cinv_r; try lca; auto.
       - rewrite Cmult_assoc, Cinv_l; try lca; auto.
Qed.

Lemma Cpow_pos_inv : forall (c : C) (p : positive),
  c <> 0 -> 
  Cpow_pos (/ c) p = / (Cpow_pos c p).
Proof. intros. 
       induction p; simpl.
       - rewrite IHp.
         repeat rewrite Cinv_mult_distr; auto.
         2 : apply Cmult_neq_0.
         all : try apply Cpow_pos_nonzero; auto.
       - rewrite IHp.
         rewrite Cinv_mult_distr; try apply Cpow_pos_nonzero; auto.
       - easy.
Qed.

Lemma Cpow_pos_real : forall (c : C) (p : positive), 
  snd c = 0 -> snd (Cpow_pos c p) = 0.
Proof. intros.
       induction p; simpl.
       - rewrite IHp, H; lra.
       - rewrite IHp; lra.
       - easy.
Qed.


Lemma Cpow_pos_1 : forall (p : positive),
  Cpow_pos C1 p = C1.
Proof. intros.
       induction p; simpl.
       - rewrite IHp; lca.
       - rewrite IHp; lca.
       - lca.
Qed.


(* exponentiation by integers *)
Definition Cpow_int (c : C) (z : Z) : C :=  
  match z with
    | Z0 => C1
    | Zpos p => Cpow_pos c p
    | Zneg p => / Cpow_pos c p
  end.


Infix "^^" := Cpow_int (at level 10) : C_scope.



Lemma Cpow_int_nonzero : forall (c : C) (z : Z), c <> C0 -> c ^^ z <> C0. 
Proof. intros.
       destruct z.
       - apply C1_neq_C0.
       - apply Cpow_pos_nonzero; easy.
       - apply nonzero_div_nonzero.
         apply Cpow_pos_nonzero; easy.
Qed.


Lemma Cpow_int_add_1 : forall (c : C) (z : Z), 
  c <> C0 -> c ^^ (1 + z) = c * c^^z.
Proof. intros.
       destruct z; try lca.
       - destruct p; simpl; try lca. 
         rewrite Cpow_pos_succ; lca.
       - destruct p; simpl.
         + rewrite <- Cmult_assoc, (Cinv_mult_distr c); auto.
           rewrite Cmult_assoc, Cinv_r; try lca; auto.
           apply Cmult_neq_0; apply Cpow_pos_nonzero; easy.
         + rewrite Cpow_pos_pred_double, Cinv_mult_distr, Cinv_inv; auto.
           apply nonzero_div_nonzero; auto. 
           apply Cmult_neq_0; apply Cpow_pos_nonzero; easy.
         + rewrite Cinv_r; easy.
Qed.

Lemma Cpow_int_minus_1 : forall (c : C) (z : Z), 
  c <> C0 -> c ^^ (-1 + z) = / c * c^^z.
Proof. intros.
       destruct z; try lca.
       - destruct p; simpl; try lca. 
         + repeat rewrite Cmult_assoc.
           rewrite Cinv_l; auto; lca.
         + rewrite Cpow_pos_pred_double; auto.
         + rewrite Cinv_l; easy.
       - destruct p; simpl; try lca. 
         + rewrite Cpow_pos_succ, <- Cinv_mult_distr; auto.
           apply f_equal; lca.
           repeat apply Cmult_neq_0; try apply Cpow_pos_nonzero; auto.
         + rewrite <- Cmult_assoc, Cinv_mult_distr; auto.
           apply Cmult_neq_0; apply Cpow_pos_nonzero; auto.
         + rewrite Cinv_mult_distr; easy.
Qed.

Lemma Cpow_int_add_nat : forall (c : C) (n : nat) (z : Z), 
  c <> C0 -> c ^^ (Z.of_nat n + z) = c^^(Z.of_nat n) * c^^z.
Proof. intros.
       induction n; try lca.
       replace (S n + z)%Z with (1 + (n + z))%Z by lia.
       replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.       
       repeat rewrite Cpow_int_add_1; auto.
       rewrite IHn; lca.
Qed.

Lemma Cpow_int_minus_nat : forall (c : C) (n : nat) (z : Z), 
  c <> C0 -> c ^^ (- Z.of_nat n + z) = c^^(- Z.of_nat n) * c^^z.
Proof. intros. 
       induction n; try lca.
       replace (- S n + z)%Z with (- 1 + (- n + z))%Z by lia.
       replace (- (S n))%Z with (- 1 + - n)%Z by lia.       
       repeat rewrite Cpow_int_minus_1; auto.
       rewrite IHn; lca.
Qed.

Theorem Cpow_int_add_r : forall (c : C) (z1 z2 : Z), 
  c <> C0 -> c ^^ (z1 + z2) = c^^z1 * c^^z2.
Proof. intros.
       destruct (Z_plusminus_nat z1) as [n [H0 | H0]].
       - rewrite H0, Cpow_int_add_nat; easy.
       - rewrite H0, Cpow_int_minus_nat; easy.
Qed.

Lemma Cpow_int_mult_r : forall (c : C) (z1 z2 : Z), 
  c <> C0 -> c ^^ (z1 * z2) = (c ^^ z1) ^^ z2.
Proof. intros. 
       destruct z1; destruct z2; try lca; simpl.
       all : try (rewrite Cpow_pos_1; lca).
       all : rewrite Cpow_pos_mult_r; try lca. 
       all : rewrite Cpow_pos_inv; try apply Cpow_pos_nonzero; auto.
       rewrite Cinv_inv; auto.
       do 2 apply Cpow_pos_nonzero; easy.
Qed.

Lemma Cpow_int_mult_l : forall (c1 c2 : C) (z : Z), 
  c1 <> C0 -> c2 <> C0 -> (c1 * c2) ^^ z = (c1 ^^ z) * (c2 ^^ z).
Proof. intros. 
       destruct z; try lca; simpl. 
       rewrite Cpow_pos_mult_l; easy.
       rewrite Cpow_pos_mult_l, Cinv_mult_distr; auto; 
       apply Cpow_pos_nonzero; easy.
Qed.


Lemma Cpow_inv1 : forall (c : C) (z : Z), c <> C0 -> c^^(-z) = / (c^^z).
Proof. intros.
       replace (-z)%Z with (z * -1)%Z by lia.
       rewrite Cpow_int_mult_r; easy.
Qed.

Lemma Cpow_inv2 : forall (c : C) (z : Z), c <> C0 -> (/ c)^^z = / (c^^z).
Proof. intros.
       replace z with (-1 * -z)%Z by lia.
       rewrite Cpow_int_mult_r. 
       replace ((/ c) ^^ (-1)) with (/ / c) by easy.
       replace (-1 * - z)%Z with z by lia.
       rewrite Cinv_inv, Cpow_inv1; auto.
       apply nonzero_div_nonzero; auto.
Qed.


(* checking that Cpow_int is consistent with Cpow on nats *)
Lemma Cpow_int_cons : forall (c : C) (n : nat),
  c^n = c ^^ n.
Proof. intros. 
       destruct n; try lca.
       unfold Cpow_int.
       destruct (Z.of_nat (S n)) eqn:E; try easy.
       rewrite Cpow_pos_to_nat.
       apply f_equal_gen; try apply f_equal; auto.
       apply Pos2Z.inj_pos in E.
       rewrite <- E, SuccNat2Pos.id_succ.
       easy.
Qed.


Lemma Cpow_int_real : forall (c : C) (z : Z), 
  c <> 0 -> snd c = 0 -> snd (c ^^ z) = 0.
Proof. intros.
       destruct z; auto.
       - simpl; apply Cpow_pos_real; auto.
       - replace (Z.neg p) with (- Z.pos p)%Z by lia.
         rewrite Cpow_inv1; auto.
         apply div_real.
         apply Cpow_pos_real; auto.
Qed.



(* foreboding: translating between Cpow_int and Zpow *)
Lemma ZtoC_pow_nat : forall (z : Z) (n : nat), 
  RtoC (IZR (z^n)%Z) = (RtoC (IZR z))^^n.
Proof. intros. 
       induction n; try easy.
       rewrite <- Cpow_int_cons in *.
       replace (S n) with (1 + n)%nat by lia.
       rewrite Nat2Z.inj_add, Z.pow_add_r, Cpow_add_r; try lia.
       rewrite mult_IZR, <- IHn, RtoC_mult, RtoC_pow, pow_IZR.
       apply f_equal_gen; auto.
Qed.



(* foreboding: translating between Cpow_int and Zpow *)
Lemma ZtoC_pow : forall (z n : Z), 
  (n >= 0)%Z ->
  RtoC (IZR (z^n)%Z) = (RtoC (IZR z))^^n.
Proof. intros.
       destruct (Z_plusminus_nat n) as [x [H0 | H0]]; subst.
       - rewrite ZtoC_pow_nat; easy.
       - destruct x; try lia.
         replace (-O)%Z with (Z.of_nat O) by lia.
         rewrite ZtoC_pow_nat; easy.
Qed.




