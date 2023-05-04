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

Lemma nonzero_Gdiv_nonzero : forall {F} `{Field F} (c : F), c <> 0 -> / c <> 0.
Proof. intros. 
       unfold not; intros. 
        assert (H' : c * (/ c) = c * 0). 
        { rewrite H6; easy. } 
        rewrite Ginv_r in H'; try easy.
        rewrite Gmult_0_r in H'.
        apply G1_neq_0; easy.
Qed.

Lemma Ginv_inv : forall {F} `{Field F} (c : F), c <> 0 -> / / c = c.
Proof. intros. 
       apply (Gmult_cancel_r _ _ (/ c)).
       apply nonzero_Gdiv_nonzero; auto.
       rewrite Ginv_l, Ginv_r; auto.
       apply nonzero_Gdiv_nonzero; auto.
Qed.       


Global Program Instance RingMult_is_Monoid : forall (R : Type) `{Ring R}, Monoid R :=
  { Gzero := 1
  ; Gplus := Gmult
  }.                    
Next Obligation. apply Gmult_1_l. Qed.
Next Obligation. apply Gmult_1_r. Qed.
Next Obligation. apply Gmult_assoc. Qed.



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

(* slightly more simplified terms *)
Fixpoint Gpow' {R} `{Ring R} (r : R) (n : nat) : R :=  
  match n with
  | 0%nat => 1
  | 1%nat => r
  | S n' => Gmult r (Gpow' r n')
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

Definition big_prod {G : Type} `{Ring G} (f : nat -> G) (n : nat) : G :=
  @big_sum G (RingMult_is_Monoid G) f n.

(** * Gpow Lemmas *)

Lemma Gpow_same : forall {R} `{Ring R} (r : R), Gpow r = Gpow' r.
Proof. intros.
       apply functional_extensionality; intros. 
       induction x; simpl; auto.
       destruct x. 
       simpl. rewrite Gmult_1_r; auto.
       rewrite IHx; auto.
Qed.

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

Lemma big_prod_mult : forall {G} `{Comm_Ring G} f g n, 
    big_prod (fun x => f x * g x) n = big_prod f n * big_prod g n.
Proof.
  intros.
  induction n; unfold big_prod in *; simpl. 
  + rewrite Gmult_1_l; easy.
  + rewrite IHn.
    repeat rewrite <- Gmult_assoc.
    apply f_equal_gen; try easy. 
    rewrite Gmult_comm.  
    repeat rewrite <- Gmult_assoc.
    apply f_equal_gen; try easy.
    rewrite Gmult_comm; easy.
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
  
Lemma big_plus_0_l : forall {G} `{Group G} l,
  G_big_plus (0 :: l) = G_big_plus l.
Proof. 
  intros; simpl. 
  rewrite Gplus_0_l; easy.
Qed.

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

Lemma big_plus_cancel_l : forall {G} `{Group G} a l1 l2,
  G_big_plus l1 = G_big_plus l2 ->
  G_big_plus (a :: l1) = G_big_plus (a :: l2).
Proof. 
  intros; simpl. 
  rewrite H1; easy.
Qed.


Ltac reify_grp G ge :=
  match ge with
  | 0 => constr:(@gIdent G)
  | ?ge1 + ?ge2 =>
      let r1 := reify_grp G ge1 in
      let r2 := reify_grp G ge2 in
      constr:(gOp r1 r2)
  | ?ge1 - ?ge2 => (* technically not needed because we unfold Gminus *)
      let r1 := reify_grp G ge1 in
      let r2 := reify_grp G ge2 in
      constr:(gOp r1 (gInv r2))             
  | -?ge => 
      let r := reify_grp G ge in
      constr:(gInv r)
  | _ => constr:(gVar ge)
  end.

Ltac solve_group :=
  match goal with
  | [ |- @eq ?G ?me1 ?me2 ] =>
      let r1 := reify_grp G me1 in
      let r2 := reify_grp G me2 in
      (* replace me1 with (gdenote r1) by easy;
         replace me2 with (gdenote r2) by easy; *)      
      replace (eq me1) with (eq (gdenote r1)) by (apply f_equal; easy); symmetry;
      replace (eq me2) with (eq (gdenote r2)) by (apply f_equal; easy); symmetry;
      (* change (@eq ?G ?me1 ?me2) with (gdenote r1 = gdenote r2); *)
      apply group_reflect; simpl gflatten;
      repeat (rewrite Gopp_involutive); 
      repeat (repeat 
                (try rewrite big_plus_inv_r; 
                 try rewrite big_plus_inv_l; 
                 try rewrite big_plus_0_l;
                 try apply big_plus_cancel_l);
              try rewrite big_plus_reduce); simpl; try easy;
      repeat (rewrite Gplus_0_l); 
      repeat (rewrite Gplus_0_r);
      repeat (rewrite Gplus_assoc); 
      repeat (apply f_equal_gen; 
              match goal with
              | [ |- Gplus ?me1 = Gplus ?me2 ] => apply f_equal
              | [ |- ?me1 = ?me2 ] => easy
              end); try easy
  end. 

Lemma test2 : forall {G} `{Group G} a b c d, a + b + c + d + 0 - d = a + (b + c) + d - d.
Proof. intros. solve_group. Qed.
 
Lemma test3 : forall {G} `{Group G} a b c, - (a + b + c) + a  = 0 - c - b.
Proof. intros. solve_group. Qed.

Lemma test4 : forall {G} `{Group G} a, 0 = a + -a.
Proof. intros. solve_group. Qed.

Lemma test5 : forall {G} `{Group G} a, a = -a + a + a.
Proof. intros. solve_group. Qed. 

(* TODO: figure out how to do this in one call of solve_group *)
Lemma test6 : forall {G} `{Group G} a b, 0 = -b -a + a + b.
Proof. intros. solve_group. solve_group. Qed.

Lemma test7 : forall {G} `{Group G}, 0 = -0.
Proof. intros. solve_group. Qed.
               
Lemma test8 : forall {G} `{Comm_Group G} a b c, a + b + (c + b + a) = a + --b + b + c + a - a + a.
Proof. intros. solve_group. 
       apply Gplus_comm.
Qed.       


(** * multiplication by integers: needed for solve_comm_group *)


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
       - rewrite times_pos_comm1, <- Gplus_assoc, times_pos_comm1; solve_group.
       - rewrite IHp; solve_group.
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

Corollary times_z_opp_r : forall {R : Type} `{Group R} (r : R) (z : Z), 
  times_z r (- z) = - times_z r z.
Proof. intros.
       apply Gopp_unique_l.
       rewrite <- times_z_add_r, Z.add_opp_diag_l.
       easy.
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

(* here, nth l i 0 gives the mapping between actual group elems and cgVar i *) 
Fixpoint cgdenote {G} `{Group G} (l : list G) (ge : cgexp) : G :=
  match ge with
  | cgIdent => 0
  | cgVar i => nth i l 0
  | cgOp ge1 ge2 => cgdenote l ge1 + cgdenote l ge2
  | cgInv ge' => - cgdenote l ge'
  end.

Lemma cgdenote_op : forall {G} `{Group G} (l : list G) (ge1 ge2 : cgexp),
  cgdenote l (cgOp ge1 ge2) = cgdenote l ge1 + cgdenote l ge2.
Proof. easy. Qed.


Definition cgexp_normal : Type := list Z.

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

Fixpoint cgenOp (gen1 gen2 : cgexp_normal) : cgexp_normal :=
  match gen1, gen2 with 
  | [], _ => gen2
  | _, [] => gen1
  | z1 :: gen1', z2 :: gen2' => (z1 + z2)%Z :: cgenOp gen1' gen2'
  end.

Definition cgenInv (gen : cgexp_normal) : cgexp_normal :=
  map Z.opp gen. 

Fixpoint cgexp_to_normal (ge : cgexp) : cgexp_normal :=
  match ge with 
  | cgIdent => []
  | cgVar i => Vi i
  | cgOp ge1 ge2 => cgenOp (cgexp_to_normal ge1) (cgexp_to_normal ge2)
  | cgInv ge' => cgenInv (cgexp_to_normal ge')
  end.

Definition cgendenote {G} `{Group G} (l : list G) (gen : cgexp_normal) : G :=
  big_sum (fun i => times_z (nth i l 0) (nth i gen 0%Z)) (length l).

Fixpoint cgendenote' {G} `{Group G} (l : list G) (gen : cgexp_normal) : G :=
  match gen, l with 
  | [], _ => 0
  | _, [] => 0
  | z :: gen', g :: l' => 
      match z with
      | Z0 => cgendenote' l' gen'
      | _ => times_z g z + cgendenote' l' gen'
      end
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
         destruct z; try
         apply f_equal_gen; try apply f_equal; auto.
         solve_group.
Qed.

Lemma test_cgendenote : forall {G} `{Group G} (a b c : G), 
  cgendenote [a; b; c] [1; -1; 2]%Z = a - b + c + c.
Proof. intros. 
       unfold cgendenote; simpl. 
       solve_group. 
Qed.


(* two helpers *)

Lemma cgenOp_nth : forall (i : nat) (gen1 gen2 : cgexp_normal),
  nth i (cgenOp gen1 gen2) 0%Z = ((nth i gen1 0) + (nth i gen2 0))%Z.
Proof. induction i; intros. 
       - destruct gen1; destruct gen2; auto. 
         simpl; lia.
       - destruct gen1; destruct gen2; auto; simpl.
         lia.
         rewrite IHi; auto.
Qed.

Lemma cgenInv_nth : forall (i : nat) (gen : cgexp_normal),
  nth i (cgenInv gen) 0%Z = (- nth i gen 0)%Z.
Proof. induction i; intros. 
       - destruct gen; auto. 
       - destruct gen; auto; simpl.
         rewrite IHi; auto.
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
         rewrite <- times_z_add_r, cgenInv_nth, Z.add_opp_diag_l. 
         easy. 
         intros. 
         rewrite Gopp_plus_distr. 
         apply Gplus_comm.
Qed.

Lemma cgexp_to_normal_correct : forall {G} `{Comm_Group G} (l : list G) (ge1 ge2: cgexp),
  cgendenote' l (cgexp_to_normal ge1) = cgendenote' l (cgexp_to_normal ge2) ->
  cgdenote l ge1 = cgdenote l ge2.
Proof. intros.  
       do 2 rewrite cgexp_to_normal_correct', cgendenote_same.
       easy. 
Qed.

Ltac intern vars e :=
  let rec loop n vars' :=
    match vars' with
    | [] =>
      let vars'' := eval simpl in (vars ++ [e]) in
      constr:((n, vars''))
    | e :: ?vars'' => constr:((n, vars))
    | _ :: ?vars'' => loop (S n) vars''
    end in
  loop O vars.

Ltac reify_cgrp vars ge :=
  match ge with
  | Gzero => constr:((cgIdent, vars))
  | ?ge1 + ?ge2 => 
    let r1 := reify_cgrp vars ge1 in
    match r1 with
    | (?qe1, ?vars') => 
      let r2 := reify_cgrp vars' ge2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((cgOp qe1 qe2, vars''))
      end
    end
  | ?ge1 - ?ge2 => 
    let r1 := reify_cgrp vars ge1 in
    match r1 with
    | (?qe1, ?vars') => 
      let r2 := reify_cgrp vars' ge2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((cgOp qe1 (cgInv qe2), vars''))
      end
    end
  | -?ge => 
      let r := reify_cgrp vars ge in
      match r with
      | (?qe, ?vars') => constr:((cgInv qe, vars'))
      end
  | _ => 
    let r := intern vars ge in
    match r with
    | (?n, ?vars') => constr:((cgVar n, vars'))
    end
  end.

Ltac solve_comm_group :=
  match goal with
  | [ |- @eq ?G ?ge1 ?ge2 ] =>
      let r1 := reify_cgrp (@nil G) ge1 in
      match r1 with 
      | (?qe1, ?vars) =>
          let r2 := reify_cgrp vars ge2 in
          match r2 with
          | (?qe2, ?vars') => 
              replace (eq ge1) with (eq (cgdenote vars' qe1)) by (apply f_equal; easy); 
              symmetry;
              replace (eq ge2) with (eq (cgdenote vars' qe2)) by (apply f_equal; easy); 
              symmetry;
              apply cgexp_to_normal_correct; simpl
          end
       end
  end; solve_group.

Lemma test_scg1 : forall {G} `{Comm_Group G} a b c d, a - b + 0 + c - d + -a + d = c - b. 
Proof. intros. solve_comm_group. Qed.

Lemma test_scg2 : forall {G} `{Comm_Group G} a b, a + a + b + a - a = b + a + a.
Proof. intros. solve_comm_group. Qed.


(** solve_comm_monoid (really just ring mult) tactic *)

(* this time, we use nats to track vars since they are easily ordered *)
Inductive cmexp : Type :=
  | cmIdent : cmexp
  | cmVar : nat -> cmexp 
  | cmOp : cmexp -> cmexp -> cmexp.

(* here, nth l i 0 gives the mapping between actual group elems and cgVar i *) 
Fixpoint cmdenote {G} `{Ring G} (l : list G) (ge : cmexp) : G :=
  match ge with
  | cmIdent => 1
  | cmVar i => nth i l 1
  | cmOp ge1 ge2 => cmdenote l ge1 * cmdenote l ge2
  end.

Lemma cmdenote_op : forall {G} `{Ring G} (l : list G) (me1 me2 : cmexp),
  cmdenote l (cmOp me1 me2) = cmdenote l me1 * cmdenote l me2.
Proof. easy. Qed.


Definition cmexp_normal : Type := list nat.

Definition V0' : cmexp_normal := [1%nat].

Definition Vi' (i : nat) : cmexp_normal := repeat O i ++ [1%nat].

Lemma nth_Vi' : forall (i : nat) (z : nat), nth i (Vi' i) z = 1%nat.
Proof. intros.
       unfold Vi'.
       rewrite app_nth2. 
       all : rewrite repeat_length; try lia.
       replace (i - i)%nat with O by lia; easy.
Qed.

Lemma nth_Vi'_miss : forall (i j : nat), i <> j -> nth i (Vi' j) 0%nat = 0%nat.
Proof. intros.
       unfold Vi'.
       bdestruct (i <? j)%nat; bdestruct (j <? i)%nat; bdestruct (i =? j)%nat; try lia. 
       - rewrite app_nth1. 
         rewrite nth_repeat; auto.
         rewrite repeat_length; auto. 
       - rewrite app_nth2. 
         all : rewrite repeat_length; auto.
         destruct (i - j)%nat as [|n] eqn:E; try lia; simpl.
         destruct n; auto.
Qed.

Lemma succ_Vi' : forall (i : nat),
  Vi' (S i) = O :: Vi' i.
Proof. easy. Qed.

Fixpoint cmenOp (men1 men2 : cmexp_normal) : cmexp_normal :=
  match men1, men2 with 
  | [], _ => men2
  | _, [] => men1
  | n1 :: men1', n2 :: men2' => (n1 + n2)%nat :: cmenOp men1' men2'
  end.

Fixpoint cmexp_to_normal (ge : cmexp) : cmexp_normal :=
  match ge with 
  | cmIdent => []
  | cmVar i => Vi' i
  | cmOp ge1 ge2 => cmenOp (cmexp_to_normal ge1) (cmexp_to_normal ge2)
  end.

Definition cmendenote {G} `{Ring G} (l : list G) (gen : cmexp_normal) : G :=
  big_prod (fun i => Gpow (nth i l 1) (nth i gen 0%nat)) (length l).

(* this is more complex to make the Ltac better *)
Fixpoint cmendenote' {G} `{Ring G} (l : list G) (gen : cmexp_normal) : G :=
  match gen, l with 
  | [], _ => 1
  | _, [] => 1
  | [n], [g] => match n with 
               | O => 1
               | _ => Gpow' g n
               end
  | n :: gen', g :: l' => 
      match n with
      | O => cmendenote' l' gen'
      | _ => Gpow' g n * cmendenote' l' gen'
      end
  end.

Lemma cmendenote_same : forall {G} `{Ring G} l gen,
  cmendenote l gen = cmendenote' l gen.
Proof. induction l; intros. 
       - do 2 (destruct gen; auto). 
       - destruct gen.
         unfold cmendenote, big_prod.
         rewrite big_sum_0_bounded; try easy.
         intros; simpl. 
         destruct x; auto.
         replace (cmendenote' (a :: l) (n :: gen)) with 
           (Gpow' a n * cmendenote' l gen).
         rewrite <- IHl.
         unfold cmendenote, big_prod; simpl length.         
         rewrite <- big_sum_extend_l.
         apply f_equal_gen; try apply f_equal; auto.
         simpl. 
         rewrite Gpow_same; auto.
         destruct gen; destruct l; destruct n; simpl;
           try rewrite Gmult_1_r; auto;
           rewrite Gmult_1_l; auto.
Qed.

Lemma test_cmendenote : forall {G} `{Ring G} (a b c : G), 
  cmendenote [a; b; c] [1; 1; 2]%nat = a * b * c * c.
Proof. intros.  
       rewrite cmendenote_same.
       simpl. 
       repeat rewrite Gmult_assoc.
       easy. 
Qed.


(* one helper *)

(* note how this harder lemma means more efficient Ltac *)
Lemma cmenOp_nth : forall (i : nat) (men1 men2 : cmexp_normal),
  nth i (cmenOp men1 men2) 0%nat = ((nth i men1 0) + (nth i men2 0))%nat.
Proof. induction i; intros. 
       - destruct men1; destruct men2; auto. 
       - destruct men1; destruct men2; auto; simpl.
         rewrite IHi; auto.
Qed.

Lemma cmendenote_Vi' : forall {G} `{Ring G} (n : nat) (l : list G),
  cmendenote l (Vi' n) = nth n l 1.
Proof. intros. 
       unfold cmendenote, big_prod.
       bdestruct (n <? length l)%nat.
       - unfold big_prod.
         rewrite (big_sum_unique (nth n l 1)); auto. 
         exists n.
         split; auto.
         split. 
         rewrite nth_Vi'; simpl; auto.
         rewrite Gmult_1_r; auto.
         intros.
         rewrite nth_Vi'_miss.
         easy.
         auto.
       - rewrite big_sum_0_bounded.
         rewrite nth_overflow; auto.
         intros. 
         rewrite nth_Vi'_miss; try lia.
         easy.
Qed.

(* we don't even use Comm_Group until here! *)
Lemma cmexp_to_normal_correct : forall {G} `{Comm_Ring G} (l : list G) (me : cmexp),
  cmdenote l me = cmendenote l (cmexp_to_normal me).
Proof. induction me; simpl.
       - rewrite cmendenote_same. 
         destruct l; try easy.
       - rewrite cmendenote_Vi'; auto.
       - rewrite IHme1, IHme2.
         unfold cmendenote.
         rewrite <- big_prod_mult. 
         apply big_sum_eq_bounded; intros.
         rewrite cmenOp_nth, Gpow_add_r.
         easy. 
Qed.

Lemma cmexp_to_normal_correct' : forall {G} `{Comm_Ring G} (l : list G) (me1 me2: cmexp),
  cmendenote' l (cmexp_to_normal me1) = cmendenote' l (cmexp_to_normal me2) ->
  cmdenote l me1 = cmdenote l me2.
Proof. intros.  
       do 2 rewrite cmexp_to_normal_correct, cmendenote_same.
       easy. 
Qed.


Ltac reify_cmrp vars me :=
  match me with
  | Gone => constr:((cmIdent, vars))
  | ?me1 * ?me2 => 
    let r1 := reify_cmrp vars me1 in
    match r1 with
    | (?qe1, ?vars') => 
      let r2 := reify_cmrp vars' me2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((cmOp qe1 qe2, vars''))
      end
    end
  | _ => 
    let r := intern vars me in
    match r with
    | (?n, ?vars') => constr:((cmVar n, vars'))
    end
  end.

Ltac solve_comm_monoid :=
  match goal with
  | [ |- @eq ?G ?ge1 ?ge2 ] =>
      let r1 := reify_cmrp (@nil G) ge1 in
      match r1 with 
      | (?qe1, ?vars) =>
          let r2 := reify_cmrp vars ge2 in
          match r2 with
          | (?qe2, ?vars') => 
              replace (eq ge1) with (eq (cmdenote vars' qe1)) by (apply f_equal; easy); 
              symmetry;
              replace (eq ge2) with (eq (cmdenote vars' qe2)) by (apply f_equal; easy); 
              symmetry;
              apply cmexp_to_normal_correct'; simpl; auto
          end
       end 
  end. 



Lemma test_scm1 : forall {G} `{Comm_Ring G} a b, a * b * 1 = b * a. 
Proof. intros. solve_comm_monoid; auto. Qed.

Lemma test_scm2 : forall {G} `{Comm_Ring G} a b c, a * (b * c) = a * b * c.
Proof. intros. solve_comm_monoid; auto. Qed.



(* Might be useful to develop strong induction for positives *)
(* TODO: move somewhere else *)


Local Open Scope nat_scope. 

Definition true_lt_n (P : nat -> Prop) (k : nat) : Prop :=
  forall i, i < k -> P i.

Lemma strong_ind' : forall (P : nat -> Prop) (n : nat),
  (forall m, (forall k : nat, (k < m)%nat -> P k) -> P m) ->
  true_lt_n P n.
Proof. intros. 
       induction n.
       - unfold true_lt_n; intros; lia.
       - unfold true_lt_n in *; intros.
         bdestruct (i <? n).
         apply IHn; auto.
         bdestruct (i =? n); try lia.
         apply H; intros. 
         apply IHn; subst; auto.
Qed.

Lemma strong_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m)%nat -> P k) -> P m) -> forall n, P n.
Proof. intros. 
       assert (H' : true_lt_n P (S n)).
       apply strong_ind'; auto.
       unfold true_lt_n in H'.
       apply H'.
       lia.
Qed.

Lemma strong_ind_pos_nat : forall (P : positive -> Prop) (n : nat), 
  (forall p, (forall p', (p' < p) -> P p')%positive -> P p) -> 
  P (Pos.of_nat (S n)).
Proof. intros. 
       generalize dependent n.
       apply strong_ind; intros. 
       apply H; intros.
       rewrite <- Pos2Nat.id.
       destruct (Pos.to_nat p') as [| n'] eqn:E; try lia.
       apply H0.
       lia. 
Qed.

Lemma strong_ind_pos : forall (P : positive -> Prop), 
  (forall p', (forall k, (k < p') -> P k)%positive -> P p') -> 
  forall p, P p.
Proof. intros.  
       rewrite <- Pos2Nat.id.
       destruct (Pos.to_nat p) as [| n'] eqn:E; try lia.
       apply strong_ind_pos_nat; auto.
Qed.

Lemma strong_ind_pos_in_ctx : forall (P : positive -> Prop) (p : positive), 
  (forall p', (forall k, (k < p') -> P k)%positive -> P p') -> 
  P p.
Proof. intros. 
       generalize dependent p.
       apply strong_ind_pos; auto.
Qed.

Lemma pos_sub_simpl_l : forall i p p0,
  Z.pos_sub (i + p) (i + p0) = Z.pos_sub p p0.
Proof. intros. 
       rewrite <- 2 Pos2Z.add_neg_pos, <- Pos2Z.add_neg_neg, <- Pos2Z.add_pos_pos.
       lia. 
Qed.


(* We need jump for the next section *)
(*TODO: move this elsewhere *)

Fixpoint jump {X} (l : list X) (p : positive) : list X :=
  match p with
  | xH => tail l
  | xO p' => jump (jump l p') p'
  | xI p' => jump (jump (tail l) p') p'
  end.


Lemma jump_nil : forall {X} (p : positive),
  jump (@nil X) p = [].
Proof. induction p; simpl;
       repeat rewrite IHp; easy.
Qed.

Lemma jump_singleton : forall {X} (x : X) (p : positive),
  jump [x] p = [].
Proof. induction p; simpl; auto.
       do 2 rewrite jump_nil; auto.
       rewrite IHp, jump_nil; auto.
Qed.

Lemma jump_tail_comm : forall {X} (p : positive) (l : list X),
  jump (tl l) p = tl (jump l p).
Proof. induction p; simpl; auto; intros. 
       do 2 rewrite IHp; auto.
       do 2 rewrite IHp; auto.
Qed.

Lemma jump_succ : forall {X} (p : positive) (l : list X) (x : X),
  jump (x :: l) (Pos.succ p) = jump l p.
Proof. induction p; intros; simpl; auto.
       rewrite IHp, 2 jump_tail_comm.
       destruct ((jump l p)).
       rewrite 2 jump_nil; easy.
       rewrite IHp, <- jump_tail_comm.
       easy.
Qed.

Lemma jump_add_nat : forall {X} (n : nat) (p : positive) (l : list X),
  jump l (Pos.of_nat (S n) + p) = jump (jump l (Pos.of_nat (S n))) p.
Proof. induction n.  
       - intros; simpl Pos.of_nat.
         rewrite Pos.add_1_l.
         destruct l; simpl. 
         repeat rewrite jump_nil; easy.
         rewrite jump_succ; easy.
       - intros.
         destruct l. 
         repeat rewrite jump_nil; easy.
         replace (Pos.of_nat (S (S n)) + p)%positive with 
           (1 + (Pos.of_nat (S n) + p))%positive by lia.
         rewrite Pos.add_1_l, jump_succ, IHn; auto.
         simpl. 
         rewrite jump_succ; easy.
Qed.     

Lemma jump_add : forall {X} (p1 p2 : positive) (l : list X),
  jump l (p1 + p2) = jump (jump l p1) p2.
Proof. intros. 
       rewrite <- (Pos2Nat.id p1).
       destruct (Pos.to_nat p1) eqn:E; try lia.
       rewrite jump_add_nat.
       easy.
Qed.

Lemma jump_tail : forall {X} (p : positive) (l : list X),
  jump (tl l) p = jump l (1 + p).  
Proof. intros. 
       rewrite jump_add. 
       easy.
Qed.



(** solve_comm_ring tactic *)

Local Open Scope group_scope.

(* this time, we use nats to track vars since they are easily ordered *)
Inductive crexp : Type :=
  | cr0 : crexp
  | cr1 : crexp
  | crVar : nat -> crexp 
  | crAdd : crexp -> crexp -> crexp
  | crOpp : crexp -> crexp
  | crMul : crexp -> crexp -> crexp.


Fixpoint crdenote {R} `{Ring R} (l : list R) (re : crexp) : R :=
  match re with
  | cr0 => 0
  | cr1 => 1
  | crVar i => nth i l 0
  | crAdd re1 re2 => crdenote l re1 + crdenote l re2
  | crOpp re => - crdenote l re 
  | crMul re1 re2 => crdenote l re1 * crdenote l re2
  end.

Lemma crdenote_add : forall {R} `{Ring R} (l : list R) (re1 re2 : crexp),
  crdenote l (crAdd re1 re2) = crdenote l re1 + crdenote l re2.
Proof. easy. Qed.

Lemma crdenote_mul : forall {R} `{Ring R} (l : list R) (re1 re2 : crexp),
  crdenote l (crMul re1 re2) = crdenote l re1 * crdenote l re2.
Proof. easy. Qed.





(* this is the normal form of crexp *)
Inductive Pol : Type :=
  | Pz : Z -> Pol
  | Pinj : positive -> Pol -> Pol
  | PX : Pol -> positive -> Pol -> Pol.

Fixpoint Pol_denote {R} `{Ring R} (l : list R) (P : Pol) : R :=
  match P with
  | Pz z => times_z 1 z
  | Pinj j Q => Pol_denote (jump l j) Q
  | PX P i Q => (Gpow' (nth 1 l 0) (Pos.to_nat i)) * (Pol_denote l P) + Pol_denote (tail l) Q
  end.


Definition P0 := Pz 0.
Definition P1 := Pz 1.

(* these help force when p : Pol must be a certain form *)
Definition Pz_pol (P : Pol) : Prop := 
  match P with
  | Pz _ => True
  | _ => False
  end. 





Fixpoint Peq (P P' : Pol) : bool :=
  match P, P' with
  | Pz z, Pz z' => (z =? z')%Z
  | Pinj j Q, Pinj j' Q' =>
      match (j ?= j')%positive with
      | Eq => Peq Q Q'
      | _ => false
      end
  | PX P i Q, PX P' i' Q' =>
      match (i ?= i')%positive with
      | Eq => if Peq P P' then Peq Q Q' else false
      | _ => false
      end
  | _, _ => false
  end.


Definition mkPinj j P :=
  match P with
  | Pz _ => P
  | Pinj j' Q => Pinj ((j + j'):positive) Q
  | _ => Pinj j P
  end.

Definition mkPinj_pred j P:=
  match j with
  | xH => P
  | xO j => Pinj (Pdouble_minus_one j) P
  | xI j => Pinj (xO j) P
  end.

Definition mkPX P i Q :=
  match P with
  | Pz z => if (z =? 0)%Z then mkPinj xH Q else PX P i Q
  | Pinj _ _ => PX P i Q
  | PX P' i' Q' => if (Peq Q' P0) then PX P' (i' + i) Q else PX P i Q
  end.

Definition mkXi i := PX P1 i P0.

(* note that this is just V1 *)
Definition mkX := mkXi 1.

(* note that 0 -> Vi 1, 1 -> Vi 2, etc... *)
Definition mkVi i := 
  match i with
  | O => mkX
  | _ => Pinj (Pos.of_nat i) mkX
  end.


Lemma Pol_mkPinj_add : forall {R} `{Ring R} (p : Pol) (i j : positive),
  mkPinj i (mkPinj j p) = mkPinj (i + j) p.
Proof. intros. 
       destruct p; try easy.
       simpl. 
       rewrite Pos.add_assoc.
       easy.
Qed.

Lemma Pol_denote_mkPinj : forall {R} `{Ring R} (l : list R) (j : positive) (p : Pol),
  Pol_denote (jump l j) p = Pol_denote l (mkPinj j p).
Proof. intros.
       destruct p; simpl; auto.
       unfold mkPinj.
       rewrite jump_add.
       easy.
Qed.

Lemma Pol_denote_mkPinj_to_Pinj : forall {R} `{Ring R} (l : list R) (j : positive) (p : Pol),
  Pol_denote l (mkPinj j p) = Pol_denote l (Pinj j p).
Proof. intros.
       destruct p; simpl; auto.
       rewrite jump_add.
       easy.
Qed.

Lemma Pol_denote_mkPX_to_PX : forall {R} `{Comm_Ring R} (l : list R) (j : positive) (p1 p2 : Pol),
  Pol_denote l (mkPX p1 j p2) = Pol_denote l (PX p1 j p2).
Proof. intros.
       destruct p1; simpl; auto.
       destruct z; simpl; auto.
       rewrite <- Pol_denote_mkPinj; simpl.
       rewrite Gmult_0_r, Gplus_0_l; auto.
       destruct p1_2; simpl; auto.
       destruct z; simpl; auto.
       rewrite Pos2Nat.inj_add, <- Gpow_same, Gpow_add_r.
       apply f_equal_gen; auto; apply f_equal.
       rewrite Gplus_0_r.
       solve_comm_monoid.
Qed.

Lemma Pol_denote_mkVi : forall {R} `{Ring R} (n : nat) (l : list R) (r : R),
  Pol_denote (r :: l) (mkVi n) = nth n l 0.
Proof. induction n. 
       - intros; simpl.
         rewrite Gmult_1_r; solve_group.
       - intros. 
         destruct l; unfold mkVi. 
         simpl. 
         rewrite jump_singleton; simpl.
         rewrite Gmult_1_r; solve_group.
         simpl nth. 
         rewrite <- (IHn l r0).
         unfold mkVi. destruct n; simpl; auto.
         destruct n. simpl.
         rewrite Gmult_1_r; solve_group.
         rewrite jump_succ; auto.
Qed.


(** Additive inverses *)

Fixpoint Popp (P:Pol) : Pol :=
  match P with
  | Pz z => Pz (- z)
  | Pinj j Q => Pinj j (Popp Q)
  | PX P i Q => PX (Popp P) i (Popp Q)
  end.


(* opp lemmas *)

Lemma Pol_denote_Popp_correct : forall {R} `{Comm_Ring R} (l : list R) (p : Pol),
  - Pol_denote l p = Pol_denote l (Popp p).
Proof. intros.
       generalize dependent l.
       induction p; intros; simpl.
       - rewrite times_z_opp_r; easy.
       - rewrite IHp.
         easy. 
       - rewrite <- IHp1, <- IHp2, Gopp_plus_distr, Gplus_comm.
         apply f_equal_gen; auto; apply f_equal.
         rewrite Gopp_mult_distr_r; easy.
Qed.

(** Addition *)

Fixpoint PaddZ (P:Pol) (z:Z) : Pol :=
  match P with
  | Pz z1 => Pz (z1 + z)
  | Pinj j Q => Pinj j (PaddZ Q z)
  | PX P i Q => PX P i (PaddZ Q z)
  end.

Section PopI.

  Variable Pop : Pol -> Pol -> Pol.
  Variable Q : Pol.

  Fixpoint PaddI (j:positive) (P:Pol){struct P} : Pol :=
   match P with
   | Pz z => mkPinj j (PaddZ Q z)
   | Pinj j' Q' =>
     match ZPminus j' j with
     | Zpos k =>  mkPinj j (Pop (Pinj k Q') Q)
     | Z0 => mkPinj j (Pop Q' Q)
     | Zneg k => mkPinj j' (PaddI k Q')
     end
   | PX P i Q' =>
     match j with
     | xH => PX P i (Pop Q' Q)
     | xO j => PX P i (PaddI (Pdouble_minus_one j) Q')
     | xI j => PX P i (PaddI (xO j) Q')
     end
   end.

  Variable P' : Pol.

  Fixpoint PaddX (i':positive) (P:Pol) {struct P} : Pol :=
   match P with
   | Pz z => PX P' i' P
   | Pinj j Q' =>
     match j with
     | xH =>  PX P' i' Q'
     | xO j => PX P' i' (Pinj (Pdouble_minus_one j) Q')
     | xI j => PX P' i' (Pinj (xO j) Q')
     end
   | PX P i Q' =>
     match ZPminus i i' with
     | Zpos k => mkPX (Pop (PX P k P0) P') i' Q'
     | Z0 => mkPX (Pop P P') i Q'
     | Zneg k => mkPX (PaddX k P) i Q'
     end
   end.

End PopI.

 Fixpoint Padd (P P': Pol) {struct P'} : Pol :=
  match P' with
  | Pz z' => PaddZ P z'
  | Pinj j' Q' => PaddI Padd Q' j' P
  | PX P' i' Q' =>
    match P with
    | Pz z => PX P' i' (PaddZ Q' z)
    | Pinj j Q =>
      match j with
      | xH => PX P' i' (Padd Q Q')
      | xO j => PX P' i' (Padd (Pinj (Pdouble_minus_one j) Q) Q')
      | xI j => PX P' i' (Padd (Pinj (xO j) Q) Q')
      end
    | PX P i Q =>
      match ZPminus i i' with
      | Zpos k => mkPX (Padd (PX P k P0) P') i' (Padd Q Q')
      | Z0 => mkPX (Padd P P') i (Padd Q Q')
      | Zneg k => mkPX (PaddX Padd P' k P) i (Padd Q Q')
      end
    end
  end.

Notation "P ++ P'" := (Padd P P').


(* Add lemmas *)
 

Lemma Pol_mkPinj_opp : forall {R} `{Ring R} (p1 p2 : Pol) (i : positive),
  mkPinj i (p1 ++ p2) = mkPinj i p1 ++ mkPinj i p2. 
Proof. intros. 
       destruct p1; destruct p2; simpl; try easy.
       - rewrite Pol_mkPinj_add; auto.
       - rewrite pos_sub_simpl_l.
         destruct (Z.pos_sub p p0);
           rewrite Pol_mkPinj_add; auto. 
       - rewrite <- Pos2Z.add_neg_pos, <- Pos2Z.add_pos_pos. 
         replace (Z.neg i + (Z.pos i + Z.pos p))%Z with (Z.pos p) by lia; auto.
       - rewrite <- Pos2Z.add_neg_pos, <- Pos2Z.add_neg_neg. 
         replace (Z.neg i + Z.neg p0 + Z.pos i)%Z with (Z.neg p0) by lia; auto.
       - rewrite Z.pos_sub_diag; auto. 
Qed.

Lemma Pol_denote_PaddZ_correct : forall {R} `{Comm_Ring R} (l : list R) (p1 : Pol) (z : Z),
  Pol_denote l p1 + Pol_denote l (Pz z) = Pol_denote l (PaddZ p1 z).
Proof. intros. 
       generalize dependent l.
       generalize dependent z.
       induction p1; intros; simpl. 
       - rewrite times_z_add_r; auto.
       - rewrite <- IHp1; auto.
       - rewrite <- IHp1_2; 
         solve_group.
Qed.

Lemma Pol_denote_PaddI_correct : forall {R} `{Comm_Ring R} (l : list R) (Pop : Pol -> Pol -> Pol)
                                        (p1 p2 : Pol) (j : positive),
  (forall i p1 p2, mkPinj i (Pop p1 p2) = Pop (mkPinj i p1) (mkPinj i p2)) -> 
  (forall p1 l, Pol_denote l p1 + Pol_denote l p2 = Pol_denote l (Pop p1 p2)) ->
  Pol_denote l p1 + Pol_denote l (Pinj j p2) = Pol_denote l (PaddI Pop p2 j p1).
Proof. intros.
       generalize dependent l.
       generalize dependent p2.
       generalize dependent j.
       induction p1.
       - intros.  
         rewrite Gplus_comm, Pol_denote_PaddZ_correct.
         simpl. 
         rewrite Pol_denote_mkPinj.
         easy.
       - intros; simpl.   
         destruct (Z.pos_sub p j) eqn:E.             
         + rewrite H4.  
           rewrite <- Pos2Z.add_neg_pos in E. 
           replace p with j by lia.
           rewrite H5, <- H4, Pol_denote_mkPinj; auto.
         + rewrite H4; simpl. (* critical step *)
           rewrite <- Pos2Z.add_neg_pos in E.           
           replace p with (j + p0)%positive by lia.   
           replace (Pinj (j + p0) p1) with (mkPinj j (Pinj p0 p1)) by easy.
           rewrite <- H4, <- Pol_denote_mkPinj, <- H5, <- Pol_denote_mkPinj_to_Pinj,
             <- Pol_denote_mkPinj, jump_add; auto. 
         + rewrite <- Pol_denote_mkPinj, <- IHp1; auto. (* critical step *)
           apply f_equal. 
           rewrite <- Pos2Z.add_neg_pos in E.           
           replace j with (p + p0)%positive by lia. 
           rewrite <- Pol_denote_mkPinj_to_Pinj, <- Pol_denote_mkPinj, jump_add; auto.
       - intros.
         destruct j; simpl; rewrite <- Gplus_assoc; apply f_equal.
         + rewrite <- IHp1_2; auto.
         + rewrite <- IHp1_2; auto.
           rewrite <- Pol_denote_mkPinj_to_Pinj, <- Pol_denote_mkPinj.
           rewrite <- jump_add, jump_tail.
           replace (1 + Pos.pred_double j)%positive with (j + j)%positive by lia. 
           easy.  
         + rewrite H5; auto.
Qed.

Lemma Pol_denote_PaddX_correct : forall {R} `{Comm_Ring R} (l : list R) (Pop : Pol -> Pol -> Pol)
                                        (p1 p2 : Pol) (j : positive),
  (* (forall i p1 p2, mkPinj i (Pop p1 p2) = Pop (mkPinj i p1) (mkPinj i p2)) -> *)
  (forall p1 l, Pol_denote l p1 + Pol_denote l p2 = Pol_denote l (Pop p1 p2)) ->
  Pol_denote l p1 + nth 1 l 0 ^ Pos.to_nat j * Pol_denote l p2 = 
    Pol_denote l (PaddX Pop p2 j p1).
Proof. intros. 
       generalize dependent l.
       generalize dependent p2.
       generalize dependent j.
       induction p1.
       - intros; simpl. 
         rewrite Gpow_same.
         rewrite Gplus_comm; easy.
       - intros.
         destruct p; simpl.
         + rewrite Gpow_same, Gplus_comm; easy.
         + rewrite Gpow_same, Gplus_comm. 
           rewrite jump_tail, <- jump_add.
           replace (1 + Pos.pred_double p)%positive with (p + p)%positive by lia.
           easy.
         + rewrite Gpow_same, Gplus_comm; easy.
       - intros; simpl.
         destruct (Z.pos_sub p j) eqn:E.
         + rewrite <- Pos2Z.add_neg_pos in E. 
           replace p with j by lia.
           rewrite Gpow_same, Pol_denote_mkPX_to_PX; simpl.
           rewrite <- H4, Gmult_plus_distr_l.
           solve_comm_group.
         + rewrite <- Pos2Z.add_neg_pos in E. 
           replace p with (j + p0)%positive by lia.   
           rewrite <- Gpow_same, Pos2Nat.inj_add, Pol_denote_mkPX_to_PX, Gpow_add_r; simpl.
           rewrite <- H4; simpl. 
           rewrite <- Gpow_same, Gmult_plus_distr_l, <- Gmult_assoc.
           do 2 solve_comm_group. 
         + rewrite <- Pos2Z.add_neg_pos in E. 
           replace j with (p + p0)%positive by lia.   
           rewrite Pos2Nat.inj_add, Pol_denote_mkPX_to_PX; simpl.
           rewrite <- IHp1_1, Gpow_add_r, <- Gpow_same, Gmult_plus_distr_l, Gmult_assoc; auto.
           solve_comm_group.
Qed.

Lemma Pol_denote_Padd_correct : forall {R} `{Comm_Ring R} (l : list R) (p1 p2 : Pol),
  Pol_denote l p1 + Pol_denote l p2 = Pol_denote l (p1 ++ p2).
Proof. intros. 
       generalize dependent l.
       generalize dependent p1.
       induction p2.
       - intros. 
         rewrite Pol_denote_PaddZ_correct; auto.
       - intros. 
         rewrite (Pol_denote_PaddI_correct l Padd); auto.
         intros. 
         rewrite Pol_mkPinj_opp; auto.
       - intros. 
         destruct p1; simpl. 
         + rewrite <- Pol_denote_PaddZ_correct; simpl. 
           solve_comm_group.
         + destruct p0; simpl. 
           * rewrite <- IHp2_2, <- Pol_denote_mkPinj_to_Pinj, <- Pol_denote_mkPinj.
             simpl; solve_comm_group.
           * rewrite <- IHp2_2, <- Pol_denote_mkPinj_to_Pinj, <- Pol_denote_mkPinj.
             replace (tl l) with (jump l 1) by easy.
             rewrite <- 2 jump_add.
             replace (1 + Pos.pred_double p0)%positive with (p0 + p0)%positive by lia.
             solve_comm_group.
           * rewrite <- IHp2_2.
             solve_comm_group.
         + destruct (Z.pos_sub p0 p) eqn:E. 
           all : rewrite Pol_denote_mkPX_to_PX; simpl.
           * rewrite <- Pos2Z.add_neg_pos in E. 
             replace p0 with p by lia.
             rewrite <- IHp2_2, <- IHp2_1.
             rewrite Gmult_plus_distr_l.
             solve_comm_group. 
           * rewrite <- Pos2Z.add_neg_pos in E. 
             replace p0 with (p1 + p)%positive by lia.
             rewrite <- IHp2_2, <- IHp2_1.
             rewrite Gmult_plus_distr_l; simpl. 
             rewrite Pos2Nat.inj_add, <- Gpow_same, Gpow_add_r.
             rewrite <- 2 Gplus_assoc.
             apply f_equal_gen; try apply f_equal.
             rewrite Gplus_0_r.
             solve_comm_monoid.
             solve_comm_group. 
           * rewrite <- Pos2Z.add_neg_pos in E. 
             replace p with (p0 + p1)%positive by lia.
             rewrite <- IHp2_2.
             rewrite Pos2Nat.inj_add, <- Gpow_same, Gpow_add_r.
             rewrite 2 Gplus_assoc.
             apply f_equal_gen; try apply f_equal; auto.
             rewrite <- Gplus_assoc, (Gplus_comm (Pol_denote (tl l) p1_2)), Gplus_assoc.
             apply f_equal_gen; try apply f_equal; auto.
             erewrite <- Pol_denote_PaddX_correct.
             rewrite Gmult_plus_distr_l, Gmult_assoc; easy. 
             intros. 
             apply IHp2_1.
Qed.


(** Multiplication *)

 Fixpoint PmulZ_aux (P:Pol) (z:Z) {struct P} : Pol :=
  match P with
  | Pz z' => Pz (z' * z)%Z
  | Pinj j Q => mkPinj j (PmulZ_aux Q z)
  | PX P i Q => mkPX (PmulZ_aux P z) i (PmulZ_aux Q z)
  end.

 Definition PmulZ P z :=
  match z with 
  | Z0 => P0
  | _ => if (z =? 1)%Z then P else PmulZ_aux P z
  end. 

Section PmulI.

  Variable Pmul : Pol -> Pol -> Pol.
  Variable Q : Pol.

  Fixpoint PmulI (j:positive) (P:Pol) {struct P} : Pol :=
   match P with
   | Pz z => mkPinj j (PmulZ Q z)
   | Pinj j' Q' =>
     match ZPminus j' j with
     | Zpos k => mkPinj j (Pmul (Pinj k Q') Q)
     | Z0 => mkPinj j (Pmul Q' Q)
     | Zneg k => mkPinj j' (PmulI k Q')
     end
   | PX P' i' Q' =>
     match j with
     | xH => mkPX (PmulI xH P') i' (Pmul Q' Q)
     | xO j' => mkPX (PmulI j P') i' (PmulI (Pdouble_minus_one j') Q')
     | xI j' => mkPX (PmulI j P') i' (PmulI (xO j') Q')
     end
   end.

 End PmulI.
(* A symmetric version of the multiplication *)

 Fixpoint Pmul (P P'' : Pol) {struct P''} : Pol :=
   match P'' with
   | Pz z => PmulZ P z
   | Pinj j' Q' => PmulI Pmul Q' j' P
   | PX P' i' Q' =>
     match P with
     | Pz z => PmulZ P'' z
     | Pinj j Q =>
       let QQ' :=
         match j with
         | xH => Pmul Q Q'
         | xO j => Pmul (Pinj (Pdouble_minus_one j) Q) Q'
         | xI j => Pmul (Pinj (xO j) Q) Q'
         end in
       mkPX (Pmul P P') i' QQ'
     | PX P i Q=>
       let QQ' := Pmul Q Q' in
       let PQ' := PmulI Pmul Q' xH P in
       let QP' := Pmul (mkPinj xH Q) P' in
       let PP' := Pmul P P' in
       (mkPX (mkPX PP' i P0 ++ QP') i' P0) ++ mkPX PQ' i QQ'
     end
  end.

(* Non symmetric *)
(*
 Fixpoint Pmul_aux (P P' : Pol) {struct P'} : Pol :=
  match P' with
  | Pc c' => PmulC P c'
  | Pinj j' Q' => PmulI Pmul_aux Q' j' P
  | PX P' i' Q' =>
     (mkPX (Pmul_aux P P') i' P0) ++ (PmulI Pmul_aux Q' xH P)
  end.
 Definition Pmul P P' :=
  match P with
  | Pc c => PmulC P' c
  | Pinj j Q => PmulI Pmul_aux Q j P'
  | PX P i Q =>
    (mkPX (Pmul_aux P P') i P0) ++ (PmulI Pmul_aux Q xH P')
  end.
*)
Notation "P ** P'" := (Pmul P P') (at level 50).


(* Mul lemmas *)
 

Lemma Pol_denote_PmulZ_aux_correct : forall {R} `{Comm_Ring R} (l : list R) (p1 : Pol) (z : Z),
  Pol_denote l p1 * times_z 1 z = Pol_denote l (PmulZ_aux p1 z).
Proof. intros. 
       generalize dependent l.
       generalize dependent z.
       induction p1; intros; simpl. 
       - replace 1 with (1 * 1) by solve_comm_monoid.
         rewrite times_z_mult, Gmult_1_r; easy.
       - rewrite Pol_denote_mkPinj_to_Pinj, IHp1; easy.
       - rewrite Pol_denote_mkPX_to_PX; simpl. 
         rewrite <- IHp1_1, <- IHp1_2, Gmult_plus_distr_r, Gmult_assoc; easy.
Qed.

Lemma Pol_denote_PmulZ_correct : forall {R} `{Comm_Ring R} (l : list R) (p1 : Pol) (z : Z),
  Pol_denote l p1 * Pol_denote l (Pz z) = Pol_denote l (PmulZ p1 z).
Proof. intros. 
       destruct z; simpl. 
       rewrite Gmult_0_r; easy.
       destruct p; 
       try rewrite <- Pol_denote_PmulZ_aux_correct; try easy.
       simpl. rewrite Gmult_1_r; easy.
       rewrite <- Pol_denote_PmulZ_aux_correct.
       easy. 
Qed.

Lemma Pol_denote_PmulI_correct : forall {R} `{Comm_Ring R} (l : list R) (Pmul : Pol -> Pol -> Pol)
                                        (p1 p2 : Pol) (j : positive),
  (forall p1 l, Pol_denote l p1 * Pol_denote l p2 = Pol_denote l (Pmul p1 p2)) ->
  Pol_denote l p1 * Pol_denote l (Pinj j p2) = Pol_denote l (PmulI Pmul p2 j p1).
Proof. intros.
       generalize dependent l.
       generalize dependent p2.
       generalize dependent j.
       induction p1.
       - intros; simpl. 
         rewrite Pol_denote_mkPinj_to_Pinj; simpl. 
         rewrite <- Pol_denote_PmulZ_correct; simpl.
         rewrite Gmult_comm; easy.
       - intros; simpl.
         destruct (Z.pos_sub p j) eqn:E; 
           rewrite <- Pos2Z.add_neg_pos in E; 
           rewrite Pol_denote_mkPinj_to_Pinj; simpl.
         + replace p with j by lia.
           rewrite H4; easy.
         + replace p with (j + p0)%positive by lia.   
           rewrite <- H4; simpl.
           rewrite jump_add; easy.
         + replace j with (p + p0)%positive by lia.   
           rewrite <- IHp1; auto.
           rewrite jump_add; easy.
       - intros; simpl. 
         destruct j; simpl; rewrite Pol_denote_mkPX_to_PX; simpl.
         + rewrite <- IHp1_1, <- IHp1_2; auto.
           rewrite Gmult_plus_distr_r; simpl.
           rewrite Gmult_assoc; easy.
         + rewrite <- IHp1_1, <- IHp1_2; auto.
           rewrite Gmult_plus_distr_r; simpl.
           rewrite Gmult_assoc. 
           rewrite jump_tail, <- jump_add.
           replace (1 + Pos.pred_double j)%positive with (j + j)%positive by lia.
           easy.
         + rewrite <- IHp1_1; auto.
           rewrite Gmult_plus_distr_r, <- H4; simpl.
           rewrite Gmult_assoc. 
           easy.
Qed.

Lemma Pol_denote_Pmul_correct : forall {R} `{Comm_Ring R} (l : list R) (p1 p2 : Pol),
  Pol_denote l p1 * Pol_denote l p2 = Pol_denote l (p1 ** p2). 
Proof. intros. 
       generalize dependent l.
       generalize dependent p1.
       induction p2.
       - intros. 
         simpl. 
         rewrite <- Pol_denote_PmulZ_correct; easy.
       - intros.
         erewrite Pol_denote_PmulI_correct; easy.
       - intros. 
         simpl. 
         destruct p1; simpl.
         + rewrite <- Pol_denote_PmulZ_correct; simpl.
           rewrite Gmult_plus_distr_l, Gmult_plus_distr_r.
           apply f_equal_gen; try apply f_equal;
             solve_comm_monoid.
         + destruct p0; rewrite Pol_denote_mkPX_to_PX; simpl;
             rewrite <- IHp2_1, <- IHp2_2, Gmult_plus_distr_l; simpl; 
             apply f_equal_gen; try apply f_equal;
             solve_comm_monoid.
             rewrite jump_tail, <- jump_add.
             replace (1 + Pos.pred_double p0)%positive with (p0 + p0)%positive by lia.
             solve_comm_monoid.
         + rewrite Gmult_plus_distr_l, 2 Gmult_plus_distr_r, 
             <- Pol_denote_Padd_correct, Pol_denote_mkPX_to_PX; simpl.
           rewrite <- Pol_denote_Padd_correct, 2 Pol_denote_mkPX_to_PX; simpl.
           rewrite <- 2 IHp2_1, <- IHp2_2, <- Pol_denote_PmulI_correct; auto.
           repeat (rewrite Gplus_assoc).
           rewrite 2 Gplus_0_r, Gmult_plus_distr_l.
           apply f_equal_gen; try apply f_equal; auto; simpl. 
           apply f_equal_gen; try apply f_equal; auto; simpl.
           apply f_equal_gen; try apply f_equal; auto; simpl.
           solve_comm_monoid.
           rewrite Pol_denote_mkPinj_to_Pinj; simpl.
           solve_comm_monoid.
           solve_comm_monoid.
Qed.


Fixpoint crexp_to_Pol (re : crexp) : Pol :=
  match re with
  | cr0 => P0
  | cr1 => P1
  | crVar i => mkVi i
  | crAdd re1 re2 => crexp_to_Pol re1 ++ crexp_to_Pol re2
  | crOpp re => Popp (crexp_to_Pol re) 
  | crMul re1 re2 => crexp_to_Pol re1 ** crexp_to_Pol re2
  end.


(* we don't even use Comm_Group until here! *)
Lemma crexp_to_Pol_correct : forall {R} `{Comm_Ring R} (l : list R) (re : crexp),
  crdenote l re = Pol_denote (0 :: l) (crexp_to_Pol re).
Proof. induction re; simpl; try easy.
       - rewrite Pol_denote_mkVi.
         easy.
       - rewrite IHre1, IHre2. 
         rewrite Pol_denote_Padd_correct; easy.
       - rewrite IHre.
         rewrite Pol_denote_Popp_correct; easy.
       - rewrite IHre1, IHre2. 
         rewrite Pol_denote_Pmul_correct; easy.
Qed.

Lemma crexp_to_Pol_correct' : forall {R} `{Comm_Ring R} (l : list R) (re1 re2: crexp),
  Pol_denote (0 :: l) (crexp_to_Pol re1) = Pol_denote (0 :: l) (crexp_to_Pol re2) ->
  crdenote l re1 = crdenote l re2.
Proof. intros.  
       do 2 rewrite crexp_to_Pol_correct. 
       easy. 
Qed.



Ltac reify_crexp vars ge :=
  match ge with
  | Gzero => constr:((cr0, vars))
  | Gone => constr:((cr1, vars))             
  | ?ge1 + ?ge2 => 
    let r1 := reify_crexp vars ge1 in
    match r1 with
    | (?qe1, ?vars') => 
      let r2 := reify_crexp vars' ge2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((crAdd qe1 qe2, vars''))
      end
    end
  | ?ge1 - ?ge2 => 
    let r1 := reify_crexp vars ge1 in
    match r1 with
    | (?qe1, ?vars') => 
      let r2 := reify_crexp vars' ge2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((crAdd qe1 (crOpp qe2), vars''))
      end
    end
  | -?ge => 
      let r := reify_crexp vars ge in
      match r with
      | (?qe, ?vars') => constr:((crOpp qe, vars'))
      end
  | ?ge1 * ?ge2 => 
    let r1 := reify_crexp vars ge1 in
    match r1 with
    | (?qe1, ?vars') => 
      let r2 := reify_crexp vars' ge2 in
      match r2 with
      | (?qe2, ?vars'') => constr:((crMul qe1 qe2, vars''))
      end
    end
  | _ => 
    let r := intern vars ge in
    match r with
    | (?n, ?vars') => constr:((crVar n, vars'))
    end
  end.



Ltac solve_comm_ring :=
  match goal with
  | [ |- @eq ?G ?re1 ?re2 ] =>
      let r1 := reify_crexp (@nil G) re1 in
      match r1 with 
      | (?qe1, ?vars) =>
          let r2 := reify_crexp vars re2 in
          match r2 with
          | (?qe2, ?vars') => 
              replace (eq re1) with (eq (crdenote vars' qe1)) by (apply f_equal; easy); 
              symmetry;
              replace (eq re2) with (eq (crdenote vars' qe2)) by (apply f_equal; easy); 
              symmetry;
              apply crexp_to_Pol_correct'; simpl
          end
       end
  end.


  

Lemma test_scr1 : forall {R} `{Comm_Ring R} a b c d,
    a * (b * a + c) - d = c * a + (a * b) * a - d.
Proof. intros. solve_comm_ring; auto. Qed.


Lemma test_scr2 : forall {R} `{Comm_Ring R} a b c d,
    a * (1 + 1 + (b - 1) * a + c) - d = 
      -a + c * a + (-a * a) + (a * b) * a - d + (1 + 1 + 1) * a.
Proof.  intros. solve_comm_ring; auto. Qed.

Lemma test_scr3 : forall {R} `{Comm_Ring R} a,
    a * 0 = 0.
Proof. intros. solve_comm_ring; auto. Qed.

Lemma test_scr4 : forall {R} `{Comm_Ring R} a b,
    - (a * b) = a * (-b).
Proof. intros. solve_comm_ring; auto. Qed.


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

Lemma Gpow_pos_succ: forall {R} `{Ring R} (r : R) (p : positive), 
  Gpow_pos r (Pos.succ p) = r * Gpow_pos r p.
Proof. intros.
       induction p; simpl; auto.
       - rewrite IHp, <- 2 Gmult_assoc.
         apply f_equal_gen; auto.
         rewrite Gmult_assoc, <- Gpow_pos_comm1, Gmult_assoc; auto.
       - rewrite Gmult_assoc; auto.
Qed.

Lemma Gpow_pos_pred_double : forall {R} `{Field R} (c : R) (p : positive), 
  c <> 0 -> 
  Gpow_pos c (Pos.pred_double p) = (/ c) * (Gpow_pos c p * Gpow_pos c p).
Proof. intros.
       induction p; simpl; auto.
       - repeat rewrite Gmult_assoc.
         rewrite Ginv_l; auto.
         solve_comm_monoid.
       - rewrite IHp.
         repeat rewrite Gmult_assoc.
         rewrite Ginv_r; auto. 
         solve_comm_monoid.
       - rewrite Gmult_assoc, Ginv_l; auto.
         solve_comm_monoid.
Qed.

Lemma Gpow_pos_inv : forall {R} `{Field R} (c : R) (p : positive),
  c <> 0 -> 
  Gpow_pos (/ c) p = / (Gpow_pos c p).
Proof. intros. 
       induction p; simpl; auto.
       - rewrite IHp.
         repeat rewrite Ginv_mult_distr; auto.
         2 : apply Gmult_neq_0; auto.
         all : try apply Gpow_pos_nonzero; auto.
       - rewrite IHp.
         rewrite Ginv_mult_distr; try apply Gpow_pos_nonzero; auto.
Qed.

Lemma Gpow_pos_1 : forall {R} `{Field R} (p : positive),
  Gpow_pos 1 p = 1.
Proof. intros.
       induction p; simpl.
       - rewrite IHp; solve_comm_monoid.
       - rewrite IHp; solve_comm_monoid.
       - solve_comm_monoid.
Qed.


(* exponentiation by integers *)
Definition Gpow_int {R} `{Field R} (c : R) (z : Z) : R :=  
  match z with
    | Z0 => 1
    | Zpos p => Gpow_pos c p
    | Zneg p => / Gpow_pos c p
  end.


Infix "^^" := Gpow_int (at level 10) : group_scope.


Lemma Gpow_int_nonzero : forall {R} `{Field R} (c : R) (z : Z), c <> 0 -> c ^^ z <> 0. 
Proof. intros.
       destruct z.
       - apply G1_neq_0.
       - apply Gpow_pos_nonzero; easy.
       - apply nonzero_Gdiv_nonzero.
         apply Gpow_pos_nonzero; easy.
Qed.


Lemma Gpow_int_add_1 : forall {R} `{Field R} (c : R) (z : Z), 
  c <> 0 -> c ^^ (1 + z) = c * c^^z.
Proof. intros.
       destruct z; try (solve_comm_monoid; easy).
       - destruct p; simpl; try solve_comm_monoid. 
         rewrite Gpow_pos_succ; solve_comm_monoid. 
       - destruct p; simpl.
         + rewrite <- Gmult_assoc, (Ginv_mult_distr c); auto.
           rewrite Gmult_assoc, Ginv_r; try solve_comm_monoid; auto.
           apply Gmult_neq_0; apply Gpow_pos_nonzero; easy.
         + rewrite Gpow_pos_pred_double, Ginv_mult_distr, Ginv_inv; auto.
           apply nonzero_Gdiv_nonzero; auto. 
           apply Gmult_neq_0; apply Gpow_pos_nonzero; easy.
         + rewrite Ginv_r; easy.
Qed.

Lemma Gpow_int_minus_1 : forall {R} `{Field R} (c : R) (z : Z), 
  c <> 0 -> c ^^ (-1 + z) = / c * c^^z.
Proof. intros.
       destruct z; try (solve_comm_monoid; easy).
       - destruct p; simpl; try (solve_comm_monoid; easy).
         + repeat rewrite Gmult_assoc.
           rewrite Ginv_l; auto; solve_comm_monoid.
         + rewrite Gpow_pos_pred_double; auto.
         + rewrite Ginv_l; easy.
       - destruct p; simpl; try (solve_comm_monoid; easy).
         + rewrite Gpow_pos_succ, <- Ginv_mult_distr; auto.
           apply f_equal; solve_comm_monoid.
           repeat apply Gmult_neq_0; try apply Gpow_pos_nonzero; auto.
         + rewrite <- Gmult_assoc, Ginv_mult_distr; auto.
           apply Gmult_neq_0; apply Gpow_pos_nonzero; auto.
         + rewrite Ginv_mult_distr; easy.
Qed.

Lemma Gpow_int_add_nat : forall {R} `{Field R} (c : R) (n : nat) (z : Z), 
  c <> 0 -> c ^^ (Z.of_nat n + z) = c^^(Z.of_nat n) * c^^z.
Proof. intros.
       induction n; try (solve_comm_monoid; easy).
       replace (S n + z)%Z with (1 + (n + z))%Z by lia.
       replace (Z.of_nat (S n)) with (1 + Z.of_nat n)%Z by lia.       
       repeat rewrite Gpow_int_add_1; auto.
       rewrite IHn; solve_comm_monoid.
Qed.

Lemma Gpow_int_minus_nat : forall {R} `{Field R} (c : R) (n : nat) (z : Z), 
  c <> 0 -> c ^^ (- Z.of_nat n + z) = c^^(- Z.of_nat n) * c^^z.
Proof. intros. 
       induction n; try (solve_comm_monoid; easy).
       replace (- S n + z)%Z with (- 1 + (- n + z))%Z by lia.
       replace (- (S n))%Z with (- 1 + - n)%Z by lia.       
       repeat rewrite Gpow_int_minus_1; auto.
       rewrite IHn; solve_comm_monoid.
Qed.

Theorem Gpow_int_add_r : forall {R} `{Field R} (c : R) (z1 z2 : Z), 
  c <> 0 -> c ^^ (z1 + z2) = c^^z1 * c^^z2.
Proof. intros.
       destruct (Z_plusminus_nat z1) as [n [H6 | H6]].
       - rewrite H6, Gpow_int_add_nat; easy.
       - rewrite H6, Gpow_int_minus_nat; easy.
Qed.

Lemma Gpow_int_mult_r : forall {R} `{Field R} (c : R) (z1 z2 : Z), 
  c <> 0 -> c ^^ (z1 * z2) = (c ^^ z1) ^^ z2.
Proof. intros. 
       destruct z1; destruct z2; simpl; try solve_comm_monoid; simpl.
       all : try (rewrite Gpow_pos_1; solve_comm_monoid).
       apply (Gmult_cancel_l _ _ 1).
       apply G1_neq_0.
       rewrite Ginv_r, Gmult_1_l; auto.
       apply G1_neq_0.
       all : rewrite Gpow_pos_mult_r; try solve_comm_monoid. 
       all : rewrite Gpow_pos_inv; try apply Gpow_pos_nonzero; auto.
       solve_comm_monoid.
       rewrite Ginv_inv; auto.
       solve_comm_monoid.
       do 2 apply Gpow_pos_nonzero; easy.
Qed.

Lemma Gpow_int_mult_l : forall {R} `{Field R} (c1 c2 : R) (z : Z), 
  c1 <> 0 -> c2 <> 0 -> (c1 * c2) ^^ z = (c1 ^^ z) * (c2 ^^ z).
Proof. intros. 
       destruct z; try solve_comm_monoid; simpl. 
       rewrite Gpow_pos_mult_l; solve_comm_monoid.
       rewrite Gpow_pos_mult_l, Ginv_mult_distr; auto;
       try apply Gpow_pos_nonzero; auto; solve_comm_monoid.
Qed.


Lemma Gpow_inv1 : forall {R} `{Field R} (c : R) (z : Z), c <> 0 -> c^^(-z) = / (c^^z).
Proof. intros.
       replace (-z)%Z with (z * -1)%Z by lia.
       rewrite Gpow_int_mult_r; easy.
Qed.

Lemma Gpow_inv2 : forall {R} `{Field R} (c : R) (z : Z), c <> 0 -> (/ c)^^z = / (c^^z).
Proof. intros.
       replace z with (-1 * -z)%Z by lia.
       rewrite Gpow_int_mult_r. 
       replace ((/ c) ^^ (-1)) with (/ / c) by easy.
       replace (-1 * - z)%Z with z by lia.
       rewrite Ginv_inv, Gpow_inv1; auto.
       apply nonzero_Gdiv_nonzero; auto.
Qed.


(* checking that Cpow_int is consistent with Cpow on nats *)
Lemma Gpow_int_cons : forall {R} `{Field R} (c : R) (n : nat),
  c^n = c ^^ n.
Proof. intros. 
       destruct n; try easy. 
       unfold Gpow_int.
       destruct (Z.of_nat (S n)) eqn:E; try easy.
       rewrite Gpow_pos_to_nat.
       apply f_equal_gen; try apply f_equal; auto.
       apply Pos2Z.inj_pos in E.
       rewrite <- E, SuccNat2Pos.id_succ.
       easy.
Qed.




