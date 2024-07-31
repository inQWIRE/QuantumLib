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

Class Vector_Space V F `{Comm_Group V} `{Field F}. 




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

Lemma Gopp_0 : forall {R} `{Group R}, - 0 = 0.
Proof.
  symmetry.
  apply Gopp_unique_r.
  apply Gplus_0_l.
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

Lemma Gmult_if : forall {R} `{Ring R} (b c : bool) (r s : R),
  (if b then r else 0) * (if c then s else 0) =
  if b && c then r * s else 0.
Proof.
  intros.
  destruct b, c; now rewrite ?Gmult_0_l, ?Gmult_0_r.
Qed.

Lemma Gopp_neg_1 : forall {R} `{Ring R} (r : R), -1%G * r = -r.
Proof. intros.
       apply (Gplus_cancel_l _ _ r).
       rewrite Gopp_r.
       replace (Gplus r) with (Gplus (1 * r)) by (rewrite Gmult_1_l; easy).
       rewrite <- Gmult_plus_distr_r, Gopp_r, Gmult_0_l; easy.
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

Global Program Instance nat_is_monoid : Monoid nat := 
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

Lemma big_sum_opp : forall {G} `{Comm_Group G} (f : nat -> G) n,
  - big_sum f n = big_sum (fun k => - f k) n.
Proof.
  induction n; simpl.
  - apply Gopp_0.
  - rewrite Gopp_plus_distr.
    now rewrite Gplus_comm, IHn.
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

Lemma big_sum_if_or : forall {G} `{Comm_Group G}
  (ifl ifr : nat -> bool)
  (f : nat -> G) (n : nat),
  big_sum (fun k => if ifl k || ifr k then f k else 0) n =
  big_sum (fun k => if ifl k then f k else 0) n + 
  big_sum (fun k => if ifr k then f k else 0) n - 
  big_sum (fun k => if ifl k && ifr k then f k else 0) n.
Proof.
  intros.
  unfold Gminus.
  rewrite big_sum_opp.
  rewrite <- 2!big_sum_plus.
  apply big_sum_eq_bounded.
  intros k Hk.
  destruct (ifl k), (ifr k); simpl; 
    rewrite <- Gplus_assoc, ?Gopp_r, 
    ?Gopp_0, ?Gplus_0_r, ?Gplus_0_l; easy.
Qed.

Lemma big_sum_if_eq : forall {G} `{Monoid G} (f : nat -> G) n k,
  big_sum (fun x => if x =? k then f x else 0) n =
  if k <? n then f k else 0.
Proof.
  intros.
  induction n; [easy|]. 
  simpl.
  rewrite IHn.
  bdestruct_all; subst; now rewrite ?Gplus_0_l, ?Gplus_0_r.
Qed.

Lemma big_sum_if_eq' : forall {G} `{Monoid G} (f : nat -> G) n k,
  big_sum (fun x => if k =? x then f x else 0) n =
  if k <? n then f k else 0.
Proof.
  intros.
  rewrite <- big_sum_if_eq.
  apply big_sum_eq_bounded.
  intros.
  now rewrite Nat.eqb_sym.
Qed.

Lemma big_sum_if_or_eq_ne : forall {G} `{Comm_Group G} 
  (f : nat -> G) n k l, k <> l ->
  big_sum (fun x => if (x =? k) || (x =? l) then f x else 0) n =
  (if k <? n then f k else 0) +
  (if l <? n then f l else 0).
Proof.
  intros * ? f n k l Hkl.
  induction n; [symmetry; apply Gplus_0_l|]. 
  simpl.
  rewrite IHn.
  bdestruct_all; subst; simpl;
   rewrite 2?Gplus_0_l, 2?Gplus_0_r; easy + apply Gplus_comm.
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

Lemma big_sum_split : forall {G} `{Monoid G} n i (v : nat -> G) (Hi : (i < n)),
  big_sum v n = (big_sum v i) + v i 
  + (big_sum (fun k => v (k + i + 1)%nat) (n - 1 - i)).
Proof.
  intros.
  induction n; [lia|].
  bdestruct (i =? n).
  - subst.
    replace (S n - 1 - n)%nat with O by lia.
    rewrite <- big_sum_extend_r. 
    simpl. 
    symmetry.
    apply Gplus_0_r.
  - specialize (IHn ltac:(lia)).
    replace (S n - 1 - i)%nat with (S (n - 1 - i))%nat by lia.
    rewrite <- !big_sum_extend_r.
    rewrite IHn.
    replace (n - 1 - i + i + 1)%nat with n by lia.
    now rewrite Gplus_assoc.
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

Lemma big_sum_product_div_mod_split : forall {G} `{Monoid G} n m (f : nat -> G), 
  big_sum f (n * m) = 
  big_sum (fun i => big_sum (fun j => f (j + i * n)%nat) n) m.
Proof.
  intros.
  rewrite big_sum_double_sum.
  apply big_sum_eq_bounded.
  intros k Hk.
  f_equal.
  rewrite (Nat.div_mod_eq k n) at 1.
  lia.
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

(* developing l_a tactics for all these new typeclasses *)


  
Inductive mexp {G} : Type :=
| Ident : mexp
| Var : G -> mexp
| Op : mexp -> mexp -> mexp.


(* turns mexp into g *)
Fixpoint mdenote {G} `{Monoid G} (me : mexp) : G :=
  match me with
  | Ident => 0
  | Var v => v
  | Op me1 me2 => mdenote me1 + mdenote me2
  end.

(* we also want something that takes list G to G, this is done by G_big_plus *)

(* turns mexp into list G *)
Fixpoint flatten {G} `{Monoid G} (me : mexp) : list G :=
  match me with
  | Ident => nil
  | Var x => x :: nil
  | Op me1 me2 => flatten me1 ++ flatten me2
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


Ltac reify_mon me :=
  match me with
  | 0 => Ident
  | ?me1 + ?me2 =>
      let r1 := reify_mon me1 in
      let r2 := reify_mon me2 in
      constr:(Op r1 r2)
  | _ => constr:(Var me)
  end.

Ltac solve_monoid :=
  match goal with
  | [ |- ?me1 = ?me2 ] =>
      let r1 := reify_mon me1 in
      let r2 := reify_mon me2 in
      change (mdenote r1 = mdenote r2);
      apply monoid_reflect; simpl;
      repeat (rewrite Gplus_0_l); 
      repeat (rewrite Gplus_0_r);
      repeat (rewrite Gplus_assoc); try easy  
  end.

 
Lemma test : forall {G} `{Monoid G} a b c d, a + b + c + d = a + (b + c) + d.
Proof. intros.
       solve_monoid.
Qed.


(* there is a lot of repeated code here, perhaps could simplify things *)
Inductive gexp {G} : Type :=
| Gident : gexp
| Gvar : G -> gexp
| Gop : gexp -> gexp -> gexp
| Gmin : gexp -> gexp.

Fixpoint gdenote {G} `{Group G} (ge : gexp) : G :=
  match ge with
  | Gident => 0
  | Gvar v => v
  | Gop me1 me2 => gdenote me1 + gdenote me2
  | Gmin v => - gdenote v
  end.

Fixpoint gflatten {G} `{Group G} (ge : gexp) : list G :=
  match ge with
  | Gident => nil
  | Gvar x => x :: nil
  | Gop ge1 ge2 => gflatten ge1 ++ gflatten ge2
  | Gmin ge' => map Gopp (rev (gflatten ge'))
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

Ltac reify_grp ge :=
  match ge with
  | 0 => Gident
  | ?ge1 + ?ge2 =>
      let r1 := reify_grp ge1 in
      let r2 := reify_grp ge2 in
      constr:(Gop r1 r2)
  | ?ge1 - ?ge2 =>
      let r1 := reify_grp ge1 in
      let r2 := reify_grp ge2 in
      constr:(Gop r1 (Gmin r2))             
  | -?ge => 
      let r := reify_grp ge in
      constr:(Gmin r)
  | _ => constr:(Gvar ge)
  end.

Ltac solve_group :=
  unfold Gminus;
  match goal with
  | [ |- ?me1 = ?me2 ] =>
      let r1 := reify_grp me1 in
      let r2 := reify_grp me2 in
      change (gdenote r1 = gdenote r2);
      apply group_reflect; simpl gflatten;
      repeat (rewrite Gopp_involutive);
      repeat (try (rewrite big_plus_inv_r); 
              try (rewrite big_plus_inv_l); 
              try rewrite big_plus_reduce); simpl;
      repeat (rewrite Gplus_0_l); repeat (rewrite Gplus_0_r);
      repeat (rewrite Gplus_assoc); try easy      
  end.

Lemma test2 : forall {G} `{Group G} a b c d, a + b + c + d - d = a + (b + c) + d - d.
Proof. intros. solve_group. Qed.
 
Lemma test3 : forall {G} `{Group G} a b c, - (a + b + c) + a  = 0 - c - b.
Proof. intros. solve_group. Qed.
