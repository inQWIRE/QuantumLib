Require Import List.
Require Import Prelim.
Require Import Summation. 
Require Import FinFun. 
Require Import ListDec.
Require Import Setoid.

(* two important list functions used are NoDup and incl *)
(* in the following sections, we expand on these list functions *)





Global Program Instance list_is_monoid {X} : Monoid (list X) := 
  { Gzero := []
  ; Gplus := @app X
  }.
Next Obligation. rewrite app_nil_end; easy. Qed.
Next Obligation. rewrite app_assoc; easy. Qed.


Lemma big_sum_list_length : forall {X} (l : list (list X)) (l' : list X),
  G_big_plus l = l' -> G_big_plus (map (@length X) l) = length l'.
Proof. induction l.
       - intros.  
         destruct l'; easy.
       - intros.
         simpl in *; subst.
         rewrite app_length, (IHl (G_big_plus l)); easy. 
Qed.

Lemma length_big_sum_list : forall {X} (l : list (list X)),
  length (G_big_plus l) = G_big_plus (map (@length X) l).
Proof. intros. 
       rewrite (big_sum_list_length _ (G_big_plus l)); easy.
Qed.

Lemma In_big_sum_list_In_part : forall {X} (l : list (list X)) (x : X),
  In x (G_big_plus l) -> 
  exists l1, In l1 l /\ In x l1.
Proof. induction l. 
       - easy.
       - intros. 
         simpl in H; apply in_app_or in H.
         destruct H. 
         exists a; split; try left; easy. 
         apply IHl in H.
         destruct H as [l1 [H H0]].
         exists l1; split.
         right; easy. 
         easy. 
Qed.

Lemma In_part_In_big_sum_list : forall {X} (l : list (list X)) (x : X),
  (exists l1, In l1 l /\ In x l1) ->
  In x (G_big_plus l).
Proof. induction l.
       - intros. 
         destruct H; easy. 
       - intros. 
         destruct H as [l1 [H H0]].
         destruct H; subst.
         simpl; apply in_or_app; left; easy.
         simpl; apply in_or_app; right. 
         apply IHl.
         exists l1.
         easy. 
Qed.


Inductive eq_mod_perm {X} (l1 l2 : list X) : Prop := 
  | eq_list : NoDup l1 -> NoDup l2 -> incl l1 l2 -> incl l2 l1 -> eq_mod_perm l1 l2.

Infix "⩦" := eq_mod_perm (at level 70).


Definition disjoint {X} (l1 l2 : list X) : Prop := NoDup (l1 ++ l2).



Lemma In_EMP_compat : forall {X} (l1 l2 : list X) (x : X),
  l1 ⩦ l2 -> (iff (In x l1) (In x l2)).
Proof. intros; split; intros; inversion H.
       apply H3; easy.
       apply H4; easy.
Qed.




Add Parametric Morphism {X} : (@In X)
  with signature eq ==> eq_mod_perm ==> iff as Pplusf_mor.
Proof. intros x l1 l2 H. 
       apply In_EMP_compat; easy. 
Qed.


Lemma NoDup_app : forall {X} (l1 l2 : list X),
  NoDup l1 -> NoDup l2 ->
  (forall x, In x l1 -> ~ (In x l2)) ->
  NoDup (l1 ++ l2).
Proof. induction l1; intros. 
       - easy. 
       - simpl; apply NoDup_cons.
         unfold not; intros; apply (H1 a);  try (left; easy). 
         apply in_app_or in H2.
         destruct H2; auto.
         inversion H; easy.
         apply IHl1; auto.
         inversion H; auto.
         intros. 
         apply H1; right; easy.
Qed.

Lemma length_lt_new_elem : forall {X} (l2 l1 : list X) 
                                  (eq_dec : forall x y : X, {x = y} + {x <> y}),
  length l1 < length l2 ->
  NoDup l2 -> 
  exists x, In x l2 /\ ~ (In x l1).
Proof. induction l2; intros. 
       - destruct l1; try easy.
       - destruct (In_dec eq_dec a l1); simpl in *.
         apply (remove_length_lt eq_dec l1 a) in i.
         assert (H' : length (remove eq_dec a l1) < length l2). lia. 
         apply IHl2 in H'; auto.
         destruct H' as [x [H1 H2]].
         exists x; split.
         right; easy.
         unfold not; intros; apply H2.
         apply in_in_remove; auto.
         destruct (eq_dec x a); auto; subst.
         inversion H0; easy.
         inversion H0; easy.
         exists a; split; auto.
Qed.         

Lemma length_gt_EMP : forall {X} (l1 l2 : list X),
  NoDup l1 -> NoDup l2 -> 
  incl l1 l2 -> 
  length l1 >= length l2 ->
  l1 ⩦ l2.
Proof. intros. 
       split; auto.
       apply NoDup_length_incl; auto; lia.
Qed.

Lemma EMP_reduce : forall {X} (l1 l21 l22 : list X) (a : X), 
  (a :: l1) ⩦ (l21 ++ (a::l22)) -> l1 ⩦ (l21 ++ l22). 
Proof. intros; inversion H.
       apply eq_list. 
       apply NoDup_cons_iff in H0; easy.
       apply NoDup_remove_1 in H1; easy. 
       unfold incl; intros.
       apply NoDup_cons_iff in H0.
       destruct H0.
       assert (H4' := H4).
       apply (in_cons a) in H4.
       apply H2 in H4.
       apply in_or_app; apply in_app_or in H4.
       destruct H4; try (left; easy).
       destruct H4; subst.
       easy.
       right; easy. 
       unfold incl; intros. 
       assert (H' : In a0 (a :: l1)).
       { apply H3.  
         apply in_or_app; apply in_app_or in H4.
         destruct H4; try (left; easy). 
         right; right; easy. }
       destruct H'; try easy. 
       apply NoDup_remove_2 in H1.
       subst; easy.
Qed.

Lemma EMP_eq_length : forall {X} (l1 l2 : list X), 
  l1 ⩦ l2 -> length l1 = length l2.
Proof. induction l1; intros; inversion H.
       - apply incl_l_nil in H3; subst; easy.
       - destruct (in_split a l2) as [l21 [l22 H4]].
         apply H2; left; easy.
         subst. 
         apply EMP_reduce in H.
         apply IHl1 in H.
         rewrite app_length; simpl. 
         rewrite Nat.add_succ_r; apply eq_S. 
         rewrite <- app_length.
         easy. 
Qed.




(* Could work, but needs eq decidability 
Lemma eq_length_gives_map : forall {X} (h : decidable_eq X) (l1 l2 : list X),
  NoDup l1 -> NoDup l2 -> length l1 = length l2 ->
  exists f, Bijective f /\ map f l2 = l1.
Proof. induction l1.
       - intros; destruct l2; try easy; simpl. 
         exists (fun a => a); split; auto.
         unfold Bijective; intros. 
         exists (fun a => a); easy. 
       - intros. 
         destruct l2; try easy.
         simpl in *.
         apply Nat.succ_inj in H1.
         apply NoDup_cons_iff in H; apply NoDup_cons_iff in H0.
         apply IHl1 in H1; try easy.
         destruct H1 as [f [H1 H2]].
         exists (fun b => match b with 
                  | x => a
                  | _ => f b
                  end). 
*)


(* quick little lemma useing FinFun's Listing *)
Lemma list_rep_length_eq : forall {X} (l1 l2 : list X),
  Listing l1 -> Listing l2 -> length l1 = length l2.
Proof. intros. 
       destruct H; destruct H0.
       apply Nat.le_antisymm; apply NoDup_incl_length; auto; unfold incl; intros. 
       apply H2.
       apply H1.
Qed.


(* testing for NoDup tactic, to be developted... *)
Lemma test : NoDup [1;2;3;4;5]%nat.                                            
Proof. repeat (apply NoDup_cons; unfold not; intros; repeat (destruct H; try lia)).
       apply NoDup_nil.
Qed.






(* TODO: figure out how to get rid of Geq_dec - it is already in Summation.v for rings *)
(* shouldn't equality on finite types be decidable? *)
Class FiniteGroup G `{Group G} :=
  { G_list_rep : list G
  ; G_finite_ver : Listing G_list_rep      
  ; Geq_dec : forall g h : G, { g = h } + { g <> h }           
  }.

Infix "·" := Gplus (at level 40) : group_scope.

Definition group_size G `{FiniteGroup G} := length G_list_rep.

Lemma group_size_gt_0 : forall G `{FiniteGroup G},
  group_size G > 0.
Proof. intros. 
       assert (H' : In 0 G_list_rep).
       { apply G_finite_ver. }
       unfold group_size.
       destruct G_list_rep; try easy; simpl; lia.
Qed.

Lemma finitegroup_finite : forall G `{FiniteGroup G},
  Finite' G.
Proof. intros. 
       unfold Finite'. 
       exists G_list_rep.
       apply G_finite_ver.
Qed.
 
Lemma Gplus_injective : forall G `{Group G} (g : G),
  Injective (Gplus g).
Proof. intros. 
       unfold Injective; intros.
       apply Gplus_cancel_l in H1; easy.
Qed.

Lemma Gplus_surjective : forall G `{Group G} (g : G),
  Surjective (Gplus g).
Proof. intros. 
       unfold Surjective; intros.
       exists (Gopp g · y).
       rewrite Gplus_assoc, Gopp_r, Gplus_0_l; easy. 
Qed.


Lemma mul_by_g_perm : forall G `{FiniteGroup G} (g : G),
  Listing (map (Gplus g) G_list_rep).
Proof. intros.
       destruct G_finite_ver.
       split. 
       - apply Injective_map_NoDup; auto.
         apply Gplus_injective.
         inversion H1; easy. 
       - intros.
         unfold Full; intros. 
         replace a with (g · ((Gopp g) · a)).
         apply in_map; apply H3.
         rewrite Gplus_assoc, Gopp_r, Gplus_0_l; easy. 
Qed.

  

(* defining homomorphisms between groups *)


(* it would be quite nice to change the order of the inputs here, mirroring f : G -> H *)
Definition group_homomorphism (H G : Type) `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) : Prop :=
  forall x1 x2, f (x1 · x2) = f x1 · f x2.


Definition inclusion_map (H G : Type) `{FiniteGroup H} `{FiniteGroup G}  (f : H -> G) : Prop :=
  Injective f /\ group_homomorphism H G f.


Definition sub_group (H G : Type) `{FiniteGroup H} `{FiniteGroup G} : Prop :=
  exists f, inclusion_map H G f.


Lemma homo_id : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G),
  group_homomorphism H G f -> f 0 = 0.
Proof. intros.
       apply (Gplus_cancel_l (f 0) 0 (f 0)).
       rewrite Gplus_0_r, <- H6, Gplus_0_r.
       easy. 
Qed.

Lemma homo_inv : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (h : H),
  group_homomorphism H G f -> f (- h) = - (f h).
Proof. intros. 
       apply (Gplus_cancel_l _ _ (f h)).
       rewrite Gopp_r, <- H6, Gopp_r.
       apply homo_id in H6.
       easy. 
Qed.

Lemma sub_group_closed_under_inv : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a : G),
  inclusion_map H G f -> 
  In a (map f G_list_rep) -> In (- a) (map f G_list_rep).
Proof. intros.
       apply in_map_iff in H7; destruct H7 as [x [H7 H8]].
       apply in_map_iff.
       exists (-x); split.
       rewrite <- H7; apply (homo_inv H G).
       inversion H6; easy.
       apply G_finite_ver.
Qed.

Lemma sub_group_closed_under_mul : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a b : G),
  inclusion_map H G f -> 
  In a (map f G_list_rep) -> In b (map f G_list_rep) ->
  In (a · b) (map f G_list_rep).
Proof. intros. 
       apply in_map_iff in H7; destruct H7 as [xa [H7 H9]].
       apply in_map_iff in H8; destruct H8 as [xb [H8 H10]].
       apply in_map_iff.
       exists (xa · xb); split.
       inversion H6.
       rewrite H12; subst; easy.
       apply G_finite_ver.
Qed.

Lemma in_own_coset : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a : G),
  inclusion_map H G f -> 
  In a (map (Gplus a) (map f G_list_rep)).
Proof. intros. 
       rewrite map_map.
       apply in_map_iff.
       exists 0; split.
       erewrite homo_id, Gplus_0_r; auto.
       inversion H6; easy. 
       apply G_finite_ver.
Qed.


Lemma in_coset_cancel : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a b : G),
  inclusion_map H G f -> 
  In a (map (Gplus b) (map f G_list_rep)) <-> In ((- b) · a) (map f G_list_rep).
Proof. split; intros. 
       - rewrite map_map in H7.
         apply in_map_iff in H7; destruct H7 as [x [H7 H8]].
         apply in_map_iff. 
         exists x; split; auto.
         rewrite <- H7; solve_group.  
       - rewrite map_map.
         apply in_map_iff in H7; destruct H7 as [x [H7 H8]].
         apply in_map_iff. 
         exists x; split; auto.
         rewrite H7; solve_group.
Qed.

Lemma cosets_same1 : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a b : G),
  inclusion_map H G f -> 
  (exists x, In x (map (Gplus a) (map f G_list_rep)) /\ In x (map (Gplus b) (map f G_list_rep))) ->
  (map (Gplus a) (map f G_list_rep)) ⩦ (map (Gplus b) (map f G_list_rep)).
Proof. intros. 
       destruct H7 as [x [H7 H8]].
       rewrite map_map in H7, H8.
       apply in_map_iff in H7; apply in_map_iff in H8.
       destruct H7 as [xa [H7 H9]].
       destruct H8 as [xb [H8 H10]].
       apply eq_list.
       all : repeat (try apply Injective_map_NoDup; try apply Gplus_injective); 
         inversion H2; auto.
       all : try (destruct H6; easy); try apply G_finite_ver.
       - repeat rewrite map_map.
         unfold incl; intros. 
         apply in_map_iff in H11; destruct H11 as [a1 [H11 H12]].
         apply in_map_iff; subst.
         exists ((xb · - xa) · a1); split; try apply G_finite_ver.
         apply (Gplus_cancel_l _ _ (Gopp b)).
         apply (f_equal (Gplus (Gopp b))) in H8.
         rewrite Gplus_assoc, Gopp_l, Gplus_0_l, Gplus_assoc in *.
         apply (f_equal (fun g => g · (Gopp (f xa)))) in H8.
         rewrite <- Gplus_assoc, Gopp_r, Gplus_0_r in H8.
         inversion H6; subst.
         rewrite <- H8, <- (homo_inv _ _ _ xa); auto.
         do 2 rewrite <- H11.
         inversion H6; easy. 
       - repeat rewrite map_map.
         unfold incl; intros. 
         apply in_map_iff in H11; destruct H11 as [a1 [H11 H12]].
         apply in_map_iff; subst.
         exists ((xa · - xb) · a1); split; try apply G_finite_ver.
         apply (Gplus_cancel_l _ _ (Gopp a)).
         apply (f_equal (Gplus (Gopp a))) in H8.
         rewrite (Gplus_assoc _ a), Gopp_l, Gplus_0_l, Gplus_assoc in *.
         apply (f_equal (fun g => g · (Gopp (f xb)))) in H8.
         rewrite <- Gplus_assoc, Gopp_r, Gplus_0_r in H8.
         inversion H6; subst.
         rewrite H8, <- (homo_inv _ _ _ xb); auto.
         do 2 rewrite <- H11.
         inversion H6; easy. 
Qed.

Lemma cosets_same2 : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a b : G),
  inclusion_map H G f -> 
  (In b (map (Gplus a) (map f G_list_rep))) ->
  (map (Gplus a) (map f G_list_rep)) ⩦ (map (Gplus b) (map f G_list_rep)).
Proof. intros. 
       apply (cosets_same1 _ _ _ a b); auto.
       exists b; split; auto.
       apply (in_own_coset _ _ _ b); auto.
Qed.

Lemma cosets_diff : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a b : G),
  inclusion_map H G f ->
  ~ (In b (map (Gplus a) (map f G_list_rep))) ->
  NoDup ((map (Gplus a) (map f G_list_rep)) ++ (map (Gplus b) (map f G_list_rep))).
Proof. intros.
       inversion H6; subst.
       apply NoDup_app.
       all : repeat (try apply Injective_map_NoDup; try apply Gplus_injective); auto. 
       all : try (apply G_finite_ver).
       intros. 
       unfold not; intros; apply H7.
       apply (In_EMP_compat _ (map (Gplus b) (map f G_list_rep))).
       apply (cosets_same1 _ _ _ a b H6); auto.
       exists x; split; easy. 
       apply (in_own_coset _ _ _ b); auto.
Qed.


(*
Ltac lfa (


 lfa H. instead, assert F is a field, use tactic, then prove assertion.
 Put all in Ltac. use frech H, etc... like in prep_mat_eq 


instead of 
`assert (H : field G) by auto`,
do
let H := fresh “H” in assert ...

... clear H


*)


       
(* how do I avoid having to state list_monoid_G here? *)
Definition coset_rep_list_to_cosets H G `{FiniteGroup H} `{FiniteGroup G} 
                                      (f : H -> G) (l : list G) : list G :=
(G_big_plus (map (fun g => map (Gplus g) (map f G_list_rep)) l)).



Lemma extend_coset_rep_list : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (l : list G),
  inclusion_map H G f -> 
  NoDup (coset_rep_list_to_cosets H G f l) ->
  length (coset_rep_list_to_cosets H G f l) < group_size G ->
  exists g, NoDup (coset_rep_list_to_cosets H G f (g::l)).
Proof. intros.
       apply length_lt_new_elem in H8.
       destruct H8 as [x [H8 H9]].
       exists x; unfold coset_rep_list_to_cosets; simpl. 
       apply NoDup_app.
       repeat (try apply Injective_map_NoDup; try apply Gplus_injective); 
         inversion H6; auto; apply G_finite_ver.
       apply H7.
       intros. 
       unfold not; intros; apply H9.
       unfold coset_rep_list_to_cosets.
       apply In_big_sum_list_In_part in H11. 
       destruct H11 as [l1 [H11 H12]].
       apply (in_coset_cancel H G) in H10; auto.
       apply in_map_iff in H11.
       destruct H11 as [a [H11 H13]]; subst.
       apply (in_coset_cancel H G) in H12; auto. 
       apply (sub_group_closed_under_inv H G) in H10; auto.  
       rewrite Gopp_plus_distr, Gopp_involutive in H10.
       apply (sub_group_closed_under_mul H G f (- a · x0) (- x0 · x)) in H10; auto.
       rewrite Gplus_assoc, <- (Gplus_assoc _ x0), Gopp_r, Gplus_0_r in H10.
       apply In_part_In_big_sum_list.
       exists (map (Gplus a) (map f G_list_rep)); split.
       apply in_map_iff.
       exists a; split; easy.
       apply (in_coset_cancel H G); auto.
       apply Geq_dec.
       apply G_finite_ver.
Qed.       

Lemma length_cosets : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (l : list G),
  inclusion_map H G f -> 
  length (coset_rep_list_to_cosets H G f l) = (group_size H * length l)%nat.
Proof. intros.  
       unfold coset_rep_list_to_cosets.
       rewrite length_big_sum_list.
       rewrite (big_plus_constant _ (group_size H)).
       rewrite times_n_nat, map_map, map_length; easy. 
       intros.
       rewrite map_map in H7.
       apply in_map_iff in H7; destruct H7 as [x [H7 H8]]; subst.
       rewrite map_map, map_length; easy.
Qed.


Lemma get_coset_rep_list1 : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (n : nat),
  inclusion_map H G f -> 
  group_size H * n <= group_size G ->
  exists l, length l = n /\ NoDup (coset_rep_list_to_cosets H G f l).
Proof. induction n.
       - intros.
         exists []; split; try easy.
         unfold coset_rep_list_to_cosets; simpl.
         apply NoDup_nil.
       - intros. 
         assert (H8 : group_size H * n < group_size G). 
         { assert (H' := group_size_gt_0 H). lia. }
         assert (H9 := H6).
         apply IHn in H9; try lia.
         destruct H9 as [l [H9 H10]].
         apply (extend_coset_rep_list H G) in H10; auto.
         destruct H10 as [g H10].
         exists (g :: l); split; simpl; try lia; auto.
         rewrite length_cosets; subst; easy.
Qed.

Lemma get_coset_rep_list2 : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G),
  inclusion_map H G f -> 
  exists l, group_size H * length l >= group_size G /\ NoDup (coset_rep_list_to_cosets H G f l).
Proof. intros. 
       destruct (get_coset_rep_list1 H G f (group_size G / group_size H)%nat) as [l [H7 H8]]; auto.
       apply Nat.mul_div_le. 
       assert (H' := group_size_gt_0 H). lia. 
       bdestruct (group_size H * length l <? group_size G).
       - destruct (extend_coset_rep_list H G f l) as [g H10]; auto.
         rewrite length_cosets; auto.
         exists (g :: l); split; auto.
         simpl; rewrite H7.
         assert (H' := group_size_gt_0 H).
         assert (H'' : group_size H <> 0). 
         destruct (group_size H); try easy.
         apply (Nat.mul_succ_div_gt (group_size G) (group_size H)) in H''.
         lia.
       - exists l; split; easy.
Qed.         



Lemma get_full_coset_reps1 : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G),
  inclusion_map H G f -> 
  exists (l : list G), (coset_rep_list_to_cosets H G f l) ⩦ G_list_rep.
Proof. intros. 
       destruct (get_coset_rep_list2 H G f) as [l [H7 H8]]; auto. 
       exists l. 
       apply length_gt_EMP; auto.
       apply G_finite_ver.
       unfold incl; intros; apply G_finite_ver.
       rewrite length_cosets; easy.
Qed.   


Theorem Lagranges_Theorem : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G),
  inclusion_map H G f -> 
  exists d, (group_size H * d)%nat = group_size G.
Proof. intros. 
       destruct (get_full_coset_reps1 H G f) as [l H7]; auto.
       exists (length l).
       rewrite <- (length_cosets H G f); auto. 
       unfold group_size.
       apply EMP_eq_length.
       easy.
Qed.       


(*
n

Lemma cosets_add : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (l : list G) (a : G),
  inclusion_map H G f -> ~ (In a (G_big_plus (map (fun b -> map (Gplus b) (map f G_list_rep))))) ->
  *) 



(* This is only true for abelian groups. 

(* important lemma we are trying to prove *)
Lemma sum_of_elems_invr : forall G `{FiniteGroup G} (l1 l2 : list G),
  list_rep G l1 -> list_rep G l2 -> G_big_plus l1 = G_big_plus l2.

*)







(**********************************)
(* Some examples of finite groups *)
(**********************************)

Inductive Quaternion :=
| p_1
| n_1
| p_i
| n_i
| p_j
| n_j
| p_k
| n_k.

Definition quatNeg (q : Quaternion) : Quaternion :=
  match q with
  | p_1 => n_1
  | n_1 => p_1
  | p_i => n_i
  | n_i => p_i
  | p_j => n_j 
  | n_j => p_j
  | p_k => n_k
  | n_k => p_k
  end.

Definition quatInv (q : Quaternion) : Quaternion :=
  match q with
  | p_1 => p_1
  | n_1 => n_1
  | p_i => n_i
  | n_i => p_i
  | p_j => n_j 
  | n_j => p_j
  | p_k => n_k
  | n_k => p_k
  end.

Lemma quatNeg_inv : forall (q : Quaternion), quatNeg (quatNeg q) = q.
Proof. destruct q; easy.
Qed.

Lemma quatInv_inv : forall (q : Quaternion), quatInv (quatInv q) = q.
Proof. destruct q; easy.
Qed.


(* could split this up into multiple functions like in Types.v, but would overcomplicate *)
Definition quatMul (q1 q2 : Quaternion) : Quaternion :=
  match (q1, q2) with
  | (p_1, _) => q2
  | (_, p_1) => q1
  | (n_1, _) => quatNeg q2
  | (_, n_1) => quatNeg q1
  | (p_i, p_i) => n_1
  | (p_i, n_i) => p_1
  | (p_i, p_j) => p_k
  | (p_i, n_j) => n_k
  | (p_i, p_k) => n_j
  | (p_i, n_k) => p_j
  | (n_i, p_i) => p_1
  | (n_i, n_i) => n_1
  | (n_i, p_j) => n_k
  | (n_i, n_j) => p_k
  | (n_i, p_k) => p_j
  | (n_i, n_k) => n_j
  | (p_j, p_i) => n_k
  | (p_j, n_i) => p_k
  | (p_j, p_j) => n_1
  | (p_j, n_j) => p_1
  | (p_j, p_k) => p_i
  | (p_j, n_k) => n_i
  | (n_j, p_i) => p_k
  | (n_j, n_i) => n_k
  | (n_j, p_j) => p_1
  | (n_j, n_j) => n_1
  | (n_j, p_k) => n_i
  | (n_j, n_k) => p_i
  | (p_k, p_i) => p_j
  | (p_k, n_i) => n_j
  | (p_k, p_j) => n_i
  | (p_k, n_j) => p_i
  | (p_k, p_k) => n_1
  | (p_k, n_k) => p_1
  | (n_k, p_i) => n_j
  | (n_k, n_i) => p_j
  | (n_k, p_j) => p_i
  | (n_k, n_j) => n_i
  | (n_k, p_k) => p_1
  | (n_k, n_k) => n_1
  end.


  
Global Program Instance quat_is_monoid : Monoid Quaternion := 
  { Gzero := p_1
  ; Gplus := quatMul
  }.
Solve All Obligations with program_simpl; destruct g; try easy; destruct h; destruct i; easy. 


Global Program Instance quat_is_group : Group Quaternion :=
  { Gopp := quatInv }.
Solve All Obligations with program_simpl; destruct g; try easy. 



Lemma quatMul_comm : forall (q1 q2 : Quaternion), 
    q1 · q2 = q2 · q1 \/ q1 · q2 = quatNeg (q2 · q1).
Proof. intros. 
       destruct q1;
       destruct q2;
       try (left; easy); try (right; easy).  
Qed.


Definition quat_list : list Quaternion := [p_1; p_i; p_j; p_k; n_1; n_i; n_j; n_k].


Global Program Instance quat_is_finitegroup : FiniteGroup Quaternion := 
  { G_list_rep := quat_list
  }.
Next Obligation. 
Proof. split. 
       - repeat (apply NoDup_cons; unfold not; intros; 
                 repeat (destruct H; try easy)).
         apply NoDup_nil.
       - unfold Full; intros. 
         destruct a; simpl; 
           repeat (try (left; easy); right).
Qed.
Next Obligation.
Proof. destruct g; destruct h; try (left; easy); right; easy. Qed.


(* **) 

(***)
(****) 
