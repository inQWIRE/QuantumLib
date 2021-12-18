Require Export Polynomial.

(************************************)
(* First, we define a topology on C *)
(************************************)

Declare Scope topology_scope.
Delimit Scope topology_scope with T.
Open Scope topology_scope.


(* we define a subset of C as a function from C to {True, False} *)  
(* so c is in A if A(c) = True *)
Definition Csubset := C -> Prop.

Definition union (A B : Csubset) : Csubset :=
  fun c => A c \/ B c.

Definition intersection (A B : Csubset) : Csubset :=
  fun c => A c /\ B c.

Definition complement (A : Csubset) : Csubset :=
  fun c => not (A c).

Definition setminus (A B : Csubset) : Csubset :=
  intersection A (complement B).

Definition is_in (a : C) (A : Csubset) : Prop := A a.

Definition subset (A B : Csubset) : Prop :=
  forall c, A c -> B c.

Definition ϵ_disk (a : C) (ϵ : R) : Csubset :=
  fun c => Cmod (c - a) < ϵ.

Definition bounded (A : Csubset) : Prop :=
  exists ϵ, subset A (ϵ_disk C0 ϵ). 

Definition image (f : C -> C) (A : Csubset) : Csubset := 
  fun c => (exists c', A c' /\ f c' = c).

Definition preimage (f : C -> C) (B : Csubset) : Csubset :=
  fun c => B (f c).

Definition continuous_on (f : C -> C) (A : Csubset) : Prop :=
  forall c, A c -> continuous_at f c.

Infix "∪" := union (at level 50, left associativity) : topology_scope.
Infix "∩" := intersection (at level 40, left associativity) : topology_scope.
Infix "⊂" := subset (at level 0) : topology_scope.
Infix "\" := setminus (at level 0) : topology_scope.
Infix "@" := image (at level 0) : topology_scope.
Notation "f *{ A }" := (preimage f A) (at level 0) : topology_scope.
Notation "A *" := (complement A) (at level 0) : topology_scope.
Infix "∈" := is_in (at level 0) : topology_scope.
Notation "B( a , ϵ )" := (ϵ_disk a ϵ) (at level 30, no associativity) : topology_scope.


Definition open (A : Csubset) : Prop :=
  forall c, A c -> exists ϵ, ϵ > 0 /\ B(c,ϵ) ⊂ A.

Definition closed (A : Csubset) : Prop :=
  open (A*).

Definition empty_set : Csubset :=
  fun _ => False. 

Definition C_ : Csubset :=
  fun _ => True. 


(** Subset lemmas *)

Lemma subset_cup_l : forall (A B : Csubset),
  A ⊂ (A ∪ B).
Proof. unfold subset, union; left; easy. Qed.

Lemma subset_cup_r : forall (A B : Csubset),
  B ⊂ (A ∪ B).
Proof. unfold subset, union; right; easy. Qed.

Lemma subset_cap_l : forall (A B : Csubset),
  (A ∩ B) ⊂ A.
Proof. unfold subset, intersection; easy. Qed.

Lemma subset_cap_r : forall (A B : Csubset),
  (A ∩ B) ⊂ B.
Proof. unfold subset, intersection; easy. Qed.

Lemma subset_self : forall (A : Csubset),
  A ⊂ A.
Proof. easy. Qed. 

Lemma subset_transitive : forall (A B C : Csubset),
  A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof. unfold subset; intros. 
       apply H0; apply H; easy. 
Qed.

#[global] Hint Resolve subset_cup_l subset_cup_r subset_cap_l subset_cap_r subset_self subset_transitive : Csub_db.

Lemma subset_cup_reduce : forall (A B C : Csubset),
  A ⊂ B \/ A ⊂ C -> A ⊂ (B ∪ C). 
Proof. unfold subset, union; intros. 
       destruct H.
       - left; apply H; easy. 
       - right; apply H; easy. 
Qed.

Lemma subset_cap_reduce : forall (A B C : Csubset),
  A ⊂ B /\ A ⊂ C -> A ⊂ (B ∩ C). 
Proof. unfold subset, intersection; intros. 
       destruct H; split.
       apply H; easy.
       apply H1; easy.
Qed.

Lemma subset_ball_l : forall (a : C) (ϵ1 ϵ2 : R),
  B(a, Rmin ϵ1 ϵ2) ⊂ B(a, ϵ1).
Proof. unfold subset, ϵ_disk; intros. 
       eapply Rlt_le_trans; eauto.
       apply Rmin_l.
Qed.

Lemma subset_ball_r : forall (a : C) (ϵ1 ϵ2 : R),
  B(a, Rmin ϵ1 ϵ2) ⊂ B(a, ϵ2).
Proof. unfold subset, ϵ_disk; intros. 
       eapply Rlt_le_trans; eauto.
       apply Rmin_r.
Qed.

Lemma subset_C_ : forall (A : Csubset),
  A ⊂ C_.
Proof. unfold subset; easy. Qed.

#[global] Hint Resolve subset_cup_reduce subset_cap_reduce subset_ball_l subset_ball_r subset_C_ : Csub_db.

Lemma subset_not : forall (A B : Csubset), 
  ~ (A ⊂ B) -> (exists a, A a /\ B* a).
Proof. intros. 
       destruct (Classical_Prop.classic (exists a : C, A a /\ (B) * a)); auto. 
       assert (H1 : forall a, ~ (A a /\ (B) * a)).
       { unfold not; intros. 
         apply H0; exists a; easy. }
       assert (H2 : A ⊂ B).
       { unfold subset; intros. 
         assert (H' := H1 c). 
         apply Classical_Prop.not_and_or in H'.
         destruct H'; try easy.
         unfold not, complement in H3.
         apply Decidable.dec_not_not; auto. 
         unfold Decidable.decidable.
         apply Classical_Prop.classic. }
       easy.
Qed.

(** some lemmas about open/closed sets *)

Lemma subset_equal : forall (A B : Csubset),
  A ⊂ B -> B ⊂ A -> A = B.
Proof. unfold subset; intros. 
       apply functional_extensionality; intros. 
       destruct (Classical_Prop.classic (A x)).
       Admitted.

Lemma Cmod_switch : forall (a b : C),
  Cmod (a - b) = Cmod (b - a).
Proof. intros. 
       replace (b - a) with (- (a - b)) by lca. 
       rewrite Cmod_opp; easy.
Qed.

Lemma Cmod_triangle_le : forall (a b : C) (ϵ : R),
  Cmod a + Cmod b < ϵ -> Cmod (a + b) < ϵ.
Proof. intros. 
       assert (H0 := Cmod_triangle a b).
       lra. 
Qed.

Lemma Cmod_triangle_diff : forall (a b c : C) (ϵ : R),
  Cmod (c - b) + Cmod (b - a) < ϵ -> Cmod (c - a) < ϵ.
Proof. intros. 
       replace (c - a) with ((c - b) + (b - a)) by lca. 
       apply Cmod_triangle_le.
       easy. 
Qed.

Lemma emptyset_open : open empty_set.
Proof. easy. Qed.

Lemma C_open : open C_.
Proof. unfold open, C_, is_in; intros. 
       exists 1; split; try lra. 
       easy. 
Qed.

Lemma ball_open : forall (a : C) (ϵ : R),
  ϵ > 0 -> open (B(a,ϵ)).
Proof. unfold open; intros.
       unfold ϵ_disk in H0.
       exists (ϵ - Cmod (c - a))%R.
       split; try lra.
       unfold subset; intros.
       unfold ϵ_disk in *.
       assert (H2 : Cmod (c0 - c) + Cmod (c - a) < ϵ). { lra. }
       apply Cmod_triangle_diff in H2.
       easy. 
Qed.

Lemma closed_ball_complement_open : forall (c : C) (r : R),
  open (fun c' => Cmod (c' - c) > r).
Proof. unfold open; intros.
       exists (Cmod (c0 - c) - r)%R.
       split; try lra. 
       unfold subset, ϵ_disk; intros. 
       assert (H' := Cmod_triangle (c1 - c) (c0 - c1)).
       replace (c1 - c + (c0 - c1)) with (c0 - c) in H' by lca. 
       rewrite Cmod_switch in H0; lra. 
Qed.

Lemma closed_ball_closed : forall (a : C) (ϵ : R),
  closed (fun c' => Cmod (c' - a) <= ϵ).
Proof. intros; unfold closed. 
       assert (H' : (fun c' : C => Cmod (c' - a) <= ϵ) * = (fun c' : C => Cmod (c' - a) > ϵ)).
       { apply subset_equal; unfold subset, complement; intros; lra. }
       rewrite H'.
       apply closed_ball_complement_open.
Qed.

Lemma cup_open : forall (A B : Csubset),
  open A -> open B -> open (A ∪ B).
Proof. unfold open; intros.  
       unfold union in H1.
       destruct H1.
       - destruct ((H c) H1) as [ϵ [H2 H3] ].
         exists ϵ.
         split; eauto with Csub_db. 
       - destruct ((H0 c) H1) as [ϵ [H2 H3] ].
         exists ϵ.
         split; eauto with Csub_db. 
Qed.

Lemma cap_open : forall (A B : Csubset),
  open A -> open B -> open (A ∩ B).
Proof. unfold open; intros.  
       unfold intersection in H1.
       destruct H1.
       destruct ((H c) H1) as [ϵ1 [H3 H4] ].
       destruct ((H0 c) H2) as [ϵ2 [H5 H6] ].
       exists (Rmin ϵ1 ϵ2).
       split. 
       apply Rmin_Rgt_r; easy.       
       eauto with Csub_db.
Qed.




(** lemmas about preimage *)

(** some lemmas showing basic properties *)

Lemma complement_involutive : forall (A : Csubset),
  (A*)* = A.
Proof. unfold complement; intros. 
       apply subset_equal.
       - unfold subset; intros. 
         apply Classical_Prop.NNPP; easy. 
       - unfold subset; intros. 
         unfold not. intros.
         easy. 
Qed.

Lemma bounded_cup : forall (A B : Csubset),
  bounded A -> bounded B -> bounded (A ∪ B).
Proof. intros. 
       destruct H as [ϵ1 H].
       destruct H0 as [ϵ2 H0].
       exists (Rmax ϵ1 ϵ2).
       unfold subset, ϵ_disk in *; intros. 
       destruct H1. 
       - apply H in H1.
         eapply Rlt_le_trans; eauto. 
         apply Rmax_l.
       - apply H0 in H1.
         eapply Rlt_le_trans; eauto. 
         apply Rmax_r.
Qed.       


(************************)
(* Defining compactness *)
(************************)

Definition Ccover := Csubset -> Prop.

Definition open_cover (G : Ccover) : Prop :=
  forall A, G A -> open A.

Definition subcover (G1 G2 : Ccover) : Prop :=
  forall A, G1 A -> G2 A.

Definition list_to_cover (l : list Csubset) : Ccover :=
  fun A => In A l.

Definition finite_cover (G : Ccover) : Prop :=
  exists l, list_to_cover l = G.

Definition big_cup (G : Ccover) : Csubset :=
  fun c => (exists A, G A /\ A c).

Definition big_cap (G : Ccover) : Csubset :=
  fun c => (forall A, G A -> A c).

Definition compact (A : Csubset) : Prop :=
  forall G, open_cover G -> A ⊂ (big_cup G) -> 
       (exists G', finite_cover G' /\ subcover G' G /\ A ⊂ (big_cup G')).

(** now some lemmas *)

Lemma open_cover_reduce : forall (l : list Csubset) (A : Csubset),
  open_cover (list_to_cover (A :: l)) ->
  open A /\ open_cover (list_to_cover l).
Proof.  intros; split; unfold open_cover in H.
        apply H; left; easy.  
        unfold open_cover; intros. 
        apply H; right; easy. 
Qed.

Lemma subcover_reduce : forall (l : list Csubset) (A : Csubset) (G : Ccover),
  subcover (list_to_cover (A :: l)) G ->
  G A /\ subcover (list_to_cover l) G.
Proof. intros; split.       
       apply H; left; easy. 
       unfold subcover; intros. 
       apply H; right; easy. 
Qed.

Lemma big_cup_extend_l : forall (l : list Csubset) (A : Csubset),
  A ∪ (big_cup (list_to_cover l)) = big_cup (list_to_cover (A :: l)).
Proof. intros.
       unfold union, big_cup, list_to_cover; intros.        
       apply subset_equal.
       - unfold subset; intros. 
         destruct H.
         + exists A; split; try left; easy. 
         + destruct H as [A0 [H H0] ]. 
           exists A0. split; try right; easy. 
       - unfold subset; intros. 
         destruct H as [A0 [ [H | H] H0] ]; subst.
         left; easy. 
         right; exists A0; split; easy. 
Qed.

Lemma big_cap_extend_l : forall (l : list Csubset) (A : Csubset),
  A ∩ (big_cap (list_to_cover l)) = big_cap (list_to_cover (A :: l)).
Proof. intros.
       unfold intersection, big_cap, list_to_cover; intros.        
       apply subset_equal.
       - unfold subset; intros. 
         destruct H; destruct H0; subst; try easy.
         apply H1; apply H0.
       - unfold subset; intros. 
         split.
         apply H; left; easy. 
         intros; apply H; right; apply H0.
Qed.

Lemma arb_cup_open : forall (G : Ccover),
  open_cover G -> open (big_cup G).
Proof. unfold open_cover, open, big_cup in *; intros. 
       destruct H0 as [A [H0 H1] ].
       destruct (H A H0 c) as [ϵ [H2 H3] ]; auto.
       exists ϵ.
       split; auto. 
       eapply subset_transitive; eauto. 
       unfold subset; intros. 
       exists A; split; easy. 
Qed.

Lemma ltc_open : forall (l : list Csubset),
  open_cover (list_to_cover l) -> open (big_cap (list_to_cover l)).
Proof. induction l as [| h].
       - intros. 
         unfold list_to_cover, big_cap, open; intros. 
         exists 1; split; try easy; lra. 
       - intros. 
         apply open_cover_reduce in H.
         rewrite <- big_cap_extend_l.
         apply cap_open; try easy. 
         apply IHl; easy. 
Qed.

Lemma fin_cap_open : forall (G : Ccover),
  open_cover G -> finite_cover G -> open (big_cap G).
Proof. intros. 
       unfold finite_cover in H0.
       destruct H0 as [l H0].
       rewrite <- H0.
       apply ltc_open.
       rewrite H0; easy. 
Qed.

(* we have not yet defined enough setup to define preimage for functions whose domains differ
   from C_. This is fine when proving FTA, since polynomials are continuous everywhere.
   Could be expanded if we want to make a general topology library *)
Lemma continuous_preimage_open : forall (f : C -> C),
  continuous_on f C_ -> (forall A, open A -> open f*{A}).
Proof. intros. 
       unfold open in *; intros. 
       unfold preimage in H1. 
       destruct (H0 (f c) H1) as [ϵ [H2 H3] ]. 
       assert (H' : C_ c). easy. 
       destruct (H c H' ϵ) as [δ [H4 H5] ]; auto.  
       exists δ; split; auto.
       unfold subset, preimage, ϵ_disk in *; intros.  
       destruct (Ceq_dec c0 c); subst; try easy. 
       apply H3; apply H5; try easy.  
Qed.

Lemma preimage_open_continuous : forall (f : C -> C),
  (forall A, open A -> open f*{A}) -> continuous_on f C_.
Proof. unfold continuous_on; intros. 
       unfold continuous_at, limit_at_point; intros. 
       assert (H2 := (H ( B(f c,ϵ) ) (ball_open (f c) ϵ H1))).
       unfold open in H2. 
       destruct (H2 c) as [δ [H3 H4] ].
       unfold preimage, ϵ_disk. 
       replace (f c - f c)%C with C0 by lca. 
       rewrite Cmod_0; lra. 
       exists δ; split; auto; intros. 
       unfold preimage, subset, ϵ_disk in H4.
       apply H4; easy.  
Qed.

(* we define the preimage of a cover *)
Definition preimage_cover (f : C -> C) (G : Ccover) : Ccover :=
  fun A => (exists A', G A' /\ A = f*{A'}).

Lemma open_cover_preimage_open : forall (f : C -> C) (G : Ccover),
  open_cover G -> continuous_on f C_ ->
  open_cover (preimage_cover f G).
Proof. intros. 
       unfold open_cover, preimage_cover; intros. 
       destruct H1 as [A' [H1 H2] ]; subst.
       apply H in H1.
       apply (continuous_preimage_open _ H0); easy.
Qed.

Lemma subset_preimage_pres : forall (f : C -> C) (A : Csubset) (G : Ccover),
  ((f) @ (A)) ⊂ (big_cup G) ->
  A ⊂ (big_cup (preimage_cover f G)).
Proof. unfold subset; intros. 
       unfold big_cup, preimage_cover.
       assert (H' : big_cup G (f c)).
       { apply H.
         exists c; split; easy. }
       unfold big_cup in H'.
       destruct H' as [A0 [H1 H2] ].
       exists (f*{A0}); split; try easy. 
       exists A0; split; easy.
Qed.       

Lemma extract_finite_image : forall (f : C -> C) (l : list Csubset) (A : Csubset) (G : Ccover),
  subcover (list_to_cover l) (preimage_cover f G) -> 
  A ⊂ (big_cup (list_to_cover l)) ->
  exists l', subcover (list_to_cover l') G /\ (f @ A) ⊂ (big_cup (list_to_cover l')).
Proof. induction l as [| A0].
       - intros.
         exists []; split; auto.  
         unfold subcover; easy. 
         unfold subset in *; intros. 
         destruct H1 as [c0 [H1 H2] ].
         apply H0 in H1.
         unfold list_to_cover, big_cup in H1.
         destruct H1; easy. 
       - intros.
         apply subcover_reduce in H.
         destruct H. 
         apply (IHl (A \ A0)) in H1.
         destruct H as [A'0 [H H2] ].
         destruct H1 as [l' [H1 H3] ].
         exists (A'0 :: l'); split. 
         unfold subcover, list_to_cover; intros. 
         destruct H4; subst; try easy.
         apply H1; easy.  
         unfold subset in *; intros. 
         rewrite <- big_cup_extend_l.
         destruct (Classical_Prop.classic (A'0 c)).
         left; easy. 
         right; apply H3.
         destruct H4 as [c' [H4 H6] ]. 
         exists c'; repeat split; auto. 
         unfold complement, not; intros. 
         apply H5; rewrite H2 in H7.
         unfold preimage in H7; subst; easy. 
         unfold subset in *; intros. 
         rewrite <- big_cup_extend_l in H0.
         destruct H2; apply H0 in H2.
         destruct H2; try easy.
Qed.

Lemma continuous_image_compact : forall (f : C -> C) (A : Csubset),
  continuous_on f C_ -> compact A ->
  compact (f @ A).
Proof. intros. 
       unfold compact; intros. 
       assert (H3 := (subset_preimage_pres _ _ _ H2)). (*****)
       apply H0 in H3.
       destruct H3 as [G' [H3 [H4 H5] ] ].
       destruct H3 as [l H3]; subst.
       destruct (extract_finite_image f l A G) as [l' [H6 H7] ]; try easy.
       exists (list_to_cover l'); repeat split; try easy.
       exists l'; easy. 
       apply open_cover_preimage_open; easy. 
Qed.

(**********************************************)
(* Showing that compact is closed and bounded *)
(**********************************************)

Definition ball_cover : Ccover :=
  fun G => open G /\ exists r, r > 0 /\ G ⊂ B(0,r).

Lemma open_cover_ball_cover : open_cover ball_cover.
Proof. unfold ball_cover; easy. Qed.
      
Lemma ball_cover_elems_bounded : forall (A : Csubset),
  ball_cover A -> bounded A.
Proof. intros. 
       unfold ball_cover, bounded in *.
       destruct H.
       destruct H0 as [r [H0 H1] ].
       exists r; easy.
Qed.

Lemma C_subset_ball_cover : 
  C_ ⊂ (big_cup ball_cover).
Proof. unfold subset, big_cup, ball_cover; intros. 
       exists (B(0, Cmod c + 1)).
       repeat split. 
       apply ball_open; apply Rle_lt_0_plus_1; apply Cmod_ge_0.
       exists ((Cmod c) + 1)%R. 
       split; auto with Csub_db.
       apply Rle_lt_0_plus_1; apply Cmod_ge_0.
       unfold ϵ_disk. 
       replace (c - 0) with c by lca. 
       lra. 
Qed.

Lemma list_cover_ball_cover_bounded : forall (l : list Csubset),
  subcover (list_to_cover l) ball_cover ->
  bounded (big_cup (list_to_cover l)).
Proof. induction l as [| A].
       - intros. 
         exists 1. 
         unfold subset; intros. 
         unfold big_cup, list_to_cover in H0.
         destruct H0; easy.
       - intros. 
         rewrite <- big_cup_extend_l.
         unfold subcover in H.
         apply bounded_cup.
         apply ball_cover_elems_bounded; apply H.
         left; easy. 
         apply IHl. 
         unfold subcover; intros. 
         apply H; right; easy. 
Qed.

Lemma fin_subcover_ball_cover_bounded : forall (G : Ccover),
  finite_cover G -> subcover G ball_cover -> 
  bounded (big_cup G).
Proof. intros. 
       destruct H as [l H]; subst.
       apply list_cover_ball_cover_bounded; easy. 
Qed.

Lemma compact_implies_bounded : forall (A : Csubset),
  compact A -> bounded A. 
Proof. intros. 
       unfold compact in H.
       destruct (H ball_cover).
       apply open_cover_ball_cover.
       eapply subset_transitive.
       eapply subset_C_.
       apply C_subset_ball_cover.
       destruct H0 as [H0 [H1 H2] ].
       apply fin_subcover_ball_cover_bounded in H0; auto.
       unfold bounded in *.
       destruct H0 as [ϵ H0].
       exists ϵ; eauto with Csub_db.
Qed.

Definition bad_point_cover (c : C) : Ccover :=
  fun G => open G /\ exists r, r > 0 /\ G ⊂ (fun c' => Cmod (c' - c) > r).

Lemma open_cover_bpc : forall c, open_cover (bad_point_cover c).
Proof. unfold bad_point_cover; easy. Qed.

Lemma bpc_covers_almost_all : forall (c : C) (A : Csubset),
  A* c -> A ⊂ (big_cup (bad_point_cover c)).
Proof. unfold subset; intros. 
       unfold bad_point_cover, big_cup.
       exists (fun c' => Cmod (c' - c) > Cmod (c0 - c) / 2).
       assert (H' :  Cmod (c0 - c) > 0).
       { apply Cmod_gt_0.
         apply Cminus_eq_contra.
         destruct (Ceq_dec c0 c); subst; easy. }
       repeat split; try lra.
       apply closed_ball_complement_open.
       exists ((Cmod (c0 - c)) / 2)%R.
       split; auto with Csub_db.
       apply Rdiv_lt_0_compat; try lra. 
Qed.

Lemma bpc_separates_from_c : forall (c : C) (l : list Csubset),
  subcover (list_to_cover l) (bad_point_cover c) ->
  exists r, r > 0 /\ (big_cup (list_to_cover l)) ⊂ (fun c' => Cmod (c' - c) > r).
Proof. induction l as [| A].
       - intros; exists 1; split; try lra. 
         unfold subset; intros. 
         unfold list_to_cover, big_cup in H0. 
         destruct H0; easy. 
       - intros. 
         apply subcover_reduce in H; repeat destruct H.
         destruct H1 as [r1 [H1 H2] ].
         apply IHl in H0.
         destruct H0 as [r2 [H0 H3] ].
         exists (Rmin r1 r2); split. 
         apply Rmin_glb_lt; auto. 
         unfold list_to_cover, big_cup, subset; intros. 
         destruct H4 as [A0 [ [H4 | H4] H5] ]; subst. 
         + apply H2 in H5.
           eapply Rgt_ge_trans; eauto.
           assert (H' := Rmin_l r1 r2). lra. 
         + assert (H' : (big_cup (list_to_cover l)) c0).
           { exists A0; split; easy. }
           apply H3 in H'.
           eapply Rgt_ge_trans; eauto.
           assert (H'' := Rmin_r r1 r2). lra. 
Qed.

Lemma compact_implies_closed : forall (A : Csubset),
  compact A -> closed A. 
Proof. unfold compact, closed, open; intros. 
       destruct (H (bad_point_cover c)) as [G' [H1 [H2 H3] ] ].
       apply open_cover_bpc.
       apply bpc_covers_almost_all; easy. 
       destruct H1 as [l H1]; subst.
       apply bpc_separates_from_c in H2.
       destruct H2 as [r [H2 H4] ].
       exists r; split; auto.
       unfold complement, ϵ_disk, subset, not; intros. 
       apply H3 in H5; apply H4 in H5; lra. 
Qed.


(****)
(****)
(****)






Lemma poly_min : forall (p : Polynomial), 
  exists m, (forall c, Cmod p[[m]] <= Cmod p[[c]]).
Proof. Admitted.


(******************)
(* Must prove FTA *)
(******************)
 

Theorem Fundamental_Theorem_Algebra : forall (p : Polynomial),
  (Polynomial.degree p > 0)%nat -> (exists c : Complex.C, p[[c]] = C0).
Proof. Admitted. 
