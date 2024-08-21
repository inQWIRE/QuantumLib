Require Export Polynomial.
Require Import Setoid.

(************************************)
(* First, we define a topology on C *)
(************************************)

Declare Scope topology_scope.
Delimit Scope topology_scope with T.
Open Scope topology_scope.

 

(* we define a subset of C as a function from C to {True, False} *)  
(* so c is in A if A(c) = True *)
Definition Cset := C -> Prop.

Definition union (A B : Cset) : Cset :=
  fun c => A c \/ B c.

Definition intersection (A B : Cset) : Cset :=
  fun c => A c /\ B c.

Definition complement (A : Cset) : Cset :=
  fun c => not (A c).

Definition setminus (A B : Cset) : Cset :=
  intersection A (complement B).

Definition is_in (a : C) (A : Cset) : Prop := A a.

Definition subset (A B : Cset) : Prop :=
  forall c, A c -> B c.

Definition eq_set (A B : Cset) : Prop :=
  forall c, A c <-> B c.

Definition ϵ_disk (a : C) (ϵ : R) : Cset :=
  fun c => Cmod (c - a) < ϵ.

Definition open_square (cen : C) (s : R) : Cset :=
  fun c => Rabs (fst c - fst cen) < s /\ Rabs (snd c - snd cen) < s. 

Definition open_rect (cen : C) (s1 s2 : R) : Cset := 
  fun c => Rabs (fst c - fst cen) < s1 /\ Rabs (snd c - snd cen) < s2. 

Definition bounded (A : Cset) : Prop :=
  exists ϵ, subset A (ϵ_disk C0 ϵ). 

Definition image (f : C -> C) (A : Cset) : Cset := 
  fun c => (exists c', A c' /\ f c' = c).

Definition preimage (f : C -> C) (B : Cset) : Cset :=
  fun c => B (f c).

Definition continuous_on (f : C -> C) (A : Cset) : Prop :=
  forall c, A c -> continuous_at f c.

Infix "∪" := union (at level 50, left associativity) : topology_scope.
Infix "∩" := intersection (at level 40, left associativity) : topology_scope.
Infix "⊂" := subset (at level 0) : topology_scope.
Infix "⩦" := eq_set (at level 0) : topology_scope.
Infix "\" := setminus (at level 0) : topology_scope.
Infix "@" := image (at level 0) : topology_scope.
Notation "f *{ A }" := (preimage f A) (at level 0) : topology_scope.
Notation "A `" := (complement A) (at level 0) : topology_scope.
Infix "∈" := is_in (at level 0) : topology_scope.
Notation "B( a , ϵ )" := (ϵ_disk a ϵ) (at level 30, no associativity) : topology_scope.


Definition open (A : Cset) : Prop :=
  forall c, A c -> exists ϵ, ϵ > 0 /\ B(c,ϵ) ⊂ A.

Definition closed (A : Cset) : Prop :=
  open (A`).

Definition empty_set : Cset :=
  fun _ => False. 

Definition C_ : Cset :=
  fun _ => True. 


(** showing that all the above def's are preserved by eq_set *)

Lemma eq_set_refl : forall (A : Cset), A ⩦ A.
Proof. easy. Qed.

Lemma eq_set_symm : forall (A B : Cset), A ⩦ B -> B ⩦ A. 
Proof. easy. Qed. 

Lemma eq_set_trans : forall (A B C : Cset), 
  A ⩦ B -> B ⩦ C -> A ⩦ C.
Proof. intros. 
       unfold eq_set in *; intros. 
       split; intros. 
       apply H0; apply H; easy.
       apply H; apply H0; easy.
Qed.

Add Parametric Relation : Cset eq_set
  reflexivity proved by eq_set_refl
  symmetry proved by eq_set_symm
  transitivity proved by eq_set_trans
  as eq_set_equiv_rel.


Add Parametric Morphism : subset
  with signature eq_set ==> eq_set ==> iff as subset_mor.
Proof. unfold subset, eq_set; split; intros;
       apply H0; apply H1; apply H; easy. 
Qed.

Add Parametric Morphism : union
  with signature eq_set ==> eq_set ==> eq_set as union_mor.
Proof. unfold union, eq_set; split; intros; destruct H1; 
         try (left; apply H; easy); right; apply H0; easy.
Qed.

Add Parametric Morphism : intersection
  with signature eq_set ==> eq_set ==> eq_set as intersection_mor.
Proof. unfold intersection, eq_set; split; intros; split; 
       try (apply H; apply H1); apply H0; apply H1.
Qed.

Add Parametric Morphism : bounded
  with signature eq_set ==> iff as bounded_mor.
Proof. unfold bounded; split; intros;
         destruct H0; exists x0. 
       rewrite <- H; easy. 
       rewrite H; easy. 
Qed.

Add Parametric Morphism : open
  with signature eq_set ==> iff as open_mor.
Proof. unfold open; split; intros;
       apply H in H1; apply H0 in H1; destruct H1 as [e [H2 H3] ];
       exists e; split; auto.
       rewrite <- H; easy. 
       rewrite H; easy. 
Qed.

(* one quick helper *)
Lemma Cmod_lt_helper : forall (c : C) (ϵ : R),
  Cmod c < ϵ -> Rabs (fst c) < ϵ /\ Rabs (snd c) < ϵ.
Proof. intros. 
       assert (H' := Rmax_Cmod c).
       split. 
       - eapply Rle_lt_trans. 
         eapply Rle_trans.
         apply Rmax_l.
         apply H'. 
         easy. 
       - eapply Rle_lt_trans. 
         eapply Rle_trans.
         apply Rmax_r.
         apply H'. 
         easy. 
Qed.

(** Subset lemmas *)

Lemma subset_cup_l : forall (A B : Cset),
  A ⊂ (A ∪ B).
Proof. unfold subset, union; left; easy. Qed.

Lemma subset_cup_r : forall (A B : Cset),
  B ⊂ (A ∪ B).
Proof. unfold subset, union; right; easy. Qed.

Lemma subset_cap_l : forall (A B : Cset),
  (A ∩ B) ⊂ A.
Proof. unfold subset, intersection; easy. Qed.

Lemma subset_cap_r : forall (A B : Cset),
  (A ∩ B) ⊂ B.
Proof. unfold subset, intersection; easy. Qed.

Lemma subset_self : forall (A : Cset),
  A ⊂ A.
Proof. easy. Qed. 

Lemma subset_transitive : forall (A B C : Cset),
  A ⊂ B -> B ⊂ C -> A ⊂ C.
Proof. unfold subset; intros. 
       apply H0; apply H; easy. 
Qed.

#[global] Hint Resolve subset_cup_l subset_cup_r subset_cap_l subset_cap_r subset_self subset_transitive : Csub_db.

Lemma subset_cup_reduce : forall (A B C : Cset),
  A ⊂ B \/ A ⊂ C -> A ⊂ (B ∪ C). 
Proof. unfold subset, union; intros. 
       destruct H.
       - left; apply H; easy. 
       - right; apply H; easy. 
Qed.

Lemma subset_cap_reduce : forall (A B C : Cset),
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

Lemma subset_C_ : forall (A : Cset),
  A ⊂ C_.
Proof. unfold subset; easy. Qed.

#[global] Hint Resolve subset_cup_reduce subset_cap_reduce subset_ball_l subset_ball_r subset_C_ : Csub_db.

Lemma subset_equal : forall (A B : Cset),
  A ⊂ B -> B ⊂ A -> A ⩦ B.
Proof. unfold subset, eq_set; intros. 
       split; try apply H; apply H0. 
Qed.

Lemma subset_not : forall (A B : Cset), 
  ~ (A ⊂ B) -> (exists a, A a /\ B` a).
Proof. intros. 
       destruct (Classical_Prop.classic (exists a : C, A a /\ (B) ` a)); auto. 
       assert (H1 : forall a, ~ (A a /\ (B) ` a)).
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


(* some image and preimage relationships with subsets *)

Lemma subset_image : forall (A B : Cset) (f : C -> C),
  A ⊂ B -> (f @ A) ⊂ (f @ B).
Proof. unfold subset; intros. 
       destruct H0 as [x [H0 H1] ].
       apply H in H0.
       exists x; easy. 
Qed.

(* showing subset relationships between squares, circles, and rectangles *) 
Lemma circle_in_square : forall (cen : C) (s : R),
  (ϵ_disk cen s) ⊂ (open_square cen s).
Proof. unfold subset, ϵ_disk, open_square; intros. 
       apply Cmod_lt_helper in H.
       easy. 
Qed.

Lemma square_in_circle : forall (cen : C) (ϵ : R),
  (open_square cen (ϵ / √ 2)) ⊂ (ϵ_disk cen ϵ).
Proof. unfold subset, ϵ_disk, open_square; intros. 
       destruct H.
       destruct (Rle_lt_dec ϵ 0).
       - assert (H' : ϵ / √ 2 <= 0). 
         { unfold Rdiv.
           rewrite <- (Rmult_0_r ϵ).
           apply Rmult_le_compat_neg_l; auto; left. 
           apply Rinv_0_lt_compat; apply Rlt_sqrt2_0. }
         assert (H1 := Rabs_pos ((fst c - fst cen))).
         lra.
       - assert (H' : 0 < ϵ / √ 2).
         unfold Rdiv; apply Rmult_lt_0_compat; auto.
         apply Rinv_0_lt_compat; apply Rlt_sqrt2_0.
         assert (H1 : (ϵ / √ 2 = Rabs (ϵ / √ 2))%R).
         { unfold Rabs.
           destruct (Rcase_abs (ϵ / √ 2)); lra. }
         rewrite H1 in *.
         apply Rsqr_lt_abs_1 in H; apply Rsqr_lt_abs_1 in H0.
         assert (H2 : ((ϵ / √ 2)² = ϵ² / 2)%R).
         { unfold Rsqr, Rdiv. 
           R_field_simplify; try easy.
           apply sqrt2_neq_0. }
         rewrite H2 in *.
         unfold Cmod.
         rewrite <- sqrt_Rsqr; try lra. 
         apply sqrt_lt_1_alt. split. 
         apply Rplus_le_le_0_compat; apply pow2_ge_0.
         rewrite double_var.
         apply Rplus_lt_compat;
         unfold Rsqr in *; simpl; lra. 
Qed.

Lemma square_is_rectangle : forall (cen : C) (s : R),
  (open_square cen s) ⩦ (open_rect cen s s).
Proof. intros; easy. Qed.

Lemma square_in_rect_at_point : forall (cen c : C) (s1 s2 : R),
  s1 > 0 -> s2 > 0 ->
  (open_rect cen s1 s2) c ->
  exists s, s > 0 /\ (open_square c s) ⊂ (open_rect cen s1 s2).
Proof. intros. 
       exists (Rmin (s1 - (Rabs (fst c - fst cen))) (s2 - (Rabs (snd c - snd cen)))).
       destruct H1 as [H1 H2].
       repeat split.
       apply Rmin_pos; try lra. 
       all : destruct H3.
       - eapply Rlt_le_trans in H3; try apply Rmin_l.
         replace (fst c0 - fst cen)%R with ((fst c0 - fst c) + (fst c - fst cen))%R by lra.
         eapply Rle_lt_trans; try apply Rabs_triang; lra.
       - eapply Rlt_le_trans in H4; try apply Rmin_r.
         replace (snd c0 - snd cen)%R with ((snd c0 - snd c) + (snd c - snd cen))%R by lra.
         eapply Rle_lt_trans; try apply Rabs_triang; lra.
Qed.

Lemma square_contains_center : forall (cen : C) (s : R),
  s > 0 -> open_square cen s cen.
Proof. intros. 
       unfold open_square.
       do 2 rewrite Rminus_eq_0, Rabs_R0; easy.
Qed.

(** some lemmas about open/closed sets *)

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
       assert (H' : (fun c' : C => Cmod (c' - a) <= ϵ) ` ⩦ (fun c' : C => Cmod (c' - a) > ϵ)).
       { apply subset_equal; unfold subset, complement; intros; lra. } 
       rewrite H'.
       apply closed_ball_complement_open.
Qed.

Lemma rect_open : forall (cen : C) (s1 s2 : R),
  s1 > 0 -> s2 > 0 -> open (open_rect cen s1 s2).
Proof. unfold open; intros. 
       apply square_in_rect_at_point in H1; auto.
       destruct H1 as [s [H1 H2] ].
       exists s; split; auto.
       eapply subset_transitive; try apply H2.
       apply circle_in_square.
Qed.

Lemma cup_open : forall (A B : Cset),
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

Lemma cap_open : forall (A B : Cset),
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

Lemma complement_involutive : forall (A : Cset),
  (A`)` ⩦ A.
Proof. unfold complement; intros. 
       apply subset_equal.
       - unfold subset; intros. 
         apply Classical_Prop.NNPP; easy. 
       - unfold subset; intros. 
         unfold not. intros.
         easy. 
Qed.

Lemma bounded_cup : forall (A B : Cset),
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

Definition Ccover := Cset -> Prop.

Definition WF_cover (G : Ccover) : Prop :=
  forall A A', (A ⩦ A' /\ G A) -> G A'.

Definition WFify_cover (G : Ccover) : Ccover :=
  fun A => exists A', A ⩦ A' /\ G A'.

Definition open_cover (G : Ccover) : Prop :=
  forall A, G A -> open A.

Definition subcover (G1 G2 : Ccover) : Prop :=
  forall A, G1 A -> G2 A.

Definition eq_cover (G1 G2 : Ccover) : Prop :=
  forall A, G1 A <-> G2 A.

(* used in list_to_cover *)
Fixpoint In' (A : Cset) (l : list Cset) : Prop :=
  match l with
  | [] => False
  | (A' :: l) => A ⩦ A' \/ In' A l
  end.

Definition list_to_cover (l : list Cset) : Ccover :=
  fun A => In' A l.

Definition finite_cover (G : Ccover) : Prop :=
  exists l, eq_cover G (list_to_cover l).

Definition big_cup (G : Ccover) : Cset :=
  fun c => (exists A, G A /\ A c).

Definition big_cap (G : Ccover) : Cset :=
  fun c => (forall A, G A -> A c).

(* the star of the show! *)
Definition compact (A : Cset) : Prop :=
  forall G, open_cover G -> WF_cover G -> A ⊂ (big_cup G) -> 
       (exists G', finite_cover G' /\ subcover G' G /\ A ⊂ (big_cup G')).

(* showing some basic wf lemmas *)

Lemma WF_WFify : forall (G : Ccover),
  WF_cover (WFify_cover G).
Proof. intros. unfold WF_cover, WFify_cover. intros. 
       destruct H as [H [A0 [H0 H1 ] ] ].
       exists A0; split; try easy. 
       symmetry in H.
       eapply eq_set_trans;
       try apply H; easy.
Qed.

Lemma WF_finitecover : forall (l : list Cset),
  WF_cover (list_to_cover l).
Proof. induction l as [| A]. 
       - unfold WF_cover, list_to_cover; intros. 
         destruct H.
         easy. 
       - unfold WF_cover, list_to_cover in *; intros. 
         destruct H; destruct H0.
         left; rewrite <- H, <- H0; easy. 
         right; apply (IHl A0); easy. 
Qed.

Lemma WFify_is_projection : forall (G : Ccover),
  WF_cover G -> 
  eq_cover G (WFify_cover G).
Proof. unfold eq_cover; intros; split; intros.  
       exists A; easy. 
       destruct H0 as [A0 [H0 H1] ].
       apply (H A0 A); easy. 
Qed.


(* showing that all the def's are preserved by eq_cover *)

Lemma eq_cover_refl : forall (G : Ccover), eq_cover G G.
Proof. easy. Qed.

Lemma eq_cover_symm : forall (G1 G2 : Ccover), eq_cover G1 G2 -> eq_cover G2 G1.  
Proof. easy. Qed. 

Lemma eq_cover_trans : forall (G1 G2 G3 : Ccover), 
  eq_cover G1 G2 -> eq_cover G2 G3 -> eq_cover G1 G3.
Proof. intros. 
       unfold eq_cover in *; intros. 
       split; intros. 
       apply H0; apply H; easy.
       apply H; apply H0; easy.
Qed.

Add Parametric Relation : Ccover eq_cover
  reflexivity proved by eq_cover_refl
  symmetry proved by eq_cover_symm
  transitivity proved by eq_cover_trans
  as eq_cover_equiv_rel.

Add Parametric Morphism : subcover
  with signature eq_cover ==> eq_cover ==> iff as subcover_mor.
Proof. intros. unfold subcover, eq_cover; split; intros;
       apply H0; apply H1; apply H; easy. 
Qed.

Add Parametric Morphism : open_cover
  with signature eq_cover ==> iff as opencover_mor.
Proof. unfold eq_cover, open_cover; split; intros;
         apply H0; apply H; easy. 
Qed.

Add Parametric Morphism : big_cup
  with signature eq_cover ==> eq_set as bigcup_mor.
Proof. unfold eq_cover, big_cup; split; intros; 
         destruct H0 as [A [H0 H1] ]; exists A; split; auto; apply H; auto. 
Qed.

Add Parametric Morphism : big_cap
  with signature eq_cover ==> eq_set as bigcap_mor.
Proof. unfold eq_cover, big_cap; split; intros;
         apply H0; apply H; apply H1.
Qed.

(* must also show that compactness is preserved by eq_set *)

Add Parametric Morphism : compact
  with signature eq_set ==> iff as compact_mor.
Proof. intros. unfold compact; split; intros. 
       - rewrite <- H in *.
         apply H0 in H3; try easy. 
         destruct H3 as [G' [H3 [H4 H5] ] ].
         rewrite H in H5.
         exists G'; easy. 
       - rewrite H in *.
         apply H0 in H3; try easy. 
         destruct H3 as [G' [H3 [H4 H5] ] ].
         rewrite <- H in H5.
         exists G'; easy. 
Qed.

(** now some lemmas *)

Lemma list_to_cover_reduce : forall (A A0 : Cset) (l : list Cset),
  list_to_cover (A :: l) A0 <->
  A ⩦ A0 \/ list_to_cover l A0.
Proof. intros; split; intros; 
         destruct H; try (left; easy); right; easy. 
Qed.

Lemma open_cover_reduce : forall (l : list Cset) (A : Cset),
  open_cover (list_to_cover (A :: l)) ->
  open A /\ open_cover (list_to_cover l).
Proof.  intros; split; unfold open_cover in H.
        apply H. 
        apply list_to_cover_reduce; left; easy. 
        unfold open_cover; intros. 
        apply H. 
        apply list_to_cover_reduce; right; easy. 
Qed.

Lemma subcover_reduce : forall (l : list Cset) (A : Cset) (G : Ccover),
  subcover (list_to_cover (A :: l)) G ->
  G A /\ subcover (list_to_cover l) G.
Proof. intros; split.       
       apply H. 
       apply list_to_cover_reduce; left; easy. 
       unfold subcover; intros. 
       apply H. 
       apply list_to_cover_reduce; right; easy. 
Qed.

Lemma finite_cover_subset : forall (l : list Cset) (G : Ccover),
  WF_cover G -> subcover G (list_to_cover l) ->
  finite_cover G.
Proof. induction l as [| A].
       - intros.  
         exists []; split; intros; auto; easy. 
       - intros. 
         destruct (IHl (fun A' => G A' /\ ~ (eq_set A' A))).
         + unfold WF_cover in *; intros; split; 
           destruct H1 as [H1 [H2 H3] ].
           apply (H A0 A'); easy. 
           unfold not; intros; apply H3.
           rewrite H1; easy. 
         + unfold subcover in *; intros. 
           destruct H1.
           apply H0 in H1.
           apply list_to_cover_reduce in H1.
           destruct H1; try easy. 
           unfold not in H2.
           symmetry in H1.
           apply H2 in H1; easy.
         + destruct (Classical_Prop.classic (G A)).
           * exists (A :: x).
             unfold eq_cover; split; intros; simpl. 
             destruct (Classical_Prop.classic (A ⩦ A0)); try (left; easy). 
             right; apply H1; split; auto.
             unfold not; intros; apply H4; easy. 
             apply list_to_cover_reduce in H3.
             destruct H3.
             apply (H A A0); easy.
             apply H1 in H3; easy. 
           * exists x. 
             unfold eq_cover; intros; split; intros. 
             apply H1; split; auto.
             unfold not; intros; apply H2.
             apply (H A0 A); easy. 
             apply H1 in H3; easy. 
Qed.
         
Lemma big_cup_extend_l : forall (l : list Cset) (A : Cset),
  (A ∪ (big_cup (list_to_cover l))) ⩦ (big_cup (list_to_cover (A :: l))).
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
         left; apply H; easy. 
         right; exists A0; split; easy. 
Qed.

Lemma big_cap_extend_l : forall (l : list Cset) (A : Cset),
  (A ∩ (big_cap (list_to_cover l))) ⩦ (big_cap (list_to_cover (A :: l))).
Proof. intros.
       unfold intersection, big_cap, list_to_cover; intros.        
       apply subset_equal.
       - unfold subset; intros. 
         destruct H; destruct H0; subst; try easy.
         apply H0; easy.  
         apply H1; apply H0.
       - unfold subset; intros. 
         split.
         apply H; left; easy. 
         intros; apply H; right; apply H0.
Qed.

Lemma app_union : forall (l1 l2 : list Cset),
  (big_cup (list_to_cover (l1 ++ l2))) ⩦ 
  ((big_cup (list_to_cover l1)) ∪ (big_cup (list_to_cover l2))).
Proof. induction l1 as [| A].
       - intros; simpl. 
         apply subset_equal; auto with Csub_db.
         unfold subset; intros. 
         destruct H; try easy. 
         destruct H; easy. 
       - intros. 
         rewrite <- app_comm_cons.
         rewrite <- big_cup_extend_l.
         rewrite IHl1.
         rewrite <- big_cup_extend_l.
         split; intros. 
         + destruct H. 
           left; left; easy.
           destruct H. left; right; easy.
           right; easy. 
         + destruct H. destruct H. 
           left; easy. 
           right; left; easy. 
           right; right; easy. 
Qed.

Lemma In'_app_or : forall (l1 l2 : list Cset) (A : Cset),
  In' A (l1 ++ l2) -> In' A l1 \/ In' A l2.
Proof. induction l1 as [| A0].
       - intros; right; easy.
       - intros. 
         rewrite <- app_comm_cons in H.
         destruct H.
         left; left; easy.
         apply IHl1 in H.
         destruct H.
         left; right; easy. 
         right; easy.
Qed.

Lemma In'_map : forall {X} (l : list X) (f : X -> Cset) (A : Cset),  
  In' A (map f l) -> exists (x : X), (f x) ⩦ A /\ In x l.
Proof. induction l; firstorder (subst; auto).
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

Lemma ltc_open : forall (l : list Cset),
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
       rewrite H0.
       apply ltc_open.
       rewrite <- H0; easy. 
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
  fun A => (exists A', G A' /\ A ⩦ (f*{A'})).

Lemma open_cover_preimage_open : forall (f : C -> C) (G : Ccover),
  open_cover G -> continuous_on f C_ ->
  open_cover (preimage_cover f G).
Proof. intros. 
       unfold open_cover, preimage_cover; intros. 
       destruct H1 as [A' [H1 H2] ]; subst.
       apply H in H1.
       rewrite H2.
       apply (continuous_preimage_open _ H0); easy.
Qed.

Lemma WF_preimage_cover : forall (f : C -> C) (G : Ccover),
  WF_cover (preimage_cover f G).
Proof. unfold WF_cover, preimage_cover; intros. 
       destruct H as [H [A0 [H0 H1] ] ].
       exists A0; split; auto. 
       rewrite <- H; easy. 
Qed.

Lemma subset_preimage_pres : forall (f : C -> C) (A : Cset) (G : Ccover),
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

Lemma extract_finite_image : forall (f : C -> C) (l : list Cset) (A : Cset) (G : Ccover),
  WF_cover G -> 
  subcover (list_to_cover l) (preimage_cover f G) -> 
  A ⊂ (big_cup (list_to_cover l)) ->
  exists l', subcover (list_to_cover l') G /\ (f @ A) ⊂ (big_cup (list_to_cover l')).
Proof. induction l as [| A0].
       - intros.
         exists []; split; auto.  
         unfold subcover; easy. 
         unfold subset in *; intros. 
         destruct H2 as [c0 [H2 H3] ].
         apply H1 in H2.
         unfold list_to_cover, big_cup in H2.
         destruct H2; easy. 
       - intros.
         apply subcover_reduce in H0.
         destruct H0. 
         apply (IHl (A \ A0)) in H2; auto.
         destruct H0 as [A'0 [H0 H3] ].
         destruct H2 as [l' [H2 H4] ].
         exists (A'0 :: l'); split. 
         unfold subcover, list_to_cover; intros. 
         destruct H5; try (apply (H A'0 A1); easy).         
         apply H2; easy.  
         unfold subset in *; intros. 
         apply big_cup_extend_l.
         destruct (Classical_Prop.classic (A'0 c)).
         left; easy. 
         right; apply H4.
         destruct H5 as [c' [H5 H7] ]. 
         exists c'; repeat split; auto. 
         unfold complement, not; intros. 
         apply H6; apply H3 in H8.
         unfold preimage in H8; subst; easy. 
         unfold subset in *; intros. 
         destruct H3; apply H1 in H3.
         apply big_cup_extend_l in H3.
         destruct H3; easy.
Qed. 

Lemma continuous_image_compact : forall (f : C -> C) (A : Cset),
  continuous_on f C_ -> compact A ->
  compact (f @ A).
Proof. intros. 
       unfold compact; intros. 
       assert (H4 := (subset_preimage_pres _ _ _ H3)). 
       apply H0 in H4.
       destruct H4 as [G' [H4 [H5 H6] ] ].
       destruct H4 as [l H4]; subst.
       destruct (extract_finite_image f l A G) as [l' [H7 H8] ]; auto.
       all : try (rewrite <- H4; easy).
       exists (list_to_cover l'); repeat split; try easy.
       exists l'; easy. 
       apply open_cover_preimage_open; easy. 
       apply WF_preimage_cover.
Qed.


(*************************************************************************)
(* We now introduce cube_compact and show that is is the same as compact *)
(*************************************************************************)

Definition cube_cover (G : Ccover) : Prop := 
  forall A, G A -> exists s cen, s > 0 /\ A ⩦ (open_square cen s). 

Definition cube_compact (A : Cset) : Prop :=
  forall G, cube_cover G -> WF_cover G -> A ⊂ (big_cup G) -> 
       (exists G', finite_cover G' /\ subcover G' G /\ A ⊂ (big_cup G')).

(* we use this to turn covers to cube_covers *)
Definition cover_to_cube_cover (G : Ccover) : Ccover :=
  fun A => (exists s cen A', s > 0 /\ (A ⩦ (open_square cen s)) /\ G A' /\ (open_square cen s) ⊂ A').

Lemma cube_cover_open_cover : forall (G : Ccover),
  cube_cover G -> open_cover G.
Proof. unfold open_cover, cube_cover; intros.
       apply H in H0.
       destruct H0 as [s [cen [H0 H1] ] ].
       rewrite H1, square_is_rectangle.
       apply rect_open; easy.
Qed.

Lemma WF_ctcc : forall (G : Ccover),
  WF_cover (cover_to_cube_cover G).
Proof. unfold WF_cover; intros. 
       destruct H.
       destruct H0 as [s [cen [A0 [H0 [H1 [H2 H3] ] ] ] ] ].
       exists s, cen, A0; split; auto.
       split; try easy.
       rewrite <- H1; easy.
Qed.

Lemma cube_cover_ctcc : forall (G : Ccover),
  cube_cover (cover_to_cube_cover G).
Proof. unfold cube_cover; intros. 
       destruct H as [s [cen [A0 [H0 [H1 [H2 H3] ] ] ] ] ].
       exists s, cen.
       split; easy.
Qed.

Lemma ctcc_in_cover : forall (G : Ccover),
  open_cover G -> (big_cup G) ⩦ (big_cup (cover_to_cube_cover G)).
Proof. intros; split; intros. 
       - destruct H0 as [A [H0 H1] ].
         assert (H0' := H0).
         apply H in H0.
         assert (H2 := H1); apply H0 in H1.
         destruct H1 as [ϵ [H1 H3] ].
         exists (open_square c (ϵ / √ 2)). 
         split. 
         unfold cover_to_cube_cover.
         exists (ϵ / √ 2)%R, c, A; split.
         apply lt_ep_helper in H1; easy. 
         split; try easy.
         split; try easy.
         eapply subset_transitive; try apply H3.
         apply square_in_circle.
         apply square_contains_center.
         apply (lt_ep_helper ϵ); easy.
       - destruct H0 as [A [H0 H1] ].
         destruct H0 as [s [cen [A0 [H0 [H2 [H3 H4] ] ] ] ] ].
         exists A0; split; auto.
         apply H4; apply H2; easy.
Qed.

Lemma fin_cubecover_gives_fin_cover : forall (l : list Cset) (G : Ccover),
  WF_cover G ->
  subcover (list_to_cover l) (cover_to_cube_cover G) -> 
  exists l', subcover (list_to_cover l') G /\ 
          (big_cup (list_to_cover l)) ⊂ (big_cup (list_to_cover l')).
Proof. induction l as [| A].
       - intros. exists []; split; try easy.
       - intros.
         apply subcover_reduce in H0; destruct H0.
         apply IHl in H1; auto.
         destruct H1 as [l' [H1 H2] ].
         destruct H0 as [s [cen [A0 [H0 [H3 [H4 H5] ] ] ] ] ].
         exists (A0 :: l').
         split. 
         unfold subcover, list_to_cover; intros. 
         destruct H6.
         apply (H A0 A1); easy.
         apply H1; easy.
         do 2 rewrite <- big_cup_extend_l.
         unfold subset; intros. 
         destruct H6. 
         left; apply H5; apply H3; easy.
         right; apply H2; easy.
Qed.

Lemma compact_is_cube_compact : forall (A : Cset),
  compact A <-> cube_compact A.
Proof. split; intros. 
       - unfold cube_compact; intros. 
         apply cube_cover_open_cover in H0.
         apply H in H2; easy.
       - unfold compact, cube_compact in *; intros. 
         destruct (H (cover_to_cube_cover G)) as [G' [H3 [H4 H5] ] ].
         apply cube_cover_ctcc.
         apply WF_ctcc.
         rewrite <- ctcc_in_cover; easy.
         destruct H3 as [l H3].
         destruct (fin_cubecover_gives_fin_cover l G) as [l' [H6 H7] ]; auto.
         rewrite <- H3; easy.
         exists (list_to_cover l'); repeat split; try easy.
         exists l'; easy.
         eapply subset_transitive; try apply H7.
         rewrite <- H3; easy.
Qed.

(*******************************************)
(* Showing that the closed ball is compact *)
(*******************************************)

(* we first consider the line [0,1] ∈ C *)
Definition unit_line : Cset :=
  fun c => 0 <= fst c <= 1 /\ snd c = 0.

Definition partial_line (x : R) : Cset :=
  fun c => 0 <= fst c <= x /\ snd c = 0.

Definition partial_line_covered (G : Ccover) (x : R) : Prop :=
  exists G', finite_cover G' /\ subcover G' G /\ (partial_line x) ⊂ (big_cup G').

Lemma zero_always_covered : forall (G : Ccover),
  WF_cover G -> unit_line ⊂ (big_cup G) -> 
  partial_line_covered G 0.
Proof. intros. 
       assert (H' : (big_cup G) C0).
       { apply H0. 
         repeat split; simpl; lra. } 
       destruct H'.
       exists (list_to_cover [x]). 
       repeat split. 
       exists [x]; easy. 
       unfold subcover, list_to_cover; intros. 
       destruct H1; destruct H2; try easy. 
       apply (H x A); easy.
       unfold subset, partial_line; intros. 
       destruct H2 as [ [H2 H3] H4].
       apply Rle_antisym in H2; auto. 
       replace 0 with (fst C0) in H2 by easy. 
       apply c_proj_eq in H2; try easy; subst.  
       exists x; split; try easy. 
       left; easy. 
Qed.

Lemma plc_le_subset : forall (x x' : R),
  x' <= x -> 
  (partial_line x') ⊂ (partial_line x).
Proof. unfold partial_line, subset; intros. 
       repeat split; try easy. 
       destruct H0 as [ [H0 H1] H2].
       lra. 
Qed.       

(* showing that if x is covered than so are all points less than x *)
Lemma plc_less : forall (x x' : R) (G : Ccover),
  x' <= x ->
  partial_line_covered G x ->
  partial_line_covered G x'.
Proof. intros. 
       unfold partial_line_covered in *.
       destruct H0 as [G' [H0 [H1 H2] ] ].
       exists G'; repeat split; auto. 
       eapply subset_transitive.
       apply plc_le_subset; eauto.
       easy. 
Qed.

Lemma not_ub_implies_larger_elem : forall (E : R -> Prop) (a b : R),
  E a -> ~ (is_upper_bound E b) ->
  exists a', E a' /\ b < a'.
Proof. intros. 
       destruct (Classical_Prop.classic (exists a' : R, E a' /\ b < a')); auto. 
       assert (H' : is_upper_bound E b). 
       { unfold is_upper_bound; intros. 
         destruct (Classical_Prop.classic (x <= b)); auto. 
         apply Rnot_le_lt in H3.
         assert (H'' : False).
         apply H1. 
         exists x; easy. 
         easy. }
       easy. 
Qed.

Lemma extract_elem_lt_lub : forall (E : R -> Prop) (a lub ϵ : R),
  E a -> ϵ > 0 -> is_lub E lub ->
  exists x, (E x /\ lub - ϵ < x). 
Proof. intros. 
       apply (not_ub_implies_larger_elem _ a); auto. 
       unfold not; intros. 
       destruct H1.
       apply H3 in H2.
       lra. 
Qed.


Theorem unit_line_compact : compact unit_line. 
Proof. unfold compact, unit_line; intros. 
       destruct (Classical_Prop.classic (partial_line_covered G 1)).
       - destruct H2 as [G' [H2 [H3 H4] ] ].
         exists G'; repeat split; easy. 
       - destruct (Classical_Prop.classic (is_upper_bound (partial_line_covered G) 1)).
         + destruct (completeness (partial_line_covered G)).
           exists 1; easy. 
           exists 0. 
           apply zero_always_covered; easy. 
           destruct i.
           assert (H6 : x <= 1). 
           { apply H5; easy. }
           assert (H7 : 0 <= x). 
           { apply H4; apply zero_always_covered; easy. } 
           assert (H' : big_cup G (x, 0)).
           apply H1; repeat split; easy. 
           destruct H' as [A [H8 H9] ].  
           assert (H8' := H8).
           apply H in H8; apply H8 in H9.
           destruct H9 as [ϵ [H9 H10] ].
           assert (H11 : ϵ / 2 > 0).
           { unfold Rdiv. apply Rmult_gt_0_compat; lra. } 
           assert (H12 : partial_line_covered G (x - ϵ / 2)). 
           { apply (extract_elem_lt_lub (partial_line_covered G) 0 x (ϵ / 2)) in H11; try easy.
             destruct H11 as [x0 [H11 H12] ].
             apply (plc_less x0); auto; lra.  
             apply zero_always_covered; easy. }
           assert (H13 : partial_line_covered G (x + ϵ / 2)).
           { destruct H12 as [G' [H13 [H14 H15] ] ].
             destruct H13 as [l H13].
             exists (list_to_cover (A :: l)); repeat split. 
             exists (A :: l); easy.  
             unfold subcover, list_to_cover; intros. 
             destruct H12.
             apply (H0 A A0); easy.
             apply H14; apply H13; easy. 
             unfold subset, partial_line; intros. 
             destruct H12 as [ [H12 H16] H17 ].
             destruct (Rle_dec (fst c) (x - ϵ / 2)).
             apply big_cup_extend_l. right. 
             rewrite H13 in H15.
             apply H15; repeat split; auto. 
             apply Rnot_le_gt in n.
             exists A; split. 
             left; easy. 
             apply H10.
             unfold ϵ_disk. 
             apply (Rplus_le_compat_r (-x)) in H16.
             apply (Rplus_lt_compat_r (-x)) in n.
             replace (x + ϵ / 2 + - x)%R with (ϵ / 2)%R in H16 by lra. 
             replace (x - ϵ / 2 + - x)%R with (- ϵ / 2)%R in n by lra. 
             unfold Cmod; simpl; rewrite H17. 
             rewrite Rmult_1_r, Ropp_0, Rplus_0_r, Rmult_0_l, Rplus_0_r. 
             replace (Rmult (fst c + - x) (fst c + - x))%R with ((fst c + - x)²)%R by easy. 
             rewrite sqrt_Rsqr_abs; apply Rabs_def1; lra. }
           apply H4 in H13. lra. 
         + apply (not_ub_implies_larger_elem _ 0) in H3.
           destruct H3 as [a' [H3 H4] ].
           apply (plc_less a' 1 G) in H3; try lra; easy. 
           apply zero_always_covered; easy. 
Qed.

Definition horiz_Cline (a b h : R) : Cset :=
   fun c => a <= fst c <= b /\ snd c = h.
       
Definition horiz_from_01_poly (a b h : R) : Polynomial := [(a, h) ; ((b - a)%R, 0)].

Lemma horiz_Cline_image : forall (a b h : R), 
  a <= b -> ((Peval (horiz_from_01_poly a b h)) @ unit_line) ⩦ (horiz_Cline a b h).
Proof. intros; split; intros. 
       - destruct H0 as [c0 [H0 H1] ]. 
         unfold Peval, horiz_Cline, horiz_from_01_poly in *; simpl in *.
         destruct H0 as [ [H0 H2] H3].
         unfold Cmult in H1; rewrite H3 in H1; simpl in H1.
         assert (H1' := H1).
         apply (f_equal fst) in H1; simpl in H1.
         apply (f_equal snd) in H1'; simpl in H1'.
         rewrite <- H1, <- H1'; simpl.
         split; try lra. 
         unfold Rminus.
         rewrite Rmult_0_r, Rmult_0_l, Ropp_0, Rplus_0_r, Rplus_0_l.
         rewrite Rmult_0_r, Rmult_0_l, Ropp_0, Rplus_0_r.
         do 2 rewrite Rmult_1_r; rewrite Rplus_0_r.
         split. 
         assert (H' : forall a b : R, 0 <= b -> a <= a + b). intros. lra. 
         apply H'; apply Rmult_le_pos; lra. 
         assert (H' : 0 <= (b + - a)). lra.
         apply (Rmult_le_compat_l _ (fst c0) 1) in H'; auto; lra. 
       - unfold horiz_Cline in H0. 
         destruct (Req_dec a b); subst.
         + assert (H' : fst c = b). lra. 
           exists C0; split. 
           unfold unit_line; simpl; lra. 
           unfold horiz_from_01_poly, Peval; simpl. 
           apply c_proj_eq. simpl. 
           rewrite H'. lra. 
           destruct H0; rewrite H1; simpl; lra.
         + assert (H' : b - a > 0). lra. apply Rinv_0_lt_compat in H'.
           exists (((fst c) - a) / (b - a), 0)%R; split.
           split; auto; simpl. 
           destruct H0 as [ [H0 H2] H3].
           split. unfold Rdiv. apply Rmult_le_pos; lra. 
           apply (Rmult_le_reg_r (b - a)); try lra. 
           unfold Rdiv. rewrite Rmult_assoc, Rinv_l; lra. 
           unfold horiz_from_01_poly, Peval; simpl.
           C_field_simplify. unfold Cmult; simpl.
           do 2 rewrite Rmult_0_r; rewrite Rmult_0_l.
           apply c_proj_eq; simpl; try lra. 
           unfold Rminus, Rdiv; rewrite Ropp_0, Rplus_0_r, Rmult_comm, Rmult_assoc, Rinv_l; lra.
Qed.

Lemma horiz_Cline_compact : forall (a b h : R), 
  compact (horiz_Cline a b h). 
Proof. intros. 
       destruct (Rle_lt_dec a b).
       - rewrite <- horiz_Cline_image; auto.
         apply continuous_image_compact.
         unfold continuous_on; intros. 
         apply polynomial_continuous.
         apply unit_line_compact.
       - exists (list_to_cover []).
         repeat split.
         exists []; easy. 
         unfold subcover; intros; easy. 
         unfold subset; intros. 
         unfold horiz_Cline in H2.
         lra. 
Qed.

(* we now do it again for a vertical line *)
Definition verti_Cline (a b h : R) : Cset :=
   fun c => a <= snd c <= b /\ fst c = h.

Definition switch_pair (c : C) : C := (snd c, fst c).

Lemma switch_pair_Cmod : forall c, Cmod c = Cmod (switch_pair c).
Proof. intros. 
       unfold Cmod, switch_pair; simpl. 
       rewrite Rplus_comm; easy. 
Qed.

Lemma switch_pair_minus : forall c c0, switch_pair (c - c0) = switch_pair c - switch_pair c0.
Proof. intros.
       unfold switch_pair; easy.
Qed.

Lemma switch_pair_continuous_on_C : continuous_on switch_pair C_.
Proof. unfold continuous_on, continuous_at, limit_at_point; intros. 
       exists ϵ; split; auto; intros. 
       rewrite <- switch_pair_minus, <- switch_pair_Cmod; easy. 
Qed.

Lemma verti_Cline_image : forall (a b h : R),
  switch_pair @ (horiz_Cline a b h) ⩦ (verti_Cline a b h).
Proof. intros; split; intros.  
       - destruct H as [c0 [H H0] ].
         unfold horiz_Cline, verti_Cline, switch_pair in *.
         destruct c; destruct c0; simpl in *.
         assert (H1 := H0).
         apply (f_equal fst) in H0; apply (f_equal snd) in H1; simpl in *; subst; easy. 
       - exists (snd c, fst c).
         split. 
         unfold horiz_Cline, verti_Cline in *; simpl; easy. 
         unfold switch_pair; destruct c; simpl; easy. 
Qed.

Lemma verti_Cline_compact : forall (a b h : R), 
  compact (verti_Cline a b h). 
Proof. intros. 
       rewrite <- verti_Cline_image.
       apply continuous_image_compact.
       apply switch_pair_continuous_on_C.
       apply horiz_Cline_compact.
Qed.

(* now the main event, showing a cube is compact *)
(* we use the same lub approach as before, but need some more lemmas *)

Definition center_square (s : R) : Cset :=
  fun c => -s <= fst c <= s /\ -s <= snd c <= s.

Definition partial_center_square (s x : R) : Cset :=
  fun c => -s <= fst c <= x /\ -s <= snd c <= s.

Definition partial_center_square_covered (G : Ccover) (s x : R) : Prop :=
  exists G', finite_cover G' /\ subcover G' G /\ (partial_center_square s x) ⊂ (big_cup G').

Lemma line_in_square : forall (s h : R), 
  -s <= h <= s -> 
  ((verti_Cline (-s) s h) ⊂ (center_square s)).
Proof. unfold subset; intros. 
       unfold verti_Cline, center_square in *.
       destruct H0; subst. easy. 
Qed.      

Lemma zero_width_square : forall (s : R),
  (partial_center_square s (-s)) ⩦ (verti_Cline (-s) s (-s)).
Proof. split; intros. 
       - unfold verti_Cline, partial_center_square in *.
         split; try easy.
         symmetry; apply Rle_le_eq; easy. 
       - unfold verti_Cline, partial_center_square in *.
         split; try easy.
         destruct H; rewrite H0; lra.
Qed.

Lemma negc_always_covered : forall (G : Ccover) (s : R),
  s > 0 ->
  WF_cover G -> open_cover G ->
  (center_square s) ⊂ (big_cup G) -> 
  partial_center_square_covered G s (-s).
Proof. intros. 
       assert (H3 : (partial_center_square s (-s)) ⊂ (big_cup G)).
       eapply subset_transitive; try apply H3.
       rewrite zero_width_square.
       apply line_in_square; try lra.
       easy. 
       rewrite zero_width_square in H3.
       apply verti_Cline_compact in H3; auto.
       destruct H3 as [G' H3]. 
       exists G'; repeat split; try easy.
       rewrite zero_width_square; easy.
Qed. 

Lemma pcs_le_subset : forall (s x x' : R),
  x' <= x -> 
  (partial_center_square s x') ⊂ (partial_center_square s x).
Proof. unfold partial_center_square, subset; intros. 
       repeat split; try easy. 
       destruct H0 as [ [H0 H1] H2].
       lra. 
Qed.       

(* same analogue as plc_less *)
Lemma pcs_less : forall (s x x' : R) (G : Ccover),
  x' <= x ->
  partial_center_square_covered G s x ->
  partial_center_square_covered G s x'.
Proof. intros. 
       unfold partial_center_square_covered in *.
       destruct H0 as [G' [H0 [H1 H2] ] ].
       exists G'; repeat split; auto. 
       eapply subset_transitive.
       apply pcs_le_subset; eauto.
       easy. 
Qed.

Definition cover_to_centered_cube_cover (G : Ccover) (a b h : R) : Ccover :=
  fun A => (exists s y A', s > 0 /\ A ⩦ (open_square (h, y) s) /\ G A' /\ (open_square (h, y) s) ⊂ A').

Lemma WF_ctccc : forall (G : Ccover) (a b h : R),
  WF_cover (cover_to_centered_cube_cover G a b h).
Proof. unfold WF_cover; intros. 
       destruct H.
       destruct H0 as [s [y [A0 [H0 [H1 [H2 H3] ] ] ] ] ].
       exists s, y, A0. 
       split; auto.
       split; auto.
       rewrite <- H; easy. 
Qed.

Lemma cube_cover_ctccc : forall (G : Ccover) (a b h : R),
  cube_cover (cover_to_centered_cube_cover G a b h).
Proof. unfold cube_cover; intros.
       destruct H as [s [y [A' [H [H1 [H2 H3] ] ] ] ] ].
       exists s, (h, y); split; auto.
Qed.

Lemma ctccc_smaller : forall (G : Ccover) (a b h : R),
  (big_cup (cover_to_centered_cube_cover G a b h)) ⊂ (big_cup G).
Proof. unfold subset, big_cup; intros. 
       destruct H as [A [H H0] ].
       destruct H as [s [y [A' H] ] ].
       exists A'; split; try easy. 
       do 2 apply H; easy.
Qed.

Lemma ctccc_big_enough : forall (G : Ccover) (a b h : R),
  open_cover G -> (verti_Cline a b h) ⊂ (big_cup G) ->
  (verti_Cline a b h) ⊂ (big_cup (cover_to_centered_cube_cover G a b h)).
Proof. intros. 
       unfold subset; intros.  
       assert (H' : fst c = h). apply H1.
       apply H0 in H1.
       destruct H1 as [A [H1 H2] ].
       assert (H3 := H1); apply H in H3.
       destruct (H3 c) as [ϵ [H4 H5] ]; auto.
       assert (H6 := square_in_circle c ϵ).
       exists (open_square c (ϵ / √ 2)); split.
       exists (ϵ / √ 2)%R, (snd c), A.
       split. 
       apply (lt_ep_helper ϵ); easy.
       split. 
       destruct c; simpl in *; subst; easy.  
       split; try easy.
       eapply subset_transitive; try apply H5.
       destruct c; simpl in *; subst; easy.  
       apply square_contains_center.
       apply (lt_ep_helper ϵ); easy.
Qed.

(* maps a pair to a square whose center is (w, fst p) with side lenght snd p *)
Definition pair_to_sqaures (w : R) (p : R * R) : Cset := open_square (w, (fst p)) (snd p).

Lemma pts_gives_cube_cover : forall (h : R) (l : list (R * R)),
  (forall p, In p l -> snd p > 0) -> 
  cube_cover (list_to_cover (map (pair_to_sqaures h) l)).
Proof. induction l as [| p].
       - unfold cube_cover; intros; easy.
       - unfold cube_cover; intros. 
         destruct H0.
         exists (snd p), (h, fst p); split. 
         apply (H p); left; easy.
         rewrite H0; easy.
         apply IHl in H0; try easy.
         intros.
         apply (H p0); right; easy. 
Qed.         

Lemma gen_ccc_list : forall (G : Ccover) (a b h : R) (l : list Cset),
  subcover (list_to_cover l) (cover_to_centered_cube_cover G a b h) -> 
  exists l', (forall p, In p l' -> snd p > 0) /\ 
          eq_cover (list_to_cover (map (pair_to_sqaures h) l')) (list_to_cover l).
Proof. induction l as [| A].
       - intros; exists []; easy.  
       - intros.
         assert (H0 : subcover (list_to_cover l) (cover_to_centered_cube_cover G a b h)).
         { unfold subcover; intros. 
           apply H; right; easy. }
         apply IHl in H0.
         assert (H1 : (cover_to_centered_cube_cover G a b h) A).
         { apply H; left; easy. }
         assert (H2 : exists (s y : R), s > 0 /\ (A) ⩦ (open_square (h, y) s)).
         { destruct H1 as [s [y [A0 [H1 H2] ] ] ].
           exists s, y; easy. } 
         destruct H2 as [s [y [H2 H3] ] ].
         destruct H0 as [l' H0].
         exists ((y, s) :: l').
         split; intros. 
         destruct H4; subst; simpl; auto.
         apply H0; easy.
         split; intros. 
         + destruct H4.
           left; rewrite H3, H4; easy.
           right; apply H0 in H4; easy.
         + destruct H4.
           left; rewrite H4, H3; easy.
           right; apply H0; easy.
Qed.

Lemma min_side_length : forall (p0 : R * R) (l : list (R * R)),
  (forall p, In p (p0 :: l) -> snd p > 0) -> 
  (exists min, 0 < min /\ (forall p, In p (p0 :: l) -> min < snd p)).
Proof. induction l as [| p1].
       - intros.  
         exists ((snd p0) * /2)%R.
         split. 
         apply Rmult_lt_0_compat; try lra. 
         apply (H p0); left; easy.
         intros. 
         destruct H0; try easy; subst.
         rewrite <- Rmult_1_r.
         apply Rmult_lt_compat_l; try lra. 
         apply (H p); left; easy. 
       - intros. 
         assert (H' : (forall p : R * R, In p (p0 :: l) -> snd p > 0)).
         { intros; apply (H p); destruct H0; try (left; easy); do 2 right; auto. }
         apply IHl in H'.
         destruct H' as [min [H0 H1] ]. 
         exists (Rmin min ((snd p1) * /2))%R.
         split. apply Rmin_glb_lt; auto.
         apply Rmult_lt_0_compat; try lra. 
         apply (H p1).
         right; left; easy.  
         intros.  
         destruct H2. 
         + eapply Rle_lt_trans; try apply Rmin_l.
           apply H1; left; easy. 
         + destruct H2; subst. 
           eapply Rle_lt_trans; try apply Rmin_r.
           assert (H' : snd p > 0). apply H; right; left; easy.
           lra. 
           eapply Rle_lt_trans; try apply Rmin_l.
           apply H1; right; easy. 
Qed.

Lemma boost_line : forall (a b h : R) (O : Cset),
  a < b ->
  open O -> (verti_Cline a b h) ⊂ O ->
  exists ϵ, ϵ > 0 /\ (verti_Cline (a - ϵ) (b + ϵ) h) ⊂ O.
Proof. intros.
       assert (H2 : (verti_Cline a b h) (h, a)).
       { unfold verti_Cline; split; simpl; lra. }
       assert (H3 : (verti_Cline a b h) (h, b)).
       { unfold verti_Cline; split; simpl; lra. }
       apply H1 in H2; apply H1 in H3.
       apply H0 in H2; apply H0 in H3.
       destruct H2 as [ϵ1 [H2 H4] ].
       destruct H3 as [ϵ2 [H3 H5] ].
       exists (Rmin (ϵ1 * /2) (ϵ2 * /2)) .
       split; try (apply Rmin_Rgt_r; lra). 
       unfold subset; intros. 
       destruct H6 as [H6 H7].
       destruct (Rlt_le_dec b (snd c)).
       - apply H5.
         unfold ϵ_disk; destruct c; simpl in *; subst.
         destruct H6; unfold Cminus, Cmod; simpl. 
         replace (h + - h)%R with 0 by lra. 
         rewrite Rmult_0_l, Rplus_0_l, Rmult_1_r, sqrt_square; try lra.
         assert (H' := (Rmin_r (ϵ1 * /2) (ϵ2 * /2))); lra. 
       - destruct (Rlt_le_dec (snd c) a).
         + apply H4.
           unfold ϵ_disk; destruct c; simpl in *; subst.
           destruct H6; unfold Cminus, Cmod; simpl. 
           replace (h + - h)%R with 0 by lra.
           rewrite Rmult_0_l, Rplus_0_l, Rmult_1_r.  
           replace ((r2 + - a) * (r2 + - a))%R with (r2 + - a)² by easy.
           rewrite sqrt_Rsqr_abs, Rabs_left1; try lra.
           replace (- (r2 + - a))%R with (a - r2)%R by lra. 
           assert (H' := (Rmin_l (ϵ1 * /2) (ϵ2 * /2))); lra. 
         + apply H1.
           unfold verti_Cline; easy.
Qed.

(* or is THIS the crucial lemma? *)
Lemma rect_within_centered_sqaures : forall (a b h : R) (l : list (R * R)),
  a < b -> (forall p, In p l -> snd p > 0) ->
  (verti_Cline a b h) ⊂ (big_cup (list_to_cover (map (pair_to_sqaures h) l))) ->
  exists h' s1 s2, s1 > 0 /\ s2 > 0 /\ (verti_Cline a b h) ⊂ (open_rect (h, h') s1 s2) /\
             (open_rect (h, h') s1 s2) ⊂ (big_cup (list_to_cover (map (pair_to_sqaures h) l))).
Proof. intros. 
       destruct l as [| p].
       - simpl in H1.
         assert (H' : (verti_Cline a b h) (h, a)).
         { unfold verti_Cline; split; simpl; try lra. }
         apply H1 in H'.
         destruct H'; try easy.
       - exists ((b + a) * /2)%R.
         apply boost_line in H1; auto.
         destruct H1 as [ϵ [H1 H2] ].
         apply min_side_length in H0.
         destruct H0 as [min [H0 H3] ].
         exists min, ((b - a) * /2 + ϵ)%R.
         split; auto. split.
         apply Rplus_lt_0_compat; auto.
         apply Rmult_lt_0_compat; try lra.
         split.
         unfold subset, open_rect; intros. 
         destruct H4; destruct c; subst; simpl in *. 
         split.
         rewrite Rminus_eq_0, Rabs_R0; auto.  
         apply Rabs_def1; lra.
         unfold subset; intros. 
         destruct H4; simpl.
         assert (H' : (verti_Cline (a - ϵ) (b + ϵ) h) (h, snd c)).
         { split; simpl in *; try easy.
           apply Rabs_def2 in H5; lra. } 
         apply H2 in H'.
         destruct H' as [A [H6 H7] ].
         exists A; split; simpl; try easy. 
         unfold list_to_cover in H6.
         apply In'_map in H6.
         destruct H6 as [p0 [H6 H8] ].
         apply H3 in H8.
         apply H6; apply H6 in H7.
         destruct c; split; simpl in *; try lra.
         destruct H7; simpl in *; easy.
         apply arb_cup_open.
         apply cube_cover_open_cover.
         apply pts_gives_cube_cover; easy. 
Qed.

(* the crucial lemma *)
Lemma rect_within_fin_cubecover : forall (a b h : R) (l : list Cset),
  a < b ->
  cube_cover (list_to_cover l) -> 
  (verti_Cline a b h) ⊂ (big_cup (list_to_cover l)) -> 
  exists h' s1 s2, s1 > 0 /\ s2 > 0 /\ (verti_Cline a b h) ⊂ (open_rect (h, h') s1 s2) /\
                 (open_rect (h, h') s1 s2) ⊂ (big_cup (list_to_cover l)).
Proof. intros. 
       apply cube_cover_open_cover in H0. 
       apply ctccc_big_enough in H1; try easy.
       apply verti_Cline_compact in H1. 
       destruct H1 as [G' [H1 [H2 H3] ] ].
       destruct H1 as [l' H1]. 
       assert (H2' := H2).
       rewrite H1 in H2.
       apply gen_ccc_list in H2.
       destruct H2 as [l0 [H_ H2] ].       
       rewrite H1, <- H2 in H3. 
       apply rect_within_centered_sqaures in H3; auto.
       destruct H3 as [h' [s1 [s2 [H3 [H4 [H5 H6] ] ] ] ] ].
       exists h', s1, s2. 
       split; auto. split; auto. split; auto.
       eapply subset_transitive; try apply H6.
       rewrite H2.
       assert (H' := (ctccc_smaller (list_to_cover l) a b h)).
       unfold subset; intros; apply H'.
       assert (H8 : (big_cup G') ⩦ (big_cup ((list_to_cover l')))). rewrite H1; easy.
       apply H8 in H7.
       destruct H7 as [A [H7 H9] ].
       exists A; split; auto.
       apply cube_cover_open_cover.
       apply cube_cover_ctccc.
       apply WF_ctccc.
Qed.       


(** TODO: write a program that reads this proof and makes a more efficient FTA proof. 
    There must be a better way than this... *)
Theorem center_square_compact : forall (s : R),  
  s > 0 -> compact (center_square s).
Proof. intros. 
       apply compact_is_cube_compact.
       unfold cube_compact, center_square; intros. 
       destruct (Classical_Prop.classic (partial_center_square_covered G s s)).
       - destruct H3 as [G' H3].
         exists G'; easy.
       - destruct (Classical_Prop.classic 
                     (is_upper_bound (partial_center_square_covered G s) s)).
         + destruct (completeness (partial_center_square_covered G s)).
           exists s; easy. 
           exists (-s)%R. 
           apply negc_always_covered; try easy. 
           apply cube_cover_open_cover; easy. 
           destruct i.
           assert (H7 : x <= s). 
           { apply H6; easy. }
           assert (H8 : (-s) <= x). 
           { apply H5; apply negc_always_covered; try easy. 
             apply cube_cover_open_cover; easy. } 
           assert (H9 :  (verti_Cline (-s) s x) ⊂ (big_cup G)).
           { eapply subset_transitive; try apply H2.
             apply line_in_square; easy. }
           assert (H10 := verti_Cline_compact (-s) s x).
           apply compact_is_cube_compact in H10.
           apply H10 in H9; try easy.
           destruct H9 as [G' [H9 [H11 H12] ] ].
           destruct H9 as [l H9].
           assert (H13 : cube_cover (list_to_cover l)).
           { unfold cube_cover; intros. 
             rewrite H9 in H11.
             apply H11 in H13.
             apply H0 in H13; easy. }
           rewrite H9 in H12.
           apply rect_within_fin_cubecover in H12; auto.
           destruct H12 as [h' [s1 [s2 [H12 [H14 [H15 H16] ] ] ] ] ].
           assert (H17 : s1 / 2 > 0).
           { unfold Rdiv; apply Rmult_gt_0_compat; lra. } 
           assert (H18 : partial_center_square_covered G s (x - s1 / 2)).
           { apply (extract_elem_lt_lub 
                      (partial_center_square_covered G s) (-s) x (s1 / 2)) in H17; try easy.
             destruct H17 as [x0 [H17 H18] ].
             apply (pcs_less _ x0); auto; lra.  
             apply negc_always_covered; try easy. 
             apply cube_cover_open_cover; easy. }
           assert (H19 : partial_center_square_covered G s (x + s1 / 2)).
           { destruct H18 as [G'' [H18 [H19 H20] ] ].
             destruct H18 as [l' H18].
             exists (list_to_cover (l ++ l')).
             split. exists (l ++ l'); easy. 
             split. 
             unfold subcover; intros. 
             apply In'_app_or in H21.
             destruct H21.
             rewrite H9 in H11; apply H11; easy.
             rewrite H18 in H19; apply H19; easy.
             unfold subset; intros. 
             apply app_union.
             destruct (Rle_dec (fst c) (x - s1 / 2)).
             + right.
               rewrite H18 in H20.
               apply H20.
               destruct H21.
               split; try easy.
             + left. 
               apply Rnot_le_gt in n.
               apply H16.
               split; simpl. 
               destruct H21. 
               assert (H' : s1 / 2 < s1).
               unfold Rdiv. rewrite <- Rmult_1_r. 
               apply Rmult_lt_compat_l; lra.
               destruct H21.  
               apply Rabs_def1; lra.
               assert (H22 :  (verti_Cline (- s) s x) (x, snd c)).
               { destruct H21; split; try easy. }
               apply H15 in H22.
               destruct H22; easy. }
           apply H5 in H19; lra.
           lra.
         + apply (not_ub_implies_larger_elem _ (-s)) in H4.
           destruct H4 as [a' [H4 H5] ].
           apply (pcs_less s a' s G) in H4; try lra; easy. 
           apply negc_always_covered; try easy.
           apply cube_cover_open_cover; easy. 
Qed.


(**********************************************)
(* Showing that compact is closed and bounded *)
(**********************************************)

(* first, we show compact -> bounded *)
Definition ball_cover : Ccover :=
  fun G => open G /\ exists r, r > 0 /\ G ⊂ B(0,r).

Lemma open_cover_ball_cover : open_cover ball_cover.
Proof. unfold ball_cover; easy. Qed.
      
Lemma WF_ball_cover : WF_cover ball_cover.
Proof. unfold ball_cover, WF_cover; intros.  
       destruct H as [H [H0 [r [H1 H2] ] ] ].
       split; try (rewrite <- H; easy). 
       exists r; split; auto. 
       rewrite <- H; easy. 
Qed.

Lemma ball_cover_elems_bounded : forall (A : Cset),
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

Lemma list_cover_ball_cover_bounded : forall (l : list Cset),
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
       rewrite H in *.
       apply list_cover_ball_cover_bounded; easy. 
Qed.

Lemma compact_implies_bounded : forall (A : Cset),
  compact A -> bounded A. 
Proof. intros. 
       unfold compact in H.
       destruct (H ball_cover).
       apply open_cover_ball_cover.
       apply WF_ball_cover.
       eapply subset_transitive.
       eapply subset_C_.
       apply C_subset_ball_cover.
       destruct H0 as [H0 [H1 H2] ].
       apply fin_subcover_ball_cover_bounded in H0; auto.
       unfold bounded in *.
       destruct H0 as [ϵ H0].
       exists ϵ; eauto with Csub_db.
Qed.


(* now, we show compact -> closed *)
Definition bad_point_cover (c : C) : Ccover :=
  fun G => open G /\ exists r, r > 0 /\ G ⊂ (fun c' => Cmod (c' - c) > r).

Lemma open_cover_bpc : forall c, open_cover (bad_point_cover c).
Proof. unfold bad_point_cover; easy. Qed.

Lemma WF_bpc : forall c, WF_cover (bad_point_cover c).
Proof. unfold WF_cover, bad_point_cover; intros. 
       destruct H as [H [H1 [r [H2 H3] ] ] ].
       split; try (rewrite <- H; easy).
       exists r; split; auto; rewrite <- H; easy. 
Qed.

Lemma bpc_covers_almost_all : forall (c : C) (A : Cset),
  A` c -> A ⊂ (big_cup (bad_point_cover c)).
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

Lemma bpc_separates_from_c : forall (c : C) (l : list Cset),
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
         + apply H4 in H5.
           apply H2 in H5.
           eapply Rgt_ge_trans; eauto.
           assert (H' := Rmin_l r1 r2). lra. 
         + assert (H' : (big_cup (list_to_cover l)) c0).
           { exists A0; split; easy. }
           apply H3 in H'.
           eapply Rgt_ge_trans; eauto.
           assert (H'' := Rmin_r r1 r2). lra. 
Qed.

Lemma compact_implies_closed : forall (A : Cset),
  compact A -> closed A. 
Proof. unfold compact, closed, open; intros. 
       destruct (H (bad_point_cover c)) as [G' [H1 [H2 H3] ] ].
       apply open_cover_bpc.
       apply WF_bpc.
       apply bpc_covers_almost_all; easy. 
       destruct H1 as [l H1]; subst.
       rewrite H1 in *.
       apply bpc_separates_from_c in H2.
       destruct H2 as [r [H2 H4] ].
       exists r; split; auto.
       unfold complement, ϵ_disk, subset, not; intros. 
       apply H3 in H6; apply H4 in H6; lra. 
Qed.

Lemma add_comp_covers_all : forall (A : Cset) (G : Ccover),
  WF_cover G -> A ⊂ (big_cup G) ->
  C_ ⊂ (big_cup (fun A' : Cset => G A' \/ (A') ⩦ ((A) `) )).
Proof. intros.
       unfold subset, C_, big_cup; intros. 
       destruct (Classical_Prop.classic (A c)).
       - apply H0 in H2.
         destruct H2 as [A' [H2 H3] ].
         exists A'; split; auto. 
       - exists A`; split; auto. 
         right; easy. 
Qed.

Lemma closed_subset_compact : forall (A B : Cset),
  A ⊂ B -> compact B -> closed A -> 
  compact A.
Proof. unfold compact; intros. 
       destruct (H0 (fun A' => G A' \/ A' ⩦ ((A) `) )).
       unfold open_cover; intros. 
       destruct H5; try (rewrite H5; easy). 
       apply H2 in H5; easy.
       unfold WF_cover; intros.
       destruct H5; destruct H6. 
       left; apply (H3 A0 A'); easy. 
       right; rewrite <- H5; easy. 
       eapply subset_transitive.
       eapply subset_C_.
       apply add_comp_covers_all; easy. 
       destruct H5. destruct H5 as [l H5].
       exists (fun A' => x A' /\ ~ (A' ⩦ (A`))).
       split; try split. 
       - apply (finite_cover_subset l).
         unfold WF_cover; intros. 
         destruct H7 as [H7 [H8 H9] ].
         split. 
         apply H5 in H8; apply H5.
         apply ((WF_finitecover l) A0 A'); easy. 
         unfold not; intros; apply H9. 
         rewrite H7; easy. 
         rewrite <- H5. 
         unfold subcover; intros; easy. 
       - destruct H6.  
         unfold subcover; intros. 
         destruct H8. 
         apply H6 in H8.
         destruct H8; easy. 
       - unfold subset, big_cup; intros. 
         destruct H6. 
         apply (subset_transitive A B) in H8; auto. 
         destruct (H8 c); auto. 
         exists x0; split; try easy. 
         split; try easy. 
         unfold not; intros. 
         destruct H9; apply H10 in H11.
         apply H11; easy. 
Qed.

Lemma closed_bounded_implies_compact : forall (A : Cset),
  closed A -> bounded A ->
  compact A.
Proof. intros. 
       destruct H0 as [ϵ H0].
       assert (H1 : A ⊂ (center_square ϵ)).
       { unfold subset; intros. 
         apply H0 in H1.
         unfold ϵ_disk in H1.
         replace (c - 0)%C with c in H1 by lca. 
         assert (H' := (Rmax_Cmod c)).
         apply (Rle_lt_trans _ _ ϵ) in H'; auto.
         split. 
         + apply (Rle_lt_trans (Rabs (fst c)) _ ϵ) in H'; try apply Rmax_l.
           apply Rabs_def2 in H'; lra.
         + apply (Rle_lt_trans (Rabs (snd c)) _ ϵ) in H'; try apply Rmax_r.
           apply Rabs_def2 in H'; lra. }
       apply closed_subset_compact in H1; auto.
       destruct (Rlt_le_dec 0 ϵ).
       apply center_square_compact; easy.
       unfold compact; intros. 
       destruct (Rlt_le_dec ϵ 0).
       exists (list_to_cover []); split. 
       exists []; easy. split.
       unfold subcover; intros; easy. 
       unfold subset; intros. 
       unfold center_square in H5; lra. 
       apply Rle_antisym in r; auto; subst.
       assert (H' : (big_cup G) 0).
       apply H4. 
       unfold center_square; simpl; lra.
       destruct H' as [A' [H5 H6] ].
       exists (list_to_cover [A']).
       repeat split. 
       exists [A']; easy.
       unfold subcover; intros. 
       destruct H7; try easy.
       apply (H3 A' A0); easy. 
       unfold subset; intros. 
       destruct H7 as [ [H7 H8] [H9 H10] ]. 
       replace (-0)%R with 0 in * by lra.
       apply Rle_antisym in H7; auto.
       apply Rle_antisym in H9; auto.
       destruct c; simpl in *; subst. 
       exists A'. split; auto.
       left; easy.
Qed.

Theorem Heine_Borel : forall (A : Cset),
  compact A <-> closed A /\ bounded A.
Proof. split; intros. 
       split. 
       apply compact_implies_closed; easy.
       apply compact_implies_bounded; easy.
       apply closed_bounded_implies_compact; easy.
Qed.

(** showing that closed sets have a minimum norm element *)


Definition nonneg_real_line : Cset := 
  fun c => fst c >= 0 /\ snd c = 0.

Lemma continuous_Cmod : continuous_on Cmod C_.
Proof. unfold continuous_on, C_, continuous_at, limit_at_point; intros. 
       exists ϵ.
       split; auto; intros. 
       assert (H3 := Cmod_triangle (x - c) c).
       assert (H4 := Cmod_triangle (c - x) x).
       replace (Cminus (RtoC (Cmod x)) (RtoC (Cmod c))) with
               (RtoC (Rminus (Cmod x) (Cmod c))) by lca.
       rewrite Cmod_R.
       apply Rabs_def1.
       replace (x - c + c) with x in H3 by lca; lra. 
       replace (c - x + x) with c in H4 by lca.
       rewrite <- Ropp_minus_distr.
       apply Ropp_lt_contravar.
       rewrite Cmod_switch in H2; lra. 
Qed.

Lemma image_nnp : Cmod @ C_ ⩦ nonneg_real_line.
Proof. unfold nonneg_real_line.
       split; intros. 
       destruct H as [c0 [_ H] ]; subst; simpl.  
       split; try easy.
       assert (H' := Cmod_ge_0 c0); lra. 
       exists (fst c)%R.
       split; try easy.
       destruct H; destruct c; simpl in *; subst.
       apply injective_projections; simpl; try easy.
       rewrite Cmod_R, Rabs_right; lra.
Qed.

Lemma not_lb_implies_smaller_elem : forall (E : R -> Prop) (a b : R),
  E a -> ~ (is_lower_bound E b) ->
  exists a', E a' /\ a' < b.
Proof. intros. 
       destruct (Classical_Prop.classic (exists a' : R, E a' /\ a' < b)); auto. 
       assert (H' : is_lower_bound E b). 
       { unfold is_lower_bound; intros. 
         destruct (Classical_Prop.classic (b <= x)); auto. 
         apply Rnot_le_lt in H3.
         assert (H'' : False).
         apply H1. 
         exists x; easy. 
         easy. }
       easy. 
Qed.

Lemma extract_elem_gt_glb : forall (E : R -> Prop) (a glb ϵ : R),
  E a -> ϵ > 0 -> is_glb E glb ->
  exists x, (E x /\ x < glb + ϵ). 
Proof. intros. 
       apply (not_lb_implies_smaller_elem _ a); auto. 
       unfold not; intros. 
       destruct H1.
       apply H3 in H2.
       lra. 
Qed.

Lemma closed_line_has_min : forall (A : Cset),
  closed A -> A ⊂ nonneg_real_line -> 
  (exists c, A c) ->
  exists min, A (min, 0) /\ (forall p, A p -> min <= fst p).
Proof. intros. 
       assert (H2 : bounded_below (fun x => A (x, 0))).
       { exists 0; unfold is_lower_bound; intros.
         apply H0 in H2.
         destruct H2; simpl in *; lra. }
       destruct (glb_completeness (fun x : R => A (x, 0))) as [glb [H3 H4] ]; auto.
       destruct H1; exists (fst x); destruct x; simpl in *.
       destruct (H0 _ H1); simpl in *; subst; easy.
       exists glb; split. 
       destruct (Classical_Prop.classic (A (glb, 0))); auto.
       unfold closed in H.
       assert (H' : (A`) (glb, 0)). easy. 
       apply H in H'.
       destruct H' as [ϵ [H6 H7] ].
       destruct H1 as [c0 H1].
       destruct (extract_elem_gt_glb (fun x : R => A (x, 0)) (fst c0) glb ϵ) as [x [H8 H9] ]; auto.
       destruct (H0 _ H1); destruct c0; simpl in *; subst; easy. 
       split; auto. 
       assert (H' : glb <= x).
       { apply H3; easy. }
       assert (H10 : A` (x, 0)).
       { apply H7.
         unfold ϵ_disk, Cmod; simpl. 
         rewrite Ropp_0, Rplus_0_l, Rmult_0_l, Rplus_0_r, Rmult_1_r.
         replace ((x + - glb) * (x + - glb))%R with ((x + - glb)²) by easy.
         rewrite sqrt_Rsqr_abs.
         apply Rabs_def1; try lra. } 
       easy.
       intros. 
       apply H3.
       destruct p; destruct (H0 _ H5); simpl in *; subst; easy. 
Qed.

Lemma compact_contains_min_norn_elem : forall (A : Cset),
  (exists c, A c) -> compact A -> 
  (exists mne, A mne /\ (forall c, A c -> Cmod mne <= Cmod c)).
Proof. intros. 
       apply (continuous_image_compact Cmod) in H0; try apply continuous_Cmod.
       apply Heine_Borel in H0; destruct H0.
       apply closed_line_has_min in H0.
       destruct H0 as [min [H0 H2] ].
       destruct H0 as [mne [H0 H3] ].
       exists mne; split; auto.
       intros. 
       apply (f_equal fst) in H3; simpl in H3.
       rewrite H3.
       assert (H' : (fun x : C => Cmod x) @ (A) (Cmod c)).
       { exists c; easy. }
       apply H2 in H'; easy.  
       rewrite <- image_nnp.
       apply subset_image; easy. 
       destruct H.
       exists (Cmod x).
       exists x; easy. 
Qed.



(****)
(****)
(****)


