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
Notation "A *" := (complement A) (at level 0) : topology_scope.
Infix "∈" := is_in (at level 0) : topology_scope.
Notation "B( a , ϵ )" := (ϵ_disk a ϵ) (at level 30, no associativity) : topology_scope.


Definition open (A : Cset) : Prop :=
  forall c, A c -> exists ϵ, ϵ > 0 /\ B(c,ϵ) ⊂ A.

Definition closed (A : Cset) : Prop :=
  open (A*).

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
       assert (H' : (fun c' : C => Cmod (c' - a) <= ϵ) * ⩦ (fun c' : C => Cmod (c' - a) > ϵ)).
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
  (A*)* ⩦ A.
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
  forall A, G A -> exists s cen, A ⩦ (open_square cen s) 




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

Lemma plc_lt_subset : forall (x x' : R),
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
       apply plc_lt_subset; eauto.
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

Definition center_square (s : R) : Cset :=
  fun c => -s <= fst c <= s /\ -s <= snd c <= s.


Lemma line_in_square : forall (s h : R), 
  -s <= h <= s -> 
  ((verti_Cline (-s) s h) ⊂ (center_square s)).
Proof. unfold subset; intros. 
       unfold verti_Cline, center_square in *.
       destruct H0; subst. easy. 
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


(* now, we show compact -> open *)
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
  C_ ⊂ (big_cup (fun A' : Cset => G A' \/ (A') ⩦ ((A) *) )).
Proof. intros.
       unfold subset, C_, big_cup; intros. 
       destruct (Classical_Prop.classic (A c)).
       - apply H0 in H2.
         destruct H2 as [A' [H2 H3] ].
         exists A'; split; auto. 
       - exists A*; split; auto. 
         right; easy. 
Qed.

Lemma closed_subset_compact : forall (A B : Cset),
  A ⊂ B -> compact B -> closed A -> 
  compact A.
Proof. unfold compact; intros. 
       destruct (H0 (fun A' => G A' \/ A' ⩦ ((A) *) )).
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
       exists (fun A' => x A' /\ ~ (A' ⩦ (A*))).
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
