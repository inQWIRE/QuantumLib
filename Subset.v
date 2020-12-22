Require Import List.
Require Export Prelim.
Require Export RealAux.


Open Scope R_scope.


(* Lemmas for subsets used in Heisenberg.v *)
Definition subset {X : Type} (l1 l2 : list X) :=
  forall (x : X), In x l1 -> In x l2.


(* an alternate version of subset *)
Fixpoint subset' {X : Type} (l1 l2 : list X) :=
  match l1 with
  | [] => True
  | (l :: l1') => In l l2 /\ subset' l1' l2
  end.


Lemma subset_is_subset' : forall (X : Type) (l1 l2 : list X),
    subset' l1 l2 <-> subset l1 l2.
Proof. intros X l1 l2. split.
       - induction l1 as [| l].
         * easy.
         * simpl. intros [H1 H2].
           unfold subset'. intros x. simpl. intros [H3 | H4].
           + rewrite H3 in H1. apply H1.
           + apply IHl1 in H2. unfold subset' in H2. 
             apply H2. apply H4.
       - induction l1 as [| l].
         * easy. 
         * unfold subset'. intros H.
           simpl. split.
           + apply H. simpl. left. reflexivity.
           + apply IHl1. unfold subset'. 
             intros x H'. apply H. simpl. 
             right. apply H'.
Qed.           
           
  
Infix "⊆" := subset (at level 30, no associativity) : R_scope.


Lemma subset_cons : forall (X : Type) (l1 l2 : list X) (x : X),
  l1 ⊆ l2 -> l1 ⊆ (x :: l2).
Proof. intros X l1 l2 x.
       unfold subset; intros H.
       intros x0 H0.
       simpl; right.
       apply H; apply H0.
Qed.


Lemma subset_concat_l : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l1 ++ l2).
Proof. intros X l1 l2.
       unfold subset; intros x H.
       apply in_or_app.
       left; apply H.
Qed.


Lemma subset_concat_r : forall (X : Type) (l1 l2 : list X),
  l1 ⊆ (l2 ++ l1).
Proof. intros X l1 l2.
       unfold subset; intros x H.
       apply in_or_app.
       right; apply H.
Qed.


Corollary subset_self : forall (X : Type) (l1 : list X),
  l1 ⊆ l1. 
Proof. intros X l1. assert (H: l1 ⊆ (l1 ++ [])). { apply subset_concat_l. }
       rewrite <- app_nil_end in H. apply H. 
Qed.


Lemma subsets_add : forall (X : Type) (l1 l2 l3 : list X),
  l1 ⊆ l3 -> l2 ⊆ l3 -> (l1 ++ l2) ⊆ l3.
Proof. intros X l1 l2 l3.
       unfold subset; intros H1 H2 x H.
       apply in_app_or in H.
       destruct H as [Hl1 | Hl2].
       - apply H1; apply Hl1.
       - apply H2; apply Hl2.
Qed.


Lemma subset_trans : forall (X : Type) (l1 l2 l3 : list X),
    l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3.
Proof. intros X l1 l2 l3.
       unfold subset; intros H1 H2. 
       intros x H.
       apply H1 in H; apply H2 in H.
       apply H.
Qed.
