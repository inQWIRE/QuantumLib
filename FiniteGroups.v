Require Import List.
Require Import Prelim.
Require Import Summation. 
Require Import FinFun. 
Require Import ListDec.


(* two important list functions used are NoDup and incl *)
(* in the following sections, we expand on these list functions *)




Program Instance list_is_monoid : forall {X}, Monoid (list X) := 
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



Inductive eq_mod_perm {X} (l1 l2 : list X) : Prop := 
  | eq_list : NoDup l1 -> NoDup l2 -> incl l1 l2 -> incl l2 l1 -> eq_mod_perm l1 l2.

Infix "⩦" := eq_mod_perm (at level 70).


Definition disjoint {X} (l1 l2 : list X) : Prop := NoDup (l1 ++ l2).



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






Lemma test : NoDup [1;2;3;4;5]%nat.                                            
Proof. repeat (apply NoDup_cons; unfold not; intros; repeat (destruct H; try lia)).
       apply NoDup_nil.
Qed.



(* quick little lemma useing FinFun's Listing *)
Lemma list_rep_length_le : forall G `{Monoid G} (gs1 gs2 : list G),
  Listing gs1 -> Listing gs2 -> length gs1 = length gs2.
Proof. intros. 
       destruct H0; destruct H1.
       apply Nat.le_antisymm; apply NoDup_incl_length; auto; unfold incl; intros. 
       apply H3.
       apply H2.
Qed.




Class FiniteGroup G `{Group G} :=
  { G_list_rep : list G
  ; G_finite_ver : Listing G_list_rep      
  ; G_eq_dec : decidable_eq G
  }.

Infix "·" := Gplus (at level 40) : group_scope.

Definition group_size G `{FiniteGroup G} := length G_list_rep.


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
  group_homomorphism H G f -> f (Gopp h) = Gopp (f h).
Proof. intros. 
       apply (Gplus_cancel_l _ _ (f h)).
       rewrite Gopp_r, <- H6, Gopp_r.
       apply homo_id in H6.
       easy. 
Qed.


Lemma cosets_same : forall H G `{FiniteGroup H} `{FiniteGroup G} (f : H -> G) (a b : G),
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

(*


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


  
Program Instance quat_is_monoid : Monoid Quaternion := 
  { Gzero := p_1
  ; Gplus := quatMul
  }.
Solve All Obligations with program_simpl; destruct g; try easy; destruct h; destruct i; easy. 


Program Instance quat_is_group : Group Quaternion :=
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


Program Instance quat_is_finitegroup : FiniteGroup Quaternion := 
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


(* **) 

(***)
(****) 
