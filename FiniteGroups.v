Require Import List.
Require Import Prelim.
Require Import Summation. 
Require Import FinFun. 




(* two important list functions used are NoDup and incl *)

Lemma test : NoDup [1;2;3;4;5]%nat.                                            
Proof. repeat (apply NoDup_cons; unfold not; intros; repeat (destruct H; try lia)).
       apply NoDup_nil.
Qed.




Definition list_rep G `{Monoid G} (gs : list G) : Prop :=
  NoDup gs /\ (forall g, In g gs). 



Lemma list_rep_length_le : forall G `{Monoid G} (gs1 gs2 : list G),
  list_rep G gs1 -> list_rep G gs2 -> length gs1 = length gs2.
Proof. intros. 
       destruct H0; destruct H1.
       apply Nat.le_antisymm; apply NoDup_incl_length; auto; unfold incl; intros. 
       apply H3.
       apply H2.
Qed.




Class FiniteGroup G `{Group G} :=
  { G_list_rep : list G
  ; G_finite_ver : list_rep G G_list_rep       
  }.

Infix "·" := Gplus (at level 40) : group_scope.

Definition group_size G `{FiniteGroup G} := length G_list_rep.


Lemma mul_by_g_perm : forall G `{FiniteGroup G} (g : G),
  list_rep G (map (Gplus g) G_list_rep).
Proof. intros.
       destruct G_finite_ver.
       split. 
       - apply Injective_map_NoDup; auto.
         unfold Injective; intros.
         apply Gplus_cancel_l in H4; easy.
       - intros.
         replace g0 with (g · ((Gopp g) · g0)).
         apply in_map; apply H3.
         rewrite Gplus_assoc, Gopp_r, Gplus_0_l; easy. 
Qed.




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
       - intros. 
         destruct g; simpl; 
           repeat (try (left; easy); right).
Qed.


(* **) 

(***)
(****) 
