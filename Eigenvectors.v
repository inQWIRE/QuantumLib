Require Import List.
Require Export Complex.
Require Export Matrix.
Require Export Quantum.



(* Some preliminary lemmas/additions to tactics that could be moved to other files *)


Local Open Scope nat_scope.


(* where can I find tactics to deal with this??? *)
Lemma easy_sub : forall (n : nat), 1 + n - n = 1. Proof. lia. Qed. 
Lemma easy_sub2 : forall (n k : nat), k - (1 + n) - 1 = k - n - 2. Proof. lia. Qed.
Lemma easy_sub3 : forall (n k : nat), n <> 0 -> n + k - 0 - 1 = n - 0 - 1 + k. 
Proof. intros. 
       destruct n as [| n].
       - easy.
       - simpl. lia. 
Qed.
Lemma easy_sub4 : forall (n : nat), n - 0 = n. Proof. lia. Qed.
Lemma easy_sub5 : forall (a b : nat), a < b -> a + S (b - a) = S b.
Proof. lia. Qed.

Lemma easy_sub6 : forall (a c b : nat), 
  b < c -> a < b -> c = (a + S (b - a) + (c - b - 1)).
Proof. intros. rewrite easy_sub5; try easy. lia. Qed.
Lemma easy_sub7 : forall (n : nat), S n - 1 = n. Proof. lia. Qed.


Lemma easy_ltb : forall (n : nat), n <? 1 + n = true. 
Proof. induction n as [| n']. easy.
       simpl. unfold Nat.ltb. simpl. unfold Nat.ltb in IHn'.
       simpl in IHn'. easy.
Qed.
Lemma easy_ltb2 : forall (n : nat), S n <? 1 = false.  
Proof. intros. destruct (S n <? 1) as [|] eqn:E. 
       apply Nat.ltb_lt in E. nia. 
       easy. 
Qed.
Lemma easy_ltb3 : forall (n m : nat), (n <? m) = false -> (m =? n) = false -> m < n.
Proof. intros.  
       assert (H' : ~ (n < m)). 
           { unfold not. intros. 
             apply Nat.ltb_lt in H1.
             rewrite H1 in H. easy. }
           apply not_lt in H'.  
           unfold ge in H'.
           assert (H'' : forall (n m : nat), m <= n -> n <> m -> m < n). { nia. }
           apply H'' in H'. nia. 
           assert (H''' : forall (n m : nat), (m =? n) = false -> n <> m).
           { induction n0.
             - destruct m0; easy. 
             - intros. 
               destruct m0. easy. 
               simpl in *. apply IHn0 in H1. nia. }
           apply H'''; easy.
Qed.
Lemma easy_ltb4 : forall (n m : nat), n < S m -> n = m \/ m > n.
Proof. intros. 
       destruct (n =? m) eqn:E.
       - left. apply Nat.eqb_eq in E. easy.
       - right. assert (H' : n < m -> m > n). { nia. }
         apply H'.
         apply easy_ltb3.
         unfold Nat.ltb.
         apply leb_correct_conv; easy.
         easy.
Qed.
Lemma easy_ltb5 : forall (x r n : nat),
  r <= n -> x >= n -> x <? r = false.
Proof. intros. assert (H': r <= x).
       { apply (le_trans r n x). 
         apply H. apply H0. }
       apply Nat.le_ngt in H'. 
       bdestruct (x <? r). easy.
       easy.
Qed.


Lemma easy_pow : forall (a n m : nat), a^(n + m) = a^n * a^m.
Proof. intros. induction n as [| n'].
       - simpl. nia.
       - simpl. rewrite IHn'. nia.
Qed.
Lemma easy_pow2 : forall (a p : nat), p <> 0 -> a^p = a * a ^ (p - 0 - 1). 
Proof. intros. destruct p as [| p']. easy. simpl. 
       rewrite Nat.sub_0_r.  easy.
Qed.
Lemma easy_pow3 : forall (n m : nat), m < n -> 2^n = (2^m) * 2 * 2^(n - m - 1).
Proof. intros. 
       assert (H' : 2^m * 2 = 2^(m + 1)). 
       { rewrite easy_pow. reflexivity. } 
       rewrite H'. 
       rewrite <- easy_pow.
       assert (H'' : m < n -> m + 1 + (n - m - 1) = n).
       { nia. }
       rewrite H''. 
       reflexivity.
       assumption. 
Qed.
Lemma easy_pow4 : forall (n : nat), (0 >= 2^n) -> False. 
Proof. intros. induction n as [| n'].
       - simpl in *. nia.
       - simpl in *. 
         assert (H' : forall (a : nat), a + 0 = a). { nia. }
         rewrite H' in H.
         assert (H'' : forall (a : nat), a + a >= a). { nia. }
         apply IHn'.
         nia. 
Qed.
Lemma easy_pow5 : forall (a b c : nat), 
  b < c -> a < b ->
  2^c = (2^a * (2^(b - a) + (2^(b - a) + 0))) * 2^(c - b - 1).
Proof. intros.
       assert (H' : forall n, 2^n + (2^n + 0) = 2^(S n)).
       { reflexivity. } 
       rewrite H'.
       do 2 (rewrite <- easy_pow).
       rewrite <- (easy_sub6 a c b); try easy.
Qed.
Lemma easy_pow5' : forall (a b c : nat), 
  b < c ->  a < b ->
  2^c = (2^a * (2^(b - a) * 2)) * 2^(c - b - 1).
Proof. intros.
       assert (H' : 2 ^ (b - a) * 2 = 2 ^ (b - a) * 2^1).
       { reflexivity. } 
       rewrite H'.
       do 3 (rewrite <- easy_pow).
       assert (H'' : b - a + 1 = S (b - a)). { nia. }
       rewrite H''.
       rewrite <- (easy_sub6 a c b); try easy.
Qed.
Lemma easy_pow6 : forall (n : nat), n <> 0 -> 2*2^n = (2*2^(n-1))*2. 
Proof. destruct n.
       - easy.
       - intros. 
         simpl.  
         rewrite easy_sub4.
         nia. 
Qed.

Lemma easy_pow6' : forall (n : nat), n <> 0 -> (2^n)*2 = (2*2^(n-1))*2. 
Proof. intros. rewrite mult_comm.
       apply easy_pow6; easy.
Qed.



Lemma Csum_simplify : forall (a b c d : C), a = b -> c = d -> (a + c = b + d)%C.
Proof. intros. 
       rewrite H, H0; easy.
Qed.


Lemma Cmult_simplify : forall (a b c d : C), a = b -> c = d -> (a * c = b * d)%C.
Proof. intros. 
       rewrite H, H0; easy.
Qed.


Lemma sqrt_1_unique : forall x, √ x = 1%R -> x = 1%R.
Proof. intros. assert (H' := H). unfold sqrt in H. destruct (Rcase_abs x).
       - assert (H0: 1%R <> 0%R). { apply R1_neq_R0. }
         rewrite H in H0. easy.
       - rewrite <- (sqrt_def x). rewrite H'. lra. 
         apply Rge_le. easy.
Qed.


(*************************)
(* Some basic list stuff *)
(*************************)


Definition zipWith {X Y Z: Type} (f : X -> Y -> Z) (As : list X) (Bs : list Y) : list Z :=
  map (uncurry f) (combine As Bs).


Lemma zipWith_len_pres : forall {X Y Z : Type} (f : X -> Y -> Z) (n : nat) 
                                (As : list X) (Bs : list Y),
  length As = n -> length Bs = n -> length (zipWith f As Bs) = n.
Proof. intros. 
       unfold zipWith.
       rewrite map_length.
       rewrite combine_length.
       rewrite H, H0; lia.
Qed.


Lemma zipWith_app_product : forall {X Y Z: Type} (f : X -> Y -> Z) (n : nat) 
                               (l0s l2s : list X) (l1s l3s : list Y),
  length l0s = n -> length l1s = n -> 
  (zipWith f l0s l1s) ++ (zipWith f l2s l3s) = zipWith f (l0s ++ l2s) (l1s ++ l3s).
Proof. induction n as [| n'].
       - intros. destruct l0s; destruct l1s; easy. 
       - intros. destruct l0s; destruct l1s; try easy.
         unfold zipWith in *.
         simpl in *. 
         rewrite <- IHn'; try nia. 
         reflexivity. 
Qed.




Fixpoint first_n (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | S n' => n :: first_n n'
  end.

Lemma first_n_contains : forall (n i : nat),
  i <= n <-> In i (first_n n).
Proof. split.
       - induction n as [| n'].
         * intros. bdestruct (i =? 0). 
           + rewrite H0. simpl. left. easy.
           + apply le_n_0_eq in H. rewrite H in H0. easy.
         * intros. simpl. bdestruct (i =? S n').
           + left. rewrite H0. easy. 
           + right. apply IHn'. 
             apply le_lt_eq_dec in H. destruct H.
             ** apply Nat.lt_succ_r. apply l.
             ** rewrite e in H0. easy.
       - induction n as [| n'].
         * intros [H | F]. 
           + rewrite H. easy.
           + simpl in F. easy.
         * intros. simpl in H. destruct H.
           + rewrite H. easy.
           + apply IHn' in H. 
             apply le_n_S in H. apply le_Sn_le.
             apply H.
Qed.


(* defining switch and many lemmas having to do with switch and nth *)

Fixpoint switch {X : Type} (ls : list X) (x : X) (n : nat) :=
  match ls with
  | [] => []
  | (h :: ls') =>
    match n with
    | 0 => x :: ls'
    | S n' => h :: (switch ls' x n')
    end
  end.

Lemma switch_len : forall {X : Type} (n : nat) (ls : list X) (x : X),
    length (switch ls x n) = length ls. 
Proof. induction n as [| n'].
       - destruct ls. easy. easy.
       - intros. destruct ls. 
         easy. simpl. 
         rewrite IHn'. 
         reflexivity. 
Qed.


Lemma switch_map : forall {X Y : Type} (n : nat) (ls : list X) (x : X) (f : X -> Y),
    map f (switch ls x n) = switch (map f ls) (f x) n.
Proof. induction n as [| n'].
       - intros. destruct ls; easy.
       - intros. destruct ls. easy.
         simpl. rewrite IHn'. easy.
Qed.
         
Lemma switch_base : forall {X : Type} (ls : list X) (x : X),
    ls <> [] -> switch ls x 0 = x :: (skipn 1 ls).
Proof. intros. 
       destruct ls. 
       easy. 
       reflexivity. 
Qed.



Lemma nth_switch_hit : forall {X : Type} (n : nat) (ls : list X) (x def : X),
    n < length ls ->
    nth n (switch ls x n) def = x.
Proof. induction n as [| n'].
       - destruct ls; easy.
       - intros. 
         destruct ls; try easy.
         apply IHn'. 
         simpl in H.
         nia. 
Qed.



Lemma nth_switch_miss : forall {X : Type} (sn n : nat) (ls : list X) (x def : X),
    n <> sn ->
    nth n (switch ls x sn) def = nth n ls def.
Proof. induction sn as [| sn'].
       - destruct ls.
         easy.
         destruct n; easy.
       - intros. 
         destruct n.
         + destruct ls; easy.
         + assert (H' : n <> sn'). { nia. }
           destruct ls.                                   
           easy. simpl.  
           apply IHsn'.
           apply H'.
Qed.


 

Lemma switch_inc_helper : forall {X : Type} (n : nat) (l1 l2 : list X) (x : X),
    length l1 = n -> 
    switch (l1 ++ l2) x n = l1 ++ switch l2 x 0.
Proof. induction n as [| n'].
       - destruct l1. 
         reflexivity. 
         easy.
       - intros. destruct l1.  
         easy. 
         simpl. 
         rewrite <- IHn'.
         reflexivity. 
         simpl in H. 
         injection H. 
         easy. 
Qed.


Lemma switch_inc_helper2 : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch ls x n = (firstn n ls) ++ switch (skipn n ls) x 0.
Proof. intros. 
       assert (H' : switch ls x n = switch (firstn n ls ++ skipn n ls) x n).
       { rewrite (firstn_skipn n ls). reflexivity. }
       rewrite H'.
       rewrite switch_inc_helper.
       reflexivity. 
       rewrite firstn_length_le.
       reflexivity. 
       nia.  
Qed.




Lemma skipn_nil_length : forall {X : Type} (n : nat) (ls : list X),
    skipn n ls = [] -> length ls <= n. 
Proof. intros. 
       rewrite <- (firstn_skipn n ls).
       rewrite H. 
       rewrite <- app_nil_end.
       apply firstn_le_length.
Qed.


Lemma skipskip : forall {X : Type} (ls : list X) (n : nat),
    skipn (S n) ls = skipn 1 (skipn n ls).
Proof. induction ls as [| h].
       - destruct n. easy. easy. 
       - destruct n. easy.  
         assert (H : skipn (S n) (h :: ls) = skipn n ls). 
         { reflexivity. } 
         rewrite H.
         rewrite <- IHls. 
         reflexivity. 
Qed.


Lemma switch_inc_helper3 : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch (skipn n ls) x 0 = [x] ++ (skipn (S n) ls).
Proof. intros. destruct (skipn n ls) as [| h] eqn:E.
       - apply skipn_nil_length in E. nia. 
       - assert (H' : skipn (S n) ls = l).
         { rewrite skipskip. 
           rewrite E.
           reflexivity. }
         rewrite H'.
         reflexivity.
Qed.


Lemma switch_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> switch ls x n = (firstn n ls) ++ [x] ++ (skipn (S n) ls). 
Proof. intros. 
       rewrite switch_inc_helper2.
       rewrite switch_inc_helper3.
       reflexivity. 
       apply H. apply H.
Qed.


Lemma nth_base : forall {X : Type} (ls : list X) (x : X),
    ls <> [] -> ls = (nth 0 ls x) :: (skipn 1 ls).
Proof. intros.
       destruct ls.
       easy. 
       reflexivity. 
Qed.


Lemma nth_helper : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> skipn n ls = [nth n ls x] ++ skipn (S n) ls.
Proof. induction n as [| n']. 
       - destruct ls. easy. easy. 
       - intros. destruct ls. 
         assert (H' : forall (n : nat), S n < 0 -> False). { nia. }
         apply H' in H. easy.
         rewrite skipn_cons.
         assert (H'' : nth (S n') (x0 :: ls) x = nth n' ls x). { easy. }
         rewrite H''.
         rewrite (IHn' ls x). 
         easy. 
         simpl in H. 
         assert (H''' : forall (n m : nat), S m < S n -> m < n). { nia. } 
         apply H''' in H.
         easy.
Qed.
         


Lemma nth_inc : forall {X : Type} (n : nat) (ls : list X) (x : X),
    n < length ls -> ls = (firstn n ls) ++ [nth n ls x] ++ (skipn (S n) ls). 
Proof. intros.
       rewrite <- nth_helper.  
       rewrite (firstn_skipn n ls).
       reflexivity. easy. 
Qed.



Lemma length_change : forall {X : Type} (A B : list X) (x : X),
  2 ^ (length (A ++ [x] ++ B)) = (2 ^ (length A)) * (2 * (2 ^ (length B))).
Proof. intros. 
       do 2 (rewrite app_length).
       simpl. 
       rewrite easy_pow.
       reflexivity. 
Qed.


(* a similar lemma to the one defined by Coq, but better for our purposes *)
Lemma skipn_length' : forall {X : Type} (n : nat) (ls : list X),
    length (skipn (S n) ls) = length ls - n - 1.
Proof. intros. 
       rewrite skipn_length.
       nia. 
Qed.


Lemma firstn_subset : forall {X : Type} (n : nat) (ls : list X),
    firstn n ls ⊆ ls.
Proof. induction n as [| n']. 
       - easy.
       - intros. destruct ls. 
         easy. simpl. 
         unfold subset_gen in *.
         intros. 
         destruct H as [H | H].
         left; easy. 
         right; apply IHn'; apply H.
Qed.

Lemma skipn_subset : forall {X : Type} (n : nat) (ls : list X),
    skipn n ls ⊆ ls.
Proof. induction n as [| n']. 
       - easy.
       - intros. destruct ls. 
         easy. simpl. 
         unfold subset_gen in *.
         intros. 
         right; apply IHn'; apply H.
Qed.


(********************)
(* Other misc stuff *)
(********************)



Definition Phase : Matrix 2 2 := phase_shift (PI / 2).

Definition Phase' : Matrix 2 2 :=
  fun x y => match x, y with
          | 0, 0 => C1
          | 1, 1 => Ci
          | _, _ => C0
          end.

Definition Tgate :=  phase_shift (PI / 4).


Lemma WF_Phase : WF_Matrix Phase. Proof. show_wf. Qed.
Lemma WF_Phase' : WF_Matrix Phase'. Proof. show_wf. Qed.
Lemma WF_Tgate: WF_Matrix Tgate. Proof. show_wf. Qed.
Lemma WF_notc : WF_Matrix notc. Proof. show_wf. Qed.

Lemma WF_ket : forall (x : nat), WF_Matrix (ket x).
Proof. intros x. unfold ket. destruct (x =? 0). show_wf. show_wf. 
Qed. 

Lemma WF_bra : forall (x : nat), WF_Matrix (bra x).
Proof. intros x. unfold bra. destruct (x =? 0). show_wf. show_wf. 
Qed. 


Hint Resolve WF_Phase WF_Phase' WF_Tgate WF_notc WF_ket WF_bra : wf_db.

(* ran into problems with hadamard. Can probably make this more general. *)
Ltac Hhelper :=
   unfold Mmult;
   unfold Csum;
   unfold I;
   simpl;
   C_field_simplify;
   try lca;
   C_field.


(* these allow us to bypass WF requirements in every definition, which get annoying *)
(* we could also just make an axiom saying that all Squares are WF... *)
Axiom Mmult_1_r': forall {n m} (A : Matrix n m),
  A × I n = A.

Axiom Mmult_1_l': forall {n m} (A : Matrix n m),
  I n × A = A.

Axiom kron_1_l' : forall {n m : nat} (A : Matrix n m), 
  I 1 ⊗ A = A.


Lemma big_kron_app : forall {n m} (l1 l2 : list (Matrix n m)),
  ⨂ (l1 ++ l2) = (⨂ l1) ⊗ (⨂ l2).
Proof. induction l1.
       - intros. simpl. rewrite (kron_1_l' (⨂ l2)). easy.
       - intros. simpl. rewrite IHl1. 
         rewrite kron_assoc.
         do 2 (rewrite <- easy_pow).
         rewrite app_length.
         reflexivity.
Qed.


Lemma inverse_is_valid : forall {n} (X X' : Square n) (u v : Vector n),
  X × X' = I n -> X × u = v -> X' × v = u.
Proof. intros. 
       rewrite <- H0.
       rewrite <- Mmult_assoc.
       apply Minv_flip in H.
       rewrite H.
       rewrite Mmult_1_l'.
       reflexivity.
Qed.



(****************************)
(* Proving some indentities *)
(****************************)

Lemma Y_eq_iXZ : σy = Ci .* σx × σz. Proof. lma'. Qed.
Lemma PEqP' : Phase = Phase'.
Proof. lma'. autorewrite with Cexp_db. reflexivity.
Qed.
Lemma H_eq_Hadjoint : hadamard† = hadamard. Proof. lma'. Qed.


Hint Rewrite Y_eq_iXZ PEqP' H_eq_Hadjoint : id_db.

Lemma ItimesIid : I 2 × I 2 = I 2. Proof. lma'. Qed.      
Lemma XtimesXid : σx × σx = I 2. Proof. lma'. Qed.      
Lemma YtimesYid : σy × σy = I 2. Proof. lma'. Qed.
Lemma ZtimesZid : σz × σz = I 2. Proof. lma'. Qed.
Lemma HtimesHid : hadamard × hadamard = I 2. Proof. lma'; Hhelper. Qed.

Hint Resolve ItimesIid XtimesXid YtimesYid ZtimesZid HtimesHid : id_db.

Lemma ZH_eq_HX : σz × hadamard = hadamard × σx. Proof. lma'. Qed.
Lemma XH_eq_HZ : σx × hadamard = hadamard × σz. Proof. lma'. Qed.
Lemma PX_eq_YP : Phase × σx = σy × Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma PZ_eq_ZP : Phase × σz = σz × Phase. Proof. lma'. Qed.

Lemma cnotX1 : cnot × (σx ⊗ I 2) = (σx ⊗ σx) × cnot. Proof. lma'. Qed.
Lemma cnotX2 : cnot × (I 2 ⊗ σx) = (I 2 ⊗ σx) × cnot. Proof. lma'. Qed.
Lemma cnotZ1 : cnot × (σz ⊗ I 2) = (σz ⊗ I 2) × cnot. Proof. lma'. Qed.
Lemma cnotZ2 : cnot × (I 2 ⊗ σz) = (σz ⊗ σz) × cnot. Proof. lma'. Qed.

Hint Resolve ZH_eq_HX XH_eq_HZ PX_eq_YP PZ_eq_ZP cnotX1 cnotX2 cnotZ1 cnotZ2 : id_db.




(************************************************************************)
(* Defining a set of vectors, linear independence, other prelims etc... *)
(************************************************************************)

(* a set of m vectors of dimension n *)
Definition VecSet n m := (Matrix n m).

Definition zero_vec (n : nat) : Vector n := @Zero n 1.

Definition vecs_to_vecSet {n} (vs : list (Vector n)) : VecSet n (length vs) := 
  fun x y => (nth y vs (zero_vec n)) x 0%nat.

Definition get_vec {n m} (i : nat) (S : VecSet n m) : Vector n :=
  fun x y => (if (y =? 0) then S x i else C0).   


Definition get_row {n m} (i : nat) (S : VecSet n m) : Matrix 1 m :=
  fun x y => (if (x =? 0) then S i y else C0).  


Lemma WF_get_vec : forall {n m} (i : nat) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix (get_vec i S). 
Proof. unfold WF_Matrix, get_vec in *.
       intros.
       bdestruct (y =? 0); try lia; try easy.
       apply H.
       destruct H0. 
       left; easy.
       lia. 
Qed.

Lemma WF_get_row : forall {n m} (i : nat) (S : Matrix n m),
  WF_Matrix S -> WF_Matrix (get_row i S). 
Proof. unfold WF_Matrix, get_row in *.
       intros.
       bdestruct (x =? 0); try lia; try easy.
       apply H.
       destruct H0. 
       lia. 
       right; easy.
Qed.


Lemma get_vec_conv : forall {n m} (x y : nat) (S : VecSet n m),
  (get_vec y S) x 0 = S x y.
Proof. intros. unfold get_vec.
       easy.
Qed.


Lemma get_vec_mult : forall {n} (i : nat) (A B : Square n),
  A × (get_vec i B) = get_vec i (A × B).
Proof. intros. unfold get_vec, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0).
       - reflexivity.
       - apply Csum_0. intros.
         apply Cmult_0_r.
Qed.


Lemma det_by_get_vec : forall {n} (A B : Square n),
  (forall i, get_vec i A = get_vec i B) -> A = B.
Proof. intros. prep_matrix_equality.
       rewrite <- get_vec_conv.
       rewrite <- (get_vec_conv _ _ B).
       rewrite H.
       reflexivity.
Qed.


Definition linearly_independent {n m} (S : VecSet n m) : Prop :=
  forall (a : Vector m), WF_Matrix a -> @Mmult n m 1 S a = Zero -> a = Zero.


Definition e_i {n : nat} (i : nat) : Vector n :=
  fun x y => (if (x =? i) && (x <? n) && (y =? 0) then C1 else C0). 

Lemma WF_e_i : forall {n : nat} (i : nat),
  WF_Matrix (@e_i n i).
Proof. unfold WF_Matrix, e_i.
       intros; destruct H as [H | H].
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
       bdestruct (x =? i); bdestruct (x <? n); bdestruct (y =? 0); try lia; easy.
Qed.

Lemma I_is_eis : forall {n} (i : nat),
  get_vec i (I n) = e_i i. 
Proof. intros. unfold get_vec, e_i.
       prep_matrix_equality. 
       bdestruct (x =? i).
       - bdestruct (y =? 0).
         rewrite H. unfold I. simpl. 
         assert (H1 : (i =? i) && (i <? n) = (i <? n) && true).
         { bdestruct (i =? i). apply andb_comm. easy. }
         rewrite H1. reflexivity.
         simpl; rewrite andb_false_r; reflexivity.
       - simpl. destruct (y =? 0). unfold I.
         bdestruct (x =? i). easy.
         reflexivity. reflexivity.
Qed. 

Lemma invertible_implies_linind : forall {n} (X : Square n),
  (exists X', X' × X = I n) -> linearly_independent X.
Proof. intros. destruct H.
       unfold linearly_independent. intros.
       rewrite <- (Mmult_1_l' a); 
       rewrite <- H.
       rewrite Mmult_assoc, H1.
       rewrite Mmult_0_r.
       reflexivity.
Qed.


Lemma zero_vec_not_lin_indep : forall {n m} (S : VecSet n m) (i : nat),
  i < m -> (get_vec i S) = Zero -> ~ (linearly_independent S).
Proof. intros.
       unfold not, linearly_independent in *; intros. 
       assert (H' : @e_i m i = Zero). 
       apply H1; try apply WF_e_i.
       prep_matrix_equality.
       unfold Mmult, Zero.
       apply Csum_0_bounded.
       intros. unfold e_i.
       assert (H'' : (get_vec i S) x y = C0).
       { rewrite H0. easy. }
       unfold get_vec in H''. 
       bdestruct (x0 =? i); bdestruct (x0 <? m); bdestruct (y =? 0); try lia; try easy.
       rewrite H3, H''; lca. 
       all : simpl; try lca. 
       apply R1_neq_R0.
       assert (H'' : (@e_i m i) i 0 = C0).
       { rewrite H'. easy. }
       unfold e_i in H''.
       bdestruct (i =? i); bdestruct (i <? m); bdestruct (0 =? 0); try lia. 
       simpl in H''.
       assert (H1' : fst C1 = fst C0). 
       rewrite H''; easy. 
       apply H1'.
Qed.


Lemma lin_indep_nonzero_cols : forall {n m} (S : Matrix n m),
  linearly_independent S -> (forall i, i < m -> (get_vec i S) <> Zero). 
Proof. intros. unfold not. intros. 
       apply (zero_vec_not_lin_indep S i) in H0.
       apply H0; apply H.
       apply H1. 
Qed.


Lemma matrix_by_basis : forall {n} (X : Square n),
  WF_Matrix X ->  
  (forall i : nat, get_vec i X = X × e_i i).
Proof. intros. unfold get_vec, e_i, Mmult.
       prep_matrix_equality.
       bdestruct (y =? 0). 
       - bdestruct (i <? n).
         + rewrite (Csum_unique (X x i) _ n). 
           reflexivity. 
           exists i. split.
           apply H1. split. 
           apply Nat.ltb_lt in H1. rewrite H1. 
           bdestruct (i =? i). simpl.
           rewrite Cmult_1_r. reflexivity.
           easy.
           intros.
           bdestruct (x' =? i).
           rewrite H3 in H2; easy.
           simpl.
           rewrite Cmult_0_r. reflexivity.
         + rewrite Csum_0.
           unfold WF_Matrix in H; rewrite H.
           reflexivity. right. apply H1. 
           intros. bdestruct (x0 =? i).
           rewrite H2. bdestruct (i <? n).
           nia. simpl. rewrite Cmult_0_r.
           reflexivity.
           simpl. rewrite Cmult_0_r.
           reflexivity.
       - rewrite Csum_0. reflexivity.
         intros. rewrite andb_false_r. 
         rewrite Cmult_0_r. reflexivity.
Qed.         


Definition orthogonal {n m} (S : VecSet n m) : Prop := 
  forall i j, i <> j -> inner_product (get_vec i S) (get_vec j S) = C0.


Definition orthonormal {n m} (S : VecSet n m) : Prop :=
  orthogonal S /\ (forall (i : nat), i < m -> norm (get_vec i S) = 1%R).


Lemma inner_product_is_mult : forall {n} (i j : nat) (S : Square n),
  inner_product (get_vec i S) (get_vec j S) = ((S†) × S) i j.
Proof. intros. unfold inner_product, get_vec, Mmult, adjoint.
       apply Csum_eq.
       apply functional_extensionality; intros. simpl.
       reflexivity.
Qed.



Lemma inner_product_comm_conj : forall {n} (v u : Vector n), 
  inner_product v u = Cconj (inner_product u v).
Proof. intros. 
       unfold inner_product.
       assert (H' : forall A : Matrix 1 1, (A 0 0) ^* = A† 0 0).
       { unfold adjoint, Cconj. 
         easy. }
       rewrite H'. 
       rewrite Mmult_adjoint, adjoint_involutive.
       easy.
Qed.

(************************************************)
(* Defining different types of matrix reduction *)
(************************************************)


Definition reduce_row {n m} (A : Matrix n m) (row : nat) : Matrix (n - 1) m :=
  fun x y => if x <? row
             then A x y
             else A (1 + x) y.

Definition reduce_col {n m} (A : Matrix n m) (col : nat) : Matrix n (m - 1) :=
  fun x y => if y <? col
             then A x y
             else A x (1 + y).


Lemma WF_reduce_row : forall {n m} (row : nat) (A : Matrix n m),
  row < n -> WF_Matrix A -> WF_Matrix (reduce_row A row).
Proof. unfold WF_Matrix, reduce_row. intros. 
       bdestruct (x <? row). 
       - destruct H1 as [H1 | H1].
         + assert (nibzo : forall (a b c : nat), a < b -> b < c -> 1 + a < c).
           { lia. }
           apply (nibzo x row n) in H2.
           simpl in H2. lia. apply H.
         + apply H0; auto.
       - apply H0. destruct H1. 
         + left. simpl. lia.
         + right. apply H1. 
Qed.


Lemma WF_reduce_col : forall {n m} (col : nat) (A : Matrix n m),
  col < m -> WF_Matrix A -> WF_Matrix (reduce_col A col).
Proof. unfold WF_Matrix, reduce_col. intros. 
       bdestruct (y <? col). 
       - destruct H1 as [H1 | H1].   
         + apply H0; auto. 
         + assert (nibzo : forall (a b c : nat), a < b -> b < c -> 1 + a < c).
           { lia. }
           apply (nibzo y col m) in H2.
           simpl in H2. lia. apply H.
       - apply H0. destruct H1.
         + left. apply H1. 
         + right. simpl. lia. 
Qed.


Lemma get_vec_reduce_col : forall {n m} (i col : nat) (A : Matrix n m),
  i < col -> get_vec i (reduce_col A col) = get_vec i A.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, reduce_col.
       bdestruct (i <? col); try lia; easy.
Qed.

(* more specific form for vectors *)
Definition reduce_vecn {n} (v : Vector n) : Vector (n - 1) :=
  fun x y => if x <? (n - 1)
             then v x y
             else v (1 + x) y.

Lemma rvn_is_rr_n : forall {n : nat} (v : Vector n),
  reduce_vecn v = reduce_row v (n - 1).
Proof. intros.
       prep_matrix_equality.
       unfold reduce_row, reduce_vecn.
       easy.
Qed.

Lemma WF_reduce_vecn : forall {n} (v : Vector n),
  n <> 0 -> WF_Matrix v -> WF_Matrix (reduce_vecn v).
Proof. intros. 
       rewrite rvn_is_rr_n.
       apply WF_reduce_row; try lia; try easy. 
Qed.


(* More specific form for squares *)
Definition reduce {n} (A : Square n) (row col : nat) : Square (n - 1) :=
  fun x y => (if x <? row 
              then (if y <? col 
                    then A x y
                    else A x (1+y))
              else (if y <? col 
                    then A (1+x) y
                    else A (1+x) (1+y))).


Lemma reduce_is_redrow_redcol : forall {n} (A : Square n) (row col : nat),
  reduce A row col = reduce_col (reduce_row A row) col.
Proof. intros. 
       prep_matrix_equality.
       unfold reduce, reduce_col, reduce_row.
       bdestruct (x <? row); bdestruct (y <? col); try easy.
Qed. 


Lemma WF_reduce : forall {n} (A : Square n) (row col : nat),
  n <> 0 -> row < n -> col < n -> WF_Matrix A -> WF_Matrix (reduce A row col).
Proof. intros.
       rewrite reduce_is_redrow_redcol.
       apply WF_reduce_col; try easy.
       apply WF_reduce_row; try easy.
Qed.

     
(* We can now show that matrix_equivalence is decidable *)
Lemma vec_equiv_dec : forall {n : nat} (A B : Vector n), 
    { mat_equiv2 A B } + { ~ (mat_equiv2 A B) }.
Proof. induction n as [| n'].
       - left; easy.
       - intros. destruct (IHn' (reduce_vecn A) (reduce_vecn B)).
         + destruct (Ceq_dec (A n' 0) (B n' 0)).
           * left. 
             unfold mat_equiv2 in *.
             intros.
             apply easy_ltb4 in H.
             destruct H.
             rewrite H.
             destruct j.
             apply e. lia.
             apply (m i j) in H0.
             unfold reduce_vecn in H0.
             assert (H' : i <? S n' - 1 = true).
             { apply leb_correct. lia. }
             rewrite H' in H0.
             apply H0. lia. 
           * right. unfold not. 
             intros. unfold mat_equiv2 in H.
             apply n. apply H; lia. 
         + right. 
           unfold not in *. 
           intros. apply n.
           unfold mat_equiv2 in *.
           intros. unfold reduce_vecn.
           assert (H' : i <? S n' - 1 = true).
           { apply leb_correct. lia. }
           rewrite H'. 
           apply H; lia. 
Qed.


Lemma mat_equiv_dec : forall {n m : nat} (A B : Matrix n m), 
    { mat_equiv2 A B } + { ~ (mat_equiv2 A B) }.
Proof. induction m as [| m']. intros.  
       - left. easy.
       - intros. destruct (IHm' (reduce_col A m') (reduce_col B m')).
         + destruct (vec_equiv_dec (get_vec m' A) (get_vec m' B)).
           * left. 
             unfold mat_equiv2 in *.
             intros. 
             apply easy_ltb4 in H0.
             destruct H0.
             ++ apply (m0 i 0) in H.
                do 2 rewrite get_vec_conv in H.
                rewrite H0. easy. lia. 
             ++ apply (m i j) in H.
                unfold reduce_col in H.
                bdestruct (j <? m'); try lia; try easy.
                lia. 
           * right. 
             unfold not, mat_equiv2 in *.
             intros. apply n0.
             intros. 
             destruct j; try easy.
             do 2 rewrite get_vec_conv.
             apply H; lia.
         + right. 
           unfold not, mat_equiv2, reduce_col in *.
           intros. apply n0. 
           intros. 
           bdestruct (j <? m'); try lia.
           apply H; lia.            
Qed.



(*******************************************************************)
(* Defining Row operations and proving things about row operations *)
(*******************************************************************)



Definition col_swap {n m : nat} (S : Matrix n m) (x y : nat) : Matrix n m := 
  fun i j => if (j =? x) 
             then S i y
             else if (j =? y) 
                  then S i x
                  else S i j.

Definition row_swap {n m : nat} (S : Matrix n m) (x y : nat) : Matrix n m := 
  fun i j => if (i =? x) 
             then S y j
             else if (i =? y) 
                  then S x j
                  else S i j.

Definition col_scale {n m : nat} (S : Matrix n m) (col : nat) (a : C) : Matrix n m := 
  fun i j => if (j =? col) 
             then (a * S i j)%C
             else S i j.

Definition row_scale {n m : nat} (S : Matrix n m) (row : nat) (a : C) : Matrix n m := 
  fun i j => if (i =? row) 
             then (a * S i j)%C
             else S i j.

(* adding one column to another *)
Definition col_add {n m : nat} (S : Matrix n m) (col to_add : nat) (a : C) : Matrix n m := 
  fun i j => if (j =? col) 
             then (S i j + a * S i to_add)%C
             else S i j.

(* adding one row to another *)
Definition row_add {n m : nat} (S : Matrix n m) (row to_add : nat) (a : C) : Matrix n m := 
  fun i j => if (i =? row) 
             then (S i j + a * S to_add j)%C
             else S i j.


Lemma WF_col_swap : forall {n m : nat} (S : Matrix n m) (x y : nat),
  x < m -> y < m -> WF_Matrix S -> WF_Matrix (col_swap S x y).
Proof. unfold WF_Matrix, col_swap in *.
       intros. 
       bdestruct (y0 =? x); bdestruct (y0 =? y); destruct H2; try lia. 
       all : apply H1; try (left; apply H2).
       auto.
Qed.

Lemma WF_row_swap : forall {n m : nat} (S : Matrix n m) (x y : nat),
  x < n -> y < n -> WF_Matrix S -> WF_Matrix (row_swap S x y).
Proof. unfold WF_Matrix, row_swap in *.
       intros. 
       bdestruct (x0 =? x); bdestruct (x0 =? y); destruct H2; try lia. 
       all : apply H1; try (right; apply H2).
       auto.
Qed.

Lemma WF_col_scale : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  WF_Matrix S -> WF_Matrix (col_scale S x a).
Proof. unfold WF_Matrix, col_scale in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r.
       bdestruct (y =? x); easy.
Qed.

Lemma WF_row_scale : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  WF_Matrix S -> WF_Matrix (row_scale S x a).
Proof. unfold WF_Matrix, row_scale in *.
       intros. 
       apply H in H0.
       rewrite H0.
       rewrite Cmult_0_r.
       bdestruct (x0 =? x); easy.
Qed.


Lemma WF_col_add : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x < m -> WF_Matrix S -> WF_Matrix (col_add S x y a).
Proof. unfold WF_Matrix, col_add in *.
       intros.
       bdestruct (y0 =? x); destruct H1; try lia. 
       do 2 (rewrite H0; auto). lca. 
       all : apply H0; auto.
Qed.


Lemma WF_row_add : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x < n -> WF_Matrix S -> WF_Matrix (row_add S x y a).
Proof. unfold WF_Matrix, row_add in *.
       intros.
       bdestruct (x0 =? x); destruct H1; try lia. 
       do 2 (rewrite H0; auto). lca. 
       all : apply H0; auto.
Qed.


Lemma col_swap_same : forall {n m : nat} (S : Matrix n m) (x : nat),
  col_swap S x x = S.
Proof. intros. 
       unfold col_swap. 
       prep_matrix_equality. 
       bdestruct (y =? x); try easy.
       rewrite H; easy.
Qed. 


Lemma row_swap_same : forall {n m : nat} (S : Matrix n m) (x : nat),
  row_swap S x x = S.
Proof. intros. 
       unfold row_swap. 
       prep_matrix_equality. 
       bdestruct (x0 =? x); try easy.
       rewrite H; easy.
Qed. 

Lemma col_swap_diff_order : forall {n m : nat} (S : Matrix n m) (x y : nat),
  col_swap S x y = col_swap S y x.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y0 =? x); bdestruct (y0 =? y); try easy.
       rewrite <- H, <- H0; easy.
Qed.

Lemma row_swap_diff_order : forall {n m : nat} (S : Matrix n m) (x y : nat),
  row_swap S x y = row_swap S y x.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); try easy.
       rewrite <- H, <- H0; easy.
Qed.


Lemma col_swap_inv : forall {n m : nat} (S : Matrix n m) (x y : nat),
  S = col_swap (col_swap S x y) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap.
       bdestruct (y0 =? x); bdestruct (y0 =? y); 
         bdestruct (y =? x); bdestruct (x =? x); bdestruct (y =? y); 
         try easy. 
       all : (try rewrite H; try rewrite H0; try rewrite H1; easy).
Qed.

Lemma row_swap_inv : forall {n m : nat} (S : Matrix n m) (x y : nat),
  S = row_swap (row_swap S x y) x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); 
         bdestruct (y =? x); bdestruct (x =? x); bdestruct (y =? y); 
         try easy. 
       all : (try rewrite H; try rewrite H0; try rewrite H1; easy).
Qed.


Lemma col_swap_get_vec : forall {n m : nat} (S : Matrix n m) (x y : nat),
  get_vec y S = get_vec x (col_swap S x y).
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, col_swap. 
       bdestruct (x =? x); bdestruct (x =? y); try lia; try easy.
Qed.


Lemma col_scale_inv : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  a <> C0 -> S = col_scale (col_scale S x a) x (/ a).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_scale.
       bdestruct (y =? x); try easy.
       rewrite Cmult_assoc.
       rewrite Cinv_l; try lca; easy. 
Qed.


Lemma row_scale_inv : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  a <> C0 -> S = row_scale (row_scale S x a) x (/ a).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_scale.
       bdestruct (x0 =? x); try easy.
       rewrite Cmult_assoc.
       rewrite Cinv_l; try lca; easy. 
Qed.



Lemma col_add_double : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  col_add S x x a = col_scale S x (C1 + a).
Proof. intros. 
       prep_matrix_equality. 
       unfold col_add, col_scale. 
       bdestruct (y =? x).
       - rewrite H; lca. 
       - easy.
Qed.

Lemma row_add_double : forall {n m : nat} (S : Matrix n m) (x : nat) (a : C),
  row_add S x x a = row_scale S x (C1 + a).
Proof. intros. 
       prep_matrix_equality. 
       unfold row_add, row_scale. 
       bdestruct (x0 =? x).
       - rewrite H; lca. 
       - easy.
Qed.

Lemma col_add_swap : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  col_swap (col_add S x y a) x y = col_add (col_swap S x y) y x a. 
Proof. intros. 
       prep_matrix_equality. 
       unfold col_swap, col_add.
       bdestruct (y0 =? x); bdestruct (y =? x);
         bdestruct (y0 =? y); bdestruct (x =? x); try lia; easy. 
Qed.
       
Lemma row_add_swap : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  row_swap (row_add S x y a) x y = row_add (row_swap S x y) y x a. 
Proof. intros. 
       prep_matrix_equality. 
       unfold row_swap, row_add.
       bdestruct (x0 =? x); bdestruct (y =? x);
         bdestruct (x0 =? y); bdestruct (x =? x); try lia; easy. 
Qed.


Lemma col_add_inv : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x <> y -> S = col_add (col_add S x y a) x y (-a).
Proof. intros. 
       prep_matrix_equality.
       unfold col_add.
       bdestruct (y0 =? x); bdestruct (y =? x); try lia. 
       lca. easy. 
Qed.

Lemma row_add_inv : forall {n m : nat} (S : Matrix n m) (x y : nat) (a : C),
  x <> y -> S = row_add (row_add S x y a) x y (-a).
Proof. intros. 
       prep_matrix_equality.
       unfold row_add.
       bdestruct (x0 =? x); bdestruct (y =? x); try lia. 
       lca. easy. 
Qed.


Lemma swap_preserves_mul_lt : forall {n m o} (A : Matrix n m) (B : Matrix m o) (x y : nat),
  x < y -> x < m -> y < m -> A × B = (col_swap A x y) × (row_swap B x y).
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       bdestruct (x <? m); try lia.
       rewrite (le_plus_minus x m); try lia.
       do 2 rewrite Csum_sum. 
       apply Csum_simplify. 
       apply Csum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x1 =? x); bdestruct (x1 =? y); try lia; try easy.   
       destruct (m - x) as [| x'] eqn:E; try lia. 
       do 2 rewrite <- Csum_extend_l.
       rewrite Cplus_comm.
       rewrite (Cplus_comm (col_swap A x y x0 (x + 0)%nat * row_swap B x y (x + 0)%nat y0)%C _).
       bdestruct ((y - x - 1) <? x'); try lia.  
       rewrite (le_plus_minus (y - x - 1) x'); try lia. 
       do 2 rewrite Csum_sum.
       do 2 rewrite <- Cplus_assoc.
       apply Csum_simplify. 
       apply Csum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x + S x1 =? x); bdestruct (x + S x1 =? y); try lia; try easy. 
       destruct (x' - (y - x - 1)) as [| x''] eqn:E1; try lia. 
       do 2 rewrite <- Csum_extend_l.
       rewrite Cplus_comm.
       rewrite (Cplus_comm _ (col_swap A x y x0 (x + 0)%nat * row_swap B x y (x + 0)%nat y0)%C). 
       do 2 rewrite Cplus_assoc.
       apply Csum_simplify.
       do 2 rewrite <- plus_n_O. 
       unfold col_swap, row_swap.
       bdestruct (x + S (y - x - 1) =? x); bdestruct (x + S (y - x - 1) =? y); 
         bdestruct (x =? x); try lia.
       rewrite H5. lca. 
       apply Csum_eq_bounded.
       intros. 
       unfold col_swap, row_swap.
       bdestruct (x + S (y - x - 1 + S x1) =? x); 
         bdestruct (x + S (y - x - 1 + S x1) =? y); try lia; try easy.
Qed.           


Lemma swap_preserves_mul : forall {n m o} (A : Matrix n m) (B : Matrix m o) (x y : nat),
  x < m -> y < m -> A × B = (col_swap A x y) × (row_swap B x y).
Proof. intros. bdestruct (x <? y).
       - apply swap_preserves_mul_lt; easy.
       - destruct H1.
         + rewrite col_swap_same, row_swap_same; easy.
         + rewrite col_swap_diff_order, row_swap_diff_order. 
           apply swap_preserves_mul_lt; lia.
Qed.


Lemma scale_preserves_mul : forall {n m o} (A : Matrix n m) (B : Matrix m o) (x : nat) (a : C),
  A × (row_scale B x a) = (col_scale A x a) × B.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult. 
       apply Csum_eq_bounded.
       intros. 
       unfold col_scale, row_scale.
       bdestruct (x1 =? x).
       - rewrite Cmult_assoc.
         lca. 
       - reflexivity. 
Qed.        




Lemma col_add_preserves_mul_lt : forall {n m o} (A : Matrix n m) (B : Matrix m o) 
                                                (x y : nat) (a : C),
   x < y -> x < m -> y < m -> A × (row_add B y x a) = (col_add A x y a) × B.
Proof. intros.  
       prep_matrix_equality. 
       unfold Mmult.  
       bdestruct (x <? m); try lia.
       rewrite (le_plus_minus x m); try lia.       
       do 2 rewrite Csum_sum.
       apply Csum_simplify. 
       apply Csum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x1 =? y); bdestruct (x1 =? x); try lia; easy. 
       destruct (m - x) as [| x'] eqn:E; try lia. 
       do 2 rewrite <- Csum_extend_l.
       rewrite Cplus_comm. 
       rewrite (Cplus_comm (col_add A x y a x0 (x + 0)%nat * B (x + 0)%nat y0)%C _).
       bdestruct ((y - x - 1) <? x'); try lia.  
       rewrite (le_plus_minus (y - x - 1) x'); try lia. 
       do 2 rewrite Csum_sum.
       do 2 rewrite <- Cplus_assoc.
       apply Csum_simplify. 
       apply Csum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x + S x1 =? y); bdestruct (x + S x1 =? x); try lia; easy. 
       destruct (x' - (y - x - 1)) as [| x''] eqn:E1; try lia. 
       do 2 rewrite <- Csum_extend_l.
       rewrite Cplus_comm. 
       rewrite (Cplus_comm _ (col_add A x y a x0 (x + 0)%nat * B (x + 0)%nat y0)%C).
       do 2 rewrite Cplus_assoc.
       apply Csum_simplify. 
       unfold row_add, col_add.
       do 2 rewrite <- plus_n_O.
       bdestruct (x =? y); bdestruct (x =? x); 
         bdestruct (x + S (y - x - 1) =? y); bdestruct (x + S (y - x - 1) =? x); try lia. 
       rewrite H6. lca. 
       apply Csum_eq_bounded.
       intros. 
       unfold row_add, col_add.
       bdestruct (x + S (y - x - 1 + S x1) =? y); 
         bdestruct (x + S (y - x - 1 + S x1) =? x); try lia; easy. 
Qed.

Lemma col_add_preserves_mul : forall {n m o} (A : Matrix n m) (B : Matrix m o) 
                                             (x y : nat) (a : C),
   x < m -> y < m -> A × (row_add B y x a) = (col_add A x y a) × B.
Proof. intros. bdestruct (x <? y).
       - apply col_add_preserves_mul_lt; easy.
       - destruct H1.
         + rewrite col_add_double, row_add_double. 
           apply scale_preserves_mul.
         + rewrite (swap_preserves_mul A _ y (S m0)); try easy.
           rewrite (swap_preserves_mul _ B (S m0) y); try easy.
           rewrite col_add_swap.
           rewrite row_add_swap.
           rewrite row_swap_diff_order.
           rewrite col_swap_diff_order.
           apply col_add_preserves_mul_lt; lia. 
Qed.


Lemma lin_indep_swap : forall {n m} (S : Matrix n m) (x y : nat),
  x < m -> y < m -> linearly_independent S -> linearly_independent (col_swap S x y).
Proof. intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite (row_swap_inv a x y) in H3.
       rewrite <- (swap_preserves_mul S (row_swap a x y) x y) in H3; try easy.
       apply H1 in H3.
       rewrite (row_swap_inv a x y).
       rewrite H3.
       prep_matrix_equality.
       unfold row_swap.
       bdestruct (x0 =? x); bdestruct (x0 =? y); easy.
       apply WF_row_swap; easy.
Qed.


Lemma lin_indep_scale : forall {n m} (S : Matrix n m) (x : nat) (c : C),
  c <> C0 -> linearly_independent S -> linearly_independent (col_scale S x c).
Proof. intros. 
       unfold linearly_independent in *.
       intros. 
       rewrite <- scale_preserves_mul in H2.
       apply H0 in H2.
       rewrite (row_scale_inv _ x c); try easy.
       rewrite H2.
       prep_matrix_equality. 
       unfold row_scale.
       bdestruct (x0 =? x);
       lca. 
       apply WF_row_scale; easy.
Qed.


Lemma lin_indep_add : forall {n m} (S : Matrix n m) (x y : nat) (c : C),
  x <> y -> x < m -> y < m -> linearly_independent S -> linearly_independent (col_add S x y c).
Proof. intros.
       unfold linearly_independent in *.
       intros. 
       rewrite <- col_add_preserves_mul in H4; try easy.
       apply H2 in H4.
       rewrite (row_add_inv a y x c); try lia.
       rewrite H4.
       prep_matrix_equality. 
       unfold row_add.
       bdestruct (x0 =? y);
       lca. 
       apply WF_row_add; easy.
Qed.


(************************)
(* generalizing col_add *)
(************************)


Definition gen_new_vec (n m size : nat) (S : Matrix n m) (as' : Vector size) : Vector n :=
  Msum size (fun i => (as' i 0) .* (get_vec i S)).


Lemma WF_gen_new_vec : forall {n m} (size : nat) (S : Matrix n m) (as' : Vector size),
  WF_Matrix S -> WF_Matrix (gen_new_vec n m size S as').
Proof. intros.
       unfold gen_new_vec.
       apply WF_Msum; intros. 
       apply WF_scale. 
       unfold get_vec, WF_Matrix in *; intros. 
       destruct H1.
       - rewrite H; auto.
         bdestruct (y =? 0); easy. 
       - bdestruct (y =? 0); try lia; try easy. 
Qed.


Definition col_add_many {n m} (col size : nat) (as' : Vector size) (S : Matrix n m) : Matrix n m :=
  fun i j => if (j =? col) 
             then (S i j + (gen_new_vec n m size S as') i 0)%C
             else S i j.

Lemma WF_col_add_many : forall {n m} (col size : nat) (as' : Vector size) (S : Matrix n m),
  col < m -> size < m -> WF_Matrix S -> WF_Matrix (col_add_many col size as' S).
Proof. unfold WF_Matrix, col_add_many.
       intros. 
       bdestruct (y =? col).
       assert (H4 := (WF_gen_new_vec size S as')).
       rewrite H4, H1; try easy.
       lca. destruct H2; lia. 
       rewrite H1; easy.
Qed.


Lemma gnv_iterated_add : forall (n m col size : nat) (T : Matrix n m) (as' : Vector (S size)),
  col < m -> S size < m -> size <> col ->
  col_add_many col (S size) as' T = 
  col_add (col_add_many col size (reduce_vecn as') T) col size (as' size 0).
Proof. intros. 
       unfold col_add_many, col_add.
       prep_matrix_equality.
       bdestruct (y =? col); try easy.
       bdestruct (size =? col); try lia.
       unfold gen_new_vec.
       simpl.
       rewrite <- Cplus_assoc.
       apply Csum_simplify; try easy.
       unfold Mplus.
       apply Csum_simplify. 
       do 2 rewrite Msum_Csum. 
       apply Csum_eq_bounded.
       intros. 
       unfold scale. 
       unfold reduce_vecn.
       bdestruct (x0 <? S size - 1); try lia; easy.
       unfold scale.
       rewrite get_vec_conv.
       easy.
Qed.




Lemma lin_indep_col_add_many : forall (n m col size : nat) (T : Matrix n m) (as' : Vector size),
  size <= col -> col < m -> linearly_independent T -> 
  linearly_independent (col_add_many col size as' T).
Proof. induction size.
       - intros. 
         assert (H3 : col_add_many col 0 as' T = T).
         { unfold col_add_many.
           prep_matrix_equality.
           bdestruct (y =? col); try easy.
           unfold gen_new_vec.
           simpl. lca. }
         rewrite H3; easy.
       - intros. 
         rewrite gnv_iterated_add; try lia.
         apply lin_indep_add; try lia. 
         apply IHsize; try lia; easy.
Qed.


(**********************************************************************)
(* Defining "commuter" matrices which will be used to prove Minv_flip *)
(**********************************************************************)

Definition commuter {n} (A : Square n) : Prop := 
  forall B, A × B = B × A.










(***********************************************************)
(* Defining and proving lemmas relating to the determinant *)
(***********************************************************)


Fixpoint parity (n : nat) : C := 
  match n with 
  | 0 => C1 
  | S 0 => -C1
  | S (S n) => parity n
  end. 


Fixpoint Determinant (n : nat) (A : Square n) : C :=
  match n with 
  | 0 => C1
  | S 0 => A 0 0
  | S n' => (Csum (fun i => (parity i) * (A i 0) * (Determinant n' (reduce A i 0)))%C n)
  end.


Lemma Det_I1_1 : Determinant 1 (I 1) = C1.
Proof. easy. Qed.

Lemma Det_I2_1 : Determinant 2 (I 2) = C1.
Proof. simpl. unfold reduce. lca. Qed.

Lemma Det_I3_1 : Determinant 3 (I 3) = C1.
Proof. simpl. unfold reduce. lca. Qed.



Definition M22 : Square 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | _ => C0
  end.


Compute Determinant 2 M22.

Lemma Det_M22 : (Determinant 2 M22) = (Copp (3%R,0%R))%C.
Proof. lca. Qed.


Lemma col_scale_reduce_before : forall {n : nat} (T : Square n) (x y col : nat) (a : C),
  y < col -> reduce (col_scale T col a) x y = col_scale (reduce T x y) (col - 1) a.
Proof. intros. 
       prep_matrix_equality. 
       destruct col; try lia. 
       rewrite easy_sub7. 
       unfold reduce, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y); bdestruct (y0 =? S col);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? S col); try lia; easy. 
Qed.


Lemma col_scale_reduce_same : forall {n : nat} (T : Square n) (x y col : nat) (a : C),
  y = col -> reduce (col_scale T col a) x y = reduce T x y.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.


Lemma col_scale_reduce_after : forall {n : nat} (T : Square n) (x y col : nat) (a : C),
  y > col -> reduce (col_scale T col a) x y = col_scale (reduce T x y) col a.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_scale. 
       bdestruct (x0 <? x); bdestruct (y0 <? y);
         bdestruct (y0 =? col); bdestruct (1 + y0 =? col); try lia; easy. 
Qed.


Lemma Determinant_scale : forall {n} (A : Square n) (c : C) (col : nat),
  col < n -> Determinant n (col_scale A col c) = (c * Determinant n A)%C.
Proof. induction n.
       + intros. easy.
       + intros. simpl.  
         destruct n. 
         - simpl. unfold col_scale. 
           bdestruct (0 =? col); try lia; easy.
         - rewrite Cmult_plus_distr_l.
           apply Csum_simplify.
           * rewrite Csum_mult_l.
             apply Csum_eq_bounded.
             intros. 
             destruct col. 
             rewrite col_scale_reduce_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_reduce_before; try lia.
             rewrite easy_sub7.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca.
           * destruct col. 
             rewrite col_scale_reduce_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_reduce_before; try lia.
             rewrite easy_sub7.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca. 
Qed.




(************************************)
(* Lemmas relating to forming bases *)
(************************************)



Lemma last_zero_simplification : forall {n : nat} (v : Vector n),
  WF_Matrix v -> v (n - 1) 0 = C0 -> v = reduce_vecn v.
Proof. intros. unfold reduce_vecn.
       prep_matrix_equality.
       bdestruct (x <? (n - 1)).
       - easy.
       - unfold WF_Matrix in H.
         destruct H1.
         + destruct y. 
           * rewrite H0, H. reflexivity.
             left. nia. 
           * rewrite H. rewrite H. reflexivity.
             right; nia. right; nia.
         + rewrite H. rewrite H. reflexivity.
           left. nia. left. nia.
Qed.


Lemma zero_reduce : forall {n : nat} (v : Vector (S n)) (x : nat),
  WF_Matrix v -> (v = Zero <-> (reduce_row v x) = Zero /\ v x 0 = C0).
Proof. intros. split.    
       - intros. rewrite H0. split.
         + prep_matrix_equality. unfold reduce_row. 
           bdestruct (x0 <? x); easy. 
         + easy.
       - intros [H0 H1].
         prep_matrix_equality.
         unfold Zero.
         bdestruct (x0 =? x).
         + rewrite H2. 
           destruct y; try easy.          
           apply H; lia.
         + bdestruct (x0 <? x). 
           * assert (H' : (reduce_row v x) x0 y = C0). 
             { rewrite H0. easy. }
             unfold reduce_row in H'.
             bdestruct (x0 <? x); try lia; try easy.
           * assert (H' : x0 > x). { lia. }
             destruct x0; try lia. 
             assert (H'' : (reduce_row v x) x0 y = C0). 
             { rewrite H0. easy. }
             unfold reduce_row in H''.
             bdestruct (x0 <? x); try lia. 
             rewrite <- H''. easy.
Qed.


  

Lemma nonzero_vec_nonzero_elem : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> exists x, v x 0 <> C0.
Proof. induction n as [| n']. 
       - intros. 
         unfold not in H0.
         assert (H' : v = Zero).
         { prep_matrix_equality.
           unfold Zero.
           unfold WF_Matrix in H.
           apply H.
           left. lia. }
         apply H0 in H'.
         easy.
       - intros.   
         destruct (Ceq_dec (v n' 0) C0). 
         + destruct (vec_equiv_dec (reduce_row v n') Zero).
           * assert (H' : WF_Matrix v). { easy. }
             apply (zero_reduce _ n') in H'.
             destruct H'.
             assert (H' : v = Zero). 
             { apply H2.
               split. 
               apply mat_equiv_eq.
               apply WF_reduce_row.
               lia. 
               apply H.
               easy.
               apply mat_equivs_equivalent; easy.
               apply e. }
             easy.             
           * assert (H' : WF_Matrix (reduce_row v n')). 
             { apply WF_reduce_row.
               lia. apply H. }
             assert (H'' : exists x, (reduce_row v n') x 0 <> C0).
             { apply IHn'.
               rewrite easy_sub7 in *.
               apply H'. unfold not. intros. apply n. 
               rewrite H1. easy. }
             destruct H''. 
             exists x. 
             rewrite (last_zero_simplification v).
             rewrite rvn_is_rr_n.
             rewrite easy_sub7.
             apply H1. apply H. 
             rewrite easy_sub7.
             apply e.
         + exists n'. 
           apply n.
Qed.



Definition form_basis {n} (v : Vector n) (non_zero : nat) : Matrix n n :=
  fun x y => if (y =? non_zero) 
             then (v x 0)
             else (@e_i n y x 0).


Lemma WF_form_basis : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> x < n -> WF_Matrix (form_basis v x).
Proof. unfold WF_Matrix, form_basis, e_i. 
       intros. 
       bdestruct (y =? x).
       apply H.
       destruct H1; auto; lia.
       bdestruct (x0 =? y); try easy.
       bdestruct (x0 <? n); try lia; try easy.
Qed.       


Lemma get_v_in_basis : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> get_vec x (form_basis v x) = v.
Proof. intros. 
       prep_matrix_equality.
       unfold get_vec, form_basis.
       bdestruct (y =? 0).
       rewrite <- beq_nat_refl, H0; easy.
       unfold WF_Matrix in H.
       rewrite H; try easy.
       right. 
       destruct y; try lia; try easy.
Qed.


Lemma get_ei_in_basis : forall {n} (v : Vector n) (x y : nat),
  y < n -> y <> x -> get_vec y (form_basis v x) = e_i y.
Proof. intros. 
       prep_matrix_equality.
       unfold get_vec, form_basis.
       bdestruct (y0 =? 0).
       bdestruct (y =? x); try easy.
       rewrite H1; easy.
       unfold e_i.
       bdestruct (x0 =? y); bdestruct (x0 <? n); bdestruct (y0 =? 0); try easy. 
Qed.



Lemma reduce_mul_n : forall {n} (A : Square (S n)) (v : Vector (S n)),
  get_vec n A = @e_i (S n) n -> (reduce A n n) × (reduce_row v n) = reduce_row (A × v) n.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult, reduce, reduce_row.
       assert (H' : S n - 1 = n). { lia. }
       bdestruct (x <? n).  
       - rewrite <- Csum_extend_r.
         assert (H'' : A x n = C0).
         { rewrite <- get_vec_conv.  
           rewrite H. unfold e_i. 
           bdestruct (x =? n); try lia. 
           easy. }
         rewrite H''. rewrite Cmult_0_l. 
         rewrite Cplus_0_r.
         rewrite easy_sub7.
         apply Csum_eq_bounded. 
         intros. bdestruct (x0 <? n); try lia; try easy.
       - rewrite <- Csum_extend_r.
         assert (H'' : A (1 + x) n = C0).
         { rewrite <- get_vec_conv.  
           rewrite H. unfold e_i. 
           bdestruct (1 + x =? n); try lia. 
           easy. }
         rewrite H''. rewrite Cmult_0_l. 
         rewrite Cplus_0_r.
         rewrite easy_sub7.
         apply Csum_eq_bounded. 
         intros.
         bdestruct (x0 <? n); try lia; try easy.
Qed.
 

Lemma reduce_mul_0 : forall {n} (A : Square (S n)) (v : Vector (S n)),
  get_vec 0 A = @e_i (S n) 0 -> (reduce A 0 0) × (reduce_row v 0) = reduce_row (A × v) 0.
Proof. intros. 
       prep_matrix_equality. 
       unfold Mmult, reduce, reduce_row.
       rewrite easy_sub7. 
       bdestruct (x <? 0); try lia.  
       rewrite <- Csum_extend_l.
       assert (H' : A (1 + x) 0 = C0).
       { rewrite <- get_vec_conv.  
         rewrite H. unfold e_i. 
         bdestruct (1 + x =? 0); try lia. 
         easy. }
       rewrite H'. 
       rewrite Cmult_0_l. 
       rewrite Cplus_0_l.
       apply Csum_eq_bounded. 
       intros. bdestruct (x0 <? 0); try lia; try easy.
Qed.

(* More general case: 
Lemma reduce_mul : forall {n} (A : Square (S n)) (v : Vector (S n)) (x : nat),
  get_vec x A = @e_i (S n) x -> (reduce A x x) × (reduce_row v x) = reduce_row (A × v) x.
Proof. *)


Lemma form_basis_ind_case1 : forall {n} (T : Square (S n)),
  linearly_independent (reduce T n n) -> get_vec n T = @e_i (S n) n ->
  (forall x : nat, x < n -> T n x = C0) -> 
  linearly_independent T. 
Proof. unfold linearly_independent in *.
       intros.  
       assert (H2' := H2).
       apply (zero_reduce _ n) in H2'.
       apply H2'.
       split. 
       - apply H.
         apply WF_reduce_row; try lia; try easy. 
         rewrite reduce_mul_n. 
         rewrite H3. 
         unfold reduce_row, Zero.
         prep_matrix_equality. 
         bdestruct (x <? n); easy.
         apply H0.
       - assert (H' : (T × a) n 0 = C0).
         { rewrite H3. auto. }
         unfold Mmult in H'.
         rewrite <- H'.
         rewrite <- Csum_extend_r.
         assert (H'' : (Csum (fun y : nat => T n y * a y 0) n = C0)%C).
         { apply Csum_0_bounded.
           intros. 
           rewrite H1; try lca; try lia. }
         rewrite H''. 
         rewrite <- (get_vec_conv _ _ T).
         rewrite H0. 
         unfold e_i.
         rewrite <- beq_nat_refl. 
         bdestruct (n <? S n); try lia. 
         simpl. lca. 
Qed.

Lemma form_basis_ind_case2 : forall {n} (T : Square (S n)),
  linearly_independent (reduce T 0 0) -> get_vec 0 T = @e_i (S n) 0 ->
  (forall x : nat, x <> 0 -> T 0 x = C0) -> 
  linearly_independent T. 
Proof. unfold linearly_independent in *.
       intros.  
       assert (H2' := H2).
       apply (zero_reduce _ 0) in H2'.
       apply H2'.
       split.
       - apply H.
         apply WF_reduce_row; try lia; try easy. 
         rewrite reduce_mul_0. 
         rewrite H3. 
         unfold reduce_vecn, Zero.
         prep_matrix_equality. 
         bdestruct (x <? S n - 1); easy.
         apply H0.
       - assert (H' : (T × a) 0 0 = C0).
         { rewrite H3. auto. }
         unfold Mmult in H'.
         rewrite <- H'.
         rewrite <- Csum_extend_l.
         assert (H'' : (Csum (fun x : nat => T 0 (S x) * a (S x) 0) n = C0)%C).
         { apply Csum_0_bounded.
           intros. 
           rewrite H1; try lca; try lia. }
         rewrite H''. 
         rewrite <- (get_vec_conv _ _ T).
         rewrite H0. 
         unfold e_i.
         lca. 
Qed.


Lemma reduce_form_basis_case1 : forall {n} (v : Vector (S n)) (a : C) (x : nat),
  x < n -> reduce (col_add (form_basis v x) x n a) n n = form_basis (reduce_row v n) x.
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_add, form_basis, reduce_row. 
       bdestruct (x0 <? n); bdestruct (y =? x); bdestruct (y <? n);
         bdestruct (1 + y =? x); bdestruct (n =? x); try lia; try easy.
       unfold e_i. bdestruct (x0 =? n); try lia. 
       simpl. lca. 
       unfold e_i.
       bdestruct (x0 <? S n); bdestruct (x0 <? S n - 1); try lia; easy. 
       unfold e_i.
       bdestruct (x0 <? S n); bdestruct (x0 <? S n - 1); try lia; easy. 
       unfold e_i.
       bdestruct (x0 <? S n); bdestruct (x0 <? S n - 1); 
         bdestruct (x0 =? 1 + y); bdestruct (x0 =? y); try lia; easy. 
       unfold e_i.
       bdestruct (1 + x0 <? S n); try lia.
       rewrite andb_false_r, andb_false_l; lca.
       unfold e_i.
       bdestruct (1 + x0 =? y); bdestruct (x0 =? y); 
         bdestruct (1 + x0 <? S n); bdestruct (x0 =? S n - 1); try lia; easy. 
       unfold e_i.
       bdestruct (1 + x0 =? y); bdestruct (x0 =? y); 
         bdestruct (1 + x0 <? S n); bdestruct (x0 <? S n - 1); try lia; easy. 
       unfold e_i.
       bdestruct (1 + x0 =? 1 + y); bdestruct (x0 =? y); 
         bdestruct (1 + x0 <? S n); bdestruct (x0 <? S n - 1); try lia; easy. 
Qed.



Lemma reduce_form_basis_case2 : forall {n} (v : Vector (S n)) (a : C),
  n <> 0 -> reduce (col_add (form_basis v n) n 0 a) 0 0 = form_basis (reduce_row v 0) (n - 1).
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce, col_add, form_basis, reduce_row. 
       bdestruct (x <? 0); bdestruct (y <? 0); bdestruct (y =? n);
         bdestruct (1 + y =? n); bdestruct (0 =? n); bdestruct (y =? n - 1); try lia; try easy.
       unfold e_i. 
       bdestruct (1 + x =? 1 + y); bdestruct (x =? y); bdestruct (1 + x <? S n);
         bdestruct (x <? S n - 1); bdestruct (0 =? 0); try lia; try easy. 
       unfold e_i. bdestruct (1 + x =? 0); try lia. simpl. 
       lca. 
       unfold e_i. 
       bdestruct (1 + x =? 1 + y); bdestruct (x =? y); bdestruct (1 + x <? S n);
         bdestruct (x <? S n - 1); bdestruct (0 =? 0); try lia; try easy. 
Qed.




Lemma form_basis_ver : forall {n} (v : Vector n) (x : nat),
  v <> Zero -> WF_Matrix v -> v x 0 <> C0 -> x < n -> 
  linearly_independent (form_basis v x) /\ get_vec x (form_basis v x) = v.
Proof. induction n as [| n'].
       - intros. lia.
       - intros.
         split. 
         bdestruct (x <? n').
         + rewrite (col_add_inv _ x n' (- v (n') 0)); try lia.  (* case 1 *) 
           apply lin_indep_add; try lia. 
           apply form_basis_ind_case1.
           rewrite reduce_form_basis_case1; try lia. 
           destruct (IHn' (reduce_row v n') x) as [H4 H5].
           unfold not. intros. 
           apply H1. assert (H' : reduce_row v n' x 0 = C0).
           { rewrite H4. easy. }
           rewrite <- H'.
           unfold reduce_row.
           bdestruct (x <? n'); try lia; try easy.
           unfold WF_Matrix in *.
           intros. unfold reduce_row.
           destruct H4.
           bdestruct (x0 <? n'); try lia. 
           apply H0; lia. 
           bdestruct (x0 <? n'); apply H0; lia. 
           unfold not; intros; apply H1. 
           rewrite <- H4. 
           unfold reduce_row.
           bdestruct (x <? n'); try lia; try easy.   
           apply H3.
           rewrite easy_sub7 in *.
           apply H4.
           prep_matrix_equality.
           unfold get_vec, col_add, form_basis, e_i.
           bdestruct (y =? 0); bdestruct (n' =? x); 
             bdestruct (x0 =? n'); bdestruct (x0 <? S n'); try lia; try easy. 
           intros. 
           unfold col_add, form_basis, e_i. 
           bdestruct (x0 =? x); bdestruct (n' =? x); 
             bdestruct (n' =? n'); bdestruct (n' <? S n'); try lia. 
           simpl. lca. 
           bdestruct (n' =? x0); try lia; try easy. 
         + bdestruct (n' =? 0).                    (* weird edge case with 1x1 matrix *) 
           * rewrite H4 in *.
             bdestruct (x =? 0); try lia.
             rewrite H5. 
             unfold linearly_independent, form_basis.
             apply invertible_implies_linind. 
             exists (fun i j => if (i =? 0) && (j =? 0) then / (v 0 0) else C0).
             unfold Mmult. 
             prep_matrix_equality. 
             simpl; unfold I.
             bdestruct (y =? 0); destruct x0; bdestruct (0 =? y); try lia; try lca. 
             simpl. rewrite Cplus_0_l. apply Cinv_r. 
             rewrite H5 in H1. apply H1.
             unfold WF_Matrix in H0.
             rewrite H0; try lia. 
             all : bdestruct (S x0 <? 1); try lia; rewrite andb_false_r; lca. 
           * bdestruct (x =? n'); try lia.                         (* case 2 *)
             rewrite H5 in *.
             rewrite (col_add_inv _ n' 0 (- v 0 0)); try lia.  
             apply lin_indep_add; try lia.
             apply form_basis_ind_case2.
             rewrite reduce_form_basis_case2; try lia. 
             destruct (IHn' (reduce_row v 0) (n' - 1)) as [H6 H7].
             unfold not. intros. 
             apply H1. assert (H' : reduce_row v 0 (n' - 1) 0 = C0).
             { rewrite H6. easy. }
             unfold reduce_row in H'.
             rewrite <- H'. 
             bdestruct (n' - 1 <? 0); try lia. 
             destruct n'; try lia. simpl. 
             rewrite easy_sub4; easy. 
             unfold WF_Matrix in *.
             intros. unfold reduce_row.
             destruct H6.
             bdestruct (x0 <? 0); try lia. 
             apply H0. left. lia. 
             bdestruct (x0 <? 0); try lia. 
             apply H0; lia. 
             unfold reduce_row. 
             bdestruct (n' - 1 <? 0); try lia. 
             destruct n'; try lia. simpl. 
             rewrite easy_sub4; easy. 
             destruct n'; try lia. 
             rewrite easy_sub7.
             apply H6.  
             prep_matrix_equality.
             unfold get_vec, col_add, form_basis, e_i.
             bdestruct (y =? 0); bdestruct (0 =? n'); 
               bdestruct (x0 =? 0); bdestruct (x0 <? S n'); try lia; try easy. 
             intros. 
             unfold col_add, form_basis, e_i. 
             bdestruct (x0 =? n'); bdestruct (0 =? x0); 
               bdestruct (0 =? 0); bdestruct (0 <? S n'); destruct n'; try lia. 
             simpl. lca. easy. 
           + apply get_v_in_basis. 
             easy. 
Qed.


Lemma lin_indep_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero ->
  exists S : Matrix n n, WF_Matrix S /\ linearly_independent S /\ get_vec 0 S = v. 
Proof. intros. 
       destruct n. 
       - exists Zero. 
         split. easy. 
         split. 
         unfold linearly_independent.
         intros. unfold WF_Matrix in H1. 
         prep_matrix_equality. 
         apply H1; lia.
         prep_matrix_equality. 
         unfold get_vec, Zero.
         unfold WF_Matrix in H. 
         rewrite H; try lia. 
         bdestruct (y =? 0); easy.
       - assert (H' := H).
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         exists (col_swap (form_basis v x) x 0).
         assert (H' : x < S n).
         { bdestruct (x <? S n); try easy. 
           unfold WF_Matrix in H.
           unfold not in H1. 
           assert (H' : v x 0 = C0). 
           { apply H. lia. }
           easy. }
         assert (H'' : linearly_independent (form_basis v x) /\ get_vec x (form_basis v x) = v).
         { apply form_basis_ver; try easy. }
         split.
         apply WF_col_swap; try lia; try easy.
         apply WF_form_basis; easy.
         split. 
         + apply lin_indep_swap; try lia.
           easy. 
         + rewrite col_swap_diff_order.
           rewrite <- (col_swap_get_vec _ 0 x).
           apply get_v_in_basis. 
           easy. 
Qed.         

(************************************)
(* Quick proof of |x| = 0 iff x = 0 *)
(************************************)

Lemma inner_product_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> (inner_product v v = C0 <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         destruct (mat_equiv_dec v Zero).
         apply mat_equiv_eq'; try easy.
         assert (H' : v <> Zero). 
         { unfold not; intros. 
           apply n0. rewrite H1.
           easy. }
         apply nonzero_vec_nonzero_elem in H'; try easy.
         destruct H'. 
         unfold WF_Matrix in H.
         bdestruct (x <? n).
         assert (H0' := Rle_0_sqr).  
         unfold Rsqr in H0'. 
         assert (H' : (0 < fst (inner_product v v))%R).
         { unfold inner_product.
           unfold Mmult. 
           apply Csum_gt_0.
           unfold adjoint. 
           intros.
           rewrite <- Cmod_sqr.
           simpl. autorewrite with R_db.
           apply H0'. 
           exists x. split; try easy.
           unfold adjoint. 
           rewrite <- Cmod_sqr.
           simpl. autorewrite with R_db.
           assert (H' : (0 <= Cmod (v x 0%nat) * Cmod (v x 0%nat))%R). 
           { apply H0'. } 
           destruct H'; try easy. 
           assert (H' := Rsqr_0_uniq).
           unfold Rsqr in H'. 
           assert (H'' : forall a b : R, a = b -> b = a). { easy. }
           apply H'' in H3. 
           apply H' in H3.
           apply Cmod_gt_0 in H1.
           rewrite H3 in H1.
           lra. }
         rewrite H0 in H'. 
         simpl in H'. lra. 
         assert (H' : v x 0 = C0).
         { apply H. left; easy. }
         rewrite H' in H1; easy. 
       - intros. 
         unfold inner_product.  
         rewrite H0. 
         rewrite Mmult_0_r. 
         easy.
Qed.


Lemma norm_zero_iff_zero : forall {n} (v : Vector n),
  WF_Matrix v -> (norm v = 0%R <-> v = Zero). 
Proof. intros. split. 
       - intros. 
         unfold norm in H0.
         apply inner_product_zero_iff_zero in H.
         unfold inner_product in H. 
         apply sqrt_eq_0 in H0.
         apply H. 
         apply c_proj_eq.
         apply H0.
         apply norm_real.
         apply inner_product_ge_0.
       - intros. 
         rewrite H0. 
         unfold norm.
         rewrite Mmult_0_r. 
         simpl. apply sqrt_0. 
Qed.     






(*****************************************************************************************)
(* Defining and verifying the gram_schmidt algorythm and proving v can be part of an onb *)
(*****************************************************************************************)
 

Definition col_append {n m} (T : Matrix n m) (v : Vector n) : Matrix n (S m) :=
  fun i j => if (j =? m) then v i 0 else T i j.


Definition row_append {n m} (T : Matrix n m) (v : Matrix 1 m) : Matrix (S n) m :=
  fun i j => if (i =? n) then v 0 j else T i j.

Lemma WF_col_append : forall {n m} (T : Matrix n m) (v : Vector n),
  WF_Matrix T -> WF_Matrix v -> WF_Matrix (col_append T v).
Proof. unfold WF_Matrix in *.
       intros; destruct H1 as [H1 | H1]. 
       - unfold col_append.
         rewrite H, H0; try lia. 
         bdestruct (y =? m); easy. 
       - unfold col_append.
         bdestruct (y =? m); try lia. 
         apply H; lia. 
Qed.


Lemma WF_row_append : forall {n m} (T : Matrix n m) (v : Matrix 1 m),
  WF_Matrix T -> WF_Matrix v -> WF_Matrix (row_append T v).
Proof. unfold WF_Matrix in *.
       intros; destruct H1 as [H1 | H1]. 
       - unfold row_append.
         bdestruct (x =? n); try lia. 
         apply H; lia. 
       - unfold row_append.
         rewrite H, H0; try lia. 
         bdestruct (x =? n); easy. 
Qed.


Lemma get_vec_reduce_append_miss : forall {n m} (T : Matrix n (S m)) (v : Vector n) (i : nat),
  i < m -> get_vec i (col_append (reduce_col T m) v) = get_vec i T.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, col_append, reduce_col.
       bdestruct (i =? S m - 1); bdestruct (i <? m); try lia; easy.
Qed.


Lemma get_vec_reduce_append_hit : forall {n m} (T : Matrix n (S m)) (v : Vector n),
  WF_Matrix v -> get_vec m (col_append (reduce_col T m) v) = v.
Proof. intros.        
       unfold get_vec, col_append, reduce_col.
       prep_matrix_equality. 
       bdestruct (y =? 0).
       - bdestruct (m =? S m - 1); try lia.
         rewrite H0; easy.
       - rewrite H; try lia; easy.
Qed.


Lemma get_vec_reduce_append_over : forall {n m} (T : Matrix n (S m)) (v : Vector n) (i : nat),
  WF_Matrix T -> i > m -> 
  get_vec i (col_append (reduce_col T m) v) = Zero.
Proof. intros. 
       prep_matrix_equality. 
       unfold get_vec, col_append, reduce_col.
       bdestruct (i =? S m - 1); bdestruct (i <? m); try lia; try easy.
       rewrite H. bdestruct (y =? 0); easy.
       right. lia. 
Qed.






(* with row_append, we now get this lemma. May want to reorganize so this comes earlier *)
Lemma lin_indep_col_reduce_n : forall {n m} (A : Matrix n (S m)),
  linearly_independent A -> linearly_independent (reduce_col A m).
Proof. intros. 
       unfold linearly_independent in *. 
       intros. 
       assert (H' : row_append a Zero = Zero).
       { apply H.
         rewrite easy_sub7 in *.
         apply WF_row_append; try easy.
         prep_matrix_equality. 
         unfold Mmult, row_append, Zero. 
         rewrite <- Csum_extend_r. 
         bdestruct (m =? S m - 1); try lia. 
         autorewrite with C_db.
         assert (H' : (reduce_col A m × a) x y = C0).
         { rewrite H1; easy. }
         rewrite <- H'. 
         unfold Mmult. 
         rewrite easy_sub7.
         apply Csum_eq_bounded. 
         intros.
         unfold reduce_col.
         bdestruct (x0 =? m); bdestruct (x0 <? m); try lia. 
         reflexivity. } 
       prep_matrix_equality. 
       assert (H'' : row_append a Zero x y = C0). { rewrite H'. easy. }
       unfold Zero; simpl. rewrite <- H''. 
       unfold row_append.
       rewrite easy_sub7. 
       bdestruct (x =? m); try easy.
       unfold WF_Matrix in H0. 
       unfold Zero; simpl. 
       apply H0. lia. 
Qed.





(* more general than append *)
Definition smash {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) : Matrix n (m1 + m2) :=
  fun i j => if j <? m1 then T1 i j else T2 i (j - m1).


Lemma WF_smash : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix (smash T1 T2).
Proof. unfold WF_Matrix, smash in *.
       intros. 
       bdestruct (y <? m1).
       - apply H; lia. 
       - apply H0; lia.
Qed.


Lemma smash_zero : forall {n m} (T : Matrix n m) (i : nat),
  WF_Matrix T -> smash T (@Zero n i) = T. 
Proof. intros. 
       prep_matrix_equality.
       unfold smash, Zero. 
       bdestruct (y <? m); try easy.
       rewrite H; try lia; easy.
Qed.


Lemma smash_assoc : forall {n m1 m2 m3}
                           (T1 : Matrix n m1) (T2 : Matrix n m2) (T3 : Matrix n m3),
  smash (smash T1 T2) T3 = smash T1 (smash T2 T3).
Proof. intros. 
       unfold smash.
       prep_matrix_equality.
       bdestruct (y <? m1 + m2); bdestruct (y <? m1); 
         bdestruct (y - m1 <? m2); try lia; try easy.
       assert (H' : y - (m1 + m2) = y - m1 - m2).
       lia. rewrite H'; easy.
Qed.


Lemma smash_append : forall {n m} (T : Matrix n m) (v : Vector n),
  WF_Matrix T -> WF_Matrix v ->
  col_append T v = smash T v.
Proof. intros. 
       unfold smash, col_append, WF_Matrix in *.
       prep_matrix_equality. 
       bdestruct (y =? m); bdestruct (y <? m); try lia; try easy.
       rewrite H1.
       rewrite <- minus_diag_reverse; easy. 
       rewrite H0, H; try lia; try easy.
Qed.       


Lemma smash_reduce : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n (S m2)),
  reduce_col (smash T1 T2) (m1 + m2) = smash T1 (reduce_col T2 m2).
Proof. intros. 
       prep_matrix_equality. 
       unfold reduce_col, smash. 
       bdestruct (y <? m1 + m2); bdestruct (y <? m1); bdestruct (1 + y <? m1);
         bdestruct (y - m1 <? m2); try lia; try easy.
       assert (H' : 1 + y - m1 = 1 + (y - m1)). lia.  
       rewrite H'; easy.
Qed.

Lemma split : forall {n m} (T : Matrix n (S m)), 
  T = smash (get_vec 0 T) (reduce_col T 0).
Proof. intros. 
       prep_matrix_equality. 
       unfold smash, get_vec, reduce_col.
       bdestruct (y <? 1); bdestruct (y =? 0); bdestruct (y - 1 <? 0); try lia; try easy.
       rewrite H0; easy. 
       destruct y; try lia. 
       simpl. rewrite easy_sub4; easy.
Qed.




(* similarly to lin_indep_col_reduce_n, could introduce this earlier  *)
Lemma lin_indep_smash : forall {n m2 m1} (A1 : Matrix n m1) (A2 : Matrix n m2),
  linearly_independent (smash A1 A2) -> linearly_independent A1. 
Proof. induction m2 as [| m2'].
       - intros. 
         unfold linearly_independent in *. 
         intros. assert (H' : m1 + 0 = m1). lia. 
         rewrite H' in *.
         apply H; try easy.
         rewrite <- H1.
         unfold smash, Mmult. 
         prep_matrix_equality. 
         apply Csum_eq_bounded.
         intros. 
         bdestruct (x0 <? m1); try lia; easy.
       - intros. 
         assert (H1 := @lin_indep_col_reduce_n n (m1 + m2') (smash A1 A2)). 
         assert (H' : (Init.Nat.add m1 (S m2')) = (S (Init.Nat.add m1 m2'))). { lia. }
         rewrite H' in H.
         apply H1 in H.
         assert (H1' : S (Nat.add m1 m2') = Nat.add m1 (S m2')). { lia. } 
         rewrite H1' in H. 
         rewrite smash_reduce in H.
         apply (IHm2' m1 A1 (reduce_col A2 m2')).
         rewrite easy_sub7 in *.
         assert (H2' : (m1 + S m2' - 1) = m1 + m2'). { lia. }
         rewrite H2' in *; easy.
Qed.



(* proj of v onto u *)
Definition proj {n} (u v : Vector n) : Vector n :=
  ((inner_product u v) / (inner_product u u)) .* u.


Definition proj_coef {n} (u v : Vector n) : C :=
  ((inner_product u v) / (inner_product u u)).


Lemma proj_inner_product : forall {n} (u v : Vector n),
  (norm u) <> 0%R -> inner_product u (proj u v) = inner_product u v.
Proof. intros. 
       unfold proj, inner_product. 
       distribute_scale.
       unfold scale. 
       unfold Cdiv.  
       rewrite <- Cmult_assoc. 
       rewrite Cinv_l.
       lca. 
       unfold norm in H.
       intro. apply H.
       rewrite H0. simpl. 
       rewrite sqrt_0.
       easy. 
Qed.




Definition gram_schmidt_on_v (n m : nat) (v : Vector n) (S : VecSet n m) :=
  v .+ (Msum m (fun i => (-C1) .* (proj (get_vec i S) v))).


Definition delta_T {n m} (T : Matrix n (S m)) (i : nat) : C := 
  match i =? m with 
  | true => C1
  | _ => - (proj_coef (get_vec i T) (get_vec m T))
  end. 


(* slightly different version thats easier to work with in general case *)
Definition gram_schmidt_on_T (n m : nat) (T : Matrix n (S m)) : Vector n :=
  Msum (S m) (fun i => (delta_T T) i .* (get_vec i T)).



Lemma WF_gs_on_T : forall {n m} (T : Matrix n (S m)),
  WF_Matrix T -> WF_Matrix (gram_schmidt_on_T n m T).
Proof. intros.
       unfold gram_schmidt_on_T.
       apply WF_Msum; intros. 
       apply WF_scale. 
       unfold get_vec, WF_Matrix in *; intros. 
       destruct H1.
       - rewrite H; auto.
         bdestruct (y =? 0); easy. 
       - bdestruct (y =? 0); try lia; try easy. 
Qed.


Lemma gram_schmidt_compare : forall {n m} (T : Matrix n (S m)),
  inner_product (get_vec m T) (get_vec m T) <> C0 -> 
  gram_schmidt_on_T n m T = gram_schmidt_on_v n m (get_vec m T) (reduce_col T m).
Proof. intros. 
       unfold gram_schmidt_on_T, gram_schmidt_on_v.
       prep_matrix_equality. 
       unfold Mplus. 
       do 2 rewrite Msum_Csum. 
       rewrite Cplus_comm. 
       rewrite <- Csum_extend_r.
       apply Csum_simplify.
       - apply Csum_eq_bounded.
         intros. 
         unfold delta_T.
         bdestruct (x0 =? m); try lia. 
         unfold proj, proj_coef. 
         distribute_scale.
         assert (H' : get_vec x0 (reduce_col T m) = get_vec x0 T).
         { prep_matrix_equality; 
           unfold get_vec, reduce_col.
           bdestruct (x0 <? m); try lia; easy. }
         rewrite easy_sub7 in *.
         rewrite H'. unfold scale. lca. 
       - unfold delta_T. 
         bdestruct (m =? m); try lia. 
         unfold scale. lca. 
Qed.


(* here, we show that gs_on_v preserves normalness *)
Lemma gram_schmidt_orthogonal : forall {n m} (v : Vector n) (S : VecSet n m) (i : nat),
  orthonormal S -> i < m -> inner_product (get_vec i S) (gram_schmidt_on_v n m v S) = C0.
Proof. intros. 
       destruct H as [H H1]. 
       unfold orthogonal in H.
       unfold inner_product in *.
       unfold gram_schmidt_on_v.
       rewrite Mmult_plus_distr_l.
       rewrite Mmult_Msum_distr_l.
       unfold Mplus. 
       rewrite Msum_Csum. 
       rewrite (Csum_unique (-C1 * ((get_vec i S) † × v) 0 0) _ m); try lca. 
       exists i. split; try easy.
       split.
       - distribute_scale.
         unfold scale.
         apply H1 in H0. 
         assert (H' : norm (get_vec i S) <> 0%R).
         { rewrite H0. lra. }
         apply (proj_inner_product _ v) in H'. 
         unfold inner_product in H'.
         rewrite H'. 
         reflexivity. 
       - intros. apply H in H2. 
         unfold proj. 
         distribute_scale.
         unfold scale. 
         rewrite H2. 
         lca. 
Qed.




Definition f_to_vec (n : nat) (f : nat -> C) : Vector n :=
  fun i j => if (j =? 0) && (i <? n) then f i else C0. 


Lemma WF_f_to_vec : forall (n : nat) (f : nat -> C), WF_Matrix (f_to_vec n f).
Proof. intros. 
       unfold WF_Matrix, f_to_vec. 
       intros x y [H | H]. 
       - bdestruct (y =? 0); bdestruct (x <? n); try lia; easy. 
       - bdestruct (y =? 0); bdestruct (x <? n); try lia; easy. 
Qed.

Lemma Msum_to_Mmult : forall {n m} (T : Matrix n (S m)) (f : nat -> C),
  Msum (S m) (fun i => f i .* get_vec i T) = T × (f_to_vec (S m) f).              
Proof. intros. 
       prep_matrix_equality. 
       rewrite Msum_Csum. 
       unfold Mmult. 
       apply Csum_eq_bounded.
       intros. 
       unfold f_to_vec, get_vec, scale.
       bdestruct (x0 <? S m); bdestruct (y =? 0); try lia; try lca. 
Qed.

(* here, we show gs_on_T is nonzero, true since T is lin indep *)
Lemma gram_schmidt_non_zero : forall {n m} (T : Matrix n (S m)),
  linearly_independent T -> gram_schmidt_on_T n m T <> Zero. 
Proof. intros. 
       unfold not, gram_schmidt_on_T; intros. 
       rewrite (Msum_to_Mmult T (delta_T T)) in H0. 
       unfold linearly_independent in H.
       apply H in H0.
       assert (H' : C1 <> C0). 
       { apply C0_fst_neq.
         simpl. 
         apply R1_neq_R0. }
       apply H'.
       assert (H'' : f_to_vec (S m) (delta_T T) m 0 = C0).
       { rewrite H0. easy. }
       rewrite <- H''. 
       unfold f_to_vec, delta_T.
       bdestruct (m <? S m); bdestruct (m =? m); try lia; easy.
       apply WF_f_to_vec.
Qed.


Lemma inner_product_zero_normalize : forall {n} (u v : Vector n),
  inner_product u v = C0 -> inner_product u (normalize v) = C0.
Proof. intros. 
       unfold inner_product, normalize in *.
       distribute_scale.
       unfold scale. 
       rewrite H.
       lca. 
Qed.


Lemma Cconj_simplify : forall (c1 c2 : C), c1^* = c2^* -> c1 = c2.
Proof. intros. 
       assert (H1 : c1 ^* ^* = c2 ^* ^*). { rewrite H; easy. }
       do 2 rewrite Cconj_involutive in H1.   
       easy. 
Qed.


Lemma extend_onb_ind_step_part1 : forall {n m} (T : Matrix n (S m)),
  WF_Matrix T -> linearly_independent T -> orthonormal (reduce_col T m) ->
  orthonormal (col_append (reduce_col T m) (normalize (gram_schmidt_on_T n m T))). 
Proof. intros. 
       split. 
       - unfold orthogonal. 
         intros. 
         bdestruct (m <? i); bdestruct (m <? j); try lia. 
         + rewrite get_vec_reduce_append_over; try easy.
           unfold inner_product.
           rewrite zero_adjoint_eq.
           rewrite Mmult_0_l.
           easy. 
         + rewrite get_vec_reduce_append_over; try easy.
           unfold inner_product.
           rewrite zero_adjoint_eq.
           rewrite Mmult_0_l.
           easy. 
         + rewrite (get_vec_reduce_append_over _ _ j); try easy.
           unfold inner_product.
           rewrite Mmult_0_r.
           easy. 
         + bdestruct (i =? m); bdestruct (j =? m); try lia. 
           * rewrite H5.
             rewrite get_vec_reduce_append_hit.
             bdestruct (j <? m); bdestruct (m <? j); try lia.  
             rewrite get_vec_reduce_append_miss; try easy.
             rewrite inner_product_comm_conj.
             apply Cconj_simplify.
             rewrite Cconj_involutive, Cconj_0.
             apply inner_product_zero_normalize.
             rewrite gram_schmidt_compare.
             rewrite easy_sub7 in *.
             apply (gram_schmidt_orthogonal (get_vec m T) _ j) in H1; try lia.
             assert (H9 := (@get_vec_reduce_col n (S m) j m T)). 
             rewrite easy_sub7 in *.
             rewrite H9 in H1; try lia.
             apply H1.
             assert (H' : WF_Matrix (get_vec m T)).
             { apply WF_get_vec; easy. }
             apply inner_product_zero_iff_zero in H'.
             destruct (Ceq_dec (inner_product (get_vec m T) (get_vec m T)) C0); try easy.
             apply H' in e.
             apply lin_indep_nonzero_cols in e; try lia; try easy.
             unfold normalize.
             apply WF_scale.
             apply WF_gs_on_T; easy.
           * rewrite H6.
             rewrite get_vec_reduce_append_hit.
             bdestruct (i <? m); bdestruct (m <? i); try lia.  
             rewrite get_vec_reduce_append_miss; try easy.
             apply inner_product_zero_normalize.
             rewrite gram_schmidt_compare.
             rewrite easy_sub7 in *.
             apply (gram_schmidt_orthogonal (get_vec m T) _ i) in H1; try lia.
             assert (H9 := (@get_vec_reduce_col n (S m) i m T)). 
             rewrite easy_sub7 in *.
             rewrite H9 in H1; try lia.
             apply H1.
             assert (H' : WF_Matrix (get_vec m T)).
             { apply WF_get_vec; easy. }
             apply inner_product_zero_iff_zero in H'.
             destruct (Ceq_dec (inner_product (get_vec m T) (get_vec m T)) C0); try easy.
             apply H' in e.
             apply lin_indep_nonzero_cols in e; try lia; try easy.
             unfold normalize.
             apply WF_scale.
             apply WF_gs_on_T; easy.
           * bdestruct (i <? m); bdestruct (j <? m); try lia.  
             rewrite get_vec_reduce_append_miss; try easy.
             rewrite get_vec_reduce_append_miss; try easy.
             unfold orthonormal in H1.
             destruct H1 as [H1 _].
             unfold orthogonal in H1.
             apply (@get_vec_reduce_col n (S m) i m T) in H7.
             apply (@get_vec_reduce_col n (S m) j m T) in H8.
             rewrite easy_sub7 in *.
             apply H1 in H2.             
             rewrite H7, H8 in H2; easy. 
       - intros. 
         bdestruct (i =? m); bdestruct (i <? m); try lia. 
         + rewrite H3. 
           rewrite get_vec_reduce_append_hit.
           apply normalized_norm_1.
           assert (H' := H).  
           apply WF_gs_on_T in H'. 
           apply norm_zero_iff_zero in H'. 
           destruct (Req_EM_T (norm (gram_schmidt_on_T n m T)) 0%R); try easy.
           apply H' in e.
           apply gram_schmidt_non_zero in H0; easy.
           unfold normalize. 
           apply WF_scale.
           apply WF_gs_on_T; easy.
         + destruct H1 as [_ H1].
           rewrite get_vec_reduce_append_miss; try lia. 
           assert (H' := (@get_vec_reduce_col n (S m) i m T)).
           rewrite <- H'; try lia. 
           apply H1; lia. 
Qed.     


Definition delta_T' {n m} (T : Matrix n m) (v : Vector n) (i : nat) : C := 
 - (proj_coef (get_vec i T) v). 




Lemma gs_on_T_cols_add : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  WF_Matrix v ->
  smash (col_append T1 (gram_schmidt_on_T n m1 (col_append T1 v))) T2 = 
  col_add_many m1 m1 (f_to_vec m1 (delta_T' T1 v)) (smash (col_append T1 v) T2).
Proof. intros. 
       prep_matrix_equality. 
       unfold smash, col_append, gram_schmidt_on_T, col_add_many.
       bdestruct (y <? S m1); bdestruct (y =? m1); try lia; try easy.
       unfold delta_T, delta_T', gen_new_vec, f_to_vec, get_vec, scale.
       do 2 rewrite Msum_Csum. 
       rewrite <- Csum_extend_r.
       bdestruct (m1 =? m1); bdestruct (0 =? 0); try lia. 
       rewrite Cplus_comm.
       apply Csum_simplify; try lca. 
       unfold get_vec.
       apply Csum_eq_bounded; intros.
       bdestruct (x0 =? m1); bdestruct (x0 <? m1); try lia.
       simpl. 
       bdestruct (x0 <? S m1); try lia. 
       assert (H' : (fun x1 y0 : nat => if y0 =? 0 then v x1 0 else C0) = v).
       { prep_matrix_equality.
         bdestruct (y0 =? 0).
         rewrite H8; easy.
         rewrite H; try lia; easy. }
       rewrite H'; easy.
Qed.


Lemma smash_scale : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  smash (col_append T1 (normalize v)) T2 = 
  col_scale (smash (col_append T1 v) T2) m1 (/ norm v).
Proof. intros. 
       unfold smash, col_append, normalize, col_scale.
       prep_matrix_equality. 
       bdestruct (y <? S m1); bdestruct (y =? m1); try lia; try easy. 
Qed.


Lemma extend_onb_ind_step_part2 : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2)
                                                   (v : Vector n),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix v -> v <> Zero -> 
  linearly_independent (smash (col_append T1 v) T2) -> 
  linearly_independent (smash (col_append T1 
                                    (normalize (gram_schmidt_on_T n m1 (col_append T1 v)))) T2).
Proof. intros. 
       rewrite smash_scale. 
       apply lin_indep_scale.
       unfold not; intros. 
       assert (H4' : (norm (gram_schmidt_on_T n m1 (col_append T1 v)) * 
                     / norm (gram_schmidt_on_T n m1 (col_append T1 v)) = 
                     norm (gram_schmidt_on_T n m1 (col_append T1 v)) * C0)%C).
       { rewrite H4; easy. }
       rewrite Cmult_0_r, Cinv_r in H4'. 
       assert (H5 : C1 <> C0). 
       { apply C0_fst_neq.
         simpl. 
         apply R1_neq_R0. }
       apply H5; easy.
       unfold not; intros.
       assert (H5' : WF_Matrix (gram_schmidt_on_T n m1 (col_append T1 v))).
       { apply WF_gs_on_T.
         apply WF_col_append; easy. }
       apply norm_zero_iff_zero in H5'.
       apply RtoC_inj in H5.
       rewrite H5 in H5'. 
       apply (gram_schmidt_non_zero (col_append T1 v)).
       apply lin_indep_smash in H3; easy.
       apply H5'; lra.
       rewrite gs_on_T_cols_add; try easy.
       apply lin_indep_col_add_many; try lia; easy.
Qed.       




Lemma extend_onb_ind_step : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  WF_Matrix T1 -> WF_Matrix T2 -> WF_Matrix v -> 
  linearly_independent (smash (col_append T1 v) T2) -> orthonormal T1 ->
  exists v1, WF_Matrix v1 /\ orthonormal (col_append T1 v1) /\ 
             linearly_independent (smash (col_append T1 v1) T2).
Proof. intros. 
       exists (normalize (gram_schmidt_on_T n m1 (col_append T1 v))).
       split. unfold normalize.
       apply WF_scale.
       apply WF_gs_on_T.
       apply WF_col_append; try easy.
       split. 
       - apply lin_indep_smash in H2.
         assert (H4 := extend_onb_ind_step_part1 (col_append T1 v)).
         assert (H' :  reduce_col (col_append T1 v) m1 = T1).
         { intros. 
           prep_matrix_equality. 
           unfold reduce_col, col_append.
           bdestruct (y <? m1); bdestruct (y =? m1); 
             bdestruct (1 + y =? m1); try lia; try easy.
           all : rewrite H; try lia; rewrite H; try lia; lca. }
         rewrite H' in H4.
         rewrite easy_sub7 in *.
         apply H4; try easy.
         apply WF_col_append; easy.
       - apply extend_onb_ind_step_part2; try easy.
         apply lin_indep_smash in H2.
         assert (H4 := @lin_indep_nonzero_cols n (S m1) (col_append T1 v)). 
         assert (H' : get_vec m1 (col_append T1 v) = v).
         { prep_matrix_equality. 
           unfold get_vec, col_append.
           bdestruct (y =? 0); bdestruct (m1 =? m1); try lia.
           rewrite H5; easy.
           rewrite H1; try lca; lia. }
         rewrite <- H'. 
         apply H4; try lia; easy.
Qed.







Lemma extend_onb : forall (n m2 m1 : nat) (T1 : Matrix n (S m1)) (T2 : Matrix n m2),
  WF_Matrix T1 -> WF_Matrix T2 ->  
  linearly_independent (smash T1 T2) -> orthonormal T1 ->
  exists T2' : Matrix n m2, WF_Matrix T2' /\ orthonormal (smash T1 T2').
Proof. induction m2 as [| m2'].
       - intros. 
         exists Zero.
         split. easy.
         rewrite smash_zero; try easy.
         rewrite plus_0_r.
         apply H2.
       - intros. 
         rewrite (split T2) in *.
         assert (H3 := (smash_assoc T1 (get_vec 0 T2) (reduce_col T2 0))). 
         rewrite easy_sub7 in *.
         simpl in *.
         rewrite <- H3 in H1. 
         rewrite <- smash_append in H1; try easy.
         assert (exists v1, WF_Matrix v1 /\ orthonormal (col_append T1 v1) /\ 
             linearly_independent (smash (col_append T1 v1) (reduce_col T2 0))).
         { apply (extend_onb_ind_step _ _ (get_vec 0 T2)); try easy.
           apply WF_reduce_col. lia. 
           rewrite (split T2). easy.
           apply WF_get_vec.
           rewrite (split T2). easy.
           rewrite easy_sub7 in *.
           assert (add1 : S (m1 + S m2') = S (S m1) + m2'). { lia. }
           assert (add2 : S (m1 + 1) = S (S m1)). { lia. }
           rewrite add1, add2 in H1.
           apply H1. }
         destruct H4 as [v [H4 [H5 H6]]].
         assert (H7 : exists T2' : Matrix n m2', 
                    WF_Matrix T2' /\ orthonormal (smash (smash T1 v) T2')).
         { apply (IHm2' _ (smash T1 v) (reduce_col T2 0)).            
           assert (H' : Nat.add m1 (S O) = S m1). lia. 
           unfold Nat.add in H'.
           rewrite H'. 
           assert (H'' := (@WF_smash n (S m1) (S O) T1 v)).
           assert (H''' : Nat.add (S m1) (S O) = S (S m1)). lia. 
           rewrite H''' in *.
           apply H''. 
           easy. 
           easy. 
           assert (H7 := (WF_reduce_col 0 T2)).
           rewrite easy_sub7 in *. 
           apply H7. 
           lia. 
           rewrite (split T2).
           easy. 
           assert (add1 : S (Nat.add m1 (S m2')) = S (Nat.add (Nat.add m1 (S O)) m2')). lia. 
           rewrite add1 in H1.
           unfold Nat.add in H1.
           unfold Nat.add.
           rewrite <- smash_append; try easy.
           rewrite easy_sub7 in *.
           assert (add2 : Nat.add (S (S m1)) m2' = S (Nat.add (Nat.add m1 (S O)) m2')). lia. 
           assert (add3 : (S (S m1)) = S (Nat.add m1 (S O))). lia. 
           rewrite add2, add3 in H6.
           unfold Nat.add in H6.
           apply H6.
           rewrite <- smash_append; try easy.
           assert (add4 : S (S m1) = S (Nat.add m1 (S O))). lia. 
           rewrite add4 in H5.
           unfold Nat.add in H5.
           apply H5. }
         destruct H7. 
         rewrite smash_assoc in H7.
         exists (smash v x).
         split. 
         assert (H' : S m2' = 1 + m2'). lia. rewrite H'.
         apply WF_smash; try easy.
         assert (add5 : Nat.add (Nat.add (S m1) (S O)) m2' = S (Nat.add m1 (S m2'))). lia.
         assert (add6 : (Init.Nat.add (S O) m2') = (S m2')). lia. 
         rewrite add5, add6 in H7.    
         apply H7. 
         apply WF_get_vec.
         rewrite (split T2).
         easy. 
Qed.


Lemma get_vec_vec : forall {n} (v : Vector n),
  WF_Matrix v -> get_vec 0 v = v.
Proof. intros. 
       unfold get_vec.
       prep_matrix_equality. 
       bdestruct (y =? 0). 
       - rewrite H0; easy.
       - unfold WF_Matrix in H.  
         rewrite H; try easy.
         right. 
         bdestruct (y <? 1); try lia.          
Qed.


Lemma orthonormal_normalize_v : forall {n} (v : Vector n),
  v <> Zero -> WF_Matrix v -> orthonormal (normalize v).
Proof. intros. 
       split. 
       unfold orthogonal, inner_product. 
       intros. destruct i.
       + assert (H' : get_vec j (normalize v) = Zero).
         { prep_matrix_equality. 
           unfold get_vec, normalize.
           bdestruct (y =? 0); try easy.
           unfold scale. rewrite H0; try lia; lca. }
         rewrite H'.
         rewrite Mmult_0_r; easy.
       + assert (H' : get_vec (S i) (normalize v) = Zero).
         { prep_matrix_equality. 
           unfold get_vec, normalize.
           bdestruct (y =? 0); try easy.
           unfold scale. rewrite H0; try lia; lca. }
         rewrite H'.
         rewrite zero_adjoint_eq.
         rewrite Mmult_0_l; easy.
       + intros. 
         destruct i; try lia. 
         rewrite get_vec_vec.
         apply normalized_norm_1.
         unfold not; intros; apply H.
         apply norm_zero_iff_zero in H0.
         apply H0; easy.
         unfold normalize.
         auto with wf_db.
Qed.


Theorem onb_out_of_v : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> 
  exists S : Matrix n n, WF_Matrix S /\ orthonormal S /\ get_vec 0 S = normalize v.
Proof. intros. 
       destruct n as [| n].
       - assert (H' : v = Zero).
         prep_matrix_equality.
         rewrite H; try lia; easy.
         easy.
       - assert (H' : WF_Matrix (normalize v)). 
         { unfold normalize. 
           auto with wf_db. }
         apply lin_indep_out_of_v in H'; try easy.
         destruct H' as [S0 [H1 [H2 H3]]].
         rewrite (split S0) in H2.
         apply (extend_onb (S n) n 0 (get_vec 0 S0) (reduce_col S0 0)) in H2. 
         destruct H2 as [T [H4 H5]].
         exists (smash (get_vec 0 S0) T). split; try easy.
         assert (H' : S n = 1 + n). lia. rewrite H'.
         apply WF_smash; try easy.
         apply WF_get_vec; easy.
         apply WF_get_vec; easy.
         apply (WF_reduce_col 0) in H1.
         rewrite easy_sub7 in *; easy.
         lia. 
         rewrite H3; apply orthonormal_normalize_v; easy.
         unfold not; intros; apply H0.
         prep_matrix_equality. 
         assert (H2 : (normalize v) x y = C0).
         { rewrite H1; easy. }
         unfold Zero; simpl. 
         unfold normalize, scale in H2.
         destruct (Ceq_dec (v x y) C0); try easy.
         assert (H3 : norm v <> 0%R).
         { unfold not; intros.
           apply norm_zero_iff_zero in H.
           apply H in H3; easy. }
         assert (H4 : / norm v <> C0).
         { destruct (Ceq_dec (/ norm v) C0); try easy.
           assert (H4' : (norm v * / norm v = norm v * C0)%C).
           rewrite e; easy.
           rewrite Cmult_0_r, Cinv_r in H4'. 
           assert (H5 : C1 <> C0). 
           { apply C0_fst_neq.
             simpl. 
             apply R1_neq_R0. }
           easy.
           apply RtoC_neq; easy. }
         apply (Cmult_neq_0 _ (v x y)) in H4; easy.
Qed.


(********************************************************************)
(* Defining unitary matrices and proving some basic lemmas/examples *)
(********************************************************************)


Definition unitary {n : nat} (A : Square n) : Prop :=
  A × (A†) = I n. 



Lemma X_unitary : unitary σx. Proof. lma'. Qed.
Lemma Y_unitary : unitary σy. Proof. lma'. Qed.
Lemma Z_unitary : unitary σz. Proof. lma'. Qed.
Lemma P_unitary : unitary Phase. Proof. rewrite PEqP'. lma'. Qed.
Lemma T_unitary : unitary Tgate. 
Proof. lma'. unfold Mmult, adjoint, I.
       simpl. 
       assert (H : (Cexp (PI / 4)) ^* = Cexp (- PI / 4)).
       { autorewrite with Cexp_db. lca. }
       assert (H1 : (- PI / 4 = - (PI / 4))%R ). { lra. } 
       rewrite H1 in H; rewrite H.
       rewrite Cexp_mul_neg_r. lca. 
Qed.


Lemma cnot_unitary : unitary cnot. Proof. lma'. Qed.
Lemma notc_unitary : unitary notc. Proof. lma'. Qed.


Lemma H_unitary : unitary hadamard.
Proof. assert (H : hadamard † = hadamard). { lma'. }
       unfold unitary; rewrite H.
       lma'; Hhelper.
Qed.

Lemma unit_I : forall (n : nat), unitary (I n).
Proof. intros. unfold unitary. rewrite Mmult_1_l'.
       apply id_adjoint_eq. 
Qed.


Lemma unit_mult : forall {n} (A B : Square n),
  unitary A -> unitary B -> unitary (A × B).
Proof. intros. unfold unitary in *.
       rewrite Mmult_adjoint.
       rewrite Mmult_assoc.
       rewrite <- (Mmult_assoc B _ _).
       rewrite H0. rewrite Mmult_1_l'.
       rewrite H. reflexivity.
Qed.

Lemma unit_kron : forall {n m} (A : Square n) (B : Square m),
  unitary A -> unitary B -> unitary (A ⊗ B).
Proof. intros. unfold unitary in *.
       rewrite kron_adjoint.
       rewrite kron_mixed_product.
       rewrite H, H0.
       rewrite id_kron.
       reflexivity.
Qed.


Lemma unit_scale : forall {n} (c : C) (A : Square n),
  unitary A -> (c * c ^*)%C = C1 -> unitary (c .* A).
Proof. intros. 
       simpl. unfold unitary. 
       distribute_adjoint.
       distribute_scale.
       rewrite H, H0. 
       lma'. 
Qed.


Lemma unit_big_kron : forall (n : nat) (ls : list (Square n)), 
  (forall a, In a ls -> unitary a) -> unitary (⨂ ls).
Proof. intros. induction ls as [| h].
       - simpl. apply unit_I.
       - simpl. 
         apply unit_kron. 
         apply H. left. easy. 
         apply IHls. 
         intros. 
         apply H. right. easy.
Qed.


Lemma unit_adjoint : forall {n} (A : Square n),
  unitary A -> unitary (A†).
Proof. intros.
       unfold unitary in *.
       rewrite adjoint_involutive.
       apply Minv_flip.
       assumption.
Qed.


Hint Resolve X_unitary Y_unitary Z_unitary P_unitary H_unitary T_unitary : unit_db.
Hint Resolve cnot_unitary notc_unitary unit_I unit_mult unit_kron unit_adjoint unit_scale unit_big_kron: unit_db.



Lemma unit_is_orthonormal : forall {n} (U : Square n),
  WF_Matrix U -> (unitary U <-> orthonormal U).
Proof. intros n U H0'. split. 
       - split.
         * unfold orthogonal. intros.
           rewrite inner_product_is_mult.
           unfold unitary in H. apply Minv_flip in H.
           rewrite H. 
           unfold I. bdestruct (i =? j).
           + rewrite H1 in H0. easy.
           + reflexivity.
         * intros. unfold norm.
           assert (H1 : ((get_vec i U) † × get_vec i U) 0%nat 0%nat = 
                        inner_product (get_vec i U) (get_vec i U)).
           { unfold inner_product. reflexivity. }
           rewrite H1. rewrite inner_product_is_mult.
           unfold unitary in H. apply Minv_flip in H.
           rewrite H. unfold I.
           apply Nat.ltb_lt in H0. rewrite H0.
           assert (H' : i =? i = true). { apply Nat.eqb_eq. easy. }
           rewrite H'. simpl. apply sqrt_1. 
       - intros [H1 H2]. unfold unitary.
         apply Minv_flip.
         prep_matrix_equality.
         rewrite <- inner_product_is_mult.
         unfold orthogonal in H1. unfold I.
         bdestruct (x =? y).
         * bdestruct (x <? n).
           + simpl. apply H2 in H0.
             unfold norm in H0; unfold inner_product.
             apply sqrt_1_unique in H0.
             unfold RtoC.
             apply c_proj_eq.
             rewrite <- H, H0. easy.
             rewrite H.
             rewrite norm_real. easy.
           + unfold get_vec, inner_product, Mmult.
             simpl. apply Csum_0.
             unfold adjoint. intros.
             unfold WF_Matrix in H0'.
             rewrite H0'. simpl.
             rewrite Cconj_0.
             rewrite Cmult_0_l.
             reflexivity. right. apply H0.
         * simpl. rewrite H1.
           reflexivity. apply H.
Qed.


Lemma unit_out_of_v : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> v <> Zero -> 
  exists S : Matrix n n, WF_Matrix S /\ unitary S /\ get_vec 0 S = normalize v.
Proof. intros.
       apply onb_out_of_v in H; try easy.
       destruct H as [S [H1 [H2 H3]]].
       exists S. split; try easy.
       split; try easy.
       apply unit_is_orthonormal; easy.
Qed.


Lemma det_by_unit : forall {n} (A B X : Square n),
  unitary X -> (forall i, A × (get_vec i X) = B × (get_vec i X)) -> A = B.
Proof. intros. assert (H' : A × X = B × X).
       { apply det_by_get_vec. intros.
         do 2 (rewrite <- get_vec_mult).
         apply H0. }
       rewrite <- Mmult_1_r'.
       rewrite <- (Mmult_1_r' A).
       rewrite <- H.
       do 2 (rewrite <- Mmult_assoc).
       rewrite H'.
       reflexivity. 
Qed.


(***********************************************************************************)
(* We now define diagonal matrices and diagonizable matrices, proving basic lemmas *)
(***********************************************************************************)

Definition diagonal {n : nat} (A : Square n) : Prop := 
  forall i j, i <> j -> A i j = C0.


Lemma diag_Zero : forall n : nat, diagonal (@Zero n n).
Proof. intros n. unfold diagonal. reflexivity. Qed.

Lemma diag_I : forall n : nat, diagonal (I n). 
Proof. 
  unfold diagonal, I; intros.
  bdestruct (i =? j). 
  - easy. 
  - easy.
Qed.

Lemma diag_I1 : diagonal (I 1). Proof. apply diag_I. Qed.

Lemma diag_scale : forall {n : nat} (r : C) (A : Square n), 
  diagonal A -> diagonal (r .* A).
Proof.
  unfold diagonal, scale.
  intros n r A H i j H0. 
  apply H in H0. 
  rewrite H0.
  rewrite Cmult_0_r.
  reflexivity.
Qed.

Lemma diag_plus : forall {n} (A B : Square n), 
  diagonal A -> diagonal B -> diagonal (A .+ B).
Proof.
  unfold diagonal, Mplus.
  intros n A B H H0 i j H1. 
  rewrite H, H0. 
  rewrite Cplus_0_l.
  reflexivity.
  apply H1. apply H1. 
Qed.

Lemma diag_mult : forall {n : nat} (A B : Square n), 
  diagonal A -> diagonal B -> diagonal (A × B).
Proof.
  unfold diagonal, Mmult.
  intros n A B H H0 i j D.
  apply Csum_0.
  intros x.
  bdestruct (x =? i).
  + rewrite <- H1 in D. 
    rewrite H0, Cmult_0_r.
    reflexivity.
    apply D.
  + rewrite H, Cmult_0_l.    
    reflexivity. auto.
Qed.

(* short lemma to prove diag_kron *)
Lemma div_mod_eq : forall (a b m : nat),
  m <> 0 -> (a / m = b / m) -> (a mod m = b mod m) -> a = b.
Proof. intros a b m H0 Hdiv Hmod.
       rewrite (Nat.mod_eq a m), (Nat.mod_eq b m) in Hmod.
       rewrite Hdiv in Hmod.
       assert (H : m * (b / m) + (a - m * (b / m)) = m * (b / m) + (b - m * (b / m))).
       { rewrite Hmod. reflexivity. }
       rewrite <- (le_plus_minus  (m * (b / m)) a) in H.
       rewrite <- (le_plus_minus  (m * (b / m)) b) in H.
       apply H.
       apply Nat.mul_div_le; apply H0.
       rewrite <- Hdiv; apply Nat.mul_div_le; apply H0.
       apply H0. apply H0.
Qed.


Lemma diag_kron : forall {n m : nat} (A : Square n) (B : Square m), 
                  m <> 0 -> 
                  diagonal A -> diagonal B -> @diagonal (m * n) (A ⊗ B).
Proof.
  unfold diagonal, kron.
  intros n m A B No H H0 i j H1.
  bdestruct (i / m =? j / m).
  - bdestruct (i mod m =? j mod m).
    + apply (div_mod_eq i j m) in No.
      rewrite No in H1. easy.
      apply H2. apply H3.
    + rewrite H0. rewrite Cmult_0_r. reflexivity.
      apply H3.
  - rewrite H. rewrite Cmult_0_l. reflexivity.
    apply H2.
Qed.


Lemma diag_transpose : forall {n : nat} (A : Square n), 
                     diagonal A -> diagonal A⊤. 
Proof. unfold diagonal, transpose. intros n A H i j H0. 
       apply H. auto. 
Qed.

Lemma diag_adjoint : forall {n : nat} (A : Square n), 
      diagonal A -> diagonal A†. 
Proof. unfold diagonal, adjoint, Cconj. intros n A H i j H0.
       rewrite H. lca. auto.
Qed.


Lemma diag_kron_n : forall (n : nat) {m : nat} (A : Square m),
   m <> 0 -> diagonal A ->  diagonal (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply (@diag_kron (m^n) m _ A). 
    apply H. apply IHn. apply H0.
Qed.

Lemma diag_big_kron : forall n (l : list (Square n)), 
                        n <> 0 -> (forall A, In A l -> diagonal A) ->
                         diagonal (⨂ l). 
Proof.                         
  intros n l nNeq0 H.
  induction l.
  - simpl. apply diag_I.
  - simpl. apply (@diag_kron _ (n^(length l)) a (⨂ l)). 
    apply Nat.pow_nonzero; apply nNeq0.
    apply H. simpl. auto. 
    apply IHl. 
    intros A H'. apply H.
    simpl. auto.
Qed. 


Lemma diag_Mmult_n : forall n {m} (A : Square m),
   diagonal A -> diagonal (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply diag_mult; assumption. 
Qed.

(* defining what it means to be diagonalizable *)
Definition diagonalizable {n : nat} (A : Square n) : Prop :=
  exists (X X' B: Square n), 
    diagonal B /\ X × X' = I n /\ B = X × A × X'.

Lemma diag_imps_diagble : forall {n} (A : Square n),
  diagonal A -> diagonalizable A.
Proof. intros. unfold diagonalizable.
       exists (I n), (I n), A. 
       split.
       apply H.  
       do 2 (rewrite Mmult_1_l'). 
       rewrite Mmult_1_r'.
       auto.
Qed.


Lemma diagble_Zero : forall n : nat, diagonalizable (@Zero n n).
Proof. intros. apply diag_imps_diagble. 
       apply diag_Zero.
Qed.


Lemma diagble_I : forall n : nat, diagonalizable (I n). 
Proof. intros. apply diag_imps_diagble.
       apply diag_I.
Qed.

Lemma diagble_I1 : diagonal (I 1). Proof. apply diag_I. Qed.
  


Lemma diagble_scale : forall {n : nat} (r : C) (A : Square n), 
  diagonalizable A -> diagonalizable (r .* A).
Proof.
  unfold diagonalizable.
  intros. do 3 (destruct H).
  destruct H as [H1 H2]; destruct H2 as [H2 H3].
  exists x, x0, (r .* x1); split. 
  apply diag_scale; apply H1. split.
  apply H2.
  rewrite Mscale_mult_dist_r;
  rewrite Mscale_mult_dist_l.
  rewrite H3.
  reflexivity. 
Qed.


(***********************************)
(* Defining Cprod, similar to Csum *)
(***********************************)

Fixpoint Cprod (f : nat -> C) (n : nat) : C := 
  match n with
  | 0 => C1
  | S n' => (Cprod f n' *  f n')%C
  end.


Lemma Cprod_0_bounded : forall (f : nat -> C) (n : nat),
  (exists i, i < n /\ f i = C0) -> Cprod f n = C0. 
Proof. intros. 
       induction n as [| n'].
       - destruct H; lia.
       - destruct H as [i [H1 H2]].
         bdestruct (i <? n'); bdestruct (i =? n'); try lia. 
         + simpl. rewrite IHn'; try lca.
           exists i. easy.
         + simpl. rewrite <- H0.
           rewrite H2; lca.
Qed.


Lemma Cprod_eq_bounded : forall (f g : nat -> C) (n : nat),
  (forall i : nat, i < n -> f i = g i) -> Cprod f n = Cprod g n.
Proof. intros.
       induction n as [| n'].
       - easy.
       - simpl.
         rewrite IHn', H; try lia; try easy.
         intros. apply H; lia. 
Qed.


         
  
Lemma Cprod_extend_r : forall (f : nat -> C) (n : nat),
  (Cprod f n * f n)%C = Cprod f (S n).
Proof. easy. Qed.


Lemma Cprod_extend_l : forall (f : nat -> C) (n : nat),
  (f 0 * (Cprod (fun x => f (S x)) n))%C = Cprod f (S n).
Proof. intros.
       induction n.
       + simpl; lca.
       + simpl.
         rewrite Cmult_assoc.
         rewrite IHn.
         simpl.
         reflexivity.
Qed.


Lemma Cprod_product : forall (f g h : nat -> C) (n : nat),
  (forall i, i < n -> h i = (f i * g i)%C) -> ((Cprod f n) * (Cprod g n))%C = Cprod h n.
Proof. induction n.
       + intros. lca. 
       + intros. simpl. 
         rewrite <- IHn, H; try lca; try lia. 
         intros. apply H; try lia. 
Qed.


(************************************)
(* Defining upper triangular matrix *) 
(************************************)

Definition upper_triangular {n} (A : Square n) : Prop :=
  forall i j, i > j -> A i j = C0.



Lemma up_tri_Zero : forall n : nat, upper_triangular (@Zero n n).
Proof. intros n. unfold upper_triangular. reflexivity. Qed.

Lemma up_tri_I : forall n : nat, upper_triangular (I n). 
Proof. 
  unfold upper_triangular, I; intros.
  bdestruct (i =? j); try lia; easy.
Qed.

Lemma up_tri_I1 : diagonal (I 1). Proof. apply diag_I. Qed.

Lemma up_tri_scale : forall {n : nat} (r : C) (A : Square n), 
  upper_triangular A -> upper_triangular (r .* A).
Proof.
  unfold upper_triangular, scale.
  intros.
  rewrite H; try lca; easy.
Qed.

Lemma up_tri_plus : forall {n} (A B : Square n), 
  upper_triangular A -> upper_triangular B -> upper_triangular (A .+ B).
Proof.
  unfold upper_triangular, Mplus.
  intros n A B H H0 i j H1. 
  rewrite H, H0; try lca; easy. 
Qed.


Lemma up_tri_mult : forall {n : nat} (A B : Square n), 
  upper_triangular A -> upper_triangular B -> upper_triangular (A × B).
Proof.
  unfold upper_triangular, Mmult.
  intros n A B H H0 i j D.
  apply Csum_0.
  intros x.
  bdestruct (x <? i); bdestruct (j <? x); try lia.
  + rewrite H; try lca; lia.
  + rewrite H; try lca; lia.
  + rewrite H0; try lca; lia.
Qed.


Lemma up_tri_reduce_0 : forall {n : nat} (A : Square n),
  upper_triangular A -> upper_triangular (reduce A 0 0).
Proof. 
  unfold upper_triangular, reduce.
  intros. 
  bdestruct (i <? 0); bdestruct (j <? 0); try lia.
  apply H; lia. 
Qed.



Lemma det_up_tri_diags : forall {n : nat} (A : Square n),
  upper_triangular A -> 
  Determinant n A = Cprod (fun i => A i i) n.
Proof. induction n as [| n'].
       - easy.
       - intros. simpl. 
         destruct n' as [| n''].
         + lca. 
         + assert (H' : (Cprod (fun i : nat => A i i) (S n'') * A (S n'') (S n'') =
                         A 0 0 * Cprod (fun i : nat => (reduce A 0 0) i i) (S n''))%C).
           { rewrite <- Cprod_extend_l.
             rewrite <- Cprod_extend_r.  
             rewrite <- Cmult_assoc; easy. }
           rewrite H'.
           rewrite <- Csum_extend_l.
           rewrite <- Cplus_0_r.
           rewrite <- Cplus_assoc.
           apply Csum_simplify.
           simpl parity. 
           rewrite IHn'; try lca.
           apply up_tri_reduce_0; easy.
           unfold upper_triangular in H.
           rewrite H; try lia. 
           rewrite <- Cplus_0_r.
           apply Csum_simplify; try lca. 
           apply Csum_0_bounded.
           intros. 
           rewrite H; try lia; lca. 
Qed.



Lemma det_multiplicative_up_tri : forall {n} (A B : Square n),
  upper_triangular A -> upper_triangular B -> 
  (Determinant n A * Determinant n B)%C = Determinant n (A × B).
Proof. intros. 
       rewrite det_up_tri_diags; try easy.
       rewrite det_up_tri_diags; try easy.
       rewrite det_up_tri_diags; try apply up_tri_mult; try easy.
       apply Cprod_product.
       intros. unfold Mmult.
       apply Csum_unique.
       exists i.
       split. easy. split. easy.
       intros. 
       bdestruct (i <? x'); bdestruct (x' <? i); try lia.
       rewrite H0; try lia; lca.
       rewrite H; try lia; lca.
Qed.



(**************************************************)
(* Defining eignestates to be used in type system *)
(**************************************************)


Definition Eigenpair {n : nat} (U : Square n) (p : Vector n * C) : Prop :=
  U × (fst p) = (snd p) .* (fst p).

Lemma all_v_eigen_I : forall (n : nat) (v : Vector n),
   Eigenpair (I n) (v, C1).
Proof. intros n v. unfold Eigenpair. 
       simpl. rewrite Mmult_1_l'. lma. 
Qed.


Lemma diags_have_basis_eigens : forall (n : nat) (U : Square n) (i : nat),
  (i < n) -> diagonal U -> Eigenpair U (e_i i, U i i).
Proof. unfold diagonal, Eigenpair, e_i. intros.
       unfold Mmult, scale.
       prep_matrix_equality.
       eapply Csum_unique. exists i. 
       split. apply H.
       split.
       - simpl. bdestruct (x =? i).
         * rewrite H1. bdestruct (i =? i). 
           reflexivity. easy. 
         * simpl.  
           rewrite H0.
           rewrite Cmult_0_l, Cmult_0_r. 
           reflexivity. apply H1.
       - intros. simpl. bdestruct (x' =? i).
         * rewrite H2 in H1. easy.
         * simpl. rewrite Cmult_0_r.
           reflexivity.
Qed.


Lemma eigen_scale : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  Eigenpair A (v, c1) -> Eigenpair (c2 .* A) (v, Cmult c1 c2).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite Mscale_mult_dist_l.
       rewrite H.
       rewrite Mscale_assoc.
       rewrite Cmult_comm.
       reflexivity.
Qed.


Lemma eigen_scale_div : forall {n} (A : Square n) (v : Vector n) (c1 c2 : C),
  c2 <> C0 -> Eigenpair (c2 .* A) (v, Cmult c2 c1) -> Eigenpair A (v, c1).
Proof. intros. 
       unfold Eigenpair in *; simpl in *. 
       rewrite <- Mscale_assoc in H0.
       rewrite Mscale_mult_dist_l in H0.
       apply Mscale_div in H0;
       assumption.
Qed.


Lemma eig_unit_conv : forall {n} (v : Vector n) (c : C) (U B : Square n),
  unitary U -> Eigenpair B (U × v, c) -> Eigenpair (U† × B × U) (v, c).  
Proof. intros. 
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H0.
       rewrite Mscale_mult_dist_r.
       rewrite <- Mmult_assoc.
       unfold unitary in H.
       apply Minv_flip in H.
       rewrite H.
       rewrite Mmult_1_l'.
       reflexivity.
Qed.




Lemma eig_unit_norm1 : forall {n} (U : Square n) (c : C),
  unitary U -> (exists v, WF_Matrix v /\ v <> Zero /\ Eigenpair U (v, c)) -> (c * c^* = C1)%C.
Proof. intros. destruct H0 as [v [H0 [H1 H2]]].
       unfold Eigenpair in H2; simpl in H2. 
       assert (H3 : (U × v)† = (c .* v)†). rewrite H2; easy.
       rewrite Mmult_adjoint, Mscale_adj in H3.
       assert (H4 : ((v) † × (U) †) × (U × v) = (c ^* .* (v) †) × (c .* v)).
       { rewrite H2, H3; easy. } 
       rewrite Mmult_assoc in H4.
       rewrite <- (Mmult_assoc _ U v) in H4.
       apply Minv_flip in H.
       rewrite H in H4.
       rewrite Mmult_1_l' in H4.
       rewrite Mscale_mult_dist_r in H4.
       rewrite Mscale_mult_dist_l in H4.
       rewrite Mscale_assoc in H4.
       assert (H' : ((v) † × v) 0 0 = (c * c ^* .* ((v) † × v)) 0 0).
       rewrite <- H4; easy.
       assert (H'' : ((v) † × v) 0 0 = inner_product v v). easy.
       unfold scale in H'.
       rewrite H'' in H'.
       apply (Cmult_simplify (inner_product v v) (c * c ^* * inner_product v v)
                            (/ (inner_product v v)) (/ (inner_product v v))) in H'; try easy.
       rewrite <- Cmult_assoc in H'.
       rewrite Cinv_r in H'.
       rewrite H'; lca.
       unfold not; intros; apply H1.
       apply inner_product_zero_iff_zero in H0.
       apply H0; easy.
Qed.


Lemma lin_ind_has_eigen : forall {n} (X : Square n),
  (exists X', X × X' = I n) -> exists p, Eigenpair X p /\ fst p <> Zero /\ WF_Matrix (fst p).
Proof. Admitted. 


Lemma ind_step1 : forall {n} (A : Square (n + 1)),
  WF_Matrix A -> unitary A -> 
  exists X, unitary X /\
  (forall x, x <> 0 -> (X†×A×X) x 0 = C0).
Proof. intros. 
       assert (H' : exists p, Eigenpair A p /\ fst p <> Zero /\ WF_Matrix (fst p)).  
       { apply lin_ind_has_eigen. exists A†. apply H0. }
       destruct H'; destruct H1 as [H1 H2]; destruct H2 as [H2 H3]; destruct x.
       simpl in *.
       assert (H' : exists x, m x 0 <> C0). 
       { apply nonzero_vec_nonzero_elem.
         apply H3. apply H2. }


Lemma nonzero_vec_nonzero_elem : forall {n} (v : Vector n),
  WF_Matrix v -> v <> Zero -> exists x, v x 0 <> C0.


       exists (v_to_onb m). split. 
       - apply onb_unit. 
         apply H3. apply H2.
       - intros x H4. 
         rewrite <- (get_vec_conv x 0 _).
         rewrite matrix_by_basis.
         rewrite Mmult_assoc.
         rewrite <- matrix_by_basis.
         assert (H' : get_vec 0 (v_to_onb m) = normalize m /\ orthonormal (v_to_onb m)).
         { apply gram_schmidt_ver. apply H2. }
         destruct H' as [H5 H6].
         rewrite H5.
         unfold normalize.
         rewrite Mmult_assoc.
         rewrite Mscale_mult_dist_r. 
         unfold Eigenpair in H1; simpl in H1.
         rewrite H1. rewrite Mscale_assoc.
         rewrite Cmult_comm.
         rewrite <- Mscale_assoc.
         rewrite Mscale_mult_dist_r. 
         assert (H' : (v_to_onb m) † × (/ norm m .* m) = @e_i (n+1) 0).
         { apply (inverse_is_valid (v_to_onb m) _ (e_i 0) _). 
           apply unit_is_orthonormal in H6; 
           unfold unitary in H6. apply H6.
           apply WF_onb. apply H3.
           rewrite <- matrix_by_basis.
           rewrite H5. reflexivity. 
           apply WF_onb. apply H3. }
         rewrite H'.
         unfold scale, e_i.
         bdestruct (x =? 0).
         + rewrite H7 in H4. easy.
         + simpl. rewrite Cmult_0_r.
           reflexivity.
         + apply WF_onb. apply H3.
         + apply WF_mult. apply WF_mult.
           apply WF_adjoint. apply WF_onb. apply H3.
           apply H. apply WF_onb. apply H3.
Qed.           


       
Lemma ind_step2 : forall {n} (A : Square (n + 1)),
  WF_Matrix A -> unitary A -> 
  exists X, unitary X /\ @unitary n (reduce (X†×A×X) 0 0) /\ 
  (forall x y, (x = 0 \/ y = 0) /\ x <> y -> (X†×A×X) x y = C0).
Admitted. 


(* Now, we build up the main important theorem *)
Theorem unit_implies_diagble : forall {n} (A : Square n),
  WF_Matrix A -> unitary A -> diagonalizable A.
Proof. induction n as [| n']. 
       - intros. assert (H' : A = Zero).
         { unfold Zero; unfold WF_Matrix in H.
           prep_matrix_equality.
           rewrite H. easy.
           left. apply le_0_n. } 
         rewrite H'. 
         apply diagble_Zero.
       - intros. unfold unitary in H0.
         assert (H' : exists p, Eigenpair A p /\ fst p <> Zero).  
Admitted. 






(* we want to prove *)

Definition eq_eigs {n : nat} (U1 U2 : Square n) : Prop := 
  forall p, Eigenpair U1 p -> Eigenpair U2 p. 


(* this is the main lemma we will need to assume *)
Lemma eq_eigs_implies_eq : forall {n} (U1 U2 : Square n),
  unitary U1 -> unitary U2 -> eq_eigs U1 U2 -> U1 = U2.
Proof. Admitted.


Theorem eigs_eq_gate : forall {n} (U1 U2 : Square n),
  unitary U1 -> unitary U2 -> (U1 = U2 <-> eq_eigs U1 U2).
Proof. intros. split.
       - intros H'; rewrite H'; easy.
       - apply eq_eigs_implies_eq.
         apply H. apply H0.
Qed.





Local Close Scope nat_scope.

(*******************************)
(* Some actual examples/lemmas *)
(*******************************)



Definition qubitP : Vector 2 := / (√ 2) .* (∣0⟩ .+ ∣1⟩).
Definition qubitM : Vector 2 := / (√ 2) .* (∣0⟩ .+ ((-1) .* ∣1⟩)).
Definition EPRpair : Vector 4 := / (√ 2) .* (∣0,0⟩ .+ ∣1,1⟩).

Lemma EPRpair_creation : cnot × (hadamard ⊗ I 2) × ∣0,0⟩ = EPRpair.
Proof. unfold EPRpair. lma'.
Qed.

                                                                 
Notation "∣+⟩" := qubitP.
Notation "∣-⟩" := qubitM.
Notation "∣Φ+⟩" := EPRpair.

Lemma WF_qubitP : WF_Matrix ∣+⟩. Proof. show_wf. Qed.
Lemma WF_qubitM : WF_Matrix ∣-⟩. Proof. show_wf. Qed.
Lemma WF_EPRpair : WF_Matrix ∣Φ+⟩. Proof. unfold EPRpair. auto with wf_db.  Qed.

Hint Resolve WF_qubitP WF_qubitM WF_EPRpair : wf_db. 

Lemma EigenXp : Eigenpair σx (∣+⟩, C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenXm : Eigenpair σx (∣-⟩, -C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenZ0 : Eigenpair σz (∣0⟩, C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenZ1 : Eigenpair σz (∣1⟩, -C1).
Proof. unfold Eigenpair. lma'.
Qed.

Lemma EigenXXB : Eigenpair (σx ⊗ σx) (∣Φ+⟩, C1).
Proof. unfold Eigenpair. lma'.
Qed.


Hint Resolve EigenXp EigenXm EigenZ0 EigenZ1 EigenXXB all_v_eigen_I : eig_db.


(***********************************************************)
(* Important lemmas about eigenvectors of unitary matrices *)
(***********************************************************)

Fixpoint list_eq {X : Type} (l1 l2 : list X) : Prop :=
  match l1 with
  | [] => l2 = []
  | h1 :: l1' => 
      match l2 with
      | [] => False
      | h2 :: l2' => h1 = h2 /\ list_eq l1' l2'
      end
  end.

Lemma list_eq_same : forall {X} (ls : list X),
  list_eq ls ls. 
Proof. induction ls as [| h].
       * easy.
       * easy.
Qed.

Lemma list_eq_implies_eq : forall {X} (l1 l2 : list X),
  list_eq l1 l2 -> l1 = l2.
Proof. induction l1 as [| h1].
       - easy.
       - intros. destruct l2 as [| h2].
         * easy.
         * simpl in H; destruct H as [H1 H2].
           apply IHl1 in H2. 
           rewrite H1, H2; reflexivity.
Qed.

Lemma list_eq_is_eq : forall {X} (l1 l2 : list X),
  l1 = l2 <-> list_eq l1 l2.  
Proof. intros. split. 
       - intros H; rewrite H; apply list_eq_same.
       - apply list_eq_implies_eq.
Qed.


Definition det2 (U : Square 2) : C := 
  ((U 0%nat 0%nat) * (U 1%nat 1%nat)) - 
  ((U 0%nat 1%nat) * (U 1%nat 0%nat)).

(* must figure out a good way to do this... *) 
Definition sqrtC (c : C) : C :=
  sqrt (fst c).


Definition quad_solver (a b c : C) : list C :=
  [(-b + sqrtC (b^2 - 4%C * a * c)) / (2*a) ; 
   (-b - sqrtC (b^2 - 4%C * a * c)) / (2*a)].


Definition get_eig_vals (U : Square 2) : list C :=
  quad_solver 1 (- (U 0%nat 0%nat + U 1%nat 1%nat)) (det2 U).

Lemma helper : sqrtC 4 = 2.
Proof. unfold sqrtC. simpl. apply c_proj_eq. simpl. 
       assert (H : 2%R ^2 = 4%R). { simpl. lca. } 
       unfold RtoC in H. apply sqrt_lem_1. lra. lra. lra. easy. 
Qed.

Lemma evs_σx : get_eig_vals σx = [C1 ; - C1].
Proof. unfold get_eig_vals. 
       unfold det2. 
       unfold quad_solver.
       apply list_eq_is_eq.
       simpl. Csimpl. 
       assert (H: (- 0 * - 0 - 4 * (0 - 1)) = 4).
       { lca. }
       rewrite H; rewrite helper. 
       split.
       - lca. 
       - split. lca. easy. 
Qed.



