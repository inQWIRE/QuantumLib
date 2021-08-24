Require Import List.    
Require Export Complex. 
Require Export Matrix.
Require Export Quantum.
Require Export Polynomial.


(* Some preliminary lemmas/additions to tactics that could be moved to other files *)


Local Open Scope nat_scope.


(* where can I find tactics to deal with this??? *)
Lemma easy_sub3 : forall (n k : nat), n <> 0 -> n + k - 0 - 1 = n - 0 - 1 + k. 
Proof. intros. 
       destruct n as [| n].
       - easy.
       - simpl. lia. 
Qed.

Lemma easy_sub6 : forall (a c b : nat), 
  b < c -> a < b -> c = (a + S (b - a) + (c - b - 1)).
Proof. intros. lia. Qed.




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
         replace (n - 0) with n by lia. 
         nia. 
Qed.

Lemma easy_pow6' : forall (n : nat), n <> 0 -> (2^n)*2 = (2*2^(n-1))*2. 
Proof. intros. rewrite mult_comm.
       apply easy_pow6; easy.
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


Lemma zipWith_cons : forall {X Y Z : Type} (f : X -> Y -> Z) (a : X) (b : Y) (A : list X) (B : list Y),
  zipWith f (a :: A) (b :: B) = (f a b) :: (zipWith f A B).
Proof. intros. 
       unfold zipWith. simpl. 
       unfold uncurry. 
       simpl. easy. 
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
         
Lemma switch_switch_diff : forall {X : Type} (n m : nat) (ls : list X) (a b : X), 
  n <> m ->
  switch (switch ls a n) b m = switch (switch ls b m) a n.
Proof. induction n as [| n'].
       - intros. 
         destruct m; destruct ls; easy. 
       - intros. 
         destruct m; try (destruct ls; easy). 
         destruct ls; try easy. 
         simpl. 
         rewrite IHn'; try easy.
         bdestruct (n' =? m); lia. 
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


Lemma big_kron_app : forall {n m} (l1 l2 : list (Matrix n m)),
  (forall i, WF_Matrix (nth i l1 (@Zero n m))) ->
  (forall i, WF_Matrix (nth i l2 (@Zero n m))) ->
  ⨂ (l1 ++ l2) = (⨂ l1) ⊗ (⨂ l2).
Proof. induction l1.
       - intros. simpl. rewrite (kron_1_l _ _ (⨂ l2)); try easy.
         apply (WF_big_kron _ _ _ (@Zero n m)); easy.
       - intros. simpl. rewrite IHl1. 
         rewrite kron_assoc.
         do 2 (rewrite <- easy_pow).
         rewrite app_length.
         reflexivity.
         assert (H' := H 0); simpl in H'; easy.
         all : try apply (WF_big_kron _ _ _ (@Zero n m)); try easy. 
         all : intros. 
         all : assert (H' := H (S i)); simpl in H'; easy.
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


Definition orthogonal {n m} (S : Matrix n m) : Prop := 
  forall i j, i <> j -> inner_product (get_vec i S) (get_vec j S) = C0.


Definition orthonormal {n m} (S : Matrix n m) : Prop :=
  orthogonal S /\ (forall (i : nat), i < m -> norm (get_vec i S) = 1%R).

(* to match WF_Unitary *)
Definition WF_Orthonormal {n m} (S : Matrix n m) : Prop := 
  WF_Matrix S /\ orthonormal S. 


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


(***********************************************************)
(* Defining and proving lemmas relating to the determinant *)
(***********************************************************)


Fixpoint parity (n : nat) : C := 
  match n with 
  | 0 => C1 
  | S 0 => -C1
  | S (S n) => parity n
  end. 


Lemma parity_S : forall (n : nat),
  (parity (S n) = -C1 * parity n)%C. 
Proof. intros.
       induction n as [| n']; try lca.
       rewrite IHn'.
       simpl. lca. 
Qed.


Fixpoint Determinant (n : nat) (A : Square n) : C :=
  match n with 
  | 0 => C1
  | S 0 => A 0 0
  | S n' => (Csum (fun i => (parity i) * (A i 0) * (Determinant n' (reduce A i 0)))%C n)
  end.


Lemma Det_simplify : forall {n} (A : Square (S (S n))),
  Determinant (S (S n)) A =  
  (Csum (fun i => (parity i) * (A i 0) * (Determinant (S n) (reduce A i 0)))%C (S (S n))).
Proof. intros. easy. Qed.


Lemma Det_simplify_fun : forall {n} (A : Square (S (S (S n)))),
  (fun i : nat => parity i * A i 0 * Determinant (S (S n)) (reduce A i 0))%C =
  (fun i : nat => (Csum (fun j => 
           (parity i) * (A i 0) * (parity j) * ((reduce A i 0) j 0) * 
           (Determinant (S n) (reduce (reduce A i 0) j 0)))%C (S (S n))))%C.
Proof. intros. 
       apply functional_extensionality; intros. 
       rewrite Det_simplify. 
       rewrite Csum_mult_l. 
       apply Csum_eq_bounded; intros. 
       lca. 
Qed.


Lemma reduce_I : forall (n : nat), reduce (I (S n)) 0 0 = I n.
Proof. intros.
       apply mat_equiv_eq.
       apply WF_reduce; try lia; auto with wf_db.
       rewrite easy_sub.
       apply WF_I.
       unfold mat_equiv; intros.
       unfold reduce, I.
       bdestruct (i <? 0); bdestruct (j <? 0); try lia. 
       easy. 
Qed.       

Lemma Det_I : forall (n : nat), Determinant n (I n) = C1.
Proof. intros.
       induction n as [| n'].
       - easy.
       - simpl. destruct n'; try easy.
         rewrite <- Csum_extend_l.
         rewrite <- Cplus_0_r.
         rewrite <- Cplus_assoc.
         apply Csum_simplify.
         rewrite reduce_I, IHn'.
         lca.
         rewrite Csum_extend_r.
         apply Csum_0_bounded; intros.
         replace (I (S (S n')) (S x) 0) with C0 by easy.
         lca. 
Qed.


Definition M22 : Square 2 :=
  fun x y => 
  match (x, y) with
  | (0, 0) => 1%R
  | (0, 1) => 2%R
  | (1, 0) => 4%R
  | (1, 1) => 5%R
  | _ => C0
  end.


Lemma Det_M22 : (Determinant 2 M22) = (Copp (3%R,0%R))%C.
Proof. lca. Qed.


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
             rewrite easy_sub.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca.
           * destruct col. 
             rewrite col_scale_reduce_same; try lia. 
             unfold col_scale. bdestruct (0 =? 0); try lia. 
             lca. 
             rewrite col_scale_reduce_before; try lia.
             rewrite easy_sub.
             rewrite IHn; try lia. 
             unfold col_scale. 
             bdestruct (0 =? S col); try lia; lca. 
Qed.


(* some helper lemmas *)
Lemma Det_diff_1 : forall {n} (A : Square (S (S (S n)))),
  Determinant (S (S (S n))) (col_swap A 0 1) = 
  Csum (fun i => (Csum (fun j => ((A i 1) * (A (skip_count i j) 0) * (parity i) * (parity j) * 
                             Determinant (S n) (reduce (reduce A i 0) j 0))%C)  
                             (S (S n)))) (S (S (S n))).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply Csum_eq_bounded; intros. 
       apply Csum_eq_bounded; intros. 
       replace (col_swap A 0 1 x 0) with (A x 1) by easy. 
       assert (H' : @reduce (S (S (S n))) (col_swap A 0 1) x 0 x0 0 = A (skip_count x x0) 0).
       { unfold reduce, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'. 
       repeat rewrite easy_sub in *.
       apply Cmult_simplify; try easy. 
       lca. 
Qed.
Lemma Det_diff_2 : forall {n} (A : Square (S (S (S n)))),
  Determinant (S (S (S n))) A = 
  Csum (fun i => (Csum (fun j => ((A i 0) * (A (skip_count i j) 1) * (parity i) * (parity j) * 
                             Determinant (S n) (reduce (reduce A i 0) j 0))%C)  
                             (S (S n)))) (S (S (S n))).
Proof. intros. 
       rewrite Det_simplify.
       rewrite Det_simplify_fun.
       apply Csum_eq_bounded; intros. 
       apply Csum_eq_bounded; intros. 
       apply Cmult_simplify; try easy. 
       assert (H' : @reduce (S (S (S n))) A x 0 x0 0 = A (skip_count x x0) 1).
       { unfold reduce, col_swap, skip_count. 
         simpl. bdestruct (x0 <? x); try easy. } 
       rewrite H'. 
       repeat rewrite easy_sub in *.
       lca. 
Qed.
  

Lemma Determinant_swap_01 : forall {n} (A : Square n),
  1 < n -> Determinant n (col_swap A 0 1) = (-C1 * (Determinant n A))%C.
Proof. intros.
       destruct n; try lia.
       destruct n; try lia. 
       destruct n.
       - simpl. unfold col_swap, reduce. lca. 
       - rewrite Det_diff_1, Det_diff_2.
         apply Csum_rearrange; intros.
         + unfold skip_count. 
           bdestruct (x <? (S y)); bdestruct (y <? x); try lia.
           rewrite Cmult_assoc.
           apply Cmult_simplify.
           rewrite parity_S.
           lca. 
           rewrite reduce_reduce_0; easy.
         + unfold skip_count. 
           bdestruct (x <? y); bdestruct (y <? (S x)); try lia.
           rewrite Cmult_assoc.
           apply Cmult_simplify.
           rewrite parity_S.
           lca. 
           rewrite <- reduce_reduce_0; easy.
Qed.

Lemma Determinant_swap_adj : forall {n} (A : Square n) (i : nat),
  S i < n -> Determinant n (col_swap A i (S i)) = (-C1 * (Determinant n A))%C.
Proof. induction n as [| n'].
       - easy.
       - intros. 
         destruct i. 
         + apply Determinant_swap_01; easy.
         + simpl. destruct n'; try lia.
           do 2 rewrite Csum_extend_r.
           rewrite Csum_mult_l.
           apply Csum_eq_bounded; intros. 
           rewrite col_swap_reduce_before; try lia. 
           rewrite IHn'; try lia. 
           replace (col_swap A (S i) (S (S i)) x 0) with (A x 0) by easy.
           lca. 
Qed.


Lemma Determinant_swap_ik : forall {n} (k i : nat) (A : Square n),
  i + (S k) < n -> Determinant n (col_swap A i (i + (S k))) = (-C1 * (Determinant n A))%C.
Proof. induction k as [| k'].
       - intros. 
         replace (i + 1) with (S i) by lia. 
         rewrite Determinant_swap_adj; try lia; lca. 
       - intros. 
         rewrite (col_swap_three A i (i + (S k')) (i + (S (S k')))); try lia. 
         rewrite IHk'; try lia. 
         replace (i + (S (S k'))) with (S (i + (S k'))) by lia. 
         rewrite Determinant_swap_adj; try lia.
         rewrite IHk'; try lia. 
         lca. 
Qed.

Lemma Determinant_swap : forall {n} (A : Square n) (i j : nat),
  i < n -> j < n -> i <> j ->
  Determinant n (col_swap A i j) = (-C1 * (Determinant n A))%C.
Proof. intros. 
       bdestruct (i <? j); bdestruct (j <? i); try lia. 
       - replace j with (i + (S (j - i - 1))) by lia. 
         rewrite Determinant_swap_ik; try lia; easy.
       - replace i with (j + (S (i - j - 1))) by lia. 
         rewrite col_swap_diff_order. 
         rewrite Determinant_swap_ik; try lia; easy.
Qed.


Lemma col_0_Det_0 : forall {n} (A : Square n),
  (exists i, i < n /\ get_vec i A = Zero) -> Determinant n A = C0.
Proof. intros n A [i [H H0]].
       destruct n; try easy.
       destruct n.
       destruct i; try lia. 
       replace C0 with (@Zero 1 1 0 0) by easy.
       rewrite <- H0. easy. 
       destruct i.
       - rewrite Det_simplify.
         apply Csum_0_bounded; intros. 
         replace (A x 0) with (@Zero (S (S n)) 1 x 0) by (rewrite <- H0; easy). 
         unfold Zero; lca.
       - rewrite (col_swap_inv _ 0 (S i)).
         rewrite Determinant_swap; try lia.
         rewrite Det_simplify.
         rewrite Csum_mult_l.
         apply Csum_0_bounded; intros. 
         replace (col_swap A 0 (S i) x 0) with 
                 (@Zero (S (S n)) 1 x 0) by (rewrite <- H0; easy). 
         unfold Zero; lca.
Qed.


Lemma col_same_Det_0 : forall {n} (A : Square n) (i j : nat),
  i < n -> j < n -> i <> j -> 
  get_vec i A = get_vec j A ->
  Determinant n A = C0.
Proof. intros. 
       apply eq_neg_implies_0.
       rewrite <- (Determinant_swap _ i j); try easy.
       rewrite (det_by_get_vec (col_swap A i j) A); try easy; intros. 
       prep_matrix_equality. 
       destruct y; try easy.
       bdestruct (i0 =? i); bdestruct (i0 =? j); try lia.
       - rewrite H3, <- col_swap_get_vec, H2; easy.
       - rewrite H4, col_swap_diff_order, <- col_swap_get_vec, H2; easy.
       - unfold col_swap, get_vec. simpl. 
         bdestruct (i0 =? i); bdestruct (i0 =? j); try lia; easy.
Qed.

Lemma col_scale_same_Det_0 : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> 
  get_vec i A = c .* (get_vec j A) ->
  Determinant n A = C0.
Proof. intros. 
       destruct (Ceq_dec c C0).
       - apply col_0_Det_0.
         exists i.
         split; try easy.
         rewrite H2, e.
         apply Mscale_0_l.
       - rewrite (col_scale_inv A j c); try easy.
         rewrite Determinant_scale; try easy.
         assert (H3 : Determinant n (col_scale A j c) = C0).
         { apply (col_same_Det_0 _ i j); try easy.
           prep_matrix_equality.
           unfold get_vec, col_scale. 
           bdestruct (y =? 0); try easy.
           bdestruct (i =? j); bdestruct (j =? j); try lia. 
           rewrite <- get_vec_conv.
           rewrite H2.
           unfold scale.
           rewrite get_vec_conv. 
           easy. }
         rewrite H3.
         lca. 
Qed.


Lemma Det_col_add_comm : forall {n} (T : Matrix (S n) n) (v1 v2 : Vector (S n)),
  (Determinant (S n) (col_wedge T v1 0) + Determinant (S n) (col_wedge T v2 0) = 
   Determinant (S n) (col_wedge T (v1 .+ v2) 0))%C.
Proof. intros. 
       destruct n; try easy.
       do 3 rewrite Det_simplify.
       rewrite <- Csum_plus.
       apply Csum_eq_bounded; intros. 
       repeat rewrite reduce_is_redcol_redrow.
       repeat rewrite col_wedge_reduce_col_same.
       unfold col_wedge, Mplus.
       bdestruct (0 <? 0); bdestruct (0 =? 0); try lia. 
       lca. 
Qed.



Lemma Determinant_col_add0i : forall {n} (A : Square n) (i : nat) (c : C),
  i < n -> i <> 0 -> Determinant n (col_add A 0 i c) = Determinant n A.     
Proof. intros. 
       destruct n; try easy.
       rewrite col_add_split.
       assert (H' := (@Det_col_add_comm n (reduce_col A 0) (get_vec 0 A) (c .* get_vec i A))).
       rewrite easy_sub in *.
       rewrite <- H'.
       replace (Determinant (S n) A) with (Determinant (S n) A + C0)%C by lca. 
       apply Csum_simplify. 
       assert (H1 : col_wedge (reduce_col A 0) (get_vec 0 A) 0 = A).
       { prep_matrix_equality.
         unfold col_wedge, reduce_col, get_vec. 
         destruct y; try easy; simpl.  
         replace (y - 0) with y by lia; easy. }
       rewrite easy_sub, H1 in *; easy.
       apply (col_scale_same_Det_0 _ 0 i c); try lia.
       prep_matrix_equality. 
       unfold get_vec, col_wedge, reduce_col, scale; simpl. 
       bdestruct (y =? 0); bdestruct (i =? 0); try lca; try lia. 
       replace (S (i - 1)) with i by lia. 
       easy. 
Qed.


Lemma Determinant_col_add : forall {n} (A : Square n) (i j : nat) (c : C),
  i < n -> j < n -> i <> j -> Determinant n (col_add A i j c) = Determinant n A.     
Proof. intros. 
       destruct j.
       - rewrite <- col_swap_col_add_0.
         rewrite Determinant_swap. 
         rewrite Determinant_col_add0i.
         rewrite Determinant_swap. 
         lca. 
         all : easy. 
       - destruct i. 
         rewrite Determinant_col_add0i; try easy.
         rewrite <- col_swap_col_add_Si.
         rewrite Determinant_swap. 
         rewrite Determinant_col_add0i.
         rewrite Determinant_swap. 
         lca. 
         all : try easy; try lia. 
Qed.


Lemma Determinant_col_add_many_some : forall (e n col : nat) (A : Square n) (as' : Vector n),
  (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> as' i 0 = C0) -> as' col 0 = C0 ->
  Determinant n A = Determinant n (col_add_many col as' A).
Proof. induction e as [| e].
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col 0)); 
           try lia; try easy.  
         rewrite Determinant_col_add; try lia.
         assert (H' : (col_add_many col (make_row_zero (skip_count col 0) as') A) = A).
         { prep_matrix_equality. 
           unfold col_add_many, make_row_zero, skip_count, gen_new_vec, scale in *. 
           bdestruct (y =? col); try lia; try easy.
           rewrite <- Cplus_0_l.
           rewrite Cplus_comm.
           apply Csum_simplify; try easy.
           rewrite Msum_Csum.
           apply Csum_0_bounded; intros. 
           destruct col; simpl in *. 
           bdestruct (x0 =? 1); try lca. 
           destruct x0; try rewrite H2; try rewrite H1; try lca; try lia. 
           destruct x0; try lca; rewrite H1; try lca; lia. }
         rewrite H'; easy.
         all : apply skip_count_not_skip.
       - intros. 
         rewrite (col_add_many_col_add _ (skip_count col (S e))); 
           try lia; try easy.
         rewrite Determinant_col_add; try lia.
         apply IHe; try lia; try easy.   
         assert (H' : e < S e). lia. 
         apply (skip_count_mono col) in H'.
         lia. 
         intros. 
         unfold skip_count, make_row_zero in *. 
         bdestruct (e <? col); bdestruct (S e <? col); try lia.
         bdestruct (i =? S e); try easy; try apply H1; try lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         bdestruct (S e =? col); try lia. rewrite H6, H8. apply H2.
         apply H1; lia. 
         bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
         apply H1; lia. 
         unfold make_row_zero, skip_count.
         bdestruct (S e <? col); try lia; bdestruct (col =? S e); bdestruct (col =? S (S e)); 
           try lia; try easy.
         all : apply skip_count_not_skip.
Qed.


Lemma Determinant_col_add_many : forall (n col : nat) (A : Square n) (as' : Vector n),
  col < n -> as' col 0 = C0 -> 
  Determinant n A = Determinant n (col_add_many col as' A).
Proof. intros. 
       destruct n; try lia. 
       destruct n.
       - assert (H' : as' == Zero).
         { unfold mat_equiv; intros. 
           destruct col; destruct i; destruct j; try lia. 
           easy. }
         rewrite <- col_add_many_0; easy. 
       - rewrite (col_add_many_mat_equiv _ _ _ (make_WF as'));
           try apply mat_equiv_make_WF.
         apply (Determinant_col_add_many_some n); try lia; try easy.
         unfold skip_count. bdestruct (n <? col); lia. 
         intros. 
         unfold skip_count in H1.
         bdestruct (n <? col).
         bdestruct (col =? S n); try lia. 
         unfold make_WF.
         bdestruct (i <? S (S n)); bdestruct (i =? S n); try lia; try easy. 
         simpl. rewrite H5, <- H3; easy.
         unfold make_WF.
         bdestruct (i <? S (S n)); try lia; easy. 
         unfold make_WF.
         bdestruct (col <? S (S n)); try lia; auto.
         
Qed.

Lemma Determinant_col_add_each_some : forall (e n col : nat) (as' : Matrix 1 n) (A : Square n),
  WF_Matrix as' -> (skip_count col e) < n -> col < n -> 
  (forall i : nat, (skip_count col e) < i -> as' 0 i = C0) -> as' 0 col = C0 ->
  Determinant n A = Determinant n (col_add_each col as' A).
Proof. induction e as [| e].
       - intros.
         rewrite (col_add_each_col_add _ (skip_count col 0)); try lia. 
         rewrite Determinant_col_add; try lia.
         assert (H' : (make_col_zero (skip_count col 0) as') = Zero).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           unfold make_col_zero, skip_count in *.
           destruct i; try lia. 
           destruct col; simpl in *. 
           all : destruct j; try easy; simpl. 
           destruct j; try easy; simpl.  
           all : apply H2; lia. }
         rewrite H'. 
         rewrite <- col_add_each_0; easy. 
         assert (H' := skip_count_not_skip col 0). auto.
         apply skip_count_not_skip.
         intros x. destruct x; try easy.
         assert (H' := skip_count_not_skip col 0). auto.
         apply H; lia.
       - intros. 
         rewrite (col_add_each_col_add _ (skip_count col (S e))); try lia. 
         rewrite Determinant_col_add; try lia.
         apply IHe; try lia; try easy; auto with wf_db. 
         + assert (H' : e < S e). lia. 
           apply (skip_count_mono col) in H'.
           lia. 
         + intros. 
           unfold skip_count, make_col_zero in *. 
           bdestruct (e <? col); bdestruct (S e <? col); try lia.
           bdestruct (i =? S e); try easy; try apply H2; try lia. 
           bdestruct (i =? S e); bdestruct (i =? S (S e)); try lia; try easy. 
           bdestruct (S e =? col); try lia. rewrite H7, H9; easy.
           apply H2. lia. 
           bdestruct (i =? S (S e)); try lia; try easy. 
           apply H2. lia. 
         + unfold make_col_zero. 
           bdestruct (col =? skip_count col (S e)); try easy. 
         + assert (H' := skip_count_not_skip col (S e)). auto.
         + apply skip_count_not_skip.
         + intros.
           destruct x; try easy.
           rewrite H; try lia; easy.
Qed.     
        
         
Lemma lin_indep_col_add_each : forall (n col : nat) (as' : Matrix 1 n) 
                                          (A : Square n),
  col < n -> WF_Matrix as' -> as' 0 col = C0 ->
  Determinant n A = Determinant n (col_add_each col as' A).
Proof. intros. 
       destruct n; try easy. 
       destruct n.
       - assert (H' : as' = @Zero 1 1).
         { apply mat_equiv_eq; auto with wf_db.
           unfold mat_equiv; intros. 
           destruct i; destruct j; destruct col; try lia. 
           easy. }
         rewrite H'. 
         unfold col_add_each.
         rewrite Mmult_0_r, Mplus_0_r.
         easy. 
       - apply (Determinant_col_add_each_some n); try lia; try easy. 
         unfold skip_count. 
         bdestruct (n <? col); lia. 
         intros.
         unfold skip_count in *.
         + bdestruct (n <? col); bdestruct (col =? S n); try lia.
           bdestruct (i =? S n); try lia.  
           rewrite H5, <- H4; apply H1.
           apply H0; right. 
           bdestruct (i =? S n); try lia. 
           apply H0; right. 
           lia. 
Qed.


Lemma Det_0_lindep : forall {n} (A : Square n), 
  WF_Matrix A -> Determinant n A = C0 -> linearly_dependent A.
Proof. induction n as [| n'].
       - intros. 
         unfold Determinant in H.
         assert (H1 := C1_neq_C0).
         easy.
       - intros.
         destruct (gt_dim_lindep (reduce_row A 0)) as [v [H2 [H3 H4]]].
         lia. 
         apply WF_reduce_row; try lia; auto.
         destruct (nonzero_vec_nonzero_elem v) as [x H5]; auto.
         bdestruct (x <? S n').
         + Admitted.
           (*
           apply (lin_dep_col_add_many_conv _ _ x A (make_row_zero x v)); try easy.
           unfold make_row_zero.
           bdestruct_all; lca. 
           rewrite (Determinant_col_add_many _ x _ (make_row_zero x v)) in H0; try easy. 
            *)
          







(***************************************************)
(* showing that all matrices have some eigenvector *)
(***************************************************)


Definition good_M {n} (A : Square n) : Prop :=
  forall (i j k : nat), (A j i <> C0 /\ A k i <> C0 -> j = k). 


Lemma good_M_I : forall (n : nat), good_M (I n).
Proof. unfold good_M, I; intros. 
       destruct H as [H H0].
       bdestruct (j =? i); bdestruct (j <? n); try lia; try easy.
       bdestruct (k =? i); bdestruct (k <? n); try lia; try easy.
Qed.


Lemma good_M_reduce : forall {n} (A : Square n) (x y : nat),
  good_M A -> good_M (reduce A x y).    
Proof. unfold good_M; intros.
       destruct H0 as [H0 H1].
       unfold reduce in *.
       bdestruct (j <? x); bdestruct (k <? x); bdestruct (i <? y).
       - apply (H i j k); auto.
       - apply (H (1 + i) j k); auto.
       - assert (H' : j = 1 + k). apply (H i); auto.
         lia.
       - assert (H' : j = 1 + k). apply (H (1 +i)); auto.
         lia.
       - assert (H' : 1 + j = k). apply (H i); auto.
         lia.
       - assert (H' : 1 + j = k). apply (H (1 +i)); auto.
         lia. 
       - assert (H' : 1 + j = 1 + k). apply (H i); auto.
         lia.
       - assert (H' : 1 + j = 1 + k). apply (H (1 + i)); auto.
         lia.
Qed.


Lemma connect : forall (n : nat) (A gM : Square (S n)),
  good_M gM ->
  exists (p : Polynomial (S n)), (forall c : C, Determinant (S n) (A .+ (-c .* gM)) = eval_P (S n) p c).
Proof. induction n as [| n'].
       - intros.
         exists [A 0 0; - gM 0 0].
         intros. 
         unfold eval_P; simpl. 
         lca. 
       - intros. 
         exists [C1]; intros. 
         rewrite Det_simplify.
         Admitted.


(*
  Σ^ S (S n')
  (fun i : nat =>
   (parity i * (A .+ - c .* gM) i 0 * Determinant (S n') (reduce (A .+ - c .* gM) i 0))%C) =
  eval_P (S (S n')) [C1] c *)




Lemma connect2 : forall (n : nat) (A : Square (S n)),
  exists (c : C), Determinant (S n) (A .+ (-c .* I (S n))) = C0.
Proof. intros. 
       assert (H' : good_M (I (S n))).
       apply good_M_I.
       apply (connect n A) in H'.
       destruct H' as [p H].
       assert (H0 : S n > 0). lia.
       apply (Fundamental_Theorem_Algebra p) in H0.
       destruct H0 as [c H0].
       exists c. rewrite <- H0.
       easy.
Qed.



Lemma exists_eigenvector : forall (n : nat) (A : Square (S n)),
  WF_Matrix A -> 
  exists (c : C) (v : Vector (S n)), WF_Matrix v /\ v <> Zero /\ A × v = c.* v.
Proof. intros. 
       destruct (connect2 n A) as [c H0].
       apply Det_0_lindep in H0.
       destruct H0 as [v [H1 [H2 H3]]].
       exists c, v.
       split; auto. 
       split; auto. 
       rewrite Mmult_plus_distr_r, Mscale_mult_dist_l, Mmult_1_l in H3; auto.
       assert (H4 : A × v .+ (-c .* v) .+ (c .* v) = (c .* v)).
       { rewrite H3. lma. }
       rewrite Mplus_assoc in H4.
       Search (_ .* ?b .+ _ .* ?b). 
       rewrite <- Mscale_plus_distr_l in H4. 
       replace (-c + c)%C with C0 in H4 by lca.
       rewrite <- H4.
       lma. 
       auto with wf_db.
Qed.
    


(************************************)
(* Lemmas relating to forming bases *)
(************************************)


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



Lemma form_basis_ver : forall {n} (v : Vector n) (x : nat),
  v <> Zero -> WF_Matrix v -> v x 0 <> C0 -> x < n -> 
  linearly_independent (form_basis v x) /\ get_vec x (form_basis v x) = v.
Proof. intros.
       destruct n; try lia. split.
       - apply (lin_indep_col_add_many_conv _ _ x _ (-C1 .* (make_row_zero x v))); try easy.
         unfold scale, make_row_zero. 
         bdestruct (x =? x); try lia; lca. 
         apply (lin_indep_scale_conv _ x (/ (v x 0))).
         apply nonzero_div_nonzero; easy.
         assert (H' : forall A : Square (S n), A = I (S n) -> linearly_independent A).
         { intros. rewrite H3. 
           apply lin_indep_invertible; auto with wf_db.
           unfold invertible. exists (I (S n)).
           unfold Minv. 
           split; rewrite Mmult_1_l; auto with wf_db. }
         apply H'. 
         apply mat_equiv_eq; auto with wf_db. 
         apply WF_col_scale. 
         apply WF_col_add_many; try easy.
         apply WF_form_basis; easy. 
         unfold mat_equiv; intros. 
         unfold col_scale, col_add_many, make_row_zero, 
         form_basis, scale, gen_new_vec, get_vec.
         assert (H0' : forall a b : C, a = C0 -> (b + a = b)%C). 
         { intros. rewrite H5. lca. }
         bdestruct (j =? x); bdestruct (j =? i).
         all : try rewrite Msum_Csum. 
         all : try unfold scale. 
         rewrite H5 in *. rewrite <- H6.
         rewrite H0'. 
         unfold I. 
         bdestruct (x =? x); bdestruct (x <? S n); try lia. 
         rewrite Cinv_l; try easy. 
         rewrite Csum_0_bounded; try easy.
         unfold e_i.
         intros. 
         bdestruct (x0 =? x); try lia; try lca. 
         bdestruct (x =? x0); try lia; lca.          
         rewrite (Csum_unique (-C1 * (v i 0))).
         unfold I. bdestruct (i =? j); try lia; simpl. 
         lca. exists i. split; try easy. 
         split. simpl. 
         rewrite H5 in *.
         bdestruct (i =? x); try lia. 
         unfold e_i. 
         bdestruct (i =? i); bdestruct (i <? S n); simpl; try lia; lca. 
         intros. 
         bdestruct (x' =? x); try lca. 
         simpl; unfold e_i.
         bdestruct (i =? x'); simpl; try lia; lca. 
         rewrite H6.
         all : unfold e_i, I.
         all : bdestruct (i =? i); bdestruct (i <? S n); simpl; try lia; try easy.  
         bdestruct (i =? j); easy.
       - apply get_v_in_basis; easy.
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
         apply mat_equiv_eq; try easy.
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




Definition gram_schmidt_on_v (n m : nat) (v : Vector n) (S : Matrix n m) :=
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
         rewrite easy_sub in *.
         rewrite H'. unfold scale. lca. 
       - unfold delta_T. 
         bdestruct (m =? m); try lia. 
         unfold scale. lca. 
Qed.


(* here, we show that gs_on_v preserves normalness *)
Lemma gram_schmidt_orthogonal : forall {n m} (v : Vector n) (S : Matrix n m) (i : nat),
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
             rewrite easy_sub in *.
             apply (gram_schmidt_orthogonal (get_vec m T) _ j) in H1; try lia.
             assert (H9 := (@get_vec_reduce_col n (S m) j m T)). 
             rewrite easy_sub in *.
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
             rewrite easy_sub in *.
             apply (gram_schmidt_orthogonal (get_vec m T) _ i) in H1; try lia.
             assert (H9 := (@get_vec_reduce_col n (S m) i m T)). 
             rewrite easy_sub in *.
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
             rewrite easy_sub in *.
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


Definition delta_T' {n m} (T : Matrix n m) (v : Vector n) (size : nat) : nat -> C := 
  fun i => if (i <? size)
           then - (proj_coef (get_vec i T) v) 
           else C0.


Lemma gs_on_T_cols_add : forall {n m1 m2} (T1 : Matrix n m1) (T2 : Matrix n m2) (v : Vector n),
  WF_Matrix v ->
  smash (col_append T1 (gram_schmidt_on_T n m1 (col_append T1 v))) T2 = 
  @col_add_many n ((S m1) + m2) m1 (f_to_vec (m1 + m2) (delta_T' T1 v m1)) 
                             (smash (col_append T1 v) T2).
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
       assert (p : S m1 + m2 = m1 + (S m2)). lia. 
       rewrite p. 
       rewrite Csum_sum.
       assert (p1 : forall a b : C, b = C0 -> (a + b = a)%C). 
       intros. rewrite H4. lca. 
       rewrite p1. 
       apply Csum_eq_bounded; intros.
       bdestruct (x0 =? m1); bdestruct (x0 <? m1); try lia.
       simpl. 
       bdestruct (x0 <? m1 + m2); try lia. 
       bdestruct (x0 <? S m1); try lia; easy.
       apply Csum_0_bounded; intros. 
       bdestruct (m1 + x0 <? m1 + m2); bdestruct (m1 + x0 <? m1); 
         try lia; simpl; lca.
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
       apply lin_indep_col_add_many; try lia; try easy.
       unfold f_to_vec, delta_T'.
       bdestruct (m1 <? m1 + m2); bdestruct (m1 <? m1); try lia; easy. 
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
         rewrite easy_sub in *.
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
         rewrite easy_sub in *.
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
           rewrite easy_sub in *.
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
           rewrite easy_sub in *. 
           apply H7. 
           lia. 
           rewrite (split T2).
           easy. 
           assert (add1 : S (Nat.add m1 (S m2')) = S (Nat.add (Nat.add m1 (S O)) m2')). lia. 
           rewrite add1 in H1.
           unfold Nat.add in H1.
           unfold Nat.add.
           rewrite <- smash_append; try easy.
           rewrite easy_sub in *.
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
  exists T : Square n, WF_Orthonormal T /\ get_vec 0 T = normalize v.
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
         unfold WF_Orthonormal; split. 
         apply WF_smash; try easy.
         apply WF_get_vec; easy.
         easy.
         apply WF_get_vec; easy.
         apply (WF_reduce_col 0) in H1.
         rewrite easy_sub in *; easy.
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


Lemma P_unitary : WF_Unitary Phase. Proof. apply phase_unitary. Qed.
Lemma T_unitary : WF_Unitary Tgate. 
Proof. unfold WF_Unitary.
       split; auto with wf_db.
       lma'. unfold Mmult, adjoint, I.
       simpl.  
       assert (H : (Cexp (PI / 4)) ^* = Cexp (- PI / 4)).
       { autorewrite with Cexp_db. lca. }
       assert (H1 : (- PI / 4 = - (PI / 4))%R ). { lra. } 
       rewrite H1 in H; rewrite H.
       rewrite Cexp_mul_neg_l. lca. 
Qed.


Lemma notc_unitary : WF_Unitary notc.
Proof.
  split. 
  apply WF_notc.
  unfold Mmult, I.
  prep_matrix_equality.
  do 4 (try destruct x; try destruct y; try lca).
  replace ((S (S (S (S x))) <? 4)) with (false) by reflexivity.
  rewrite andb_false_r.
  lca.
Qed.




Lemma unit_scale : forall {n} (c : C) (A : Square n),
  WF_Unitary A -> (c * c ^*)%C = C1 -> WF_Unitary (c .* A).
Proof. intros. 
       destruct H.
       split; auto with wf_db.        
       distribute_adjoint.
       distribute_scale.
       rewrite Cmult_comm.
       rewrite H1, H0. 
       lma'. 
Qed.


Lemma unit_big_kron : forall (n : nat) (ls : list (Square n)), 
  (forall a, In a ls -> WF_Unitary a) -> WF_Unitary (⨂ ls).
Proof. intros. induction ls as [| h].
       - simpl. apply id_unitary.
       - simpl.
         apply kron_unitary.
         apply (H h).
         left. easy.
         apply IHls.
         intros. 
         apply H. right. easy.
Qed.


Hint Resolve σx_unitary σy_unitary σz_unitary P_unitary H_unitary T_unitary : unit_db.
Hint Resolve cnot_unitary notc_unitary id_unitary Mmult_unitary kron_unitary transpose_unitary unit_scale unit_big_kron: unit_db.



Lemma unit_is_orthonormal : forall {n} (U : Square n),
  WF_Unitary U <-> WF_Orthonormal U.
Proof. intros n U. split. 
       - split; try apply H.
         split. 
         * unfold orthogonal. intros.
           rewrite inner_product_is_mult.
           destruct H as [H1 H].   
           rewrite H. 
           unfold I. bdestruct (i =? j); try lia; easy.
         * intros. unfold norm.
           assert (H1 : ((get_vec i U) † × get_vec i U) 0%nat 0%nat = 
                        inner_product (get_vec i U) (get_vec i U)).
           { unfold inner_product. reflexivity. }
           rewrite H1. rewrite inner_product_is_mult.
           destruct H.
           rewrite H2. unfold I.
           bdestruct (i =? i); bdestruct (i <? n); try lia. 
           simpl. apply sqrt_1. 
       - intros [H1 [H2 H3]]. 
         split; try easy.
         apply mat_equiv_eq; auto with wf_db.
         unfold mat_equiv; intros. 
         rewrite <- inner_product_is_mult.
         unfold orthogonal in H2. unfold I.
         bdestruct (i =? j); bdestruct (i <? n); try lia. 
         * unfold norm in H3.
           apply H3 in H0.
           apply sqrt_1_unique in H0.
           unfold RtoC.
           apply c_proj_eq.
           simpl. 
           unfold inner_product. 
           rewrite H4, H0. easy.
           simpl. 
           unfold inner_product. 
           rewrite H4.
           rewrite norm_real. easy.
         * rewrite H2; try easy.
Qed.


Lemma unit_out_of_v : forall {n} (v : Vector n) (x : nat),
  WF_Matrix v -> v <> Zero -> 
  exists S : Matrix n n, WF_Unitary S /\ get_vec 0 S = normalize v.
Proof. intros.
       apply onb_out_of_v in H; try easy.
       destruct H as [S [H1 H2]].
       exists S. split; try easy.
       apply unit_is_orthonormal; easy.
Qed.


Lemma det_by_unit : forall {n} (A B X : Square n),
  WF_Matrix A -> WF_Matrix B -> 
  WF_Unitary X -> (forall i, A × (get_vec i X) = B × (get_vec i X)) -> A = B.
Proof. intros. assert (H' : A × X = B × X).
       { apply det_by_get_vec. intros.
         do 2 (rewrite <- get_vec_mult).
         apply H2. }
       rewrite <- Mmult_1_r.
       rewrite <- (Mmult_1_r _ _ A).
       destruct H1.
       apply Minv_flip in H3; auto with wf_db.
       rewrite <- H3.
       do 2 (rewrite <- Mmult_assoc).
       rewrite H'.
       reflexivity. 
       all : easy. 
Qed.


(***********************************************************************************)
(* We now define diagonal matrices and diagonizable matrices, proving basic lemmas *)
(***********************************************************************************)

Definition WF_Diagonal {n : nat} (A : Square n) : Prop := 
  WF_Matrix A /\ forall i j, i <> j -> A i j = C0.


Lemma diag_Zero : forall n : nat, WF_Diagonal (@Zero n n).
Proof. intros n. split; auto with wf_db. Qed.

Lemma diag_I : forall n : nat, WF_Diagonal (I n). 
Proof. 
  intros.
  split; auto with wf_db.
  intros.
  unfold I. 
  bdestruct (i =? j); try lia; try easy. 
Qed.

Lemma diag_I1 : WF_Diagonal (I 1). Proof. apply diag_I. Qed.

Lemma diag_scale : forall {n : nat} (r : C) (A : Square n), 
  WF_Diagonal A -> WF_Diagonal (r .* A).
Proof.
  intros n r A [H H0]. 
  split; auto with wf_db.
  intros. 
  unfold scale. 
  rewrite H0; try lca; easy.
Qed.

Lemma diag_plus : forall {n} (A B : Square n), 
  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A .+ B).
Proof.
  intros n A B [H H0] [H1 H2]. 
  split; auto with wf_db. 
  intros. 
  unfold Mplus.
  rewrite H0, H2; try easy; lca.
Qed.

Lemma diag_mult : forall {n : nat} (A B : Square n), 
  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A × B).
Proof.
  intros n A B [H H0] [H1 H2].
  split; auto with wf_db. 
  intros.
  unfold Mmult. 
  apply Csum_0.
  intro.
  bdestruct (x =? i).
  + rewrite H2; try lia; lca. 
  + rewrite H0, Cmult_0_l.    
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
                  WF_Diagonal A -> WF_Diagonal B -> WF_Diagonal (A ⊗ B).
Proof.
  intros n m A B [H H0] [H1 H2].
  destruct m.
  rewrite (WF0_Zero_l 0); try easy.
  auto with wf_db.
  split; auto with wf_db.
  unfold kron.
  intros.
  bdestruct (i / (S m) =? j / (S m)).
  - bdestruct (i mod (S m) =? j mod (S m)).
    + apply (div_mod_eq i j (S m)) in H5; try easy.
    + rewrite H2; try lca; easy. 
  - rewrite H0; try lca; easy. 
Qed.


Lemma diag_transpose : forall {n : nat} (A : Square n), 
                     WF_Diagonal A -> WF_Diagonal A⊤. 
Proof. intros n A [H H0]. 
       split; auto with wf_db.
       intros. 
       unfold transpose.  
       apply H0. auto. 
Qed.

Lemma diag_adjoint : forall {n : nat} (A : Square n), 
      WF_Diagonal A -> WF_Diagonal A†. 
Proof. intros n A [H H0]. 
       split; auto with wf_db.
       unfold  adjoint, Cconj. 
       intros. 
       rewrite H0. lca. auto.
Qed.


Lemma diag_kron_n : forall (n : nat) {m : nat} (A : Square m),
   WF_Diagonal A ->  WF_Diagonal (kron_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - rewrite Nat.mul_comm. 
    apply (@diag_kron (m^n) m _ A). 
    apply IHn. apply H. 
Qed.

Lemma diag_big_kron : forall n (l : list (Square n)), 
                        (forall A, In A l -> WF_Diagonal A) ->
                         WF_Diagonal (⨂ l). 
Proof.                         
  intros.
  induction l.
  - simpl. apply diag_I.
  - simpl. apply (@diag_kron _ (n^(length l)) a (⨂ l)). 
    apply H.
    left. easy. 
    apply IHl. 
    intros A H'. apply H.
    simpl. auto.
Qed. 


Lemma diag_Mmult_n : forall n {m} (A : Square m),
   WF_Diagonal A -> WF_Diagonal (Mmult_n n A).
Proof.
  intros.
  induction n; simpl.
  - apply diag_I.
  - apply diag_mult; assumption. 
Qed.

(* defining what it means to be diagonalizable *)
Definition WF_Diagonalizable {n : nat} (A : Square n) : Prop :=
  WF_Matrix A /\ (exists (X X' B: Square n), 
    WF_Diagonal B /\ WF_Matrix X /\ WF_Matrix X' /\ X × X' = I n /\ B = X × A × X').

Lemma diag_imps_diagble : forall {n} (A : Square n),
  WF_Diagonal A -> WF_Diagonalizable A.
Proof. intros n A [H H0]. unfold WF_Diagonalizable.
       split; auto.
       exists (I n), (I n), A. 
       split.
       split; auto. 
       split; auto with wf_db.
       split; auto with wf_db.
       rewrite Mmult_1_l; auto with wf_db.  
       rewrite Mmult_1_l; auto with wf_db.  
       rewrite Mmult_1_r; auto with wf_db.  
Qed.


Lemma diagble_Zero : forall n : nat, WF_Diagonalizable (@Zero n n).
Proof. intros. apply diag_imps_diagble. 
       apply diag_Zero.
Qed.


Lemma diagble_I : forall n : nat, WF_Diagonalizable (I n). 
Proof. intros. apply diag_imps_diagble.
       apply diag_I.
Qed.

Lemma diagble_I1 : WF_Diagonal (I 1). Proof. apply diag_I. Qed.
  


Lemma diagble_scale : forall {n : nat} (r : C) (A : Square n), 
  WF_Diagonalizable A -> WF_Diagonalizable (r .* A).
Proof.
  intros n r A [H H0].  
  split; auto with wf_db.
  do 3 (destruct H0).
  destruct H0 as [H1 [H2 [H3 [H4 H5]]]].
  exists x, x0, (r .* x1); split. 
  apply diag_scale; apply H1. 
  split; try easy.
  split; try easy. 
  split. 
  apply H4.
  rewrite Mscale_mult_dist_r;
  rewrite Mscale_mult_dist_l.
  rewrite H5.
  reflexivity. 
Qed.


Lemma diagble_switch : forall {n : nat} (A B X X' : Square n),
  WF_Matrix A -> WF_Matrix B -> WF_Matrix X -> WF_Matrix X' -> 
  X × X' = I n -> B = X × A × X' ->
  A = X' × B × X.
Proof. intros. 
       rewrite H4. 
       repeat rewrite <- Mmult_assoc. 
       apply Minv_flip in H3; auto.
       rewrite H3, Mmult_1_l; auto.
       rewrite Mmult_assoc. 
       rewrite H3, Mmult_1_r; auto. 
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

Lemma up_tri_I1 : upper_triangular (I 1). Proof. apply up_tri_I. Qed.

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
   WF_Matrix v -> Eigenpair (I n) (v, C1).
Proof. intros n v H. unfold Eigenpair. 
       simpl. rewrite Mmult_1_l. lma. 
       easy.
Qed.


Lemma diags_have_basis_eigens : forall (n : nat) (U : Square n) (i : nat),
  (i < n) -> WF_Diagonal U -> Eigenpair U (e_i i, U i i).
Proof. unfold WF_Diagonal, Eigenpair, e_i. intros.
       unfold Mmult, scale.
       prep_matrix_equality.
       eapply Csum_unique. exists i. 
       destruct H0 as [H0 H1].
       split. apply H.
       split.
       - simpl. bdestruct (x =? i).
         * rewrite H2. bdestruct (i =? i); easy.
         * rewrite H1. lca. lia.  
       - intros. simpl. bdestruct (x' =? i); try lia; lca.
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



Lemma eig_unit_invertible : forall {n} (v : Vector n) (c : C) (X X' B : Square n),
  WF_Matrix v -> WF_Matrix X -> WF_Matrix X' -> X' × X = I n ->  
  Eigenpair B (X × v, c) -> Eigenpair (X' × B × X) (v, c).  
Proof. intros. 
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H3.
       distribute_scale. 
       rewrite <- Mmult_assoc.     
       rewrite H2.
       rewrite Mmult_1_l; easy.
Qed.



Lemma eig_unit_conv : forall {n} (v : Vector n) (c : C) (U B : Square n),
  WF_Matrix v -> WF_Unitary U -> 
  Eigenpair B (U × v, c) -> Eigenpair (U† × B × U) (v, c).  
Proof. intros. 
       destruct H0 as [H0 H2].
       unfold Eigenpair in *; simpl in *.
       do 2 (rewrite Mmult_assoc).
       rewrite H1.
       rewrite Mscale_mult_dist_r.
       rewrite <- Mmult_assoc.     
       rewrite H2.
       rewrite Mmult_1_l; easy.
Qed.




Lemma eig_unit_norm1 : forall {n} (U : Square n) (c : C),
  WF_Unitary U -> (exists v, WF_Matrix v /\ v <> Zero /\ Eigenpair U (v, c)) -> (c * c^* = C1)%C.
Proof. intros. destruct H0 as [v [H0 [H1 H2]]].
       unfold Eigenpair in H2; simpl in H2. 
       assert (H3 : (U × v)† = (c .* v)†). rewrite H2; easy.
       rewrite Mmult_adjoint, Mscale_adj in H3.
       assert (H4 : ((v) † × (U) †) × (U × v) = (c ^* .* (v) †) × (c .* v)).
       { rewrite H2, H3; easy. } 
       rewrite Mmult_assoc in H4.
       rewrite <- (Mmult_assoc _ U v) in H4.
       destruct H as [H5 H].       
       rewrite H in H4.
       rewrite Mmult_1_l in H4; auto.
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


Lemma unit_has_eigen : forall {n} (A : Square (S n)),
  WF_Unitary A -> 
  exists (c : C) (v : Vector (S n)),  Eigenpair A (v, c) /\ v <> Zero /\ WF_Matrix v.
Proof. intros n A [Hwf Hu].
       apply exists_eigenvector in Hwf.
       destruct Hwf as [c [v [H [H0 H1]]]].
       exists c. exists v.
       split. unfold Eigenpair.
       simpl; easy.
       auto.
Qed.

Lemma unitary_reduction_step1 : forall {n} (A : Square (S n)),
  WF_Unitary A ->
  exists X, WF_Unitary X /\
  (exists c : C, get_vec 0 (X†×A×X) = c .* e_i 0).
Proof. intros n A [Hwf Hu].
       apply exists_eigenvector in Hwf.
       destruct Hwf as [c [v [H [H0 H1]]]]. 
       assert (H' := H0).
       apply onb_out_of_v in H0; auto.
       destruct H0 as [T [H2 H3]].
       exists T. split. 
       apply unit_is_orthonormal; easy.
       exists c.
       rewrite matrix_by_basis; try lia. 
       do 2 rewrite Mmult_assoc. 
       rewrite <- matrix_by_basis, H3; try lia.
       unfold normalize.
       rewrite Mscale_mult_dist_r.
       rewrite H1.
       distribute_scale.
       assert (H'' : forall p1 p2 : C, p1 = p2 -> fst p1 = fst p2).
         intros. rewrite H0; easy.
       assert (H4 : v = (norm v) .* normalize v).
       { unfold normalize; distribute_scale.
         rewrite Cinv_r; try lma. 
         apply norm_zero_iff_zero in H.
         unfold not; intros. 
         apply H'.
         apply H.
         unfold RtoC in H0.
         apply H'' in H0.
         simpl in H0.
         easy. }
       rewrite H4, <- H3.
       apply unit_is_orthonormal in H2.
       destruct H2 as [Hwf HTu].
       rewrite matrix_by_basis; try lia.
       distribute_scale.
       rewrite <- Mmult_assoc, HTu. 
       rewrite <- matrix_by_basis, H3, <- H4; try lia.
       rewrite Cmult_comm, Cmult_assoc, Cinv_r, Mmult_1_l; auto with wf_db.
       lma. unfold not;intros. 
       apply H'.
       apply norm_zero_iff_zero in H.
       unfold RtoC in H0.
       apply H'' in H0; simpl in H0.
       apply H; easy.
Qed.


(* this proof is horribly long and I feel like theres probably a better way to show this *)
(* TODO : make this better *) 
Lemma unitary_reduction_step2 : forall {n} (A : Square (S n)),
  WF_Unitary A -> 
  (exists c : C, get_vec 0 A = c .* e_i 0) -> 
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0).
Proof. intros n A H [c H0] i j H1.    
       assert (Hc : A 0 0 = c). 
       { replace (A 0 0) with ((get_vec 0 A) 0 0) by easy.
         rewrite H0; lca. }
       assert (H2 : (c * c^*)%C = C1). 
       { apply (eig_unit_norm1 A); try easy.
         exists (e_i 0).
         split.
         apply WF_e_i.
         split. unfold not; intros. 
         apply C1_neq_C0.
         replace C1 with (@e_i (S n) 0 0 0) by easy.
         rewrite H2; easy.
         unfold Eigenpair; simpl. 
         rewrite <- matrix_by_basis; try easy; lia. }
       destruct H1 as [[H1 | H1] H3].
       - apply transpose_unitary in H.
         apply unit_is_orthonormal in H.
         destruct H as [Hwf [Ho Hn]].
         assert (H4 : norm (get_vec 0 A†) = 1%R).
         { apply Hn; lia. } 
         unfold norm in H4.
         apply sqrt_1_unique in H4.
         replace 1%R with (fst C1) in H4 by easy.
         apply (c_proj_eq (((get_vec 0 A†) † × get_vec 0 A†) 0 0) C1) in H4.
         unfold Mmult in H4.
         rewrite <- Csum_extend_l in H4. 
         assert (H' : ((get_vec 0 (A) †) † 0 0 * get_vec 0 (A) † 0 0)%C = C1).
         { unfold get_vec, adjoint. 
           simpl. rewrite Hc.
           rewrite Cconj_involutive; easy. }
         rewrite H' in H4.
         assert (H'' : forall c : C, (C1 + c = C1 -> -C1 + (C1 + c) = -C1 + C1)%C).
         { intros. rewrite H; easy. }
         apply H'' in H4.
         rewrite Cplus_assoc in H4.
         replace (-C1 + C1)%C with C0 in H4 by lca. 
         rewrite Cplus_0_l in H4.
         rewrite H1 in *.
         destruct j; try lia. 
         assert (H5 := Csum_squeeze (fun x : nat => ((get_vec 0 (A) †) † 0 (S x) * 
                                                get_vec 0 (A) † (S x) 0)%C) n).
         assert (H5' : forall x : nat,
       x < n ->
       fst ((fun x0 : nat => ((get_vec 0 (A) †) † 0 (S x0) * get_vec 0 (A) † (S x0) 0)%C) x) =
       fst C0).
         { apply H5. intros. 
           unfold adjoint, get_vec, Copp. 
           simpl. 
           rewrite Ropp_involutive.
           unfold Rminus.
           replace (- (snd (A 0%nat (S x)) * - snd (A 0%nat (S x))))%R with 
               ((snd (A 0%nat (S x)))^2)%R by lra. 
           replace (fst (A 0%nat (S x)) * fst (A 0%nat (S x)))%R with 
               ((fst (A 0%nat (S x)))^2)%R by lra. 
           apply Rplus_le_le_0_compat.
           all : try apply pow2_ge_0. 
           rewrite H4; easy. }
         simpl in H5'.
         assert (H6 := (H5' j)).
         bdestruct (j <? n).
         + apply H6 in H.
           rewrite Ropp_involutive in H.
           unfold Rminus in H.
           replace (- (snd (A 0%nat (S j)) * - snd (A 0%nat (S j))))%R with 
               ((snd (A 0%nat (S j)))^2)%R in H by lra. 
           replace (fst (A 0%nat (S j)) * fst (A 0%nat (S j)))%R with 
               ((fst (A 0%nat (S j)))^2)%R in H by lra. 
           assert (H7 : Cmod (A 0 (S j)) = 0%R).
           { unfold Cmod. rewrite H.
             apply sqrt_0. }
           apply Cmod_eq_0 in H7; easy.
         + apply WF_adjoint in Hwf.
           rewrite adjoint_involutive in Hwf.
           rewrite Hwf; try lca; lia.
         + unfold Mmult. 
           apply Csum_snd_0; intros. 
           unfold get_vec, adjoint. 
           simpl. lra. 
       - rewrite H1. 
         replace (A i 0) with (get_vec 0 A i 0) by easy. 
         rewrite H0.
         destruct i; try lia. 
         lca. 
Qed.


Lemma unitary_reduction_step3 : forall {n} (A : Square (S n)),
  WF_Unitary A -> 
  (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> A i j = C0) ->
  exists (A' : Square n), WF_Unitary A' /\ pad A' (A 0 0) = A.
Proof. intros n A [Hwf Hu]. 
       exists (reduce A 0 0).
       assert (H' : WF_Matrix (reduce A 0 0)).
       { apply WF_reduce; try lia; easy. } 
       split. split.        
       rewrite easy_sub in *.
       apply H'.
       apply mat_equiv_eq; auto with wf_db.
       apply WF_mult; try apply WF_adjoint.
       all : rewrite easy_sub in *; try easy.
       unfold mat_equiv; intros. 
       assert (H2 : ((A) † × A) (S i) (S j) = (I n) i j).
       { rewrite Hu. 
         unfold I.
         bdestruct_all; try easy. }
       rewrite <- H2.
       unfold Mmult.
       rewrite <- Csum_extend_l.
       rewrite H, Cmult_0_r, Cplus_0_l.
       apply Csum_eq_bounded; intros. 
       unfold adjoint. 
       unfold reduce.
       apply Cmult_simplify.
       all : simpl; try easy.
       lia. 
       unfold pad, reduce, col_wedge, row_wedge, scale, e_i.
       prep_matrix_equality.
       simpl. 
       bdestruct_all; simpl. 
       rewrite H1, H2; lca.
       3 : { destruct x; destruct y; try lia. 
             do 2 rewrite easy_sub; easy. }
       4 : { destruct x; destruct y; try lia. 
             do 2 rewrite easy_sub; easy. }
       all : try rewrite (H x y); try lca; try lia. 
Qed.
       

Lemma diagble_pad : forall {n} (A : Square n) (c : C),
  WF_Diagonalizable A -> WF_Diagonalizable (pad A c).
Proof. intros n A c [H [X [X' [B [[Hwf Hd] [H1 [H2 [H3 H4]]]]]]]].
       split. apply WF_pad; auto.
       exists (pad X C1), (pad X' C1), (pad B c).
       split. split; try (apply WF_pad; auto).
       - intros.
         destruct i; destruct j; try lia;
           unfold pad, col_wedge, row_wedge, scale, e_i;
           bdestruct_all; try easy; try lca.
         do 2 rewrite easy_sub.
         apply Hd; lia.
         apply Hd; lia. 
       - split; try (apply WF_pad; auto).
         split; try (apply WF_pad; auto).
         split. 
         rewrite <- pad_mult, H3, Cmult_1_r, pad_I.
         easy.
         do 2 rewrite <- pad_mult.
         rewrite <- H4, Cmult_1_r, Cmult_1_l.
         easy.
Qed.         

         
(* Now, we build up the main important theorem *)
Theorem unit_implies_diagble : forall {n} (A : Square n),
  WF_Unitary A -> WF_Diagonalizable A.
Proof. induction n as [| n']. 
       - intros A [H H0]. 
         apply WF0_Zero_l in H. 
         rewrite H. 
         apply diagble_Zero.
       - intros A H. 
         assert (H0 := H).
         apply unitary_reduction_step1 in H.
         destruct H as [X [H1 [c H2]]].
         assert (H3 : WF_Unitary ((X) † × A × X)).
         { do 2 try apply Mmult_unitary.
           apply transpose_unitary.
           all : easy. }
         assert (H4 : (forall (i j : nat), (i = 0 \/ j = 0) /\ i <> j -> ((X) † × A × X) i j = C0)).
         { apply unitary_reduction_step2; try easy. 
           exists c. easy. }
         apply unitary_reduction_step3 in H3; try easy.
         destruct H3 as [A' [H5 H6]].
         assert (H7 : WF_Diagonalizable ((X) † × A × X)).
         apply IHn' in H5.
         { rewrite <- H6. 
           apply diagble_pad.
           easy. }
         destruct H7 as [Hwf Hd].
         split. 
         destruct H0; easy.
         destruct Hd as [X0 [X0' [B [H7 [H8 [H9 [H10 H11]]]]]]].
         exists (X0 × (X) †).
         exists (X × X0').
         exists B.
         destruct H1 as [H1wf H1u].
         split; try easy.
         split; auto with wf_db.
         split; auto with wf_db.
         rewrite Mmult_assoc.
         rewrite <- (Mmult_assoc X †).
         rewrite H1u.
         rewrite Mmult_1_l; try easy.
         split; try easy.
         rewrite H11.
         repeat rewrite Mmult_assoc.
         easy.
Qed.


(************************************************************************************)
(* Showing that certain types of matrices are equal when their eigenpairs are equal *)
(************************************************************************************)


Definition eq_eigs {n : nat} (U1 U2 : Square n) : Prop := 
  forall p, WF_Matrix (fst p) -> (Eigenpair U1 p -> Eigenpair U2 p). 


Lemma eq_eigs_implies_eq_diag : forall {n} (D1 D2 : Square n),
  WF_Diagonal D1 -> WF_Diagonal D2 -> eq_eigs D1 D2 -> D1 = D2.
Proof. intros n D1 D2 [H1wf H1d] [H2wf H2d] H. 
       assert (H2 : forall x, x < n -> D1 x x = D2 x x).
       { intros.
         assert (H1 := H0).
         apply (diags_have_basis_eigens n D1 x) in H1.
         apply H in H1.
         unfold Eigenpair in H1; simpl in H1.
         assert (H' : (D1 x x .* @e_i n x) x 0 = D1 x x).
         { unfold scale, e_i.
           bdestruct_all; lca. }
         rewrite <- H', <- H1. 
         unfold Mmult. 
         apply (Csum_unique (D2 x x)). 
         exists x. split; try easy.
         split. unfold e_i. 
         bdestruct_all; lca.
         intros. 
         unfold e_i; bdestruct_all; lca.
         simpl. auto with wf_db.
         split; auto. }
       apply mat_equiv_eq; auto.
       unfold mat_equiv; intros. 
       bdestruct (i =? j).
       - rewrite H3, H2; try lia; easy. 
       - rewrite H1d, H2d; try lia; easy.
Qed.
         

Lemma diagble_eigenpairs_transfer : forall {n} (A B X X' : Square n),
  WF_Matrix A -> WF_Diagonal B -> WF_Matrix X -> WF_Matrix X' ->
  A = X' × B × X -> X × X' = I n ->
  (forall x, x < n -> Eigenpair A (X' × (e_i x), B x x)).
Proof. intros. 
       destruct H0 as [Hwf Hu].
       unfold Eigenpair; simpl.
       rewrite <- Mmult_assoc. 
       rewrite H3.
       do 2 rewrite Mmult_assoc. 
       rewrite <- (Mmult_assoc X), H4, Mmult_1_l; auto with wf_db.
       assert (H' := (diags_have_basis_eigens n B)).
       apply H' in H5. 
       unfold Eigenpair in H5; simpl in H5. 
       rewrite Mmult_assoc, H5. 
       distribute_scale; easy.
       split; auto.
Qed.   

Lemma eq_eigs_implies_eq_diagble : forall {n} (D1 D2 : Square n),
  WF_Diagonalizable D1 -> WF_Diagonalizable D2 -> eq_eigs D1 D2 -> D1 = D2.
Proof. intros n D1 D2 [H1wf H1d] [H2wf H2d] H. 
       destruct H1d as [X1 [X1' [B1 [[Hb1wf Hb1u] [H12 [H13 [H14 H15]]]]]]].
       destruct H2d as [X2 [X2' [B2 [[Hb2wf Hb2u] [H22 [H23 [H24 H25]]]]]]].
       apply diagble_switch in H15; apply diagble_switch in H25; auto.
       assert (H0 : D1 × X1' = X1' × B1).
       { rewrite H15.
         repeat rewrite Mmult_assoc.
         rewrite H14, Mmult_1_r; auto. }
       assert (H1 : D2 × X2' = X2' × B2).
       { rewrite H25.
         repeat rewrite Mmult_assoc.
         rewrite H24, Mmult_1_r; auto. }
       assert (H2 : forall i, i < n -> Eigenpair D1 (X1' × (e_i i), B1 i i)).
       { apply (diagble_eigenpairs_transfer D1 B1 X1 X1'); auto. 
         split; auto. }
       assert (H3 : forall i, i < n -> Eigenpair D2 (X1' × (e_i i), B1 i i)).
       { intros. apply H. simpl. 
         auto with wf_db. apply H2; easy. }
       assert (H4 : forall i, i < n -> Eigenpair (X1 × D1 × X1') (e_i i, B1 i i)).
       { intros. apply eig_unit_invertible; auto with wf_db. }
       assert (H5 : forall i, i < n -> Eigenpair (X1 × D2 × X1') (e_i i, B1 i i)).
       { intros. apply eig_unit_invertible; auto with wf_db. }
       assert (H6 : forall i, i < n -> (X1 × D1 × X1' × e_i i = X1 × D2 × X1' × e_i i)).
       { intros. 
         unfold Eigenpair in *; simpl in *.
         rewrite H4, H5; easy. }
       assert (H7 : X1 × D1 × X1' = X1 × D2 × X1').
       { apply det_by_get_vec.
         intros. 
         bdestruct (i <? n).
         - rewrite matrix_by_basis.
           rewrite matrix_by_basis. 
           apply H6. 
           all : easy. 
         - assert (H' : forall (A : Square n) (i : nat), i >= n -> WF_Matrix A -> 
                                                  get_vec i A = @Zero n 1).  
           { intros. 
             unfold get_vec. 
             prep_matrix_equality. 
             bdestruct_all; try easy.
             rewrite H9; try lia; easy. }
           rewrite H'; auto with wf_db.
           rewrite H'; auto with wf_db. }
       assert (H8 : X1' × (X1 × D1 × X1') × X1= X1' × (X1 × D2 × X1') × X1).
       { rewrite H7; easy. }
       repeat rewrite Mmult_assoc in H8.
       apply Minv_flip in H14; auto. 
       rewrite H14 in H8.
       do 2 rewrite Mmult_1_r in H8; auto. 
       do 2 rewrite <- Mmult_assoc in H8.
       rewrite H14 in H8.
       do 2 rewrite Mmult_1_l in H8; auto. 
Qed.



Lemma eq_eigs_implies_eq_unit : forall {n} (U1 U2 : Square n),
  WF_Unitary U1 -> WF_Unitary U2 -> eq_eigs U1 U2 -> U1 = U2.
Proof. intros. 
       apply unit_implies_diagble in H.
       apply unit_implies_diagble in H0.
       apply eq_eigs_implies_eq_diagble; auto. 
Qed.


Theorem eigs_eq_gate : forall {n} (U1 U2 : Square n),
  WF_Unitary U1 -> WF_Unitary U2 -> (U1 = U2 <-> eq_eigs U1 U2).
Proof. intros. split.
       - intros H'; rewrite H'; easy.
       - apply eq_eigs_implies_eq_unit.
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

