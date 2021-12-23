Require Export Complex.





Definition polar_to_rect (p : R * R) : C := 
  fst p * (exp (snd p)).



Theorem nth_root : forall (c : C) (n : nat),
  (n > 0)%nat -> 
  exists c', (Cpow c' n = c)%C.
Proof. Admitted. 


Lemma nonzero_nth_root : forall (c c' : C) (n : nat),
  (n > 0)%nat -> c' ^ n = c ->
  c <> C0 -> 
  c' <> C0.
Proof. intros. 
       destruct n; try easy.
       simpl in H0.
       unfold not; intros; apply H1; subst.
       lca.
Qed.


(****)
(*****)
(***)
