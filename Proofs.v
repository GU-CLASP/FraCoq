Load FraCoq2.

Theorem T114a: Problem114a. cbv. intros. destruct H. destruct H. exists x. split. exact H. exists (PN2object mary_PN). split. apply I. exact H0. Qed. 


Theorem T115A: Problem115a. cbv. intros. destruct H. destruct H. destruct H.  exists x. split. exact H1. exact H. Qed. 

Theorem T116a: Problem116a. cbv. intros.  split. apply mary_PN_Female. apply I. Qed.


Theorem T117a: Problem117a. cbv. intros.  elim H. intros. apply H. exact H1. Qed. 


(*Theorem T123a: Problem123a. cbv. intros. destruct H. firstorder. Qed.                        
*)


Theorem T123b: Problem123b.   cbv.  intros. destruct H. Abort all.

Theorem T124a: Problem124a.
cbv. intros. elim H. intros. destruct H0. destruct H1. destruct H1. exists x.  firstorder. 
  Abort all. 

Theorem T124b : Problem124b. 
cbv. intros. elim H.  
intros. exists x.   split. destruct H0. 
assumption. destruct H0.
destruct H1. destruct H1. elim H3. intros.  split. exists x0. exact H4. 
Theorem T124b: Problem124b. cbv. firstorder. intuition. Abort all. 

