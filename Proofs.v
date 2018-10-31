Load FraCoq2.

Theorem T114a: Problem114a. cbv. intros. destruct H. destruct H. exists x. split. exact H. exists (PN2object mary_PN). split. apply I. exact H0. Qed. 


Theorem T115A: Problem115a. cbv. intros. destruct H. destruct H. destruct H.  exists x. split. exact H1. exact H. Qed. 

Theorem T116a: Problem116a. cbv. intros.  split. apply mary_PN_Female. apply I. Qed.


Theorem T117a: Problem117a. cbv. intros.  elim H. intros. apply H. exact H1. Qed. 


Theorem T123a: Problem123a. cbv. intros. firstorder. 
Qed. 

Theorem T123b: Problem123b.   cbv.  intros. destruct H. firstorder. Abort all.

Theorem T124a: Problem124a.
cbv. intros. elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1. destruct H3. destruct H. destruct H. destruct H5. exists x. destruct H5. destruct H5. destruct H7. firstorder. 
   firstorder. Abort all. 

Theorem T124b : Problem124b. 
cbv. intros. elim H.  
intros.      destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1. destruct H3. destruct H. destruct H. destruct H5.       exists x.   split. assumption. split. exists x1. split. exact I. firstorder. destruct H5.  destruct H5. 
destruct H5. destruct H8. firstorder. 
destruct H1. firstorder. 
Abort All. 

Theorem T125a: Problem125a. 
  cbv. intros. firstorder. Abort all. (**UNK so this is fine**)

Theorem T125b: Problem125b.
  cbv. intros. firstorder. Abort all.  (**Ibid**)

Theorem T126A: Problem126a. cbv. intros.  elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1.  destruct H. destruct H. destruct H5. destruct H5. destruct H5. destruct H5. destruct H8.  Abort all.  (**Needs to be fixed**)

Theorem T126b: Problem126b.  cbv. intros.  elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1.  destruct H. destruct H. destruct H5. destruct H5. destruct H5. destruct H5. destruct H8.
 exists x. Abort all. 

                             
 Theorem T127a: Problem127a. cbv. intros. Abort all.  (**This is marked yes on a distributive reading. One of the funny examples with two readings**)

 Theorem T128a: Problem128a. cbv. intros. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x1. firstorder. Qed.

 Theorem T129a: Problem129a. cbv. intros. firstorder. Qed. 