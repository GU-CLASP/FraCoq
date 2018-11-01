Load FraCoq2.

Theorem T114a: Problem114a. cbv. intros. destruct H. destruct H. exists x. split. exact H. exists (PN2object mary_PN). split. apply I. exact H0. Qed. 


Theorem T115A: Problem115a. cbv. intros. destruct H. destruct H. destruct H.  exists x. split. exact H1. exact H. Qed. 

Theorem T116a: Problem116a. cbv. intros.  split. apply mary_PN_Female. apply I. Qed.


Theorem T117a: Problem117a. cbv. intros.  elim H. intros. apply H. exact H1. Qed. 


Theorem T123a: Problem123a. cbv. intros. firstorder. 
Qed. 

Theorem T123b: Problem123b.   cbv.  intros. destruct H. firstorder. Abort all.

Theorem T124a: Problem124a.
cbv. intros. elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1. destruct H3. destruct H. destruct H. destruct H5. exists x0. destruct H5. destruct H5. destruct H7. firstorder. 
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

 Theorem T130a: Problem130a. cbv. intros. destruct H0. destruct H1. destruct H2. Abort all.

 Theorem T131a: Problem131a. cbv. intros.  firstorder.  Abort all.

 Theorem T1312a: Problem132a. cbv. intros.  firstorder. Abort all. 

 Theorem T132b: Problem132b. cbv. intros. firstorder. Qed.

 Theorem T133a: Problem133a. cbv. intros. destruct H. destruct H. destruct H. apply H1. exact H0. Qed.

 Theorem T134a: Problem134a. cbv. intros. destruct H. destruct H1. destruct H2. destruct H2. destruct H3.  Abort all.

 Theorem T134b: Problem134b. cbv. intros. firstorder. exists x. Abort all.

 Theorem T135a: Problem135a. cbv. intros.  firstorder. Abort all.

 Theorem T135b: Problem135b. cbv. intros. firstorder. Abort all.

 Theorem T136A: Problem136a. cbv. intros. firstorder. Abort all.

 Theorem T138a: Problem138a. cbv. intros.

 Theorem T139a: Problem139a.
cbv. destruct large_A as [large]. intros. destruct H. destruct H. destruct H0. firstorder. Qed. 

 Theorem T140a: Problem140a. cbv.  intros.  firstorder. generalize H. apply sayCovariant_K. firstorder. Qed. 


 Theorem T141a: Problem141a. cbv. 
intros. firstorder. 
 Abort all. (*unk*)

 Theorem T142a: Problem142a. cbv. intros. firstorder. Qed.

 Theorem T143a: Problem143a. cbv. intros. firstorder. Abort all. (*unk*)