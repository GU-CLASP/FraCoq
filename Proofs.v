Load FraCoq2.

Theorem T114a: Problem114aTrue. cbv. intros. destruct H. destruct H. exists x. split. exact H. exists (PN2object mary_PN). split. apply I. exact H0. Qed. 


Theorem T115A: Problem115aTrue. cbv. intros. destruct H. destruct H. destruct H.  exists x. split. exact H1. exact H. Qed. 

Theorem T116a: Problem116aTrue. cbv. intros.  split. apply mary_PN_Female. apply I. Qed.


Theorem T117a: Problem117aTrue. cbv. intros.  elim H. intros. apply H. exact H1. Qed. 


Theorem T123a: Problem123aTrue. cbv. intros. firstorder. 
Qed. 

Theorem T123b: Problem123bTrue.   cbv.  intros. destruct H. firstorder. Abort all.

Theorem T124a: Problem124aTrue.
cbv. intros. elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1. destruct H3. destruct H. destruct H. destruct H5. exists x0. destruct H5. destruct H5. destruct H7. firstorder. 
   firstorder. Abort all. 

Theorem T124b : Problem124bTrue. 
cbv. intros. elim H.  
intros.      destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1. destruct H3. destruct H. destruct H. destruct H5.       exists x.   split. assumption. split. exists x1. split. exact I. firstorder. destruct H5.  destruct H5. 
destruct H5. destruct H8. firstorder. 
destruct H1. firstorder. 
Abort All. 

Theorem T125at: Problem125aTrue. 
  cbv. intros. firstorder. Abort all.

Theorem T125af: Problem125aFalse. 
  cbv. intros. firstorder. Abort all.

(**UNK so this is fine**)

Theorem T125bt: Problem125bTrue.
  cbv. intros. firstorder. Abort all.  (**Ibid**)


Theorem T125bf: Problem125bFalse.
  cbv. intros. firstorder. Abort all.  (**Ibid**)

Theorem T126A: Problem126aTrue. cbv. intros.  elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1.  destruct H. destruct H. destruct H5. destruct H5. destruct H5. destruct H5. destruct H8.  Abort all.  (**Needs to be fixed**)

Theorem T126b: Problem126bTrue.  cbv. intros.  elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. destruct H1.  destruct H. destruct H. destruct H5. destruct H5. destruct H5. destruct H5. destruct H8.
 exists x. Abort all. 

                             
 Theorem T127a: Problem127aTrue. cbv. intros. Abort all.  (**This is marked yes on a distributive reading. One of the funny examples with two readings**)

 Theorem T128a: Problem128aTrue. cbv. intros. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x1. firstorder. Qed.

 Theorem T129a: Problem129aTrue. cbv. intros. firstorder. Qed.

 Theorem T130at: Problem130aTrue. cbv. intros. destruct H0. destruct H1. destruct H2. Abort all.

 Theorem T130af: Problem130aFalse. cbv. intros. destruct H0.  firstorder. Abort all.   (**unk**)

  

 Theorem T131c: Problem131cTrue. cbv. intros.  firstorder.  Qed.  (**try 131a,b**)

 Theorem T1312at: Problem132aTrue. cbv. intros.  firstorder. Abort all. 

 Theorem T132bf: Problem132bTrue. cbv. intros. firstorder. Qed.

 Theorem T133a: Problem133aTrue. cbv. intros. destruct H. destruct H. destruct H. apply H1. exact H0. Qed.

 Theorem T134a: Problem134aTrue. cbv. intros. destruct H. destruct H1. destruct H2. destruct H2. destruct H3.  Abort all. (**donkey sentence**)

 Theorem T134b: Problem134bTrue. cbv. intros. firstorder. exists x. Abort all.

 Theorem T135a: Problem135aTrue. cbv. intros.  firstorder. Abort all.

 Theorem T135b: Problem135bTrue. cbv. intros. firstorder. Abort all.

 Theorem T136A: Problem136aTrue. cbv. intros. firstorder. Abort all.

 Theorem T138a: Problem138aTrue. cbv. intros. Abort all. 

 Theorem T139a: Problem139aTrue.
cbv. destruct large_A as [large]. intros. destruct H. destruct H. destruct H0. firstorder. Qed. 

 Theorem T140a: Problem140aTrue. cbv.  intros.  firstorder. generalize H. apply sayCovariant_K. firstorder. Qed. 


 Theorem T141a: Problem141aTrue. cbv. 
intros. firstorder. 
 Abort all. (*unk*)

 Theorem T142a: Problem142aTrue. cbv. intros. firstorder. Qed.

 Theorem T143a: Problem143aTrue. cbv. intros. firstorder. Abort all. (*unk*)

 Theorem T144a: Problem144aTrue. cbv. intros. firstorder. Qed.

 Theorem T144b: Problem144bTrue. cbv. intros. firstorder. Abort all. (**wrong reading**)

Theorem T145a: Problem145aTrue. cbv. intros. firstorder. Abort all. (**wrong reading**)
 
Theorem T145b: Problem145bTrue. cbv. intros. destruct H. exact H0. Qed.

Theorem T146a: Problem146aTrue. cbv. intros. destruct H. exact H0. Qed.



Theorem T147a:  Problem147aFalse. cbv. intro.  destruct H.  destruct on_monday_Adv as [on_mon on_mon_ver]. firstorder. Qed.

Theorem T147b: Problem147bFalse. cbv. intro. destruct H.  destruct on_monday_Adv as [on_mon on_mon_ver]. firstorder. Qed.

Theorem T148a: Problem148aTrue. cbv. intro. exact H. Qed.

Theorem T149a: Problem149aTrue. cbv. intro. destruct H as [H1 H2]. exact H2. 
Qed.

Theorem T150a: Problem150aTrue.  cbv. intros. firstorder. Abort all. (**Wrong Reading**)

Theorem T150b: Problem150bTrue.  cbv. intros. destruct H. apply H0.  Qed.

Theorem T151a: Problem151aTrue. cbv. intros. destruct H.  firstorder. Abort all.

Theorem T151b: Problem151bTrue.  cbv. intros. destruct H. firstorder. Abort all.

Theorem T151c: Problem151cTrue. cbv. intros. destruct H. firstorder. Abort all. (**All three readings are incorrect! FIXME**)
Theorem T152a: Problem152aTrue. cbv. intros. destruct H. firstorder. Abort all. 

Theorem T152b: Problem152bTrue.  cbv. intros. destruct H. Abort all.

 
Theorem T152c: Problem152cTrue.  cbv.  intros. destruct H.    destruct H.  firstorder. Abort all.

Theorem T153a: Problem153aTrue. cbv. intros. destruct H. 
firstorder.  Abort all. 

Theorem T153b: Problem153bTrue. cbv. intros. destruct H. 
                                firstorder.  Qed.

Theorem T153c: Problem153cTrue. cbv. intros. destruct H. firstorder. Abort all.

Theorem T154a: Problem154aTrue. cbv. intros. destruct H. firstorder. Abort all.

Theorem T154b: Problem154bTrue.  cbv. intros. destruct H. firstorder. Qed.

 Theorem T154c: Problem154cTrue. cbv. intros. destruct H. firstorder. Abort all. 