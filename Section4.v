Load Formulas.
Require Import Omega.


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

Theorem T149a: Problem149aTrue. cbv. firstorder. Qed.

Theorem T150a: Problem150aTrue.  cbv. intros. firstorder. Abort all. (**Wrong Reading**)

Theorem T150b: Problem150bTrue.  cbv. intros. destruct H. apply H0.  Qed.

Theorem T151b: Problem151bTrue.  cbv. intros. destruct H. firstorder. Qed.

Theorem T152a: Problem152aTrue.  cbv. intros. destruct H. firstorder. Qed.

Theorem T152b: Problem152bTrue.  cbv. intros. destruct H. Abort all.

 

Theorem T153a: Problem153aTrue. cbv. intros. firstorder.  Abort all. 

Theorem T153b: Problem153bTrue. cbv. intros.  
                                firstorder.  Qed.

Theorem T153c: Problem153cTrue. cbv. intro. firstorder. Abort all.

Theorem T154a: Problem154aTrue. cbv. intros. destruct H. firstorder. Abort all.

Theorem T154b: Problem154bTrue.  cbv. intros. destruct H. firstorder. Qed.

Theorem T154c: Problem154cTrue. cbv. intros. destruct H. firstorder. Abort all.

Theorem T155a: Problem155aTrue. cbv. intros. firstorder. Qed.

Theorem T156a : Problem156aTrue. cbv.  intros. firstorder. Abort all. (**UNK**)

Theorem T156a : Problem156aFalse. cbv.  intros. firstorder. Abort all. (**UNK**)

(** reading a: John's car appears both blue and red**)

Theorem T157b: Problem157bTrue. cbv. intros. destruct H.  destruct H0. destruct H0.  firstorder. Qed.



Theorem T158a: Problem158aTrue. cbv. intros. destruct H. destruct H0. destruct H0. firstorder.
Abort All. (**The example is UNK but it can be proven, since this gets the reading where Bill owns a car which is both red and blue!**) (* JP: apparently blue_A is now subsective? *)

Theorem T158b: Problem158bTrue. cbv.  intros. destruct H. destruct H0. firstorder. Abort all. (**This is the correct reading!**)

Theorem T159a: Problem159aTrue. cbv. intros. destruct fast_A.   destruct H.  firstorder. Abort all. (**Wrong reading**)


Theorem T159b: Problem159bTrue. cbv. intros. destruct fast_A.   destruct H.  firstorder. Qed.

Theorem T160a: Problem160aTrue. cbv. intros. firstorder. Qed.

Theorem T160b: Problem160bTrue. cbv. intros. destruct fast_A. firstorder. Abort all. (**Wrong reading**)


Theorem T161a: Problem161aTrue. cbv. intros. firstorder. Qed.

Theorem T161b: Problem161bTrue. cbv. intros. destruct fast_A. firstorder. Abort all. (**This is the exact same example as the previous, FraCaS gives the other reading as UNK, which is this one**)


Theorem T162a: Problem162aTrue. cbv. destruct fast_A. intros. firstorder. Abort all. (**Wrong reading**) 


Theorem T162b: Problem162bTrue. cbv. destruct fast_A. intros. firstorder. Qed.

Theorem T163d: Problem163dFalse. cbv. intro.  destruct H. exact H0. Qed. (**Correct reading**)

Theorem T164a: Problem164aTrue. cbv. intros. firstorder. Qed.

Theorem T165a: Problem165aTrue. cbv. intros. exact H. Qed. 

Theorem T166a: Problem166aTrue. cbv. 
destruct on_thursday_Adv as [on_thu on_thu_verid]. (*JP: made on_thursday_Adv veridical *)
firstorder.
Qed.

Theorem T167a: Problem167aFalse. cbv.
intros salesDept isSalesDept.
intros [P1 [woman [isWoman [works P2]]]].
rewrite -> P2.
intros [w' [isW' [works' H]]].
destruct H.
split.
Qed.

Theorem T168a: Problem168aTrue. cbv. intros. destruct H. exact H0. Qed.

Theorem T169a: Problem169aTrue. cbv. intros. firstorder. Qed.

Theorem T170a: Problem170aTrue. cbv. intros. Abort all.

(** Doing this would require another syntax: 'John found Mary before Bill ELLIPTIC_VP' **)

(* 171: too hard! *)
(* 172: too hard! *)

Theorem T173a: Problem173aTrue. cbv. intros.
destruct john_PN.
destruct bill_PN.
destruct H. apply H.
firstorder.
exact MARY_PERSON.
Qed.

 
Theorem T174a: Problem174aTrue. cbv. intros. firstorder. Abort all. (**unk**)

Theorem T174a: Problem174aFalse. cbv. intro. firstorder. Abort all.

Theorem T175a: Problem175aTrue. cbv. intros. firstorder. Qed.

Theorem T175b: Problem175bTrue. cbv. intros. firstorder. Abort all. (**Wrong reading**)


Theorem T176a: Problem176aTrue. cbv.
apply sayCovariant_K.
firstorder.
Qed.

Theorem T177a: Problem177aTrue. cbv. intros.  firstorder.  Abort all.

Theorem T177b: Problem177aFalse. cbv. intros.  firstorder.  Abort all. (**unk**)

Theorem T178a: Problem178aTrue. cbv. intros. destruct H as [H say]. exact say. Qed.

Theorem T179a: Problem179aTrue. cbv. intros. destruct H as [H say]. firstorder.  Qed.

Theorem T180a: Problem180aTrue. cbv. intros. destruct H as [H want]. exact want. Qed.

Theorem T181a: Problem181aTrue. cbv. intros. destruct H as [H need]. exact need. Qed. (**this is unk in the suite, I think the analysis is correct, my intuition is YES**)

Theorem T182a: Problem182aTrue. cbv. intros. destruct H. exact H0. Qed. 

Theorem T183a: Problem183bTrue. cbv. intros. destruct H. firstorder.  Qed. 

Theorem T184a: Problem184aTrue. cbv. intros. destruct H. firstorder.  Abort all.

Theorem T184a: Problem184aFalse. cbv. intros. destruct H. firstorder.  Abort all.  (**unk**)

Theorem T185a: Problem185aTrue. cbv.
intros [P1 P2].
generalize P2.
apply claimCovariant_K.
firstorder.
Qed.

Theorem T186c: Problem186cTrue. cbv. intros. destruct H. firstorder. Qed. (**reading c  works!**)

Theorem T187d: Problem187dTrue. cbv. intros. destruct H. firstorder. Qed. (**reading d works**)

Theorem T188c: Problem188cTrue. cbv. firstorder. Qed.
(**reading c works while it is supposed to be unknown! System does a good job I think**)
(* We never had a strict reading; however Jones is put into scope before the elliptic VP is evaluated.
And, it must be done this way in order to support 182, 185 at least.*)


Theorem T189a: Problem189aTrue. cbv. intros. destruct H. firstorder. Qed.

Theorem T190b: Problem190bTrue. cbv. intros. destruct H. firstorder. Qed. (**reading b works!**)


Theorem T192a: Problem192aTrue. cbv. firstorder. Abort All.
Theorem T192a: Problem192aFalse. cbv. firstorder. Abort All.

Theorem T194a: Problem194aTrue. cbv. firstorder. Abort All.
Theorem T194a: Problem194aFalse. cbv. firstorder. Abort All.


Theorem T196a: Problem196aTrue. cbv. intro. firstorder. Qed. 

