Load FraCoq2.



Require Import Omega.

Theorem T114a: Problem114aTrue. cbv. intros. destruct H. destruct H. exists x. split. exact H. exists (PN2object mary_PN). split. apply I. exact H0. Qed. 


Theorem T115A: Problem115aTrue. cbv. intros. destruct H. destruct H. destruct H.  exists x. split. exact H1. exact H. Qed. 

Theorem T116a: Problem116aTrue. cbv. intros.  split. apply mary_PN_Female.  destruct H.   destruct H. destruct mkPN. exact c. Qed.


Theorem T117a: Problem117aTrue. cbv. intros.  elim H. intros. apply H. exact H1. Qed. 

Theorem T118a: Problem118aTrue.
cbv.
firstorder.
Qed.

Transparent PN2object.
Theorem T119a: Problem119aTrue.
cbv.
firstorder.
Abort All.

Theorem T119a: Problem119aFalse.
cbv.
intros [P1 P2].
intros [ws H].
apply P1 with MARY.
assumption.
exists ws.
split.
split.
Abort All.
Opaque PN2object.

Theorem T120a: Problem120aTrue.
cbv.
firstorder.
Qed.

Theorem T121a: Problem121aTrue.
cbv.
firstorder.
Qed.

Theorem T122a: Problem122aTrue.
cbv.
firstorder.
Qed.

Theorem T123a: Problem123aTrue. cbv. intros. firstorder.
Qed. 

Theorem T123b: Problem123bTrue.   cbv.  intros. destruct H. firstorder. Abort all.

(*

-- 124-126: At least, we need to change the syntax so that "Two out of
-- ten" is interpreted as a quantifier. At GF level: Both "two" and
-- "ten" introduce a quantifier. "They" can refer to either of the
-- bound variables. Unclear what to do about this.  Really this set of
-- examples should treat "two out of ten" as a quantifier. (Needs
-- another syntax)

*)

Theorem T124a: Problem124aTrue.
cbv. intros. elim H. intros.  destruct H0. destruct H1. destruct H1.  Abort all. 

Theorem T124b : Problem124bTrue. 
cbv. intros. elim H.  
intros.      destruct H0. destruct H1. destruct H1.  
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

Theorem T126A: Problem126aTrue. cbv. intros.  elim H. intros.  destruct H0. destruct H1. destruct H1.  destruct H1. Abort all.  (** Error **)

Theorem T126b: Problem126bTrue.  cbv. intros.  elim H. intros.  destruct H0. destruct H1. destruct H1.   Abort all. 

                             
 Theorem T127a: Problem127aTrue. cbv. intros. Abort all.  (**This is marked yes on a distributive reading. One of the funny examples with two readings**)
(*-- 127: We need "they" to refer to any disjunction of NPs introduced so -- far.
*)

 Theorem T128a: Problem128aTrue. cbv. intros. destruct H0. destruct H1. destruct H1. destruct H2. destruct H3. exists x1. firstorder. Qed.

 Theorem T129a: Problem129aTrue. cbv. intros. firstorder. Qed.


 Theorem T130at: Problem130aTrue. cbv. intros. destruct H0. destruct H1. destruct H2. firstorder. Qed.

(*-- Analysis for 130:  FRACAS. Incompatible with 129. (It should be sufficent
-- that one reading allows to conclude.)
*)  

 Theorem T131c: Problem131cTrue. cbv. intros.  firstorder.  Qed.  (**try 131a,b**)
(*
-- Analysis for 131.  In H2, a plural "they" is used to refer to a
-- singular object introduced with indefArt. When the scope of
-- "forall" is closed (when the sentence is finished), the singular
-- existential is transformed to plurals. Existentially quantified
-- variables are pushed with the "dPluralizable = True" flag if a
-- universal was introduced in the sentence. When the sentence is
-- closed, all dPluralizable entries in the environment are re-written
-- to be accessible by a plural. To know if we have a pluralizable
-- context, the envPluralizingQuantifier flag is used. It is set in
-- the dyn. semantics of universals.
-- (DONE)
*)

 Theorem T1312at: Problem132aTrue. cbv. intros.  firstorder. Abort all. 

 Theorem T132bf: Problem132bTrue. cbv. intros. firstorder. Qed.

 Theorem T133a: Problem133aTrue. cbv.
  firstorder. Qed.


Theorem T134b: Problem134bTrue. cbv.
intros [P1 [P2a [compy P2]]].
intros computer [H0 H1].
cut (compy = computer).
intro H.
rewrite H in P2.
destruct P2 as [A [B C]] .
apply P1 with (x := computer).
exact A.
split.
exact P2a.
exact B.
destruct P2 as [A [B C]] .
generalize C.
apply exactEqual.
split.
exact A.
exact B.
split.
exact H1.
exact H0.
Qed.


 Theorem T135a: Problem135aTrue. cbv. intros.  firstorder. Abort all. (* b is the correct reading *)

 Theorem T135b: Problem135bTrue. cbv. intros. firstorder. Qed.

 Theorem T136A: Problem136aTrue. cbv. intros. firstorder. Abort all.

(*
-- 137.
-- a) "There are 100" --> should in general be interpreted as "at least", until we see in P4 the mention of "the other 99", implying an exact interpretation.
-- b) Difficulty to relate "THE company_N" to the set introduced in the first premise.
-- c) Difficult to interpret: (advNP (detNP (anySg_Det)) (prepNP (lexemePrep "part_Prep") (detCN (detQuant (possPron (itRefl_Pron)) (numPl)) (useN (lexemeN "computer_N")))))
*)

Theorem T138a: Problem138aTrue. cbv.
 Abort all.
(* FIXME:

FORALL (fun c=>cover_page_Npossess (PN2object r95103_PN) c) (fun c=>
  (FORALL (fun a=>report_N a) (fun a=>
    (EXISTS (fun b=>cover_page_N b) (fun b=>have_V2 b a)))) /\
  report_N (PN2object r95103_PN) /\
  sign_V2 b (PN2object smith_PN) -> sign_V2 c (PN2object smith_PN))

the EXISTS is moved upwards BUT alone.
Instead, the "forall should be taken with it."
*)

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
intro H.
firstorder.
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

