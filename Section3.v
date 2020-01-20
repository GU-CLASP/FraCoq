Load Formulas.

Require Import Coq.Program.Tactics.
Require Import Omega.

Theorem T114a:
Problem114aTrue.
cbv.
intros.
destruct_conjs.
exists H0.
firstorder.
Qed. 


Theorem T115A: Problem115aTrue.
cbv.
cbv.
intros.
destruct_conjs.
exists x.
firstorder.
Qed.

Theorem T116a: Problem116aTrue. cbv. intros.
split.
apply mary_PN_Female.
destruct mkPN. exact c. Qed.


Theorem T117: Problem117aTrue. cbv.

exists x.

elim H. intros. apply H. exact H1. Qed. 

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
  cbv. intros.
  (*firstorder.*) Abort all.  (**Ibid**)


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

Parameter reports_have_Single_Cover_Page_K : forall report cover1 cover2,
  report_N report ->
  cover_page_N cover1 ->
  cover_page_N cover2 ->
  have_V2 cover1 report ->
  have_V2 cover2 report ->
  (cover1 = cover2).
(* A true fact *)
Check reports_have_Single_Cover_Page_K.

Theorem T138a: Problem138aTrue. cbv.
intros coverPageOfR95103 [isCoverPage ofR95103].
intro P.
destruct P as [cover [isCover [repHasCover [isReport isSigned]]]].
lapply (repHasCover (PN2object r95103_PN)).
intro hasCover'.
lapply (reports_have_Single_Cover_Page_K isReport isCover isCoverPage hasCover') .
intro R.
rewrite R in isSigned.
exact isSigned.
assumption.
assumption.
Qed.

(* Commentary:
  Even though we get the above correctly, there are some difficulties with the interpretation.

  1. The logical formulation for the above problem states that all reports have the same cover page.


FORALL (fun c=>cover_page_Npossess (PN2object r95103_PN) c) (fun c=>
  (FORALL (fun a=>report_N a) (fun a=>
    (EXISTS (fun b=>cover_page_N b) (fun b=>have_V2 b a)))) /\
  report_N (PN2object r95103_PN) /\
  sign_V2 b (PN2object smith_PN) -> sign_V2 c (PN2object smith_PN))

the EXISTS is moved upwards BUT alone.
Instead, the "forall should be taken with it."

  2. But, even if we were to fix this, the problem intends to detect the fact that "the cover page" implicitly refers to the cover page of a given report (which is elided:) "Smith signed *its* cover page."
*)

 Theorem T139a: Problem139aTrue.
cbv. destruct large_A as [large]. intros. destruct H. destruct H. destruct H0. firstorder. Qed. 

 Theorem T140a: Problem140aTrue. cbv.  intros.  firstorder. generalize H. apply sayCovariant_K. firstorder. Qed. 


 Theorem T141a: Problem141aTrue. cbv. 
intros. firstorder. 
 Abort all. (*unk*)

 