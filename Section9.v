
Load Formulas.

Require Import Coq.Program.Tactics.
Require Import Psatz.

Theorem FraCaS334: Problem334aTrue.
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corpN].
destruct in_1992_Adv as [in92].
intros theContract isContract.
intros.
destruct_conjs.
specialize (know_implicature H1) as A.
destruct_conjs.
exists A.
exists H2.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
Qed.

Theorem FraCaS335: Problem335aTrue.
cbv.
firstorder.
Abort All. (* UNK *)
Theorem FraCaS335: Problem335aFalse.
cbv.
firstorder.
Abort All. (* UNK *)


Parameter manageTo_implicature : forall (x:object) (p:VP) t0 t1, manage_VV p x t0 t1 -> p x.

Theorem FraCaS336: Problem336aTrue.
cbv.
destruct in_1992_Adv as [in92 [in92Verid in92Covariant]].
destruct itel_PN as [itel corpN]. 
intros theContract isContract.
intros.
destruct_conjs.
specialize (manageTo_implicature H4) as A.
cbv in A.
repeat eexists.
Focus 4.
exact A.
exact H1.
assumption.
assumption.
Qed.


Theorem FraCaS337: Problem337aTrue.
cbv.
destruct itel_PN as [itel corpN]. 
intros.
destruct_conjs.
Abort all. (*UNK*)

Theorem FraCaS338: Problem338aTrue.
cbv.
destruct itel_PN as [itel corpN].
firstorder.
Qed.

Theorem FraCaS339: Problem339aFalse.
cbv.
destruct itel_PN as [itel corpN].
destruct false_A as [false].
firstorder.
Qed.

Variable see_implicature
: forall t0 t1 (dobject subject :object) (p:VP), see_V2V dobject p subject t0 t1 -> p dobject. 

Theorem FraCaS340: Problem340aTrue.
 cbv.
 destruct jones_PN as [jones person].
 destruct smith_PN as [smith person'].
 firstorder.
Abort all. (*UNK*)


Theorem FraCaS341: Problem341aTrue.
 cbv.
 destruct jones_PN as [jones person].
 destruct smith_PN as [smith person'].
 firstorder.
Abort all. (*UNK*)


Theorem FraCaS342: Problem342aTrue.
cbv.
intros theContract isContract.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corpN].
intros.
destruct_conjs.
specialize (see_implicature H1) as A.
cbv in A.
exists H.
split.
assumption.
assumption.
Qed.

Theorem FraCaS343: Problem343aTrue.
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corporation].
firstorder.
rewrite <- H2.
firstorder.
Qed.

Theorem FraCaS344: Problem344aTrue.
cbv.
destruct helen_PN as [helen person].
intros.
destruct_conjs.
(* Temporal error: subclause should be using a local time *)
Abort All.

Transparent PN2object.
Theorem FraCaS345: Problem345aTrue.
cbv.
destruct smith_PN as [smith person'].
destruct jones_PN as [jones person].
intros.
destruct_conjs.
(* Temporal Error: tense incorrect in premise, for unknown reason*)
Abort All.

Theorem FraCaS346: Problem346bTrue.
cbv.
intros clause isClause.
intros theContract isContract.
intuition.
Qed.
