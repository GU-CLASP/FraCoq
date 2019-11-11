Load Formulas.

Parameter y1993before1996 : Year_1993 <  Year_1996.
Parameter y1992before1996 : Year_1992 <  Year_1996.
Parameter y1992before1993 : Year_1992 <  Year_1993.

(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Parameter itIsTheCaseThatIdiom : forall p x, case_N x NOW -> that_Subj p (IMPERSONAL = x) = p.

(* If the speaker asserts that x knows p, then p holds from the speaker's perspective.*)
Parameter know_weakening : forall p x t, know_VS p x t -> p.


Theorem  problem251aTrue : Problem251aTrue.
cbv.
intro.
assumption.
Qed.

Theorem  problem252aTrue : Problem252aTrue.
cbv.
intros t tPast.
intros [P1 P2].
apply P1.
apply y1992before1993.
Qed.

Theorem  problem255aTrue : Problem255aTrue.
cbv.
intros t tPast.
intros [P1 P2].
apply P1.
apply y1992before1993.
Qed.
Require Import Psatz.

Theorem  problem260aTrue : Problem260aTrue.
cbv.
intros t tPast t2 t2Past.
intros contract isContract.
intros [P1 P2].
destruct P2 as [today [isToday P2']].
cut (NOW - ONEDAY = Date_0713).
intro H.
rewrite <- H.
assumption. 
lia.
Qed.


Parameter foundNotExisit_K : forall x o t, found_V2 x o t -> forall t', t' < t
-> exist_V x t' -> False.

Parameter y1992before1993March : Year_1992 <  Year_1993_Month_March.

Theorem  problem258aFalse : Problem258aFalse.
cbv.
intros.
apply foundNotExisit_K with (x := PN2object itel_PN) (o := (PN2object apcom_PN) )
                            (t' := Year_1992) (t := Year_1993_Month_March).
assumption.
apply y1992before1993March.
assumption.
Qed.

Theorem  problem259atrue : Problem259aTrue.
cbv.
intros.
(* Syntax wrong, using impersonal "it" in P2 *)
Abort All.


Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
intros t1 t1Past t2 t2Past t3 t3Past [p1Order [p1a [p1b [p2Order [p2a p2b]]]]].
split.
lia.
firstorder.
Qed.


Transparent PN2object.
Theorem  problem262atrue : Problem262aTrue.
cbv.
intros.
split.
lia.
firstorder.
Qed.

Transparent PN2object.
Theorem  problem267atrue : Problem267aTrue.
cbv.
intros.
destruct H2 as [a [b [H3]]].
split.
lia.
firstorder.
Qed.

Transparent PN2object.
Theorem  problem307atrue : Problem307aTrue.
cbv.
(* We need a start and end date for time intervals. "every month", can be interpreted as "every time" for now. *)

Abort All.

Transparent PN2object.
Theorem  problem311atrue : Problem311aTrue.
cbv.
intros t1 t1Past t2 t2Past theStation isStation theHouse isHouse [P1 P2].
(*TODO: fix the syntax tree so it's the same in P and H *)
Abort All.


Theorem  problem312atrue : Problem312aTrue.
cbv.
intros t1 t1Past t2 t2Past [P1 P2].
apply P1.
split.
Qed.

Theorem  problem313atrue : Problem313aFalse.
cbv.
intros t1 t1Past t2 t2Past [P1 P2] [report [isReport Q]].
apply (P1 Year_1993).
split.
exists report.
split.
exact isReport.
exact Q.
Qed.

Theorem  problem320atrue : Problem320aTrue.
cbv.
intros.
destruct H2 as [t [P1 P2]].
assert (Q := know_weakening P2).
rewrite -> itIsTheCaseThatIdiom.
split.
intros [memoir [obvious R]].
Abort All.
