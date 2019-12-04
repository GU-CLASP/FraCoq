
Load Formulas.


(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Parameter itIsTheCaseThatIdiom : forall p x, case_N x -> that_Subj p (IMPERSONAL = x) = p.

(* If the speaker asserts that x knows p, then p holds from the speaker's perspective.*)
Section Temps.
Variable y1993before1996 : Date_19931231 < Date_19960101.
Variable y1992before1993 : Date_19921231 < Date_19930101.
Variable y1991before1993 : Date_19911231 < Date_19930101.
Variable y1991before1992 : Date_19911231 < Date_19920101.
Variable y1993 : Date_19930101 < Date_19931231.
Variable y1992 : Date_19920101 < Date_19921231.
Variable future : NOW <= INDEFINITE_FUTURE.
Variable y1992before1993March : Date_19921231 <  Date_19930301.
Variable y1993March : Date_19930301 < Date_19930331.
Variable MarchIn93a : Date_19930101 < Date_19930301.
Variable MarchIn93b : Date_19930331  < Date_19931231.

Theorem  problem251aTrue : Problem251aTrue.
intro.
assumption.
Qed.

Require Import Psatz.

Theorem  problem252aTrue : Problem252aTrue.
unfold Problem252aTrue.
cbv.
intros t p.
intros [P1 P2].
eexists.
eexists.
split.
reflexivity.
split.
reflexivity.
split.
lia.
apply P1.
split.
lia.
split.
lia.
lia.
Qed.

Theorem  problem255aTrue : Problem255aTrue.
cbv.
intros t0 p0.
intros [P1 P2].
exists Date_19930101.
exists Date_19930101.
split.
lia.
split.
lia.
split.
lia.
eapply P1.
split.
lia.
split.
Focus 2.
reflexivity.
lia.
Qed.

Theorem  problem257aTrue : Problem257aTrue.
cbv.
intros t p.
intros [P1 P2].
eexists.
eexists.
split.
reflexivity.
split.
reflexivity.
split.
lia.
eapply P1.
split.
lia.
split.
reflexivity.
lia.
Qed.

Parameter foundNotExisit_K : forall x o t0 t1, found_V2 x o t0 t1 -> forall t' t1', t' < t0
-> exist_V x t' t1' -> False.



Theorem  problem258aFalse : Problem258aFalse.
cbv.
intros t0 p0.
intros t1 p1.
intros P1 P2.
assert (Date_19920101 < Date_19930301).
lia.
destruct P1 as [tF [tF' [cF1 [cF2 [cF3 P1]]]]].
destruct P2 as [tE [tE' [cE1 [cE2 [cE3 P2]]]]].
eapply foundNotExisit_K.
eapply P1.
Focus 2.
eapply P2.
lia.
Qed.

Theorem  problem259atrue : Problem259aTrue.
cbv.
(* intros conf isConf [P1 P2]. *)
(* Syntax wrong, using impersonal "it" in P2 *)
Abort All.

Theorem  problem260aTrue : Problem260aTrue.
cbv.
intros t0 p0.
intros t1 p1.
intros contract isContract.
intros [P1 P2].
destruct P2 as [today [isToday P2']].
cut (NOW - ONEDAY = Date_0713).
intro H.
rewrite <- H.
assumption. 
lia.
Qed.


Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
intros t1 t1Past t2 t2Past t3 t3Past.

intros [p1Order [p1a [p1b [p2Order [p2a p2b]]]]].
split.
lia.
split.
assumption.
assumption.
Qed.

Transparent PN2object.
Theorem  problem262atrue : Problem262aTrue.
cbv.
intros.
split.
lia.
intuition.
Qed.


Theorem  problem264atrue : Problem264aTrue.
cbv.
intros t1 past1 t2 past2 [P1 P2].

split.
lia.
split.
tauto.
tauto.
Qed.

Theorem  problem265atrue : Problem265aTrue.
cbv.
intros.
split.
lia.
split.
tauto.
tauto.
Qed.

Theorem  problem266atrue : Problem266aTrue.
cbv.
intros.
split.
lia.
split.
tauto.
tauto.
Qed.

Transparent PN2object.
Theorem  problem267atrue : Problem267aTrue.
cbv.
intros.
destruct H2 as [a [b [H3]]].
split.
lia.
intuition.
Qed.

Theorem  problem268atrue : Problem268aTrue.
cbv.
intros.
destruct H2 as [a [b [H3]]].
split.
lia.
intuition.
Qed.


Theorem  problem269atrue : Problem269aTrue.
cbv.
intros t1 p1 t2 p2 t3 p3 t4 p4 [P1 P2].
split.
Abort All.

Theorem  problem270atrue : Problem270aTrue.
cbv.
intros.
destruct H2 as [A [B [C [D E]]]].
split.
assumption.
split.
assumption.
assumption.
Qed.

Theorem  problem271atrue : Problem271aTrue.
cbv.
intros t1 p1 t2 p2 t3 p3 t4 p4 t5 p5 t6 p6 t7 p7 t8 p8 t9 p9 t10 p10.
intros [P1 [P2 P3]].
split.
(* A fluke: adjectives do not have temporal parameter *)
Abort All.

Theorem  problem273atrue : Problem273aTrue.
cbv.
intros.
destruct H5 as [P1 [P2 P3]].
split.
Abort All.

Definition UniqueEvent : (TProp) -> Prop
 := fun p => forall t0 t0' , p t0 t0 -> p t0' t0' -> t0 = t0'.

Definition UniqueActivity : (TProp) -> Prop
 := fun p => forall t0 t0' t1 t1' , p t0 t1 -> p t0' t1' -> t0 = t0' /\ t1 = t1'.

Parameter writeUnique : forall (x y : object), UniqueActivity (write_V2 x y).

Theorem  problem278atrue : Problem278aFalse.
cbv.
intros a b c e.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P1 H) as B.
lia.
Qed.

Theorem  problem279 : Problem279aFalse.
cbv.
intros tt0 p0.
intros tt1 p1.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P1 H) as B.
lia.
Qed.

Parameter discoverUnique : forall (x y : object), UniqueEvent (discover_V2 x y).

Theorem  problem282 : Problem282aFalse.
cbv.
intros tt0 p0.
intros tt1 p1.
intros species isNewSpecies P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize discoverUnique with (x := species)(y := SMITH) as A.
unfold UniqueEvent in A.
specialize (A _ _ P1 H) as B.
lia.
Qed.


Definition Time_1000 := PlusTwoHours Time_0800.
Variable hoursPositive : OneHour > 0.
Parameter past : forall t, INDEFINITE_PAST <= t.
Theorem  problem284 : Problem284aTrue.
cbv.
intros t0 p0.
intros t1 p1.
intros report isReport.
intros [P1 P2].
specialize P1 with (b := Time_0800).
destruct P2 as [t2 P2].
specialize writeUnique with (x := report)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P2 P1) as B.
eexists.
eexists.
split.
Focus 2.
exact P2.
split.
apply past.
lia.
Qed.

(*Theorem problem286 : Problem286aFalse.
Abort All.
FIXME: Horrid syntax.
*) 

Theorem problem288 : Problem288aTrue.
cbv.
intros t0 p0 t1 p1 t2 p2.
intros P1.
specialize P1 with (b := t0).
destruct P1 as [report [isReport P1]].
exists report.
split.
assumption.

(* FIXME: the event lookup fails due to the existential
quantification; but the time points are quantified at the toplevel.
Perhaps we should not quantify at the top-level (ever); but rather
always quantify locally and use the "unique" property of events more
liberally.
*)
Abort All.

Transparent PN2object.
Theorem  problem307atrue : Problem307aTrue.
cbv.
(* We need a start and end date for time intervals. "every month", can be interpreted as "every time" for now. *)

Abort All.

Transparent PN2object.
Theorem  problem311atrue : Problem311aTrue.
cbv.
intros t1 t1Past t2 t2Past theStation isStation theHouse isHouse [P1 P2].
(* Deep reason for why it won't work is that "taxi" is existentially quantified, and so, not the same event (see discussion about repeatability in Temporal.org)*)
(* And also, the syntax is anyway not the same in P and H. *)
Abort All.


Opaque PN2object.
Theorem  problem312atrue : Problem312aTrue.
cbv.
intros t0 p0 t1 p1 [P1 P2].
exists Date_19930301.
exists Date_19930331.
split.
lia.
split.
lia.
split.
lia.
eapply P1.
reflexivity.
Qed.

Theorem  problem313atrue : Problem313aFalse.
cbv.
intros t0 p0 t1 p1.
intros [P1 P2].
intro Q.
destruct Q as [t [t' [tC1 [ tC2 [tC3 [report [isReport Q]]]]]]].
eapply P1.
Focus 2.
exists report.
split.
assumption.
exact Q.
reflexivity.
Qed.

Parameter know_implicature : forall p x t0 t1, know_VS p x t0 t1 -> p.

Opaque PN2object.
Theorem  problem320btrue : Problem320aTrue.
cbv.
intros ta pa tb pb.
intros memoir hisMemoir.
intros theCase isCase.
intros failAnaphora hisMemoir'.
(*TODO: look at possible readings *)
(*destruct H5 as [t [P1 P2]].
specialize (know_implicature P2) as Q.
rewrite -> itIsTheCaseThatIdiom.
split.
intros [memoir [obvious R]].
eapply Q.
reflexivity.*)
Abort All.
