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
Variable hoursPositive : OneHour > 0.
Parameter past : forall t, INDEFINITE_PAST <= t.
Variable isPast : INDEFINITE_PAST < NOW.

Theorem  problem251aTrue : Problem251aTrue.
intro.
assumption.
Qed.

Require Import Psatz.

(* Parameter Date_19960606. *)
(* Variable someIn96 : Variable y1993before1996 : Date_19931231 < Date_19960101. *)

Theorem  problem252aTrue : Problem252aTrue.
unfold Problem252aTrue.
cbv.
intros [P1 P2].
exists INDEFINITE_PAST.
split.
lia.
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
intros [P1 P2].
exists INDEFINITE_PAST.
eexists.
lia.
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
reflexivity.
split.
lia.
lia.
Qed.


Theorem  problem257aTrue : Problem257aTrue.
cbv.
intros [P1 P2].
exists INDEFINITE_PAST.
split.
lia.
eexists.
eexists.
split.
reflexivity.
split.
reflexivity.
split.

lia.
eapply P1 with (c := Date_19931231).
split.
reflexivity.
split.
lia.
lia.
Qed.

Parameter foundNotExisit_K : forall x o t0 t1, found_V2 x o t0 t1 -> forall t' t1', t' < t0
-> exist_V x t' t1' -> False.



Theorem  problem258aFalse : Problem258aFalse.
cbv.
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
intros contract isContract.
intros [P1 P2].
destruct P2 as [today [isToday P2']].
cut (NOW - ONEDAY = Date_0713).
intro H.
rewrite <- H.
eexists.
split.
Focus 2.
apply P1.
apply isPast.
lia.
Qed.


Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
intros t1 t1Past t2 t2Past.
intro P1.
destruct P1 as [t3 [c2 [t5 [c5 [t4 [c3 [c4 Q]]]]]]].
split.
lia.
intuition.
Qed.

Transparent PN2object.
Theorem  problem262atrue : Problem262aTrue.
cbv.
intros.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
split.
lia.
split.
intuition.
intuition.
Qed.


Theorem  problem264atrue : Problem264aTrue.
cbv.
intros.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
split.
lia.
split.
tauto.
tauto.
Qed.

Theorem  problem265atrue : Problem265aTrue.
cbv.
intros.
destruct H1.
destruct H2.
destruct H3.
destruct H4.

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
intros.
exists INDEFINITE_PAST.
split.
lia.
exists INDEFINITE_PAST.
split.
lia.
exists INDEFINITE_PAST.
split.
lia.
exists (INDEFINITE_PAST - OneHour).
split.
lia.
split.
lia.
split.
firstorder.
firstorder.
(* Error: adjectives do not have temporal parameter *)
Qed.

Theorem  problem273atrue : Problem273aTrue.
cbv.
intros.
Abort All.

Definition UniqueEvent : (TProp) -> Prop
 := fun p => forall t0 t0' , p t0 t0 -> p t0' t0' -> t0 = t0'.

Definition UniqueActivity : (TProp) -> Prop
 := fun p => forall t0 t0' t1 t1' , p t0 t1 -> p t0' t1' -> t0 = t0' /\ t1 = t1'.

Parameter writeUnique : forall (x y : object), UniqueActivity (write_V2 x y).

Theorem  problem278atrue : Problem278aFalse.
cbv.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 [t4 [ct4 P1]]]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 [u4 [cu4 H]]]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P1 H) as B.
lia.
Qed.

Theorem  problem279 : Problem279aFalse.
cbv.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 [t4 [ct4 P1]]]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 [u4 [cu4 H]]]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P1 H) as B.
lia.
Qed.

Parameter discoverUnique : forall (x y : object), UniqueEvent (discover_V2 x y).

Theorem  problem282 : Problem282aFalse.
cbv.
intros species isNewSpecies P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 [t4 [ct4 P1]]]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 [u4 [cu4 H]]]]]]].
specialize discoverUnique with (x := species)(y := SMITH) as A.
unfold UniqueEvent in A.
specialize (A _ _ P1 H) as B.
lia.
Qed.


Definition Time_1000 := PlusTwoHours Time_0800.
Theorem  problem284 : Problem284aTrue.
cbv.
intros report isReport.
intros [P1 P2].
destruct P1 as [t0 [c0 P1]].
destruct P2 as [u0 [d0 P2]].
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
exists INDEFINITE_PAST.
split.
lia.
exists (INDEFINITE_PAST - OneHour - OneHour).
split.
lia.
destruct H as [t0 [p B]].
specialize B with (b := INDEFINITE_PAST - OneHour - OneHour).
destruct B.
destruct H.
exists x.
split.
assumption.
cut (INDEFINITE_PAST - OneHour - OneHour + OneHour + OneHour = INDEFINITE_PAST).
intro Q.
rewrite -> Q in H0.
assumption.
lia.
Qed.

Theorem problem289 : Problem289aFalse.
cbv.
intros species newSpecies.
intros [t1 [tPast P1]].
(* "Spend 2 hours has not a correct interpretation "*)
Abort All.

Theorem problem290 : Problem290aTrue.
cbv.
intro P1.
destruct P1 as [t1 [p1 P1]].
exists ((INDEFINITE_PAST - OneHour - OneHour) + OneHour + OneHour).
split.
Focus 2.
eapply P1.
lia.
Qed.

Theorem problem294 : Problem294aTrue.
cbv.
intros business isBusiness.
(* FIXME: inconsistent syntax for "in two years" compared to 285, etc. *)
Abort All.

Opaque PN2object.
Theorem problem298 : Problem298aTrue.
cbv.

Transparent PN2object.
Theorem  problem307atrue : Problem307aTrue.
cbv.
(* TODO  *)

Abort All.

Transparent PN2object.
Theorem  problem311atrue : Problem311aTrue.
cbv.
intros theStation isStation theHouse isHouse [P1 P2].
(* Deep reason for why it won't work is that "taxi" is existentially quantified, and so, not the same event (see discussion about repeatability in Temporal.org)*)
(* And also, the syntax is anyway not the same in P and H. *)
Abort All.


Opaque PN2object.
Theorem  problem312atrue : Problem312aTrue.
cbv.
intros [P1 P2].
eexists.
split.
Focus 2.
eexists.
eexists.
repeat split.
Focus 4.
eapply P1.
reflexivity.
reflexivity.
reflexivity.
lia.
apply isPast.
Qed.

Theorem  problem313atrue : Problem313aFalse.
cbv.
intros [P1 P2].
intro Q.
destruct Q as [t [t' [tC1 [ tC2 [tC3 [tC4 [tC5 [report [isReport Q]]]]]]]]].
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
intros memoir hisMemoir.
intros theCase isCase.
intros failAnaphora hisMemoir'.
(*TODO: look at possible readings *)
intros theJob isCIAJob.
intros [t1 [c1 [c2 [c3 [c4 P1]]]]].
destruct P1 as [gotJob knowStuff].
specialize (know_implicature knowStuff) as Q.
rewrite -> itIsTheCaseThatIdiom.
split.
intros [memoir [obvious R]].
eapply Q.
reflexivity.*)
Abort All.
