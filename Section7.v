Load Formulas.


(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Parameter itIsTheCaseThatIdiom : forall p x, case_N x -> that_Subj p (IMPERSONAL = x) = p.

(* If the speaker asserts that x knows p, then p holds from the speaker's perspective.*)

Parameter y1993before1996 : Date_19931231 < Date_19960101.
Parameter y1992before1993 : Date_19921231 < Date_19930101.
Parameter y1991before1993 : Date_19911231 < Date_19930101.
Parameter y1991before1992 : Date_19911231 < Date_19920101.
Parameter y1993 : Date_19930101 < Date_19931231.
Parameter y1992 : Date_19920101 < Date_19921231.
Parameter future : NOW <= INDEFINITE_FUTURE.

Theorem  problem251aTrue : Problem251aTrue.
intro.
assumption.
Qed.

Require Import Psatz.

Theorem  problem252aTrue : Problem252aTrue.
specialize y1993before1996 as H.
specialize y1992before1993 as H4.
specialize y1993 as H2.
specialize y1992 as H3.
specialize future as H5.
unfold Problem252aTrue.
cbv.
intros.
exists Date_19930101.
exists Date_19930101.
split.
reflexivity.
split.
lia.
split.
lia.
apply H1.
split.
lia.
split.
lia.
lia.
Qed.

Theorem  problem255aTrue : Problem255aTrue.
specialize future as F.
specialize y1993before1996 as H.
specialize y1992 as H2.
specialize y1992before1993 as H4.
specialize y1993 as H3.
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



Parameter y1992before1993March : Date_19921231 <  Date_19930301.
Parameter y1993March : Date_19930301 < Date_19930331.

Parameter foundNotExisit_K : forall x o t0 t1, found_V2 x o t0 t1 -> forall t' t1', t' < t0
-> exist_V x t' t1' -> False.



Theorem  problem258aFalse : Problem258aFalse.
cbv.
intros t0 p0.
intros t1 p1.
intros P1 P2.
specialize y1992before1993March as H.
specialize y1992 as Q.
specialize y1993March as M.
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
firstorder.
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

Transparent PN2object.
Theorem  problem267atrue : Problem267aTrue.
cbv.
intros.
destruct H2 as [a [b [H3]]].
split.
lia.
firstorder.
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


Parameter writeUnique : forall (x y : object), UniqueEvent (write_V2 x y).

Theorem  problem278atrue : Problem278aFalse.
cbv.
intros a b c e.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueEvent in A.
specialize (A _ _ P1 H) as B.
specialize y1991before1992 as C.
lia.
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
(* Deep reason for why it won't work is that "taxi" is existentially quantified, and so, not the same event (see disc. about repeatability)*)
(* And also, the syntax is anyway not the same in P and H. *)
Abort All.

Parameter MarchIn93 : (Date_19930101 < Date_19930301) /\  Date_19930331  < Date_19931231.

Opaque PN2object.
Theorem  problem312atrue : Problem312aTrue.
specialize y1993March as M.
specialize MarchIn93 as [M1 M2].
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
