Load Formulas.


(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Parameter itIsTheCaseThatIdiom : forall p x, case_N x -> that_Subj p (IMPERSONAL = x) = p.

(* If the speaker asserts that x knows p, then p holds from the speaker's perspective.*)
Parameter know_weakening : forall p x t0 t1, know_VS p x t0 t1 -> p.

Parameter y1993before1996 : Date_19931231 < Date_19960101.
Parameter y1992before1993 : Date_19921231 < Date_19930101.
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
destruct H1.
apply H1.
split.
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
intros t1 p1.
intros t2 p2.
apply P1.
split.
split.
lia.
split.
lia.
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
specialize y1992before1993March as H.
specialize y1992 as Q.
specialize y1993March as M.
assert (Date_19920101 < Date_19930301).
lia.
intros P1 P2.
eapply foundNotExisit_K.
apply P1.
split.
split.
reflexivity.
Focus 2.
reflexivity.
split.
lia.
reflexivity.
Focus 2.
apply P2.
split.
split.
reflexivity.
split.
Focus 3.
reflexivity.
lia.
reflexivity.
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


(*Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
intros t1 t1Past t2 t2Past t3 t3Past.
intros t4 p4.
intros t5 p5.
intros t6 p6.

intros [p1Order [p1a [p1b [p2Order [p2a p2b]]]]].
split.
Focus 2.
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
*)

Theorem  problem269atrue : Problem269aTrue.
cbv.
intros t1 p1 t2 p2 t3 p3 t4 p4 [P1 P2].
split.
Abort All.

Theorem  problem270atrue : Problem270aTrue.
cbv.
intros.
destruct H4 as [A [B [C [D E]]]].
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
 := fun p => forall t0 t1 t0' t1', p t0 t1 -> p t0' t1' -> t0 = t1'.


Parameter writeUnique : forall (x y : object), UniqueEvent (write_V2 x y).

Theorem  problem278atrue : Problem278aFalse.
cbv.
intros t1 p1 t2 p2.
intros novel isSmithsNovel P1 H.
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueEvent in A.
specialize (A _ _ _ _ P1 H) as B.
specialize y1991before1993 as C.
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


Theorem  problem312atrue : Problem312aTrue.
cbv.
intros [P1 P2].
apply P1.
split.
Qed.

Theorem  problem313atrue : Problem313aFalse.
cbv.
intros [P1 P2] [report [isReport Q]].
apply (P1 Year_1993).
split.
exists report.
split.
exact isReport.
exact Q.
Qed.

Opaque PN2object.
Theorem  problem320atrue : Problem320aTrue.
cbv.
intros.
destruct H5 as [t [P1 P2]].
assert (Q := know_weakening P2).
rewrite -> itIsTheCaseThatIdiom.
split.
intros [memoir [obvious R]].
apply Q with (d := NOW).
split.
Abort All.
Parameter y1992before1996 : Year_1992 <  Year_1996.
Parameter y1992before1993 : Year_1992 <  Year_1993.
Parameter y1991before1993 : Year_1991 <  Year_1992.
