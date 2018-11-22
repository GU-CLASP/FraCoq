Load FraCoq2.


Require Import Omega.

Theorem T081a: Problem081aTrue. cbv.
firstorder.
Qed.

Theorem T082a: Problem082aTrue. cbv.
firstorder.
Qed.

Theorem T083a: Problem083aTrue. cbv.
firstorder.
Abort All.

Theorem T083a: Problem083aFalse. cbv.
firstorder.
Abort All.

Transparent PN2object.
Theorem T084a: Problem084aTrue. cbv.
intros contract isContract.
destruct jones_PN as [jones] .
destruct smith_PN as [smith].
destruct anderson_PN as [andersson].
intros.
elim H.
intro.
destruct H0.
Abort All.
(* FIXME: This example needs narrow scoping *)


Theorem T085a: Problem085aFalse.
cbv.
firstorder.
Qed.

Theorem T086a: Problem086aFalse. cbv.
intros contract isContract.
firstorder.
Qed.

Theorem T087a: Problem087aTrue. cbv.
firstorder.
Qed. 

Theorem T088a: Problem088aTrue. cbv.
intros.
firstorder.
Qed. 

Theorem T089a: Problem089aTrue. cbv.
firstorder.
Qed.

Theorem T090a: Problem090aTrue. cbv.
firstorder.
Qed.

Theorem T091a: Problem091aTrue. cbv.
firstorder.
Qed.

Theorem T092a: Problem092aTrue. cbv.
firstorder.
Qed.

Theorem T093a: Problem093aTrue. cbv.
intros theMeeting isMeeting.
intros P. 
firstorder.
Qed.

Theorem T094a: Problem094aFalse. cbv. firstorder. Abort All.
Theorem T094a: Problem094aTrue. cbv. firstorder. Qed.

Theorem T095a: Problem095aTrue. cbv. firstorder. Qed.

Theorem T096a: Problem096aTrue. cbv. firstorder. Qed.

Theorem T097a: Problem097aTrue. cbv.
intros theFailure isFailure P1.
firstorder.
Qed.

Theorem T098a: Problem098aTrue. cbv. firstorder. Abort All.
Theorem T098a: Problem098aFalse. cbv. firstorder. Abort All.

Transparent PN2object.
Transparent PN2Class.
Theorem T099a: Problem099aTrue. cbv.
intros theSystem isSystem theDemo isDemo.
intros [P1 P2].
lapply (P1 SMITH).
intros [thePerf [H1 [H2 H3]]].
exists thePerf.
split.
exact H1.
split.
exact SMITH_PERSON.
assumption.
firstorder.
Qed.

Theorem T100a: Problem100aTrue. cbv.
firstorder.
apply most_card_mono1.
firstorder.
Qed.

Variable likely_weakening_K : forall (p:CN) (x:object), p x -> apSubsectiveA likely_A p x.

Theorem T101a: Problem101aTrue. cbv.
firstorder.
apply likely_weakening_K.
firstorder.
exact SMITH_PERSON.
Qed.

Theorem T102a: Problem102aTrue. cbv. firstorder.
Abort All.
Theorem T102a: Problem102aFalse. cbv. firstorder.
Abort All.

Theorem T103a: Problem103aTrue. cbv. firstorder.
Qed. 

Theorem T104a: Problem104aTrue. cbv. firstorder.
Qed.
(* We do not handle counting in this case *)

Theorem T105a: Problem105aFalse. cbv.
firstorder.
Qed.

Theorem T106a: Problem106aFalse. cbv.
firstorder.
Qed.

Theorem T107a: Problem107aTrue. cbv.
intros theMeeting isMeeting.
intro P.
firstorder.
Qed.

Theorem T108a: Problem108aTrue. cbv.
firstorder.
Qed.

Theorem T109a: Problem109aFalse. cbv.
Abort All.
(* FIXME "Some" plural ==> card > 1*)

Theorem T110a: Problem110aTrue. cbv.
firstorder.
Qed.

Theorem T111a: Problem111aTrue. cbv.
firstorder.
(*  incorrect collective reading. *)
Abort All.

Theorem T112a: Problem112aTrue. cbv.
firstorder.
Qed.

Theorem T113a: Problem113aTrue. cbv.
firstorder.
Qed.
