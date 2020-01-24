
Load Formulas.

Require Import Coq.Program.Tactics.

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
(* FIXME: In H, the negation should distribute over 'and' ("narrow scoping") *)

Require Import Psatz.

Theorem T085a: Problem085aFalse.
cbv.
intros contract isContract.
intros.
destruct_conjs.

(* TODO Temporal Error: bad interaction between unicity of events and
group readings of quantifiers; indeed; we cannt do:

specialize signUnique with (x := contract) (y := ???) as A.

because ??? is H2 in one case and H8 in another case. To sum up we
have existential quantification, whereas we should have another kind
of quantification.

*) 
Abort All.

Theorem T086a: Problem086aFalse. cbv.
intros contract isContract.
(* Temporal Error: bad interaction between unicity of events and group readings of quantifiers *) 
Abort All.

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
intros theSystem isSystem.
intros theDemo isDemo.
intros [P1 P2].
lapply (P1 SMITH).
intros.
firstorder.
exists x1.
firstorder.
exact SMITH_PERSON.
intuition.
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

Theorem T104a: Problem104aTrue. cbv.
firstorder.
Abort All.

Theorem T104a: Problem104aFalse. cbv.
firstorder.
Abort All.

Parameter attendUnique : forall (x y : object), UniqueActivity (attend_V2 x y).

Theorem T105a: Problem105aFalse. cbv.
intros.
(* Temporal Error: negation is not handled correctly *)
Abort All.

Theorem T106a: Problem106aFalse. cbv.
firstorder.
(* Temporal Error: negation is not handled correctly *)
Abort All.

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
(* FIXME "Some" plural ==> card > 1 --- however, this makes many proofs much harder. Try this maybe after we have better automation? *)

Theorem T110a: Problem110aTrue. cbv.
firstorder.
Qed.

Theorem T111a: Problem111aTrue. cbv.
firstorder.
(*  incorrect collective reading. *)
Abort All.

Theorem T112a: Problem112aTrue. cbv.
intros.
destruct_conjs.
repeat eexists.
Focus 3.
exact H9.
assumption.
assumption.
assumption.
Focus 2.
(* Temporal Error: bad interaction between unicity of events and group readings of quantifiers *) 
Abort All.

Theorem T113a: Problem113aTrue. cbv.
(* Temporal Error: bad interaction between unicity of events and group readings of quantifiers *) 
Abort All.
