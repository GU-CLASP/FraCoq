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

Theorem T084a: Problem084aTrue. cbv.
firstorder.
Abort All. (* FIXME: multiple readings? *)


Theorem T085a: Problem085aFalse. cbv.
firstorder.
Qed.

Theorem T086a: Problem086aFalse. cbv.
intros contract isContract.
firstorder.
Qed.

Theorem T087a: Problem087aTrue. cbv.
intros.
firstorder.
Abort All.
(*
FIXME
Every representative and client in this reading means
"Every representative and every client"
but it seems that the parse tree says something else. Tricky.
Use multiple readings for AND?
*)

Theorem T088a: Problem088aTrue. cbv.
intros.
firstorder.
Abort All.
(*
FIXME
Every representative and client in this reading means
"Every representative and every client"
but it seems that the parse tree says something else. Tricky.
Use multiple readings for AND?
*)

Theorem T088a': Problem088aFalse. cbv.
intros.
firstorder.
Abort All.
(*
FIXME
Every representative and client in this reading means
"Every representative and every client"
but it seems that the parse tree says something else. Tricky.
Use multiple readings for AND?
*)

Theorem T089a: Problem089aTrue. cbv.
firstorder.
Qed.

(* Fixme Interpretation of "the" as coming from the environment is incorrect for every example in the section
Multiple readings?
*)



Theorem T097a: Problem097aTrue. cbv.
firstorder.
Qed.



Theorem T099a: Problem099aTrue. cbv.
intros theSystem isSystem theDemo isDemo theClient.
Abort All.
(* FIXME: definite plural *)


Theorem T100a: Problem100aTrue. cbv.
(* FIXME: plural is existential whereas it should be universal. *)
Abort All.


Theorem T105a: Problem105aFalse. cbv.
firstorder.
Qed.

Theorem T106a: Problem106aFalse. cbv.
firstorder.
Qed.

Theorem T107a: Problem107aTrue. cbv.
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
(* FIXME: incorrect collective reading. *)
Abort All.

Theorem T112a: Problem112aTrue. cbv.
firstorder.
Qed.

Theorem T113a: Problem113aTrue. cbv.
intros [contract [isContract [[H1 H2] HC]]].
split;
exists contract;
split;
try assumption;
split;
try assumption;
generalize HC;
apply le_mono_right;
firstorder.
Qed.

