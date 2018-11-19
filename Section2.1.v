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
