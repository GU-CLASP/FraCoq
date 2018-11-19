
Load FraCoq2.

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


