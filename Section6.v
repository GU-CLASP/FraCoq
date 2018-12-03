Load FraCoq2.

Require Import Psatz.

Parameter ineqAdd : forall {a b c d}, (a <= b) -> (c <= d) -> (a + c <= b + d).

Parameter le_trans' : forall {x y z:Z}, x <= y -> y <= z -> x <= z.

Opaque Z.gt.
Opaque Z.lt.
Opaque Z.add.
Opaque Z.sub.
Opaque Z.ge.
Opaque Z.le.



Theorem T220a: Problem220aTrue. cbv.
destruct fast_A as [fast].
intros itelxz isCompy1 pc6083 isCompy2.
split.
lia.
assumption.
Qed.


Theorem T221a: Problem221aTrue. cbv.
destruct fast_A.
Abort All.


Theorem T221a: Problem221aFalse. cbv.
destruct fast_A.
intros.
Abort All.


Theorem T222a: Problem222aTrue. cbv.
destruct fast_A.
Abort All.

Theorem T222a: Problem222aFalse. cbv.
destruct fast_A.
Abort All.


Theorem T223a: Problem223aFalse.
assert (H' := fast_and_slow_opposite_K).
cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intro P.
destruct fast_A  as [fastness fastThres].
destruct slow_A  as [slowness slowThres].
destruct (H' computer_N pc6083) as [neg disj].
destruct (H' computer_N itelxz) as [neg' disj'].
destruct P.
lia.
Qed.


Theorem T224a: Problem224aTrue. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
intros.
split.
lia.
assumption.
Qed.


Theorem T225a: Problem225aTrue. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
firstorder.
Abort All.



Theorem T225a: Problem225aFalse. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
firstorder.
Abort All.


Theorem T226a: Problem226aTrue. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
split.
lia.
assumption.
Qed. (* Fracas wrong *)



Theorem T227a: Problem227aFalse. cbv.
assert (H' := fast_and_slow_opposite_K).
intros itel_xz isCompy1 pc6083 isCompy2.
intros.
apply slow_and_fast_disjoint_K with (cn := computer_N) (o := pc6083).
destruct fast_A as [fast].
destruct slow_A as [slow].
destruct (H' computer_N pc6083) as [neg disj].
destruct (H' computer_N itel_xz) as [neg' disj'].
intros.
lia.
Qed.


Theorem T228a: Problem228aFalse. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
apply slow_and_fast_disjoint_K with (cn := computer_N) (o := pc6083).
destruct fast_A as [fast].
destruct slow_A as [slow].
(*firstorder SLoooow *)
Abort All.


Theorem T228a: Problem228aTrue. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
(*firstorder SLoooow *)
Abort All.


Theorem T229a: Problem229aFalse. cbv.
intros itelxz isCompy1 pc6082 isCompy2.
assert (H' := fast_and_slow_opposite_K).
cbv.
destruct fast_A as [fastness fastThres].
destruct slow_A as [slowness slowThres].
destruct (H' computer_N pc6082) as [neg disj].
destruct (H' computer_N itelxz) as [neg' disj'].
intros P1 H.
(* This should work (Coq needs some convincing.)
lia.
Qed.
*)
Abort All.

Theorem T230a: Problem230aTrue. cbv.
intros n [P1a P1b].
firstorder.
Qed.

Theorem T231a: Problem231aTrue. cbv.
intros n [P1a P1b].
firstorder.
Abort All.

Theorem T232a: Problem232aTrue. cbv.
intros n [P1a [[orders P1c] [P1d P1e]]].
exists orders.
split.
firstorder.
split.
firstorder.
lia.
Qed.


Theorem T233a: Problem233aTrue. cbv.
intros n P1.
destruct P1 as [orders P1].
firstorder.
Qed.

Theorem T234a: Problem234aTrue. cbv.
firstorder.
Abort All.

Theorem T235a: Problem235aTrue. cbv.
intros n [P1a [[orders P1c] [P1d P1e]]].
exists orders.
split.
firstorder.
split.
firstorder.
lia.
Qed.

Theorem T236a: Problem236bTrue. cbv.
intros contract isContract P1.
firstorder.
Qed.

Theorem T237a: Problem237bTrue. cbv.
intros contract isContract [P1a [order P1b]].
exists order.
split.
firstorder.
split.
firstorder.
lia.
Qed.

Theorem T238a: Problem238aTrue. cbv.
intros n [P1a [[order [isOrder [won P1]]] [order' [isOrder' [won' P2]]]]].
exists order.
split.
firstorder.
split.
firstorder.
lia.
Qed.

Theorem T239a: Problem239aTrue. cbv.
intros n [P1a P1b].
firstorder.
Qed.

Theorem T240a: Problem240aTrue. cbv.
intros n [P1a [order P1b]].
exists order.
split.
firstorder.
Abort All.

Theorem T241a: Problem241aTrue. cbv.
intros n [P1a [[order [isOrder [won P1]]] [order' [isOrder' [lost P2]]]]].
exists order.
split.
firstorder.
split.
firstorder.
lia.
Qed.

Theorem T246a: Problem246aTrue. cbv.
destruct fast_A as [fast] eqn:fst.
destruct slow_A as [slow] eqn:slw.
firstorder.
Qed.

Theorem T247a: Problem247aTrue. cbv.
destruct fast_A as [fast] eqn:fst.
destruct slow_A as [slow] eqn:slw.
Abort All.

Theorem T247a: Problem247aFalse. cbv.
destruct fast_A as [fast] eqn:fst.
destruct slow_A as [slow] eqn:slw.
(*firstorder. slow *)
Abort All.

Theorem T248a: Problem248aTrue. cbv.
destruct fast_A as [fast] eqn:fst.
destruct slow_A as [slow] eqn:slw.
firstorder.
Qed.

Theorem T249a: Problem249aTrue. cbv.
destruct fast_A as [fast] eqn:fst.
destruct slow_A as [slow] eqn:slw.
firstorder.
Qed.


Theorem T250a: Problem250aTrue. cbv.
intros itelxz isCompy1 itelxy isCompy1' pc6083 isCompy2.
destruct fast_A as [fast] eqn:fst.
destruct slow_A as [slow] eqn:slw.
intro P1.
destruct P1 as [L | R].
(* Left branch *)
assumption.
(* Right branch *)
Abort All.
(* P1 is read as: (The PC-6082 is faster than the ITEL-ZX) or (The
PC-6082 is faster than the ITEL-ZY) Which does not imply the
conclusion.

JP: I disagree with FraCas here! "or" can only be read as "and" for
pragmatic reasons. (that is: saying "or" in this context is usually
wasteful; the listener assumes a mistake and interprets as "and" ) *)

