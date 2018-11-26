Load FraCoq2.

Require Import Psatz.

Variable ineqAdd : forall {a b c d}, (a <= b) -> (c <= d) -> (a + c <= b + d).

Parameter le_trans' : forall {x y z:Z}, x <= y -> y <= z -> x <= z.

Theorem T220a: Problem220aTrue. cbv.
destruct fast_A.
firstorder.
Qed.


Theorem T221a: Problem221aTrue. cbv.
destruct fast_A.
Abort All.


Theorem T221a: Problem221aFalse. cbv.
destruct fast_A.
firstorder.
Abort All.


Theorem T222a: Problem222aTrue. cbv.
destruct fast_A.
firstorder.
Abort All.

Theorem T222a: Problem222aFalse. cbv.
destruct fast_A.
firstorder.
Abort All.

Parameter slow_and_fast_disjoint_K : forall cn o, getSubsectiveA slow_A cn o /\ getSubsectiveA fast_A cn o -> False.

Theorem T223a: Problem223aFalse. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
apply slow_and_fast_disjoint_K with (cn := computer_N) (o := pc6083).
destruct fast_A.
destruct slow_A.
firstorder.
Qed.


Theorem T224a: Problem224aTrue. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
firstorder.
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
firstorder.
Abort All.



Theorem T226a: Problem226aFalse. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
destruct fast_A as [fast].
destruct slow_A as [slow].
firstorder.
Abort All.


Theorem T227a: Problem227aFalse. cbv.
intros itelxz isCompy1 pc6083 isCompy2.
intros.
apply slow_and_fast_disjoint_K with (cn := computer_N) (o := pc6083).
destruct fast_A as [fast].
destruct slow_A as [slow].
firstorder.
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
Definition opposite_adjectives : SubsectiveA -> SubsectiveA -> Prop
  := fun a1 a2 =>
  forall cn o,  let (mSmall,threshSmall) := a1 in
                let (mLarge,threshLarge) := a2 in
               (   (mSmall cn o = - mLarge cn o)
                /\ (1 <= threshLarge + threshSmall)).

Variable fast_and_slow_opposite_K   : opposite_adjectives slow_A  fast_A.

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
split.
intro fastItelXY.
destruct P1 as [[L1 L2] | [R1 R2]].
(* Left branch *)
apply L1.
exact fastItelXY.
(* Right branch *)
apply R1.
Abort All.
(* P1 is read as: (The PC-6082 is faster than the ITEL-ZX) or (The
PC-6082 is faster than the ITEL-ZY) Which does not imply the
conclusion.

JP: I disagree with FraCas here! "or" can only be read as "and" for
pragmatic reasons. (that is: saying "or" in this context is usually
wasteful; the listener assumes a mistake and interprets as "and" ) *)

