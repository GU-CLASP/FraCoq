
Load Formulas.


Parameter y1993before1996 : Year_1993 <  Year_1996.
Parameter y1992before1996 : Year_1992 <  Year_1996.
Parameter y1992before1993 : Year_1992 <  Year_1993.

(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Theorem  problem252aTrue : Problem252aTrue.
cbv.
intros t tPast.
intros [P1 P2].
apply P1.
apply y1992before1993.
Qed.

Theorem  problem255aTrue : Problem255aTrue.
cbv.
intros t tPast.
intros [P1 P2].
apply P1.
apply y1992before1993.
Qed.

Require Import Psatz.
Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
intros t1 t1Past t2 t2Past t3 t3Past [p1Order [p1a [p1b [p2Order [p2a p2b]]]]].
split.
lia.
firstorder.
Qed.


Transparent PN2object.
Theorem  problem262atrue : Problem262aTrue.
cbv.
lia.
Qed.
