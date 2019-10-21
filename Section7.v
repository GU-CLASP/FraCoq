Load Formulas.


Parameter y1993before1996 : Year_1993 <  Year_1996.
Parameter y1992before1996 : Year_1992 <  Year_1996.
Parameter y1992before1993 : Year_1992 <  Year_1993.

(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)



Theorem  problem252aTrue : Problem252aTrue.
cbv.
intros [P1 P2].
apply P1.
apply y1992before1993.
rewrite <- P2.
apply y1993before1996.
Qed.


Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
firstorder.
Qed.
