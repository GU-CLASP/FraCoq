Load Formulas.

Require Import Coq.Program.Tactics.

Theorem FraCaS326: Problem326aTrue. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct in_1993_Adv as [in93 [in93cov in93verid]].
(* FIXME: handling tense at the proposition level is difficult. Additionally, the Q has an anaphoric ellpsis (we mean finish building, not (say) finish destroying.) *)
Abort All.

Theorem FraCaS327: Problem327aTrue. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct in_1993_Adv as [in93].
(* Progressive prevents getting to the conclusion. *)
(* UNK *)
Abort All.

Parameter weakenWinFrom : forall a b c t0 t1, win_V2from a b c t0 t1 -> win_V2 b c t0 t1.

Section Temps.
Variable y1993before1996 : Date_19931231 < Date_19960101.
Variable y1992before1993 : Date_19921231 < Date_19930101.
Variable y1991before1993 : Date_19911231 < Date_19930101.
Variable y1991before1992 : Date_19911231 < Date_19920101.
Variable y1993 : Date_19930101 < Date_19931231.
Variable y1992 : Date_19920101 < Date_19921231.
Variable y1991 : Date_19910101 < Date_19920101.
Variable future : NOW <= INDEFINITE_FUTURE.
Variable y1992before1993March : Date_19921231 <  Date_19930301.
Variable y1993March : Date_19930301 < Date_19930331.
Variable MarchIn93a : Date_19930101 < Date_19930301.
Variable MarchIn93b : Date_19930331  < Date_19931231.
Variable hoursPositive : OneHour > 0.
Variable daysPositive : ONEDAY > 0.
Variable monthPositive : OneMonth > 0.
Parameter past : forall t, INDEFINITE_PAST <= t.

Variable isPast : INDEFINITE_PAST < NOW.


Theorem FraCaS328: Problem328aTrue. cbv.
destruct from_Prep as [from fromVerid fromCov].
(* destruct in_1993_Adv as [in93 [in93Verid in93Covariant]]. *)
destruct itel_PN as [itel corpN itelIsCorp].
destruct apcom_PN as [apcom corpN' apcomIsCorp].
intros theContract isContract.
intro P.
destruct_conjs.
repeat eexists.
Focus 5.
eapply weakenWinFrom.
exact H3.
exact H0.
assumption.
assumption.
assumption.
Qed.


Theorem FraCaS329: Problem329aTrue. cbv.
destruct from_Prep as [from fromVerid fromCov].
(* destruct in_1993_Adv as [in93 [in93Verid in93Covariant]]. *)
destruct itel_PN as [itel corpN itelIsCorp].
destruct apcom_PN as [apcom corpN' apcomIsCorp].
intros theContract isContract.
intro P.
destruct_conjs.
repeat eexists.
Focus 5.
eapply weakenWinFrom.
exact H3.
exact H0.
assumption.
assumption.
assumption.
Qed.
(* Error: no support for progressive *)


Variable y1988before1992 : Date_19880101 < Date_19920101.
Variable y1990 : Date_19900101 < Date_19901231.
Variable y1990_1991 : Date_19901231 < Date_19910101.
Variable y1988_1990 : Date_19880101 <= Date_19900101.
Require Import Psatz.

Parameter ownStative   : forall x y, StativeInclusion (have_V2 x y).

Transparent PN2object.

Theorem FraCaS330: Problem330aTrue. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct apcom_PN as [apcom corpN' apcomIsCorp].
intros.
destruct_conjs.

repeat eexists.
reflexivity.
reflexivity.
lia.
specialize ownStative with (x := apcom) (y := x) as A.
cbv in A.
eapply A.
exact H.
lia.
lia.
Qed.

Theorem FraCaS331: Problem331aTrue. cbv.
firstorder.
Qed.

Theorem FraCaS332: Problem332aTrue. cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
 intros. firstorder.
Qed.

Theorem FraCaS333: Problem333aTrue. cbv.
(* FIXME: no notion of group*)
Abort All.

End Temps.

