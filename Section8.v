Load Formulas.

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

Parameter weakenWinFrom : forall a b c, win_V2from a b c -> win_V2 b c.
Theorem FraCaS328: Problem328aTrue. cbv.
destruct from_Prep as [from fromVerid fromCov].
destruct in_1993_Adv as [in93 [in93Verid in93Covariant]].
destruct itel_PN as [itel corpN itelIsCorp].
destruct apcom_PN as [apcom corpN' apcomIsCorp].
intros theContract isContract.
intro P.
exists theContract.
split.
exact isContract.
generalize P.
apply in93Covariant.
intro contract.
apply weakenWinFrom.
Qed.

Theorem FraCaS329: Problem329aTrue. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct in_1993_Adv as [in93].
destruct apcom_PN as [apcom corpN' apcomIsCorp].
destruct from_Prep as [from fromVerid fromCov].
(* Progressive prevents getting to the conclusion. *)
(* UNK *)
Abort All.


Variable year90_included_in_88_to_92_K : forall (p:object -> Prop) (x:object), from_1988_to_1992_Adv p x -> (let (a, _) := in_1990_Adv in a) p x.

Theorem FraCaS330: Problem330aTrue. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct apcom_PN as [apcom corpN' apcomIsCorp].
apply year90_included_in_88_to_92_K.
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
