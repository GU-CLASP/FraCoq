Load FraCoq2.

Theorem T065a: Problem065aTrue. cbv.
firstorder.
Abort All.

Theorem T065a: Problem065aFalse. cbv.
firstorder.
Abort All.

Theorem T066a: Problem066aTrue. cbv.
firstorder.
Qed.

Theorem T067a: Problem067aTrue. cbv.
firstorder.
Qed.

Theorem T068a: Problem068aTrue. cbv.
firstorder.
Qed.

Theorem T069a: Problem069aTrue. cbv.
destruct major_A as [major] eqn:majorEq.
intro right.
intro isRight.
intro resident.
intro isResidentIn.
Abort All. (* Problem is broken *)

Theorem T070a: Problem070aFalse. cbv.
destruct on_time_Adv as [onTime].
destruct scandinavian_A as [scandinavian].
firstorder.
Qed. (* Note: I don't understand how this could be proven in FraCoq 1 without scandinavian_A subsective *)

Theorem T071a: Problem071aTrue. cbv.
destruct on_time_Adv as [onTime].
firstorder.
Abort All.

Theorem T071a: Problem071aFalse. cbv.
destruct on_time_Adv as [onTime].
firstorder.
Abort All.

Theorem T072a: Problem072aTrue. cbv.
firstorder.
generalize H0.
apply le_mono_right.
firstorder.
Abort All.

Theorem T072a: Problem072aFalse. cbv.
firstorder.
Abort All.

Theorem T073a: Problem073aTrue. cbv.
destruct major_A as [major] eqn:majorEq.
destruct national_A as [national].
firstorder.
generalize H0.
apply le_mono_right.
firstorder.
Abort All.

Theorem T073a: Problem073aFalse. cbv.
firstorder.
Abort All.

Theorem T074a: Problem074aTrue. cbv.
firstorder.
Abort All.


Theorem T074a: Problem074aFalse. cbv.
firstorder.
Abort All.

Theorem T075a: Problem075aTrue. cbv.
firstorder.
generalize H.
apply le_mono_right.
firstorder.
Abort All.

Theorem T075a: Problem075aFalse. cbv.
firstorder.
Abort All.

Theorem T076a: Problem076aTrue. cbv.
firstorder.
generalize H.
apply le_mono_left.
firstorder.
Qed.


Theorem T079a: Problem079aTrue. cbv.
destruct at_home_Adv as [atHome atHomeVerid].
firstorder.
exists x.
firstorder.
Abort All.

Theorem T079a: Problem079aFalse. cbv.
firstorder.
Abort All.


Theorem T080a: Problem080aTrue. cbv.
destruct at_home_Adv as [atHome atHomeVerid].
firstorder.
generalize H.
apply le_mono_left.
firstorder.
Qed.

