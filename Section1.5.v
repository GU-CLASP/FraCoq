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



