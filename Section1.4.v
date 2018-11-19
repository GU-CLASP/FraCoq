Load FraCoq2.

Theorem T049a: Problem049aTrue. cbv.
firstorder.
Qed.

Theorem T050a: Problem050aTrue. cbv.
firstorder.
Abort All.
Theorem T050a: Problem050aFalse. cbv.
firstorder.
Abort All.

Theorem T052a: Problem052aTrue. cbv.
firstorder.
Abort All.
Theorem T052a: Problem052aFalse. cbv.
firstorder.
Abort All.

Theorem T053a: Problem053aTrue. cbv.
firstorder.
Abort All.
Theorem T053a: Problem053aFalse. cbv.
firstorder.
Abort All.

Theorem T054a: Problem054aTrue. cbv.
firstorder.
Abort All.
Theorem T054a: Problem054aFalse. cbv.
firstorder.
Abort All.

Theorem T055a: Problem049aTrue. cbv.
firstorder.
Qed.

Theorem T056a: Problem056aTrue. cbv.
firstorder.
generalize H0.
apply le_mono_right.
firstorder.
Qed. (* See note in the xml *)

Theorem T057a: Problem057aTrue. cbv.
destruct major_A as [major] eqn:majorEq.
destruct national_A as [national] eqn:nationalEq.
firstorder.
generalize H0.
apply le_mono_right.
firstorder.
Qed.


Theorem T058a: Problem058aTrue. cbv.
firstorder.
generalize H.
Abort All.

Theorem T058a: Problem058aFalse. cbv.
firstorder.
Abort All.

Theorem T059a: Problem059aTrue. cbv.
firstorder.
generalize H.
apply le_mono_right.
firstorder.
Qed.

Theorem T060a: Problem060aTrue. cbv.
firstorder.
generalize H.
apply le_mono_left.
firstorder.
Abort All.

Theorem T060a: Problem060aFalse. cbv.
firstorder.
Abort All.

Theorem T063a: Problem063aTrue. cbv.
firstorder.
exists x.
firstorder.
generalize H1.
apply le_mono_right.
firstorder.
Qed.


Theorem T064a: Problem064aTrue. cbv.
apply le_mono_left.
firstorder.
Abort All.

Theorem T064a: Problem064aFalse. cbv.
firstorder.
Abort All.


