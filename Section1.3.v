
Load FraCoq2.

Theorem T033a: Problem033aTrue. cbv.
firstorder.
Abort All.

Theorem T033a: Problem033aFalse. cbv.
firstorder.
Abort All.


Theorem T034a: Problem034aTrue. cbv.
firstorder.
Abort All.

Theorem T034a: Problem034aFalse. cbv.
firstorder.
Abort All.


Theorem T035a: Problem035aTrue. cbv.
firstorder.
Abort All.

Theorem T035a: Problem035aFalse. cbv.
firstorder.
Abort All.


Theorem T036a: Problem036aTrue. cbv.
firstorder.
Abort All.

Theorem T036a: Problem036aFalse. cbv.
firstorder.
Abort All.

Theorem T037a: Problem037aTrue. cbv.
firstorder.
Abort All.

Theorem T037a: Problem037aFalse. cbv.
firstorder.
Abort All.


Theorem T038a: Problem038aFalse. cbv.
destruct on_time_Adv as [adv verid].
firstorder.
Qed.



Theorem T039a: Problem039aTrue. cbv.
destruct on_time_Adv as [adv verid].
firstorder.
Abort All.

Theorem T039a: Problem039aFalse. cbv.
destruct on_time_Adv as [adv verid].
firstorder.
Abort All.


Theorem T040a: Problem040aTrue. cbv.
destruct on_time_Adv as [adv verid].
firstorder.
generalize H0.
apply le_mono_right.
firstorder.
Abort All.

Theorem T040a: Problem040aFalse. cbv.
firstorder.
Abort All.



Theorem T041a: Problem041aTrue. cbv.
destruct major_A as [major] eqn:majorEq.
destruct national_A as [national] eqn:nationalEq.
firstorder.
generalize H0.
apply le_mono_right.
firstorder.
Abort All.

Theorem T041a: Problem041aFalse. cbv.
destruct major_A as [major] eqn:majorEq.
destruct national_A as [national] eqn:nationalEq.
firstorder.
Abort All.




Theorem T042a: Problem042aTrue. cbv.
firstorder.
Abort All.

Theorem T042a: Problem042aFalse. cbv.
firstorder.
Abort All.

Theorem T043a: Problem043aTrue. cbv.
firstorder.
Abort All.

Theorem T043a: Problem043aFalse. cbv.
firstorder.
Abort All.

Theorem T044a: Problem044aTrue. cbv.
firstorder.
generalize H.
apply le_mono_left.
firstorder.
Qed.

Theorem T045a: Problem045aTrue. cbv.
destruct leading_A as [leading].
firstorder.
Abort All.

Theorem T045a: Problem045aFalse. cbv.
destruct leading_A as [leading].
firstorder.
Abort All.

Theorem T046a: Problem046aFalse. cbv.
destruct at_home_Adv as [atHome [atHomeVerid atHomeVeridCov]].
firstorder.
Abort All.


Theorem T047a: Problem047aTrue. cbv.
destruct at_home_Adv as [atHome [atHomeVerid atHomeVeridCov]].
firstorder.
exists x.
firstorder.
Abort All.

Theorem T047a: Problem047aFalse. cbv.
destruct at_home_Adv as [atHome [atHomeVerid atHomeVeridCov]].
firstorder.
Abort All.

Theorem T048a: Problem048aTrue. cbv.
apply le_mono_left.
firstorder.
Qed.
