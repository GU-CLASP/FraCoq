Load FraCoq2.

Theorem T001a: Problem001aTrue. cbv. firstorder. Qed.

Theorem T002a: Problem002aTrue.
cbv. destruct great_A as [great].
intro H.
destruct H as [H1 [x [H2 H3]]].
exists x.
split.
split.
exact H2.
assert (H' := H1 x H2).
generalize H'.
apply wantCovariant_K.
intro H4.
exists x.
split.
exact H4.
split.
split.
Qed.

Theorem T003a: Problem003aTrue.
cbv.
destruct great_A as [great].
firstorder.
Qed.

Theorem T004a: Problem004aTrue.
cbv.
firstorder.
Qed.

Theorem T005a: Problem005aTrue.
cbv.
firstorder.
Qed.

Theorem T006a: Problem006aFalse.
cbv.
destruct great_A as [great].
firstorder.
Qed.

Theorem T007a: Problem007aTrue.
cbv.
firstorder.
Qed.


Theorem T008a: Problem008aTrue. cbv. firstorder. Qed.
Theorem T009a: Problem009aTrue. cbv. firstorder. Qed.


Theorem T010a: Problem010aTrue. cbv.
destruct great_A as [great]. firstorder.
Qed.


Theorem T011a: Problem011aTrue. cbv.
destruct great_A as [great].
 firstorder. Abort All. (* FIXME FEWQ *)
 
Theorem T013a: Problem013aTrue. cbv.
cbv.
destruct leading_A as [leading].
destruct indispensable_A as [indispensable].
destruct excellent_A as [excellent].
firstorder. exists x0. firstorder. exists x1. firstorder.


(* FIXME: we're missing indispensable (excellent x) => indispensable x.
For this, we need to interpret plural as universal.
*)


Theorem T014a: Problem014aFalse. cbv.
destruct leading_A as [leading].
intros.
destruct H.
firstorder.
 Abort All.
 
(* FIXME: one of the ... has a syntax which is difficult to interpret *)

Theorem T015a: Problem015aTrue. cbv. firstorder. Qed.
Theorem T016a: Problem016aTrue. cbv.
firstorder.
Abort All. (* FIXME: unresolved reference in P1 *)

Theorem T017a: Problem017aTrue. cbv.
intro the_nobel_prize.
intros.
destruct H as [literature].
destruct H0 as [irishman]. 
exists irishman.
split.
firstorder.
exists the_nobel_prize.
split.
exists literature.
Abort All.

Theorem T018a: Problem018aTrue. cbv. firstorder. Qed.
Theorem T019a: Problem019aTrue. cbv. firstorder. Qed.
Theorem T020a: Problem020aTrue. cbv. firstorder. Qed.


Theorem T021a: Problem021aTrue. cbv.
destruct in_Prep as [inP inV inC].
 destruct within_Prep as [within withinVerid withinCov].
destruct europe_PN as [europe regionN].
 firstorder.
Qed.

Theorem T022a: Problem022aTrue. cbv. firstorder. Abort All.
Theorem T022a: Problem022aFalse. cbv. firstorder. Abort All.
Theorem T023a: Problem023aTrue. cbv.
destruct on_time_Adv. firstorder. Qed.
Theorem T024a: Problem024aTrue. cbv.
intros.
firstorder.
generalize H0.
apply le_mono.
firstorder.
Qed.

Theorem T025a: Problem025aTrue. cbv.
destruct major_A as [major] eqn:majorEq.
destruct national_A as [national] eqn:nationalEq.
destruct in_Prep as [inPrep inVerid inVeridCov].
intro result.
intro H.
destruct H as [isResult [somewhere [T0 isPublished]]].
intro H.
destruct H as [[H0 [delegate [isDelegate [newsPaper [H1 gotIn]]]]] H2].
split.
split.
generalize H0.
apply le_mono_right.
firstorder.
generalize H6.
apply getInK.
firstorder.
exists delegate.
firstorder.
generalize gotIn.
apply getInK.
firstorder.
Qed.

Theorem T026a: Problem026aTrue. cbv.
firstorder.
generalize H.
apply le_mono_right.
firstorder.
Abort All.


Theorem T027a: Problem027aTrue. cbv.
firstorder.
generalize H.
apply le_mono_right.
firstorder.
Qed.

Theorem T028a: Problem028aTrue. cbv.
firstorder.
generalize H.
apply le_mono_left.
firstorder.
Abort All.

Theorem T028a: Problem028aFalse. cbv.
firstorder.
Abort All.


Theorem T029a: Problem029aTrue. cbv.
firstorder. destruct leading_A as [leading].
exists x.
firstorder.
exists x0. 
firstorder.
generalize H1.
apply usedToBeCov_K.
firstorder. 
generalize H2.
apply usedToBeCov_K.
firstorder. 
Qed.



Theorem T030a: Problem030aTrue. cbv.
intros. destruct at_home_Adv. firstorder.
exists x0.
split.
assumption.
exists x1. firstorder. apply H3.
Abort All.

Theorem T030a': Problem030aFalse. cbv.
destruct at_home_Adv.
firstorder.
Abort All.

Theorem T031a: Problem031aTrue. cbv.
destruct at_home_Adv as [atHome atHomeVerid].
destruct atHomeVerid as [atHomeVerid atHomeVeridCov].
firstorder.
exists x.
firstorder.
generalize H1. apply le_mono_right. firstorder.
Qed.


Theorem T032a: Problem032aTrue. cbv.
destruct at_home_Adv as [atHome verid].
firstorder.
generalize H.
apply le_mono_left.
intro commiss.
firstorder.
Abort All.

Theorem T032a: Problem032aFalse. cbv.
destruct at_home_Adv as [atHome verid].
firstorder.
Abort All.

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
