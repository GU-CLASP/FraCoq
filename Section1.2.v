Load FraCoq2.

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

Variable getInK : forall newsPaper result x, get_V2in newsPaper result x -> get_V2 result x.
(* Analysis: In "get published", published should not be intersectional. *)

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
Qed.


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
firstorder.
exists x.
firstorder.
generalize H1.
apply le_mono_right.
firstorder.
Qed. (* FIXME *)
