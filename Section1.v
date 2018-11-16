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
firstorder. exists x. firstorder.
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

