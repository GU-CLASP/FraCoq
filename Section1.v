
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
exists (THE
           (really_AdA
              (fun (x1 : object -> Prop) (x : object) => ambitious_A x1 x) tenor_N)).
firstorder.
apply THE_sat.
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

Theorem T008a: Problem008aTrue.
cbv.
firstorder.
Qed.

(* TODO MANYQ *)
