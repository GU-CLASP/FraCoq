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

