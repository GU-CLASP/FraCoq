Load FraCoq2.


Theorem T002a: Problem002aTrue.
cbv. destruct great_A as [great].
intro H.
destruct H as [H1 H2].
destruct H2 as [x H2].
destruct H2 as [H2 H3].
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

