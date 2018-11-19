
Load FraCoq2.


Theorem T097a: Problem097aTrue. cbv.
firstorder.
Qed.
Variable Impressed_cov_K : forall (impressor:object) (p q:CN), (forall x, p x -> q x) -> forall x, impressed_by_A2 impressor p x -> impressed_by_A2 impressor q x.

Variable client_people_K : forall x, client_N x -> person_N x.


Theorem T099a: Problem099aTrue. cbv.
intros theSystem isSystem theDemo isDemo theClient.
Abort All.
(* FIXME: definite plural *)


Theorem T100a: Problem100aTrue. cbv.
(* FIXME: plural is existential whereas it should be universal. *)
Abort All.

