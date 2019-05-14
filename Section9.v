Load Formulas.

Parameter know_veridical_K : forall (x:object) (p:S), know_VS p x -> p.

Theorem FraCaS334: Problem334aTrue.
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corpN].
destruct in_1992_Adv as [in92].
intros theContract isContract.
apply know_veridical_K.
Qed.

Theorem FraCaS335: Problem335aTrue.
cbv.
firstorder.
Abort All. (* UNK *)
Theorem FraCaS335: Problem335aFalse.
cbv.
firstorder.
Abort All. (* UNK *)


Parameter manageTo_veridical_K : forall (x:object) (p:VP), manage_VV p x -> p x.

Theorem FraCaS336: Problem336aTrue.
cbv.
destruct in_1992_Adv as [in92 [in92Verid in92Covariant]].
destruct itel_PN as [itel corpN]. 
intros theContract isContract.
apply in92Covariant.
intro x.
apply manageTo_veridical_K.
Qed.

Theorem FraCaS337: Problem337aTrue.
cbv.
destruct itel_PN as [itel corpN]. 
firstorder.
Abort all. (*UNK*)

Theorem FraCaS338: Problem338aTrue.
cbv.
destruct itel_PN as [itel corpN].
firstorder.
Qed.

Theorem FraCaS339: Problem339aFalse.
cbv.
destruct itel_PN as [itel corpN].
destruct false_A as [false].
firstorder.
Qed.

Variable see_veridical_K : forall (dobject subject :object) (p:VP), see_V2V dobject p subject -> p dobject. 

Theorem FraCaS340: Problem340aTrue.
 cbv.
 destruct jones_PN as [jones person].
 destruct smith_PN as [smith person'].
 firstorder.
Abort all. (*UNK*)


Theorem FraCaS341: Problem341aTrue.
 cbv.
 destruct jones_PN as [jones person].
 destruct smith_PN as [smith person'].
 firstorder.
Abort all. (*UNK*)


Theorem FraCaS342: Problem342aTrue.
cbv.
intros theContract isContract.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corpN].
apply see_veridical_K.
Qed.

Theorem FraCaS343: Problem343aTrue.
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corporation].
firstorder.
rewrite <- H2.
firstorder.
Qed.

Theorem FraCaS344: Problem344aTrue.
cbv.
destruct helen_PN as [helen person].
firstorder.
Qed.

Theorem FraCaS345: Problem345aTrue.
cbv.
destruct smith_PN as [smith person'].
destruct jones_PN as [jones person].
firstorder.
Qed.


Theorem FraCaS346: Problem346aTrue.
cbv.
intros clause isClause.
intros theContract isContract.
firstorder.

(* FIXME: ellipsis *)
Abort All.
