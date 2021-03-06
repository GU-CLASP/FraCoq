
Load Formulas.

Theorem T197a: Problem197aTrue. cbv. firstorder. Qed.

Theorem T198a: Problem198aFalse. cbv. firstorder.
destruct john_PN as [john person].
destruct former_A as [former]. firstorder. Qed.

Theorem FraCas199: Problem199aTrue. cbv. destruct successful_A as [successful].  destruct former_A as [former]. firstorder. (** FIXME: This is YES in the suite, but is says "yes for a former university student", which is not what the conclusion actually says. If we were to fix the conclusion then the example becomes trivial. **) Abort All.  (**I suggest we do not bother with this example**)


Theorem FraCas200: Problem200aTrue. cbv. firstorder.  destruct successful_A as [successful]. destruct former_A as [former]. firstorder. Abort All.  (**UNK**)

Theorem FraCas200': Problem200aFalse. cbv. firstorder.  destruct successful_A as [successful].
destruct former_A as [former]. firstorder. Abort All.  (**UNK**)


Theorem FraCas201: Problem201aTrue. cbv. firstorder.  destruct successful_A as [successful]. destruct former_A as [former]. firstorder. Abort All.  (**UNK**)

Theorem FraCas201': Problem201aFalse. cbv. firstorder.  destruct successful_A as [successful].
destruct former_A as [former]. firstorder. Abort All.  (**UNK**)

Theorem FraCas202: Problem202aTrue. cbv.  firstorder. Qed.

Theorem FraCas203: Problem203aTrue. cbv. firstorder. Qed.

Require Import Psatz.

Transparent PN2object.
Theorem FraCas204: Problem204aFalse. 
cbv. intros.
assert (H' := small_and_large_opposite_K).
destruct small_A as [smallness smallThres].
destruct large_A as [largeness largeThres].
destruct (H' animal_N MICKEY) as [neg disj].
lia. Qed.


Theorem FraCas205: Problem205aFalse. cbv. intros.
cbv. intros.
assert (H' := small_and_large_opposite_K).
destruct small_A as [smallness smallThres].
destruct large_A as [largeness largeThres].
destruct (H' animal_N DUMBO) as [neg disj].
lia. Qed.

Theorem FraCas206: Problem206aTrue. cbv. intros. destruct small_A. destruct large_A. firstorder.  Abort All. (* UNK *)

Theorem FraCas206': Problem206aFalse. cbv. intros. destruct small_A. destruct large_A. firstorder. Abort All. (* UNK *)

Theorem FraCas207: Problem207aTrue. cbv. intros. destruct small_A. destruct large_A. firstorder. Abort All. (* UNK *)

Theorem FraCas207': Problem207aFalse. cbv. intros. destruct small_A. destruct large_A. firstorder. Abort All. (* UNK *)  (**206 and 207 are correctly captured, they are marked as UNK, but the score calculation counts them as wrong**)

Transparent PN2Class.
Theorem FraCas208: Problem208aTrue.
assert (slK := small_and_large_opposite_K).
cbv.
destruct small_A as [small].
destruct large_A as [large].
intros [[P1a P1b] [P2a P2]].
destruct (slK animal_N DUMBO) as [neg disj].
lia.
Qed.

Theorem T209: Problem209aFalse.
assert (slK := small_and_large_opposite_K).
cbv.
destruct small_A as [small].
destruct large_A as [large].
intros [[P1a P1b] [P2a P2]].
destruct (slK animal_N DUMBO) as [neg disj].
destruct (slK animal_N MICKEY) as [neg' disj'].
lia.
Qed. 

Theorem FraCas210: Problem210aFalse. cbv. intros. 
apply small_and_large_disjoint_K with (cn := animal_N) (o := MICKEY).
destruct small_A.
destruct large_A.
firstorder.
cbv.
firstorder.
cbv.
firstorder.
Qed.

Theorem FraCas211: Problem211aFalse.
cbv.
intros.
apply small_and_large_disjoint_K with (cn := animal_N) (o := DUMBO).
destruct small_A as [small].
destruct large_A as [large].
cbv.
firstorder.
Qed.

Theorem FraCas212: Problem212aTrue.
cbv.
assert (slK := small_and_large_opposite_K).
destruct small_A as [small smallThreshold].
destruct large_A as [large largeThreshold].
intros [P1 [P2  [[largeM mouse] [smallD eleph]]]].
destruct (slK animal_N DUMBO) as [neg disj].
destruct (slK animal_N MICKEY) as [neg' disj'].
destruct (P1 _ mouse) as [X Y].
destruct (P2 _ eleph) as [Z W].
lia.
Qed. 

Theorem FraCas213: Problem213aTrue.
cbv.
destruct small_A as [small].
destruct large_A as [large].
intros.
firstorder.
Qed.

Theorem FraCas214: Problem214aTrue.
cbv.
intros.
destruct fat_A as [fat fatP].
firstorder.
Qed.

Theorem FraCas215: Problem215aTrue.
cbv.
intros P1 P2.
destruct competent_A as [competent].
firstorder.
(* UNK *)
Abort All.

(**Theorem FraCas216: Problem216aTrue. 
cbv.
intros P1.
destruct fat_A as [fat fatP].
destruct bill_PN as [bill].
destruct john_PN as [john].
destruct than_Prep as [than].
firstorder.
(* FIXME: syntax wrong: should be
   john is (fatter politician than bill)
 not
   (john is fatter politician) than bill
 *)
Abort All.

Theorem FraCas217: Problem217aTrue.
cbv.
(* FIXME: syntax wrong, see 216 *)
Abort All.
*)

Theorem FraCas218: Problem218aTrue. cbv.
destruct kim_PN as [kim person].
destruct clever_A.
firstorder.
Qed.
 
Theorem FraCas219: Problem219aTrue. cbv.
destruct kim_PN as [kim person].
destruct clever_A.
firstorder.
Abort All. (* UNK *)





