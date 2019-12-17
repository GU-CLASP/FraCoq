Load Formulas.


(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Parameter itIsTheCaseThatIdiom : forall p x, case_N x -> that_Subj p (IMPERSONAL = x) = p.

(* If the speaker asserts that x knows p, then p holds from the speaker's perspective.*)
Section Temps.
Variable y1993before1996 : Date_19931231 < Date_19960101.
Variable y1992before1993 : Date_19921231 < Date_19930101.
Variable y1991before1993 : Date_19911231 < Date_19930101.
Variable y1991before1992 : Date_19911231 < Date_19920101.
Variable y1993 : Date_19930101 < Date_19931231.
Variable y1992 : Date_19920101 < Date_19921231.
Variable future : NOW <= INDEFINITE_FUTURE.
Variable y1992before1993March : Date_19921231 <  Date_19930301.
Variable y1993March : Date_19930301 < Date_19930331.
Variable MarchIn93a : Date_19930101 < Date_19930301.
Variable MarchIn93b : Date_19930331  < Date_19931231.
Variable hoursPositive : OneHour > 0.
Variable daysPositive : ONEDAY > 0.
Variable monthPositive : OneMonth > 0.
Parameter past : forall t, INDEFINITE_PAST <= t.
Variable isPast : INDEFINITE_PAST < NOW.

Definition StativeInclusion : TProp -> Prop
:= fun stative => forall t0 t1 t0' t1', stative t0 t1 -> t0 <= t0' -> t1' <= t1 -> stative t0' t1'.
Definition UniqueEvent : (TProp) -> Prop
 := fun p => forall t0 t0' , p t0 t0 -> p t0' t0' -> t0 = t0'.
Definition UniqueActivity : (TProp) -> Prop
 := fun p => forall t0 t0' t1 t1' , p t0 t1 -> p t0' t1' -> t0 = t0' /\ t1 = t1'.

Parameter inStative : forall loc x, StativeInclusion (_BE_in loc x).
Definition inParisStative := inStative (loc := (PN2object paris_PN)).
Definition inBirminghamStative := inStative (loc := BIRMINGHAM).
Parameter writeUnique : forall (x y : object), UniqueActivity (write_V2 x y).

Require Import Psatz.


Theorem  problem251aTrue : Problem251aTrue.
intro.
assumption.
Qed.

Theorem  problem252aTrue : Problem252aTrue.
unfold Problem252aTrue.
cbv.
intros [P1 P2].
eexists.
eexists.
split.
reflexivity.
split.
reflexivity.
split.
lia.
specialize inBirminghamStative with (x:= PN2object itel_PN) as A.
cbv in A.
eapply A.
apply P1.
lia.
lia.
Qed.


Theorem  problem253t : Problem253aTrue. 
cbv.
intros [P1 P2].
(* No way to link d with NOW*)
Abort All.


Theorem  problem253f : Problem253aFalse. 
cbv.
intros [P1 P2].
(* The existential means that we can't use unicity of actions *)
Abort All.

Theorem  problem254t : Problem254aTrue. 
cbv.
intros [P1 P2].
eexists.
eexists.
repeat split.
Focus 4.
exact P1.
Abort All.


Theorem  problem254f : Problem253aFalse. 
cbv.
intros [P1 P2].
(* The existential means that we can't use unicity of actions *)
Abort All.


Parameter makeALossStative : forall x, StativeInclusion (fun t0 t1 => exists loss, loss_N loss /\ make8do_V2 loss x t0 t1).

Theorem  problem255 : Problem255aTrue.
cbv.
intros [P1 P2].
eexists.
eexists.
repeat split.
reflexivity.
reflexivity.
lia.
specialize makeALossStative with (x := (PN2object itel_PN)) as A.
cbv in A.
eapply A.
exact P1.
lia.
lia.
Qed.

Theorem problem256 : Problem256aTrue.
(* TODO: not sure what this reading is *)
cbv.
exact problem255.
Qed.

Theorem  problem257aTrue : Problem257aTrue.
cbv.
exact problem255.
Qed.

Parameter foundNotExisit_K : forall x o t0 t1, found_V2 x o t0 t1 -> forall t' t1', t' < t0
-> exist_V x t' t1' -> False.



Theorem  problem258aFalse : Problem258aFalse.
cbv.
intros P1 P2.
assert (Date_19920101 < Date_19930301).
lia.
destruct P1 as [tF [tF' [cF1 [cF2 [cF3 P1]]]]].
destruct P2 as [tE [tE' [cE1 [cE2 [cE3 P2]]]]].
eapply foundNotExisit_K.
eapply P1.
Focus 2.
eapply P2.
lia.
Qed.

Theorem  problem259atrue : Problem259aTrue.
cbv.
(* intros conf isConf [P1 P2]. *)
(* Syntax wrong, using impersonal "it" in P2 *)
(* Also: We do not have time span on nouns. *)
(* Also: We need special treatment for "last n days" *)
Abort All.

Theorem  problem260aTrue : Problem260aTrue.
cbv.
intros contract isContract.
intros [P1 P2].
destruct P2 as [today [isToday P2']].
cut (NOW - ONEDAY = Date_0713).
intro H.
rewrite <- H.
apply P1.
lia.
Qed.


Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
intros t1 t1Past t2 t2Past.
intro P1.
destruct P1 as [t3 [c2 [t5 [c5 [t4 [c3 [c4 Q]]]]]]].
split.
lia.
intuition.
Qed.

Transparent PN2object.
Theorem  problem262atrue : Problem262aTrue.
cbv.
intros.
destruct H1.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
destruct H6.
split.
lia.
split.
intuition.
intuition.
Qed.

Theorem problem264a : Problem263aTrue.
cbv.
firstorder.
exists INDEFINITE_PAST.
split.
lia.
eexists.
split.
Focus 2.
exists (INDEFINITE_PAST + OneYear).
split.
Focus 2.
(* FIXME: This can actually be proven because present8attending_A has no time info *)
Abort All.

Theorem  problem264atrue : Problem264aTrue.
cbv.
intros.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
split.
lia.
split.
tauto.
tauto.
Qed.

Theorem  problem265atrue : Problem265aTrue.
cbv.
intros.
destruct H1.
destruct H2.
destruct H3.
destruct H4.

split.
lia.
split.
tauto.
tauto.
Qed.

Theorem  problem266atrue : Problem266aTrue.
cbv.
intros.
split.
lia.
split.
tauto.
tauto.
Qed.

Transparent PN2object.
Theorem  problem267atrue : Problem267aTrue.
cbv.
intros.
destruct H2 as [a [b [H3]]].
split.
lia.
intuition.
Qed.

Theorem  problem268atrue : Problem268aTrue.
cbv.
intros.
destruct H2 as [a [b [H3]]].
split.
lia.
intuition.
Qed.


Theorem  problem269atrue : Problem269aTrue.
cbv.
intros t1 p1 t2 p2 t3 p3 t4 p4 [P1 P2].
split.
Abort All.

Theorem  problem270atrue : Problem270aTrue.
cbv.
intros.
destruct H2 as [A [B [C [D E]]]].
split.
assumption.
split.
assumption.
assumption.
Qed.

Theorem  problem271atrue : Problem271aTrue.
cbv.
intros.
exists INDEFINITE_PAST.
split.
lia.
exists INDEFINITE_PAST.
split.
lia.
exists INDEFINITE_PAST.
split.
lia.
exists (INDEFINITE_PAST - OneHour).
split.
lia.
split.
lia.
split.
firstorder.
firstorder.
(* FIXME Error: adjectives do not have temporal parameter *)
Qed.


Theorem  problem273atrue : Problem273aTrue.
cbv.
intros.
Abort All.


Theorem  problem274atrue : Problem274aTrue.
cbv.
(* cannot use Writeunique because of the existential (not the same report) *)
Abort All.

Theorem  problem274atrue : Problem274aFalse.
cbv.
(* obviously the events are not incompatible *)
Abort All.

(* FIXME: 275 "before" uses a conjuction, perhaps it should be changed to implication? *)

(* 276 undef *)

Theorem  problem277t : Problem277aTrue.
cbv.
intros [t0 [t1 [c0 [c1 [c2 P1]]]]].
repeat eexists.
Focus 4.
exact P1.
(* cannot conclude *)
Abort All.

Theorem  problem277f : Problem277aFalse.
cbv.
(* Even if we have inclusion we can't have a contradiction (statives are never unique)*)
Abort All.

Theorem  problem278atrue : Problem278aFalse.
cbv.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P1 H) as B.
lia.
Qed.

Theorem  problem279 : Problem279aFalse.
cbv.
intros novel isSmithsNovel P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize writeUnique with (x := novel)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P1 H) as B.
lia.
Qed.

Theorem  problem280 : Problem280aFalse.
cbv.
(* Existential means we have two different activities; so writeUnique cannot be used*)
Abort All.

Theorem  problem281 : Problem281aTrue.
cbv.
intros business isBusiness.
intro P1.
(* Can't conclude *)
Abort All.

Theorem  problem281f : Problem281aFalse.
cbv.
intros business isBusiness.
intros P1 H.
(* Note: Can't conclude, but FraCas says that "run a business" is an activity --- however if it were we could use unicity to show that there is a contradiction *)
Abort All.

Parameter discoverUnique : forall (x y : object), UniqueEvent (discover_V2 x y).

Theorem  problem282 : Problem282aFalse.
cbv.
intros species isNewSpecies P1 H.
destruct P1 as [t0 [t1 [ct1 [ct2 [ct3 P1]]]]].
destruct H as [u0 [u1 [cu1 [cu2 [cu3 H]]]]].
specialize discoverUnique with (x := species)(y := SMITH) as A.
unfold UniqueEvent in A.
specialize (A _ _ P1 H) as B.
lia.
Qed.

Theorem  problem283f : Problem283aFalse.
cbv.
intros P1 H.
(* Can't use unicity due to the existential *)
Abort All.

Theorem  problem283t : Problem283aTrue.
cbv.
intros P1.
(* Can't use unicity due to the existential *)
Abort All.

Theorem  problem284 : Problem284aTrue.
cbv.
intros report isReport.
intros [P1 P2].
destruct P1 as [t0 [c0 P1]].
destruct P2 as [u0 P2].
destruct P1 as [t1 [c3 [t3 [c2 [c4 P1]]]]].
specialize writeUnique with (x := report)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ P2 P1) as B.
eexists.
eexists.
split.
Focus 2.
exact P2.
split.
apply past.
lia.
Qed.

(* 285: No support for terrible GF syntax yet *)

(*Theorem problem286 : Problem286aFalse.
- Horrid syntax, can't interpret it
- Need special treatment for "spend ... "
Abort All.
 *)

Theorem problem287 : Problem287aTrue.
cbv. 
(* Can't use unicity due to the existential *)
Abort All.

Theorem problem287f : Problem287aFalse.
cbv. 
(* Can't use unicity due to the existential *)
Abort All.

Theorem problem288 : Problem288aTrue.
cbv.
intro P1.
destruct P1 as [t0 [c1 [t1 [c4 [t2 [c2 [c3 [report [isReport B]]]]]]]]].
exists (t2 + (OneHour + OneHour)).
split.
lia.
exists t2.
split.
lia.
exists report.
split.
assumption.
assumption.
Qed.

Theorem problem289 : Problem289aFalse.
cbv.
intros species newSpecies.
intros [t1 [tPast P1]].
(* Spend 2 hours has not a correct interpretation *)

(* Also we believe that the judgement should actually be "unknown" (he
could be faster, but it could also be exactly two hours.) *)
Abort All.

Theorem problem290 : Problem290aTrue.
cbv.
intro P1.
destruct P1 as [t1 [p1 [c2 [p2 [t3 [c3 [c4 P1]]]]]]].
exists (t3 + (OneHour + OneHour)).
split.
lia.
eapply P1.
Qed.

Theorem problem291 : Problem291aTrue.
(* meaning/syntax for spend *)
Abort All.

Theorem problem292 : Problem292aTrue.
(* meaning/syntax for spend *)
Abort All.

Theorem problem293 : Problem293aTrue.
(* meaning/syntax for spend *)
Abort All.

Theorem problem294 : Problem294aTrue.
cbv.
intros business isBusiness.
(* FIXME: inconsistent syntax for "in two years" compared to 285, etc. *)
(* TODO *)
Abort All.

Theorem problem295t : Problem295aTrue.
cbv.
(* Terrible syntax for in_two_years (what does it even mean?)*)
(* Can't conclude anyway *)
Abort All.

Theorem problem295f : Problem295aFalse.
cbv.
(* Terrible syntax for in_two_years (what does it even mean?)*)
(* Can't conclude anyway *)
Abort All.

Theorem problem296t : Problem296aTrue.
cbv.
(* Terrible syntax for in_two_years (what does it even mean?)*)
(* Can't conclude anyway *)
Abort All.
Theorem problem296f : Problem296aFalse.
cbv.
(* Terrible syntax for in_two_years (what does it even mean?)*)
(* Can't conclude anyway *)
Abort All.

Theorem problem297t : Problem297aTrue.
cbv.
(* Terrible syntax for in_two_years (what does it even mean?)*)
(* TODO *)
Abort All.


Opaque PN2object.
Theorem problem298 : Problem298aTrue.
cbv.
intro P1.
destruct P1 as [t1 [c1 [t2 [c2 [t3 [t4 [c3 [c4 P1]]]]]]]].
repeat eexists.
Focus 5.
exact P1.
Focus 3.
reflexivity.
Focus 2.
reflexivity.
lia.
lia.
Qed.


Parameter liveInUnique : forall (x y : object), UniqueActivity (live_Vin x y).
(* TODO: one should be using a stative instead; but the definition of
"for_exactly_a_year_Adv" needs to be strengthened to do that. *)

Transparent PN2object.
Theorem problem299 : Problem299aFalse.
cbv.
intros P1 Q.
destruct P1 as [t1 [c1[t2[c2 [t3 [t4 [c3 [c4 P1]]]]]]]].
destruct Q as [u1 [d1[u2[d2 [u3 [d3 [d4 Q]]]]]]].
specialize liveInUnique with (x := BIRMINGHAM)(y := SMITH) as A.
unfold UniqueActivity in A.
specialize (A _ _ _ _ Q P1) as B.
destruct B as [C D].
lia.
Qed.

Theorem problem300 : Problem300aTrue.
cbv.
firstorder.
Qed.


Theorem problem301 : Problem301aTrue.
cbv.
intros business isBusiness.
intro P1.
destruct P1 as [t1 [c1 [t2 [c2 [t3 [t4 [c3 [c4 P1]]]]]]]].
repeat eexists.
Focus 5.
exact P1.
Focus 2.
reflexivity.
Focus 2.
reflexivity.
lia.
lia.
Qed.

Theorem problem302 : Problem302aTrue.
cbv.
intros.
assumption.
Qed.

Theorem problem303 : Problem303aTrue.
cbv.
intro P1.
destruct P1 as [t1 [c1[t2[c2 [t3 [t4 [c3 [c4 [report [isReport P1]]]]]]]]]].
repeat eexists.
Focus 6.
exact P1.
Focus 2.
reflexivity.
Focus 2.
reflexivity.
lia.
lia.
assumption.
Qed.

Theorem problem304t : Problem304aTrue.
cbv.
intros [t0 [c0 [ t1 [c1 [t2 [t3 [c2 [c3 P1]]]]]]]].
destruct P1 as [report [isReport P1]].
repeat eexists.
Focus 4.
exact P1.
(*lia.  cannot conclude*)
Abort All.

Theorem  problem306atrue : Problem306aTrue.
cbv.
intro P1.
destruct P1 as [g [c1[f [c2 [b [c [c3 [c4 [report [isReport P1]]]]]]]]]].
repeat eexists.
Focus 3.
exact P1.
lia.
assumption.
Qed.


Opaque PN2object.
Theorem  problem307atrue : Problem307aTrue.
cbv.
intro P1.
apply P1.
split.
lia.
lia.
Qed.

(* 308 309 310 undef *)
Parameter taxiIdiom : forall dst taxi x t0 t1,
 (taxi_Nto dst taxi /\ take_V2 taxi x t0 t1) =
 (taxi_N taxi /\ take_V2to dst taxi x t0 t1).
(* The syntax is not the same in P and H. *)

Transparent PN2object.
Theorem  problem311atrue : Problem311aTrue.
cbv.
intros theStation isStation theHouse isHouse.
intro Ps.
destruct Ps as [t0 [c0 [c1 [ P1 [taxi P2]]]]].
specialize taxiIdiom with (dst := theStation) (taxi := taxi) (x := SMITH) (t0 := t0) (t1 := t0) as A.
exists t0.
split.
lia.
split.
lia.
split.
exists taxi.
rewrite <- A.
assumption.
assumption.
Qed.


Opaque PN2object.
Theorem  problem312atrue : Problem312aTrue.
cbv.
intros [P1 P2].
eexists.
eexists.
repeat split.
Focus 4.
eapply P1.
reflexivity.
reflexivity.
reflexivity.
lia.
Qed.

Theorem  problem313 : Problem313aFalse.
cbv.
intros [P1 P2].
intro Q.
destruct Q as [t [t' [tC1 [tC2 [ tC3 [report [isReport Q]]]]]]].
eapply P1.
Focus 2.
exists report.
split.
assumption.
exact Q.
reflexivity.
Qed.


Parameter arrive_be_in : forall loc x t0 t1, arrive_in_V2 loc x t0 t1 -> _BE_in loc x t1 t1.

Theorem  problem314 : Problem314aTrue.
unfold Problem314aTrue.
unfold appTime.
unfold UnspecifiedTime.
unfold _BE_.
unfold PAST.

intro H.
destruct H  as [P1 [[today [isToday P2]] P3]].
specialize (arrive_be_in P1) as A.
eapply inParisStative.
eapply P3.
eapply arrive_be_in.
exact P1.
cbv.
lia.
cbv.
cbv in P2.
lia.
Qed.


Theorem problem315 : Problem315aTrue.
cbv.
intros arrivalTime arrPast.
intros dayBefore [arrTime' [arrive isDay]].
intros [arrtime'' [P2]].
(* "the day before" is not interpreted correctly (we do not know that dayBefore is the day before...) *)
(* However, arrtime is inconsistent with arrtime''. arrtime'' is not a correct thing to get. *)
Abort All.

Theorem problem316 : Problem316aTrue.
(* TODO *)
Abort All.

(*
No syntax for that.
Theorem problem318 : Problem318aFalse.
Abort All.
*)

Theorem problem319 : Problem319iTrue.
cbv.
intros previousOffice isOffice.
intros currentOffice isOffice'.
intros [t0 [tp [tp' [buy [P1 P2]]]]].
(* Incorrect syntax: use of impersonal ^^ *)
(* P1  means that we have payment 8 years in the past with the buying as reference *)
(* P2  means that we have payment 8 years in the future with the buying as reference *)
(* TODO *)
Abort All.

Parameter know_implicature : forall p x t0 t1, know_VS p x t0 t1 -> p.

Opaque PN2object.
Theorem  problem320btrue : Problem320aTrue.
cbv.
intros theCase isCase.
intros memoir hisMemoir.
intros theJob isCIAJob.
intros [t1 [c1 [c2 [c3 [c4 P1]]]]].
destruct P1 as [gotJob knowStuff].
specialize (know_implicature knowStuff) as P1.
rewrite -> itIsTheCaseThatIdiom.
split.
intro H.
specialize P1  with (f := NOW) (g := NOW) as P1'.
cut (NOW <= NOW).
intro PP.
specialize (P1' PP) as P1'.
apply P1'.
apply H.
reflexivity.
apply P1.
assumption.
Qed.

(*
Theorem  problem321 : Problem321aTrue.
Abort All.
Syntactic difficulties and problem that we do not have a mechanism to count occurences of events
*)

Theorem problem322 : Problem322aTrue.
cbv.
(*TODO
P1 should be parsed as:

Last week I already knew that
  (when, in a month's time, Smith would discover that she had been duped) she would be furious. *)
Abort All.


Theorem  problem323 : Problem323aTrue.
(* need special support for continue_V / stop_V *)
(* Everything in this problem requires special treatment (start, stop, continue, until )
*)
Abort All.



Theorem problem324 : Problem324aTrue.
cbv.
intro P1.
(* need special support for continue_V / stop_V
(they should be V2V with an elliptic_VP)
*)
Abort All.

Theorem problem325 : Problem325aTrue.
cbv.
(* Problem with anaphora: people know that they ... (they does not manage to refer correctly)*)
Abort All.


