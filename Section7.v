
Load MS.
Definition now_AdV : AdV
 := fun vp subject => vp subject. (* We simply ignore "now", because currently "now" is the default *)

Inductive Temporal : Type :=
  BeforeTimeOf : TProp -> Temporal |
  UnspecifiedTime : Temporal |
  ATTIME : Time -> Temporal |
  SINCE : Time -> Temporal.

Definition RefTime := ATTIME.

Definition appTime : Temporal -> (object -> TProp) -> object -> Prop :=
  fun time vp x => match time with
  | UnspecifiedTime => vp x NOW
  | BeforeTimeOf tp => exists (t1 : Time) (t2 : Time), tp t1 /\ vp x t2
  | ATTIME t => vp x t
  | SINCE t => forall (t' : Time), (t < t') -> (t' < NOW) -> vp x t' (* apparently fracas wants the NOW constraint? (p252) *)
  end.



Parameter Year_1996 : Time.
Parameter Year_1993 : Time.
Parameter Year_1992 : Time.

Parameter y1993before1996 : Year_1993 <  Year_1996.
Parameter y1992before1996 : Year_1992 <  Year_1996.
Parameter y1992before1993 : Year_1992 <  Year_1993.

(* Parameter idiom : forall t, appAdv now_AdV (appTime (ATTIME t) _BE_) IMPERSONAL = (NOW = t). *)


Definition Problem252aTrue:= (appTime (SINCE Year_1992) (_BE_in (PN2object birmingham_PN)) (PN2object itel_PN) /\ appAdv now_AdV (appTime (ATTIME Year_1996) _BE_) IMPERSONAL -> appTime (ATTIME Year_1993) (_BE_in (PN2object birmingham_PN)) (PN2object itel_PN)).

Theorem  problem252aTrue : Problem252aTrue.
cbv.
intros [P1 P2].
apply P1.
apply y1992before1993.
rewrite <- P2.
apply y1993before1996.
Qed.

Definition Problem261aTrue:= (appTime (BeforeTimeOf (fun x1 => appTime (RefTime x1) leave_V (PN2object jones_PN))) leave_V (PN2object smith_PN) /\ appTime (BeforeTimeOf (fun x1 => appTime (RefTime x1) leave_V (PN2object anderson_PN))) leave_V (PN2object jones_PN) -> appTime (BeforeTimeOf (fun x1 => appTime (RefTime x1) leave_V (PN2object anderson_PN))) leave_V (PN2object smith_PN)).

Transparent PN2object.
Theorem  problem261atrue : Problem261aTrue.
cbv.
firstorder.
Qed.
