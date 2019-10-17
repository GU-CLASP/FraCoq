Load MS.

Inductive Temporal : Set :=
  UnspecifiedTime : Temporal |
  ATTIME : Time -> Temporal |
  SINCE : Time -> Temporal.
  
Definition appTime : Temporal -> (object -> TProp) -> object -> Prop :=
  fun time vp x => match time with
  | UnspecifiedTime => vp x NOW
  | ATTIME t => vp x t
  | SINCE t => forall (t' : Time), t < t -> vp x t
  end.


Definition _BE_inwithTime : Temporal -> object -> object -> Prop :=
 fun tmp x => appTime tmp (_BE_in x).

Parameter Year_1996 : Time.


Parameter idiom : appAdv now_AdV (_BE_withTime (ATTIME Year_1996)) -> NOW = Year_1996.

appAdv now_AdV (_BE_withTime (ATTIME Year_1996));


Definition Problem252aTrue:= (_BE_inwithTime (PN2object birmingham_PN) (SINCE Year_1992) (PN2object itel_PN) /\ appAdv now_AdV (_BE_withTime (ATTIME Year_1996)) IMPERSONAL -> _BE_inwithTime (PN2object birmingham_PN) (ATTIME Year_1993) (PN2object itel_PN)).

