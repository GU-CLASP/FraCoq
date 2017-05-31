Close Scope nat_scope.

Parameter object : Set.
Parameter MARY : object.
Parameter JOHN : object.

Inductive Gender : Set :=
    male : Gender
  | female : Gender.

Definition Descriptor := Gender.

Definition ObjEnv := Descriptor -> object.
Definition VPEnv := (object -> Prop). (* Just remember the last VP; could be more fine-grained because we have "does", "is", "has" as placehodlers in English.*)

Definition Env : Type := VPEnv * ObjEnv.

Definition Effect := Env -> (Prop * Env).
Parameter assumedObj : ObjEnv.
Parameter assumedVP : VPEnv.
Definition assumed := (assumedVP,assumedObj).
Definition
TRUE : Effect -> Set
     := fun x => let (x',_) := x assumed in x'.


Definition S := Effect.

Definition VP := object -> Effect.

Definition NP := VP -> Effect.

Definition Match : Descriptor -> Descriptor -> bool
:= fun d0 d => match d0 with
  | male => match d with
     | male => true
     | female => false
    end
  | female => match d with
     | male => false
     | female => true
    end
  end.

Definition pushObj : Descriptor -> object -> Env -> Env
:= fun descr obj env => let (vpEnv, rho) := env in
     (vpEnv, fun demandedDescr =>
     match Match descr demandedDescr with
       | true => obj
       | false => rho demandedDescr
     end).

Definition getObj : Env -> Descriptor -> object
 := fun env descr => let (vpEnv , objEnv) := env in objEnv descr.


Definition maryNP : NP
:= fun vp ρ => vp MARY (pushObj female MARY ρ).

Definition johnNP : NP
:= fun vp ρ => vp JOHN (pushObj male JOHN ρ).

Definition sheNP : NP
:= fun vp ρ => vp (getObj ρ female) ρ.

Definition heNP : NP
:= fun vp ρ => vp (getObj ρ male) ρ.


Definition lift2 : (Prop -> Prop -> Prop) -> Effect -> Effect -> Effect
:= fun op x y rho1 => let (x' , rho2) := x rho1 in
                      let (y' , rho3) := y rho2 in
                       (op x' y' , rho3).

Notation "A [IF] B" := (lift2 (fun x y => y -> x) A B) (at level 9,right associativity).


Parameter LEAVE_V : object -> Prop.


Definition pureVerb : (object -> Prop) -> VP
  := fun V x rho => let (vpEnv,objEnv) := rho in (V x, (V,objEnv)).

Definition leavesVP := pureVerb LEAVE_V.

Parameter IS_TIRED : object -> Prop.
Definition isTiredVP := pureVerb IS_TIRED.

(* EXAMPLE: john leaves if he is tired *)
Eval cbv in TRUE ((johnNP leavesVP) [IF] (heNP isTiredVP)).

Definition doesTooVP : VP
   := fun x env => let (vpEnv, objEnv) := env in (vpEnv x,env).

(* EXAMPLE: john leaves if mary does [too] *)

Eval cbv in TRUE ((johnNP leavesVP) [IF] (maryNP doesTooVP)).


Parameter attendedTheMeeting : object -> Prop.

Definition attendedTheMeetingVP : VP
  := fun x rho => (attendedTheMeeting x, rho).

Definition IMPLIES : Effect -> Effect -> Effect
:= fun x y rho1 => let (x' , rho2) := x rho1 in
                   let (y' , rho3) := y rho2 in
                    (x' -> y' , rho3).

Notation "A ==> B" := (IMPLIES A B) (at level 10,right associativity).



Theorem thm1 : TRUE (maryNP attendedTheMeetingVP ==> sheNP attendedTheMeetingVP).
cbv.
intuition.
Qed.

Theorem thm2  : TRUE (maryNP attendedTheMeetingVP ==> heNP attendedTheMeetingVP).
cbv.
intuition.
(*False: mary is not male *)