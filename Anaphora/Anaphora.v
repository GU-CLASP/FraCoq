Close Scope nat_scope.

Parameter object : Set.
Parameter MARY : object.
Parameter JOHN : object.

Inductive Gender : Set :=
    male : Gender
  | female : Gender
  | unknown : Gender.

Definition Descriptor := Gender.

Definition ObjQuery := Descriptor -> bool.
Definition ObjEnv := ObjQuery -> object.
Definition VPEnv := (object -> Prop). (* Just remember the last VP; could be more fine-grained because we have "does", "is", "has" as placehodlers in English.*)

Definition Env : Type := VPEnv * ObjEnv.

Definition Effect := Env -> (Prop * Env).
Parameter assumedObj : ObjEnv.
Parameter assumedVP : VPEnv.
Definition assumed := (assumedVP,assumedObj).
Definition
TRUE : Effect -> Prop
     := fun x => let (x',_) := x assumed in x'.


Definition S := Effect.

Definition VP := object -> Effect.

Definition TRUE_VP : VP -> (object -> Prop)
     := fun vp x => TRUE (vp x).

Definition NP := VP -> Effect.

Definition isMale := fun d => match d with
  male => true
  | _ => false
  end .

Definition isFemale := fun d => match d with
  female => true
  | _ => false
  end .


Definition pushObj : Descriptor -> object -> Env -> Env
:= fun objDescr obj env => let (vpEnv, rho) := env in
     (vpEnv, fun pred =>
     match pred objDescr with
       | true => obj
       | false => rho pred
     end).

Definition pushVP : (object -> Prop) -> Env -> Env
:= fun vp env => let (vpEnv, objEnv) := env in (vp,objEnv).

Definition getObj : Env -> ObjQuery -> object
 := fun env descr => let (vpEnv , objEnv) := env in objEnv descr.


Definition maryNP : NP
:= fun vp ρ => vp MARY (pushObj female MARY ρ).

Definition johnNP : NP
:= fun vp ρ => vp JOHN (pushObj male JOHN ρ).

Definition sheNP : NP
:= fun vp ρ => vp (getObj ρ isFemale) ρ.

Definition heNP : NP
:= fun vp ρ => vp (getObj ρ isMale) ρ.

Definition theySingNP : NP (*as in everyone owns their book *)
:= fun vp ρ => vp (getObj ρ (fun _ => true)) ρ.


Definition lift2 : (Prop -> Prop -> Prop) -> Effect -> Effect -> Effect
:= fun op x y rho1 => let (x' , rho2) := x rho1 in
                      let (y' , rho3) := y rho2 in
                       (op x' y' , rho3).

Notation "A [IF] B" := (lift2 (fun x y => y -> x) A B) (at level 9,right associativity).

Notation "A [.] B" := (lift2 (fun x y => x /\ y) A B) (at level 9,right associativity).


Parameter LEAVE_V : object -> Prop.


Definition pureVP : (object -> Prop) -> VP
  := fun V x rho => (V x, pushVP V rho).
(* push the V in the env for reference. *)

Definition leavesVP := pureVP LEAVE_V.

Parameter IS_TIRED : object -> Prop.
Definition isTiredVP := pureVP IS_TIRED.

(* EXAMPLE: john leaves if he is tired *)
Eval cbv in TRUE ((johnNP leavesVP) [IF] (heNP isTiredVP)).

Definition doesTooVP : VP
   := fun x env => let (vpEnv, objEnv) := env in (vpEnv x,env).

(* EXAMPLE: john leaves if mary does [too] *)

Eval cbv in TRUE ((johnNP leavesVP) [IF] (maryNP doesTooVP)).

Parameter ADMIT_V : Prop -> object -> Prop.
Definition admitVP : Effect -> VP
:= fun p x rho0 => let (p',rho1) := p rho0 in
                   (ADMIT_V p' x, pushVP (ADMIT_V p') rho1).

Parameter PERSON : object -> Prop.
Parameter CONGRESSMAN : object -> Prop.
Parameter ADMIRE_KENNEDY : object -> Prop.

Definition everyOne : NP
:= fun vp ρ => (forall x, PERSON x -> fst (vp x (pushObj unknown x ρ)),
                          pushVP (fun x => fst (vp x ρ)) ρ).

  
(* EXAMPLE: everyone admits that they are tired. *)
Eval cbv in TRUE (everyOne (admitVP (theySingNP isTiredVP))).

(* EXAMPLE: everyone admits that they are tired. Mary does too. *)
Eval cbv in TRUE ((everyOne (admitVP (theySingNP isTiredVP))) [.] (maryNP doesTooVP)).
(*Attn: we push the VP after resolution of anaphora. This means that
the "does too" picks the (unbound!) "they" which is evaluated when
pushing the "admits that they are tired" in the invokation of
Everyone.

Unfortunately, Coq is not to friendly environment to fix this
problem. Indeed, if the things looked up in the environment need
themselves to lookup in the environment we may have infinite
recursion. One would need to prove to Coq that this process is bound
in some way --- which is an annoyance.

*)



Parameter attendedTheMeeting : object -> Prop.

Definition attendedTheMeetingVP : VP
  := pureVP attendedTheMeeting.

Definition IMPLIES : Effect -> Effect -> Effect
:= lift2 (fun x y => x -> y).

Notation "A ==> B" := (IMPLIES A B) (at level 10,right associativity).



Theorem thm1 : TRUE (maryNP attendedTheMeetingVP ==> sheNP attendedTheMeetingVP).
cbv.
intuition.
Qed.

Theorem thm2  : TRUE (maryNP attendedTheMeetingVP ==> heNP attendedTheMeetingVP).
cbv.
intuition.
(*False: mary is not male *)