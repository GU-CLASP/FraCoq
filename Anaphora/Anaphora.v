Parameter object : Set.
Parameter mary : object.

Inductive Gender : Set :=
    male : Gender
  | female : Gender.

Definition Descriptor := Gender.

Definition Env := Descriptor -> object.

Definition Effect := Env -> (Prop * Env).

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

Definition push : Descriptor -> object -> Env -> Env
:= fun descr obj rho demandedDescr =>
     match Match descr demandedDescr with
       | true => obj
       | false => rho demandedDescr
     end.

Parameter assumed : Env.

Definition maryNP : NP
:= fun vp ρ => vp mary (push female mary ρ).

Definition sheNP : NP
:= fun vp ρ => vp (ρ female) ρ.

Definition heNP : NP
:= fun vp ρ => vp (ρ male) ρ.

Parameter attendedTheMeeting : object -> Prop.
Definition attendedTheMeetingVP : VP
  := fun x rho => (attendedTheMeeting x, rho).

Definition IMPLIES : Effect -> Effect -> Effect
:= fun x y rho1 => let (x' , rho2) := x rho1 in
                   let (y' , rho3) := y rho2 in
                    (x' -> y' , rho3).

Notation "A ==> B" := (IMPLIES A B) (at level 10,right associativity).

Definition
TRUE : Effect -> Set
     := fun x => let (x',_) := x assumed in x'.

Theorem thm1 : TRUE (maryNP attendedTheMeetingVP ==> heNP attendedTheMeetingVP).
cbv.
intuition.
Qed.
