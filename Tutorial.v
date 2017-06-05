

Parameter  PN   : Type .
Definition S    : Type := Prop .
Definition Cl   : Type := Prop .
Definition VP   : Type := PN -> Prop .
Definition NP   : Type := VP -> Prop .
(* Definition NP   : Type := PN . *)
Definition AP   : Type := PN -> Prop .
Definition A    : Type := AP .
Definition CN   : Type := PN -> Prop .
Definition Det  : Type := CN -> NP .
Definition N    : Type := CN .
Definition V    : Type := VP .
Definition V2   : Type := PN -> VP .
Definition AdA  : Type := AP -> AP .
Definition Pol  : Type := Prop -> Prop .
Definition Conj : Type := Prop -> Prop -> Prop .

Parameter man_N :  N.
Parameter woman_N : N .
Parameter house_N :  N.
Parameter tree_N : N .
Parameter   big_A : A .
Parameter small_A : A .
Parameter green_A : A .
Parameter  walk_V : V  .
Parameter arrive_V : V .
Parameter love_V2 : V2  .
Parameter please_V2 : V2 .
Parameter john_PN :PN .
Parameter mary_PN : PN.


Parameter AdAP    : AdA -> AP -> AP. 
Parameter we_NP   : NP.
Parameter you_NP : NP. 
Parameter very_AdA : AdA. 

Definition and_Conj : Conj := fun x y => x /\ y.
Definition or_Conj : Conj := fun x y => x \/ y.

Definition Pos : Pol := fun p => p.
Definition Neg : Pol := fun p => not p.
Definition UseCl   : Pol -> Cl -> S :=
  fun pol c => pol c. 

Definition UsePN    : PN -> NP := fun pn vp => vp pn.
Definition UseV    : V -> VP := fun v => v.
Definition PredVP  : NP -> VP -> Cl := fun np vp => np vp.
(* Definition PredVP  : NP -> VP -> Cl := fun np vp => vp np. *)
(* Definition UsePN   : PN -> NP := fun x => x. *)
Definition DetCN   : Det -> CN -> NP := fun det cn => det cn. 
Definition every_Det : Det := fun cn vp => forall x, cn x -> vp x.
Definition some_Det : Det := fun cn vp => exists x, cn x /\ vp x.
Definition UseN   : N -> CN := fun x => x. 
Definition ModCN   : AP -> CN -> CN := fun ap cn x => ap x /\ cn x. 
Definition CompAP  : AP -> VP := fun ap x => ap x. 
Definition UseA  : A -> AP := fun a => a. 
Definition ComplV2 : V2 -> NP -> VP := fun v object subject => object (v subject).
Definition ConjS  : Conj -> S  -> S  -> S := fun c => c.
Definition ConjNP  : Conj -> NP -> NP -> NP := fun c np1 np2 vp =>
  np1 (fun x => np2 (fun y => c (vp x) (vp y))). 


Theorem thm0 : UseCl Pos (PredVP (UsePN john_PN) walk_V) ->
               UseCl Pos (PredVP (UsePN john_PN) walk_V).
intro H.
exact H.
Qed.

Theorem thm1 : UseCl Pos (PredVP (UsePN john_PN) walk_V) ->
               UseCl Neg (PredVP (UsePN john_PN) walk_V) -> False.
cbv.
intros P N.
exact (N P).
Qed.


Eval cbv in UseCl Pos (PredVP (UsePN john_PN) walk_V).


Definition everyoneNP : NP := fun vp => forall x, vp x.


Theorem thm2 :
    UseCl Pos (PredVP (DetCN every_Det (UseN man_N)) walk_V) ->
    (man_N john_PN) ->
    (walk_V john_PN).
   
cbv.
intros H1 H2.
exact (H1 john_PN H2).
Qed.

(* "every green tree is green." *)
Theorem thm3 :
    UseCl Pos (PredVP (DetCN every_Det (ModCN (UseA green_A) (UseN tree_N))) (CompAP (UseA green_A))).
cbv.    
intuition.
Qed.


(*"John loves Mary and a tree."*)
Eval cbv in UseCl Pos (PredVP (UsePN john_PN) (ComplV2 love_V2 (ConjNP and_Conj (UsePN mary_PN) (DetCN some_Det (UseN tree_N))))).