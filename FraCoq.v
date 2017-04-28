Close Scope nat_scope.
Require Import ZArith.
Open Scope Z_scope.

(** Basic concepts **)
Parameter object : Type.
(** Categories **)
Definition S:= Prop.

Definition ADV := (object -> Prop) -> (object -> Prop).

(*Definition VeridicalAdvStrong := { adv : (object -> Prop) -> (object -> Prop) &
                          forall (x : object) (v : object -> Prop) (f : (object -> Prop) -> (object -> Prop)), f (adv v) x -> f v x}. (**) FIXME: probably too strong; consider eg. the case where f is "not". This would probably be OK for co-variant f's though. *)
Definition AdV := ADV.
Definition Adv := ADV.

Definition VeridicalAdv :=
  { adv : (object -> Prop) -> (object -> Prop)
    & prod (forall (x : object) (v : object -> Prop), (adv v) x -> v x)
           (forall (v w : object -> Prop), (forall x, v x -> w x) -> forall (x : object), adv v x -> adv w x)
    }.

Definition WkVeridical : VeridicalAdv -> Adv
                       := fun adv => projT1 adv.
Coercion WkVeridical : VeridicalAdv >-> Adv.
(* Theorem WkADV : VeridicalAdvStrong -> VeridicalAdv. cbv. intro adv. destruct adv as [adv cov]. exists adv. intros. apply cov with (f := fun p => p). exact H. Qed. *)
(* Coercion WkADV : VeridicalAdvStrong >-> VeridicalAdv. *)
Parameter CAdv : Set.
Parameter IAdv : Set.
Parameter IDet : Set.
Parameter IP : Set.
Parameter IQuant : Set.
Parameter PConj : Set.
Definition QCl := Prop.
Definition QS := Prop.
Definition Subj := Prop -> Prop -> Prop.
Definition CN:= object->Prop.
Definition VP:= forall (subjectClass : CN), object -> Prop. (* subject *)
Definition SC := VP.
Definition V := object -> Prop.
Definition V2S := object -> S -> object -> Prop.
Definition V2V := object -> VP -> object -> Prop.
Definition V3 := object -> object -> object -> Prop. (* indirect object, direct object, subject *)
Definition V2 := object->object->Prop. (* Object first, subject second. *)
Definition VV := VP -> object -> Prop.
Definition VPS := VP.
Parameter VQ : Set.
Definition VS := S -> VP.
Parameter RP : Set.

Inductive Conj : Type :=
  Associative : (Prop -> Prop -> Prop) -> Conj |
  EitherOr : Conj.


Inductive A : Type  :=
  mkA : forall (measure : (object -> Prop) -> object -> Z)
               (threshold : Z)
               (property : (object -> Prop) -> (object -> Prop)), A.

Add Printing Let A.

Definition apA : A -> (object -> Prop) -> (object -> Prop)
  := fun a cn x => let (measure,threshold,p) := a in (threshold <= measure cn x) /\ p cn x.

Definition A2 := object -> A.

Inductive IntersectiveA : Type :=
  mkIntersectiveA : forall (measure : object -> Z) (threshold : Z), IntersectiveA.

Add Printing Let IntersectiveA.

Definition apIntersectiveA : IntersectiveA -> A
 := fun a => let (measure,threshold) := a in
      mkA (fun _ => measure) threshold (fun cn (x:object) => cn x).

Coercion apIntersectiveA : IntersectiveA >-> A.

Inductive SubsectiveA : Type :=
  mkSubsective : forall (measure : (object -> Prop) -> object -> Z) (threshold : Z), SubsectiveA.
Add Printing Let SubsectiveA.

Definition apSubsectiveA
            : SubsectiveA -> A
            := fun a => let (measure, threshold) := a in
               mkA measure threshold (fun cn (x:object) => cn x) .
(* Definition getSubsectiveA : SubsectiveA -> A. *)
(* intro. destruct X. exact P. Defined. *)
Coercion apSubsectiveA : SubsectiveA >-> A.

Inductive ExtensionalSubsectiveA : Type :=
  mkExtensionalSubsective :
     forall
     (measure : (object -> Prop) -> object -> Z)
     (threshold : Z),
     (let a := fun cn x => (threshold <= measure cn x)
     in (forall (p q:object -> Prop), (forall x, p x -> q x) -> (forall x, q x -> p x) ->  forall x, a p x -> a q x))
     -> ExtensionalSubsectiveA.

Add Printing Let ExtensionalSubsectiveA.

Definition apExtensionalSubsectiveA
            : ExtensionalSubsectiveA -> SubsectiveA
            := fun a => let (measure,threshold,_) := a in
                 mkSubsective measure threshold.
Coercion apExtensionalSubsectiveA : ExtensionalSubsectiveA >-> SubsectiveA.

Inductive PrivativeA : Type :=
  mkPrivativeA : forall (measure : (object -> Prop) -> object -> Z) (threshold : Z), PrivativeA.
Add Printing Let PrivativeA.

Definition apPrivativeA : PrivativeA -> A
            := fun a => let (measure, threshold) := a in
               mkA measure threshold (fun cn (x:object) =>  not (cn x)) .
Coercion apPrivativeA : PrivativeA >-> A.

Definition NonCommitalA := A.


Definition AP:= (object -> Prop) -> (object -> Prop).
Definition N:= object->Prop.
Definition N2 := object -> object -> Prop.
Inductive Num : Type :=
  singular : Num |
  plural   : Num |
  unknownNum : Num |
  moreThan : Num -> Num |
  cardinal : Z -> Num.
Definition Card := Num.
Definition AdN : Type := Num -> Num.

Parameter LOTS_OF : CN -> CN. (* "lots of" is treated like an adjective *)
Parameter MANY : Z.
Parameter A_FEW : Z.
Parameter SOME : Z. (* the plural number *)
Parameter SEVERAL : Z.

Fixpoint interpAtLeast (num:Num) (x:Z) :=
  match num with
  | singular => x >= 1
  | plural   => x >= SOME
  | unknownNum => True
  | moreThan n => interpAtLeast n x
  | cardinal n => x >= n
  end.

Definition interpAtMost : Num -> Z -> Prop :=
  fun num x => match num with
  | singular => x <= 1
  | plural   => x <= SOME
  | unknownNum => True
  | moreThan _ => True
  | cardinal n => x <= n
  end.

Definition interpExactly : Num -> Z -> Prop :=
  fun num x => match num with
  | singular => x = 1
  | plural   => True
  | unknownNum => True
  | moreThan n => interpAtLeast n x
  | cardinal n => x = n
  end.

Definition Numeral := Z.
Definition NP0 := VP ->Prop.
Definition NP1 := (object -> Prop) ->Prop.

Definition Quant := Num -> CN -> NP0.
Definition Det := prod Num Quant.

Inductive Prep : Type :=

  mkPrep : forall (prep : NP1 -> (object -> Prop) -> (object -> Prop)),
           (forall (prepArg : NP1) (v : object -> Prop) (subject : object), prep prepArg v subject -> v subject) -> (* veridical *)
           (forall (prepArg : NP1) (v w : object -> Prop), (forall x, v x -> w x) -> forall (subject : object), prep prepArg v subject -> prep prepArg w subject) -> Prep. (* covariant in verb *)

Add Printing Let Prep.

Inductive NP : Type :=
  mkNP : Num -> Quant -> CN -> NP.
Definition npClass (np:NP) := let (_,_,cn) := np in cn.
Definition apNP : NP -> NP0.
cbv. intro np. destruct np as [num quant cn]. apply quant. exact num. exact cn. Defined.
Definition VPSlash:=object -> VP.
Definition Pron := NP.
Inductive PN : Type := mkPN : forall (x:object) (cn : CN), cn x -> PN.
Definition Cl:=Prop.
Definition Pol:= Prop->Prop. (* Polarity *)
Definition Temp:= Prop -> Prop. (* temporal information *)
Definition Phr:= Prop.
Definition Ord:=A.
Definition Comp := VP. (* complement of copula*)
Definition Predet := NP -> NP.
Definition AdA := A -> A.
Definition ClSlash := VP. (* the parameter is the direct object of the verb *)

Definition RCl := VP. (* relative clause *)
Definition RS := RCl.


(** Constructors **)


(* Adv *)
(* Parameter AdAdv : AdA -> Adv -> Adv . *)
(* Parameter ComparAdvAdj : CAdv -> A -> NP -> Adv . *)
(* Parameter ComparAdvAdjS : CAdv -> A -> S -> Adv . *)
(* Parameter ConjAdv : Conj -> ListAdv -> Adv . *)
Parameter PositAdvAdj : A -> Adv .

(* Definition VeridicalAdv := { adv : (object -> Prop) -> (object -> Prop) & forall (x : object) (v : object -> Prop), (adv v) x -> v x}. *)

Definition apNP1 : NP -> NP1 := fun np => (fun k => apNP np (fun xClass x => k x)).

Definition PrepNP : Prep -> NP -> VeridicalAdv.
intros prepRecord np.
destruct prepRecord as [prep prepVerid prepVeridCov].
cbv.
exists (prep (apNP1 np)).
split.
intros. apply prepVerid with (prepArg := apNP1 np). assumption.
intros. apply prepVeridCov with (prepArg := apNP1 np) (v:=v). assumption. assumption.
Defined.
Definition SubjS : Subj -> S -> Adv := fun subj s vp x => subj s (vp x).



(* Card *)
Definition AdNum : AdN -> Card -> Card := fun f => f.
(* Parameter NumDigits : Digits -> Card . *)
Definition NumNumeral : Numeral -> Card := fun x => cardinal x.
(* Parameter digits2numeral : Card -> Card . *)
Parameter half_a_Card : Card .

(* Num *)
Definition NumSg:= singular.
Definition NumPl:= plural.
Definition NumCard : Card -> Num := fun x => x.

(* CN *)
Definition UseN: N->CN := fun n:N=>n.
Definition AdjCN: AP->CN->CN:= fun a o x => a o x.
Definition RelCN: CN->RS->CN:= fun cn rs x => cn x /\ rs cn x. (* GF FIXME: Relative clauses should apply to NPs. See 013, 027, 044.  *)

Definition AdvCN : CN -> Adv -> CN := fun cn adv => adv cn.
Definition ComplN2 : N2 -> NP -> CN
                   := fun n2 np x => apNP np (fun _class y => n2 y x).

Definition apConj2 : Conj -> Prop -> Prop -> Prop := fun c => match c with
  Associative c => c |
  EitherOr => fun p q => (p /\ not q ) \/ (not p /\ q)
  end .

Definition ConjCN2 : Conj -> CN -> CN -> CN
                   := fun c n1 n2 o => apConj2 c (n1 o) (n2 o).

(* Parameter PartNP : CN -> NP -> CN . *)
Parameter SentCN : CN -> SC -> CN .
Parameter elliptic_CN : CN .
(* Parameter ApposCN : CN -> NP -> CN . *)
(* Parameter ConjCN : Conj -> ListCN -> CN . *)
(* Parameter PossNP : CN -> NP -> CN . *)
(* Parameter UseN2 : N2 -> CN . *)

(* SC *)
Parameter EmbedPresPart : VP -> SC .
(* Parameter EmbedQS : QS -> SC . *)
Definition EmbedS : S -> SC := fun s _ _ => s.
  (* Used in cases such as "it is true/likely/false/... that <clause>"
     So we have a copula. Thus "x" is "it". (no info, can be ignored)
     Likewise for the 'noun class' of it.
     *)

Definition EmbedVP : VP -> SC := fun vp => vp.

(* NP *)
Definition DetCN: Det->CN->NP:= fun det cn=> mkNP (fst det) (snd det) cn.
Definition UsePN: PN->NP:=
  
  fun pn => let (o,oClass,_) := pn in mkNP singular (fun (num : Num) (cn : CN) (vp : VP) => vp cn o) oClass.
Definition PredetNP: Predet -> NP -> NP
                   := fun predet np => predet np.

Definition   AdvNP : NP -> Adv -> NP
 := fun np adv => let (num,q,cn) := np in mkNP num (fun cn' k => q cn' (adv k)) cn. (* CHECK *)
(* Parameter ConjNP : Conj -> ListNP -> NP . *)


Definition apConj3 : Conj -> Prop -> Prop -> Prop -> Prop := fun c => match c with
  Associative c => fun p q r => c (c p q) r |
  EitherOr => fun p q r => (p /\ not q /\ not r)\/ (not p /\ q /\ not r)\/ (not p /\ not q /\ r)
  end .


Definition ConjNP2 : Conj -> NP -> NP -> NP
                   := fun c np1 np2 => let (num1, q1,cn1) := np1 in
                                       let (num2, q2,cn2) := np2 in
                                         mkNP (num1) (* FIXME add numbers? min? max? *)
                                              (fun num' cn' vp => apConj2 c (q1 num' cn' vp) (q2 num' cn' vp))
                                              (fun x => (cn1 x) \/ (cn2 x) ).

Definition ConjNP3 : Conj -> NP -> NP -> NP -> NP
                   := fun c np1 np2 np3 =>
                         let (num1, q1,cn1) := np1 in
                         let (num2, q2,cn2) := np2 in
                         let (num3, q3,cn3) := np3 in
                              mkNP (num1) (* FIXME add numbers? min? max? *)
                                   (fun num' cn' vp => apConj3 c (q1 num' cn' vp) (q2 num' cn' vp) (q3 num' cn' vp))
                                   (fun x => (cn1 x) \/ (cn2 x) \/ (cn3 x)).
(* Parameter CountNP : Det -> NP -> NP . *)
Parameter DetNP : Det -> NP .
(* Parameter ExtAdvNP : NP -> Adv -> NP . *)
Definition MassNP : CN -> NP
           := fun cn => mkNP singular (fun num cn' p => exists x, cn' x /\ p cn' x) cn. (* TODO: Check *)

Definition PPartNP : NP -> V2 -> NP  (* Word of warning: in FraCas partitives always behave like intersection, which is probably not true in general *)
          := fun np v2 => let (num,q,cn) := np in
                          mkNP num q (fun x => cn x /\ exists subject, v2 x subject).
(* Parameter RelNP : NP -> RS -> NP . *)
Definition RelNPa : NP -> RS -> NP
                 := fun np rs => let (num,q,cn) := np
                                 in mkNP num q (fun x => cn x /\ rs cn x).
(* Parameter SelfNP : NP -> NP . *)
Definition UsePron : Pron -> NP := fun pron => pron.
(* AP *)
Definition PositA: A -> AP := apA.

Parameter AdAP:AdA->AP->AP.

Parameter AdvAP0 : AP -> Adv -> (object -> Prop) . (* We want to ignore the class here *) 

Definition AdvAP : AP -> Adv -> AP
  := fun adj adv cn x => AdvAP0 adj adv x.

Definition ComparA : A -> NP -> AP
 := fun a np cn x => let (measure,_,_) := a in
    apNP np (fun _class y => (1 <= measure cn x - measure cn y)).
(* Remark: most of the time, the comparatives are used in a copula, and in that case the category comes from the NP.  *)
 (* x is faster than y  *)
 
Definition ComparAsAs : A -> NP -> AP
 := fun a np cn x => let (measure,_,_) := a in
    apNP np (fun _class y => measure cn x = measure cn y).
Definition ComplA2 : A2 -> NP -> AP := fun a2 np cn x => apNP np (fun yClass y => apA (a2 y) cn x).
Parameter PartVP : VP -> AP .
Definition SentAP : AP -> SC -> AP
  := fun ap clause cn x => ap (fun y => clause cn y /\ cn y) x.
Parameter UseComparA : A -> AP.
Definition UseComparA_prefix : A -> AP := fun adj cn x => apA adj cn x.
(* Parameter UseA2 : A2 -> AP . *)
(* Parameter ConjAP : Conj -> ListAP -> AP . *)
(* Parameter ReflA2 : A2 -> AP . *)
(* Parameter AdjOrd : Ord -> AP . *)
(* Parameter CAdvAP : CAdv -> AP -> NP -> AP . *)

(* Quant *)
Parameter environment : (object -> Prop) -> object.
Parameter OF : object -> object -> Prop.
Definition GenNP: NP -> Quant := (* Genitive *)
  fun np num cn vp => apNP np (fun ownerClass owner =>
    let o := environment (fun x => OF owner x /\ cn x)
    in vp cn o /\ OF owner o /\ cn o).


Parameter CARD: CN -> Z.
Parameter MOSTPART: Z -> Z.
Definition CARD_MOST := fun x => MOSTPART (CARD x).

Variable MOST_ineq : forall x, MOSTPART x <= x.
Variable CARD_monotonous : forall a b:CN, (forall x, a x -> b x) -> CARD a <= CARD b.
Parameter le_trans : forall (x y z:Z), x <= y -> y <= z -> x <= z.
Lemma most_card_mono1 : forall a b:CN, (forall x, a x -> b x) -> MOSTPART (CARD a) <= CARD b.
intros. cbv. apply le_trans with (y := CARD a). apply MOST_ineq. apply CARD_monotonous. assumption.
Qed.

Definition IndefArt:Quant:= fun (num : Num) (P:CN)=> fun Q:VP=> match num with
  cardinal n => CARD (fun x => P x /\ Q P x) = n |
  moreThan n => interpAtLeast n (CARD (fun x => P x /\ Q P x)) | (* FIXME: add one here *)
  _ => exists x, P x/\Q P x end. 
Definition DefArt:Quant:= fun (num : Num) (P:CN)=> fun Q:VP=> match num with
   plural => (forall x, P x -> Q P x) /\ Q P (environment P) /\ P (environment P) |
             (* The above implements definite plurals *)
   _ => Q P (environment P) /\ P (environment P) end.



(**Definition DefArt:Quant:= fun P:CN=> fun Q:object->Prop=>exists x,  P x/\ Q x.**)
  (* JP: "exists!" fails to identify that we refer to a thing outside the current NP ??? *)

Parameter PossPron : Pron -> Quant .
Definition  no_Quant : Quant:= fun num P Q=> forall x, not (P x -> Q P x) .
(* Parameter that_Quant : Quant . *)
Parameter the_other_Q : Quant .
Parameter this_Quant : Quant .

(* Det *)
Definition DetQuant: Quant -> Num -> Det:= fun (q:Quant) (n : Num) => (n,q). 
Definition DetQuantOrd: Quant->Num->Ord->Det:= fun q n o =>(n,q). (* Ignoring the ord for now *)
(* Parameter ConjDet : Conj -> ListDet -> Det . *)

(* VPSlash *)
Definition SlashV2a: V2->VPSlash:= fun v dobj sClass s => v dobj s.

(* Parameter AdVVPSlash : AdV -> VPSlash -> VPSlash . *)
(* Parameter AdvVPSlash : VPSlash -> Adv -> VPSlash . *)
(* Parameter SlashV2A : V2A -> AP -> VPSlash . *)
(* Parameter SlashV2Q : V2Q -> QS -> VPSlash . *)
(* Parameter SlashV2VNP : V2V -> NP -> VPSlash -> VPSlash . *)
(* Parameter VPSlashPrep : VP -> Prep -> VPSlash . *)
Definition Slash2V3 : V3 -> NP -> VPSlash
                    := fun v np indirectObject subjectClass subject => apNP np (fun class directObject => v indirectObject directObject subject).
Definition Slash3V3 : V3 -> NP -> VPSlash
                    := fun v np directObject subjectClass subject => apNP np (fun _class indirectObject => v indirectObject directObject subject).
Definition SlashV2S : V2S -> S -> VPSlash
                   := fun v2s s directObject subjectClass subject => v2s directObject s subject.
Definition SlashV2V : V2V -> VP -> VPSlash
                    := fun v2v vp directObject subjectClass subject => v2v directObject vp subject.
Definition SlashVV : VV -> VPSlash -> VPSlash
                   := fun vv v2 directObject subjectClass subject => vv (fun xClass x => v2 directObject xClass x) subject.
Parameter elliptic_VPSlash : VPSlash .

(* AdV *)


(* QS *)
(* Parameter ConjQS : Conj -> ListQS -> QS . *)
Definition ConjQS2 : Conj -> QS -> QS -> QS
                   := fun c => apConj2 c.
(* Parameter ExtAdvQS : Adv -> QS -> QS . *)
Parameter UseQCl : Temp -> Pol -> QCl -> QS .

(* QCl *)
(* Parameter ExistIP : IP -> QCl . *)
(* Parameter ExistIPAdv : IP -> Adv -> QCl . *)
Definition QuestCl : Cl -> QCl := fun c => c.
Parameter QuestIAdv : IAdv -> Cl -> QCl .
(* Parameter QuestIComp : IComp -> NP -> QCl . *)
(* Parameter QuestQVP : IP -> QVP -> QCl . *)
(* Parameter QuestSlash : IP -> ClSlash -> QCl . *)
Parameter QuestVP : IP -> VP -> QCl .


(* IQuant *)
Parameter which_IQuant : IQuant .

(* IDet *)

Parameter IdetQuant : IQuant -> Num -> IDet .
Parameter how8many_IDet : IDet .

(* IP *)
(* Parameter AdvIP : IP -> Adv -> IP . *)
Parameter IdetCN : IDet -> CN -> IP .
(* Parameter IdetIP : IDet -> IP . *)

(* IAdv *)

(* Parameter AdvIAdv : IAdv -> Adv -> IAdv . *)
(* Parameter ConjIAdv : Conj -> ListIAdv -> IAdv . *)
(* Parameter PrepIP : Prep -> IP -> IAdv . *)

(* VP *)
Definition ComplSlash: VPSlash->NP->VP:=fun v2 dobject subjectClass subject=> apNP dobject(fun oClass o => v2 o subjectClass subject).
Definition UseComp: Comp -> VP (* be ... *)
                  := fun p => p.
Definition ComplVV: VV -> VP -> VP
                  := fun vv vp xClass x => vv vp x.

Definition AdVVP : AdV -> VP -> VP
                 := fun adV vp xClass x => adV (fun y => vp xClass y) x.
                 (* can inherit the class of x, because the new VP applies to x anyway *)



Definition  AdvVP : VP -> Adv -> VP:= fun vp adV xClass x => adV (fun y => vp xClass y) x.
(* Parameter ComplBareVS : VS -> S -> VP . *)
Parameter ComplVQ : VQ -> QS -> VP .
Definition ComplVS : VS -> S -> VP
                   := fun vs s => vs s.
Definition ComplVSa : VS -> S -> VP := ComplVS. (* FIXME: what is the difference from ComplVS? *)
(* Parameter ExtAdvVP : VP -> Adv -> VP . *)
Parameter PassV2 : V2 -> VP .
Parameter PassV2s : V2 -> VP .
Parameter PassVPSlash : VPSlash -> VP .
(* Parameter ProgrVP : VP -> VP . *)
Parameter ProgrVPa : VP -> VP .
Definition ReflVP : VPSlash -> VP
                 := fun v2 subjectClass subject => v2 subject subjectClass subject.
(* Parameter SelfAdVVP : VP -> VP . *)
(* Parameter SelfAdvVP : VP -> VP . *)
(* Parameter UseCopula : VP . *)
Definition UseV : V -> VP
                := fun v xClass x => v x.
Parameter elliptic_VP : VP .

(* Comp -- complement of copula*)
Definition CompCN: CN -> Comp (* be a thing given by the CN *)
                 := fun cn xClass x => cn x.
Definition CompNP: NP -> Comp (* be the thing given by the NP *)
                 := fun np oClass o => apNP np (fun o'Class o' => o = o').

Definition CompAP: AP -> Comp (* have property given by the AP *)
                 := fun ap xClass x => ap xClass x.

Definition CompAdv : Adv -> Comp := fun adv xClass x => adv (fun _ => True) x.
(* In the above we ignore the class, because test cases 027 and 044 seem to suggest that adverbs do not depend on the class of the object that they are applied to. This makes intuitive sense as adverbs to not expect a noun class, but rather a VP. (Actually, we could propagate the class and make use of it if it were not for relative clauses being applied to common nouns instead of NPs. See RelCN above.) *)


(* Temp *)
Definition Past : Temp  := fun p => p .
Definition Present : Temp := fun p => p .

Definition Conditional : Temp := fun p => p.
Definition Future : Temp := fun p => p.
Definition FuturePerfect : Temp := fun p => p.
Definition PastPerfect : Temp := fun p => p.
Definition PresentPerfect : Temp := fun p => p.

(* fun TTAnt : Tense -> Ant -> Temp ; *)

(* Cl *)
Definition PredVP: NP->VP->Cl:= fun np vp=> apNP np vp.
Definition ExistNP: NP->Cl:= fun n=>apNP n (fun x xClass => True).
Parameter IMPERSONAL : object.
Definition ImpersCl : VP -> Cl := fun vp => vp (fun x => True) IMPERSONAL.
Parameter SoDoI : NP -> Cl .
Parameter elliptic_Cl : Cl .
(* Parameter CleftAdv : Adv -> S -> Cl . *)
(* Parameter CleftNP : NP -> RS -> Cl . *)
(* Parameter ExistNPAdv : NP -> Adv -> Cl . *)
(* Parameter GenericCl : VP -> Cl . *)
(* Parameter PredSCVP : SC -> VP -> Cl . *)
(* Parameter active2passive : Cl -> Cl . *)

(* ClSlash *)
(* Parameter AdvSlash : ClSlash -> Adv -> ClSlash . *)
(* Parameter SlashPrep : Cl -> Prep -> ClSlash . *)
(* Parameter SlashVS : NP -> VS -> SSlash -> ClSlash . *)
Definition SlashVP : NP -> VPSlash -> ClSlash
                   := fun np vp dobjectClass dobject => apNP np (fun subjectClass subject => vp dobject subjectClass subject).

(* RCl *)
Definition RelVP: RP->VP->RCl:= fun relativePronounIgnored => fun p => p.

Parameter EmptyRelSlash : ClSlash -> RCl .
(* Parameter RelCl : Cl -> RCl . *)
Definition RelSlash : RP -> ClSlash -> RCl := fun rpIgnored cl => cl. (* TODO: Check *)
Definition StrandRelSlash : RP -> ClSlash -> RCl := fun rp cl => cl.

(* RS *)
Definition UseRCl: Temp->Pol->RCl->RS:=fun t p r xClass x => p (r xClass x).

(* RP *)
(* Parameter FunRP : Prep -> NP -> RP -> RP . *)
Parameter IdRP : RP .
Parameter that_RP : RP .

(* Pol *)
Definition PPos:Pol:= fun p=>p.
Definition UncNeg : Pol := fun p => not p.
Definition PNeg : Pol := UncNeg.

(* VPS *)

(* Parameter ConjVPS : Conj -> ListVPS -> VPS . *)
Definition ConjVPS2 : Conj -> Temp -> Pol -> VP -> Temp -> Pol -> VP -> VPS
  := fun conj _t1 pol1 vp1 _t2 pol2 vp2 xClass x => apConj2 conj (pol1 (vp1 xClass x)) (pol2 (vp2 xClass x)).

(* Parameter MkVPS : Temp -> Pol -> VP -> VPS . *)


(* S *)
Definition UseCl: Temp -> Pol -> Cl -> S := fun temp pol cl => temp (pol cl).
Parameter AdvS : Adv -> S -> S .
(* Parameter ConjS : Conj -> ListS -> S . *)
Definition ConjS2 : Conj -> S -> S -> S
                  := fun c s1 s2 => apConj2 c s1 s2.
Definition ExtAdvS : Adv -> S -> S := fun adv s => adv (fun _ => s) IMPERSONAL.
Definition PredVPS : NP -> VPS -> S := fun np vp => apNP np vp.

(* Parameter RelS : S -> RS -> S . *)
(* Parameter SSubjS : S -> Subj -> S -> S . *)

(* PConj *)
(* Parameter NoPConj : PConj . *)
(* Parameter PConjConj : Conj -> PConj . *)

(* Phr *)
Definition Sentence: S->Phr:= fun sentence=> sentence.

Parameter Adverbial : Adv -> Phr .
Parameter Nounphrase : NP -> Phr .
Parameter PAdverbial : PConj -> Adv -> Phr .
Parameter PNounphrase : PConj -> NP -> Phr .
(* Parameter PQuestion : PConj -> QS -> Phr . *)
Parameter PSentence : PConj -> S -> Phr .
(* Parameter PhrUtt : PConj -> Utt -> Voc -> Phr . *)
Parameter Question : QS -> Phr .

(* Ord *)
Definition  OrdSuperl: A->Ord:= fun a=>a.

(* Parameter OrdDigits : Digits -> Ord . *)
Parameter OrdNumeral : Numeral -> Ord .
(* Parameter OrdNumeralSuperl : Numeral -> A -> Ord . *)

(* N2 *)
(* Parameter ComplN3 : N3 -> NP -> N2 . *)
(* Parameter Use2N3 : N3 -> N2 . *)
(* Parameter Use3N3 : N3 -> N2 . *)


(** Lexicon **)

Parameter person_N : N .


Parameter whatPl_IP : IP .
Parameter whatSg_IP : IP .
Parameter whoPl_IP : IP .
Parameter whoSg_IP : IP .
Parameter how8much_IAdv : IAdv .
Parameter how_IAdv : IAdv .
Parameter when_IAdv : IAdv .
Parameter where_IAdv : IAdv .
Parameter why_IAdv : IAdv .

(* VQ *)
Parameter know_VQ : VQ .
Parameter come_cheap_VP : VP .

Parameter and_PConj : PConj .
Parameter but_PConj : PConj .
Parameter otherwise_PConj : PConj .
Parameter that_is_PConj : PConj .
Parameter then_PConj : PConj .
Parameter therefore_PConj : PConj .

Definition all_AdV : AdV := fun vp x => vp x . (* Adds no info *)
Parameter already_AdV : AdV .
Parameter also_AdV : AdV .
Parameter always_AdV : AdV .
Parameter currently_AdV : AdV .
Parameter ever_AdV : AdV .
Parameter never_AdV : AdV .
Parameter now_AdV : AdV .
Parameter still_AdV : AdV .

(*Definition a_few_Det : Det := (cardinal A_FEW, fun (num:Num) (cn : CN) (vp : VP) => (exists x, cn x /\ vp x)).*)
Definition a_few_Det : Det := (cardinal A_FEW, fun (num:Num) (cn : CN) (vp : VP) =>
   A_FEW = CARD (fun x => cn x /\ vp cn x) /\ exists x, cn x /\ vp cn x).

Definition all_Quant : Quant :=fun (num:Num) (cn : CN) (vp : VP) => forall x, cn x->vp cn x.

Definition  a_lot_of_Det : Det:= (singular, fun num cn vp => (exists x, cn x /\ LOTS_OF cn x /\ vp cn x)) . (* Because this is used for "a lot of" is a mass; it's still singular. *)
Parameter another_Det : Det .
Parameter anyPl_Det : Det .
Definition  both_Det :  Det:= (cardinal 2, fun num P Q=> exists x y, (P x /\ Q P x) /\ (P y /\ Q P y) /\ not(x = y)).
Definition each_Det : Det := (unknownNum, all_Quant) .
Definition anySg_Det : Det := each_Det.
Parameter either_Det : Det .
Definition  every_Det : Det:= each_Det.
Definition  all_Det : Det:= every_Det.
Definition few_Det : Det:= (cardinal A_FEW, fun num P Q => CARD (fun x => P x /\ Q P x) <= A_FEW). (* Some tests seem to suggest that "few" does not imply existence, see eg. 044, 076. *)
(* DOUBLE NUM: Note that we ignore the cardinality in the Quantifier part, because "a few three men" make no sense. *)
Set Implicit Arguments. 

Definition  many_Det : Det:= (cardinal MANY, fun num P Q=> (exists x, P x /\ Q P x) /\ (CARD (fun x => P x /\ Q P x) >= MANY)). (* See DOUBLE NUM: above *)
Parameter much_Det : Det .
Definition neither_Det :  Det:= (cardinal 2, fun num P Q=> exists x y, P x /\ not (Q P x) /\ P y /\ not (Q P y) /\ not (x = y)). 
Parameter one_or_more_Det : Det.
Definition somePl_Det : Det:= (plural, fun num P Q=> (exists x,  P x /\ Q P x)) .
(* One would prefer, in this case, to have the cardinality informtion as well, as follows:
  Definition somePl_Det : Det:= (plural, fun num P Q=> (exists x,  P x /\ Q P x) /\ CARD ((fun x =>  P x /\ Q P x)) > 1) .
  This information is tested in 109. But then again, 107 contradicts this interpretation, so we leave the simplest definition for the time being.
*)
Definition someSg_Det : Det:= (singular, fun num P Q=> exists x,  P x /\ Q P x ).
Definition several_Det: Det:= (cardinal SEVERAL, fun num P Q=> (exists x,  P x /\ Q P x) /\ (CARD (fun x => P x /\ Q P x) >= SEVERAL)). (* See DOUBLE NUM: above *)
Parameter twice_as_many_Det : Det .

Parameter elliptic_NP_Pl : NP .
Parameter elliptic_NP_Sg : NP .
Parameter everybody_NP : NP .
Parameter everything_NP : NP .
Parameter nobody_NP : NP .
Parameter nothing_NP : NP .
Parameter somebody_NP : NP .
Parameter something_NP : NP .

(* AdA *)
Parameter almost_AdA : AdA .
Parameter quite_Adv : AdA .
Parameter really_AdA : AdA .
Parameter so_AdA : AdA .
Parameter too_AdA : AdA .
Parameter very_AdA : AdA .

(* Pron *)
Parameter anyone_Pron : Pron .
Definition everyone_Pron : Pron := mkNP unknownNum (fun num (cn : CN) (vp : VP) => forall x, cn x -> vp cn x) person_N.
Parameter heRefl_Pron : Pron .
Parameter he_Pron : Pron .
Parameter i_Pron : Pron .
Parameter itRefl_Pron : Pron .
Parameter it_Pron : Pron .
Definition no_one_Pron : Pron := mkNP unknownNum (fun num (cn : CN) (vp : VP) => forall x, cn x -> not (vp cn x)) person_N.
Parameter nobody_Pron : Pron .
Parameter sheRefl_Pron : Pron .
Parameter she_Pron : Pron .
Definition someone_Pron:Pron:= mkNP singular (fun num (cn : CN) (vp : VP) => exists x, cn x /\ (vp cn x)) person_N.
Parameter theyRefl_Pron : Pron .
Parameter they_Pron : Pron .
Parameter we_Pron : Pron .
Parameter youPl_Pron : Pron .
Parameter youPol_Pron : Pron .
Parameter youSg_Pron : Pron .

(* Predet *)
Definition all_Predet : Predet
  := fun np => let (num,qIGNORED,cn) := np
               in mkNP num all_Quant cn.

Definition at_least_Predet : Predet
  := fun np => let (num,qIGNORED,cn) := np
               in mkNP num (fun num cn vp => interpAtLeast num (CARD (fun x => cn x /\ vp cn x))) cn.
Definition at_most_Predet : Predet := fun np => let (num,qIGNORED,cn) := np
               in mkNP num (fun num cn vp => interpAtMost num (CARD (fun x => cn x /\ vp cn x))) cn.
Definition exactly_Predet : Predet := fun np => let (num,qIGNORED,cn) := np
               in mkNP num (fun num cn vp => interpExactly num (CARD (fun x => cn x /\ vp cn x))) cn.
Definition just_Predet : Predet := exactly_Predet.

Definition MOST_Quant : Quant :=
    fun num (cn : CN) (vp : VP) => CARD (fun x => cn x /\ vp cn x) >= CARD_MOST cn /\ exists x, cn x /\ vp cn x.

Definition  most_Predet : Predet
  := fun np => let (num,qIGNORED,cn0) := np
               in mkNP num MOST_Quant cn0.
Parameter most_of_Predet : Predet .
Parameter not_Predet : Predet .
Parameter only_Predet : Predet .

(* Subj *)

Parameter after_Subj : Subj .
Parameter although_Subj : Subj .
Parameter because_Subj : Subj .
Parameter before_Subj : Subj .
Definition if_Subj : Subj := fun p q => p -> q.
Parameter since_Subj : Subj .
Parameter than_Subj : Subj .
Parameter that_Subj : Subj .
Parameter until_Subj : Subj .
Parameter when_Subj : Subj .
Parameter while_Subj : Subj .

(* Prep *)

Parameter above_Prep : Prep .
Parameter after_Prep : Prep .
Parameter at_Prep : Prep .
Parameter before_Prep : Prep .
Parameter behind_Prep : Prep .
Parameter between_Prep : Prep .
Parameter by8agent_Prep : Prep .
Parameter by8means_Prep : Prep .
Parameter during_Prep : Prep .
Parameter except_Prep : Prep .
Parameter for_Prep : Prep .
Parameter from_Prep : Prep .

Parameter in8front_Prep : Prep .
Parameter in_Prep : Prep .
Parameter on_Prep : Prep .
Parameter out_of_Prep : Prep .
Parameter outside_Prep : Prep .
Parameter part_Prep : Prep .
Parameter possess_Prep : Prep .
Parameter than_Prep : Prep .
Parameter through_Prep : Prep .
Parameter to_Prep : Prep .
Parameter under_Prep : Prep .
Parameter with_Prep : Prep .
Parameter within_Prep : Prep .
Parameter without_Prep : Prep .

(* CAdv *)
Parameter as_CAdv : CAdv .
Parameter less_CAdv : CAdv .
Parameter more_CAdv : CAdv .

Parameter allow_V2V : V2V .
Parameter bring_V2V : V2V .
Parameter elliptic_V2V : V2V .
Parameter see_V2V : V2V .
Parameter take_V2V : V2V .

Parameter suggest_to_V2S : V2S .

Parameter believe_VS : VS .
Parameter claim_VS : VS .
Parameter discover_VS : VS .
Parameter know_VS : VS .
Parameter say_VS : VS .

Parameter less_than_AdN : AdN .
Definition more_than_AdN : AdN := moreThan .

Parameter impressed_by_A2 : A2 .

Definition andSg_Conj : Conj := Associative (fun p q => p /\ q).
Definition and_Conj : Conj := Associative (fun p q => p /\ q).
(* Parameter both7and_DConj : Conj . *)
Parameter comma_and_Conj : Conj .
Definition either7or_DConj : Conj := EitherOr.
Parameter if_comma_then_Conj : Conj .
(* Parameter if_then_Conj : Conj . *)
Definition or_Conj : Conj  := Associative (fun p q => p \/ q).
Parameter semicolon_and_Conj : Conj .

Parameter can8know_VV : VV .
Parameter can_VV : VV .
Parameter do_VV : VV .
Parameter finish_VV : VV .
Parameter going_to_VV : VV .
Parameter manage_VV : VV .
Parameter must_VV : VV .
Parameter need_VV : VV .
Parameter shall_VV : VV .
Parameter start_VV : VV .
Parameter try_VV : VV .
Parameter use_VV : VV .
Parameter want_VV : VV .
Parameter chairman_N2 : N2.
Definition chairman_N : N :=  fun o => exists institution, chairman_N2 institution o.
Parameter group_N2 : N2 .
Parameter inhabitant_N2 : N2 .
Parameter nobel_prize_N2 : N2 .
Parameter resident_in_N2 : N2 .
Parameter resident_on_N2 : N2 .

Parameter N_10 : Numeral .
Parameter N_100 : Numeral .
Parameter N_13 : Numeral .
Parameter N_14 : Numeral .
Parameter N_15 : Numeral .
Parameter N_150 : Numeral .
Parameter N_2 : Numeral .
Definition N_2500 : Numeral := 2500.
Definition N_3000 : Numeral := 3000.
Definition N_4 : Numeral := 4.
Definition N_500 : Numeral := 500.
Definition N_5500 : Numeral := 5500.
Parameter N_8 : Numeral .
Parameter N_99 : Numeral .
Parameter N_eight : Numeral .
Definition N_eleven : Numeral := 11 .
Parameter N_five : Numeral .
Parameter N_fortyfive : Numeral .
Parameter N_four : Numeral .
Definition N_one : Numeral := 1.
Definition N_six : Numeral := 6.
Definition N_sixteen : Numeral := 16.
Definition N_ten : Numeral := 10.
Definition N_three : Numeral := 3.
Definition N_twenty : Numeral := 20.
Definition N_two : Numeral := 2.
(* Parameter digits2num : Digits -> Numeral . *)
(* Parameter num : Sub1000000 -> Numeral . *)
Parameter beat_V : V .
Parameter come_in_V : V .
Parameter continue_V : V .
Parameter crash_V : V .
Parameter elliptic_V : V .
Parameter exist_V : V .
Parameter expand_V : V .
Parameter gamble_V : V .
Parameter go8travel_V : V .
Parameter go8walk_V : V .
Parameter graduate_V : V .
Parameter increase_V : V .
Parameter leave_V : V .
Parameter live_V : V .
Parameter meet_V : V .
Parameter start_V : V .
Parameter stop_V : V .
Parameter swim_V : V .
Parameter travel_V : V .
Parameter work_V : V .

Parameter award_V3 : V3 .
Parameter contribute_to_V3 : V3 .
Parameter deliver_V3 : V3 .
Parameter obtain_from_V3 : V3 .
Parameter put_in_V3 : V3 .
Parameter rent_from_V3 : V3 .
Parameter tell_about_V3 : V3 .

Parameter anywhere_Adv : Adv .
Parameter at_8_am_Adv : Adv .
Parameter at_a_quarter_past_five_Adv : Adv .
Parameter at_five_oclock_Adv : Adv .
Parameter at_four_oclock_Adv : Adv .
Parameter at_home_Adv : VeridicalAdv .
Parameter at_least_four_times : Adv .
Parameter at_some_time_Adv : Adv .
Parameter at_the_same_time_Adv : Adv .
Parameter by_11_am_Adv : Adv .
Parameter ever_since_Adv : Adv .
Parameter every_month_Adv : Adv .
Parameter every_week_Adv : Adv .
Parameter everywhere_Adv : Adv .
Parameter for_8_years_Adv : Adv .
Parameter for_a_total_of_15_years_or_more_Adv : Adv .
Parameter for_a_year_Adv : Adv .
Parameter for_an_hour_Adv : Adv .
Parameter for_exactly_a_year_Adv : Adv .
Parameter for_more_than_10_years_Adv : Adv .
Parameter for_more_than_two_years_Adv : Adv .
Parameter for_three_days_Adv : Adv .
Parameter for_two_hours_Adv : Adv .
Parameter for_two_years_Adv : VeridicalAdv .
Parameter friday_13th_Adv : Adv .
Parameter from_1988_to_1992_Adv : Adv .
Parameter here7from_Adv : Adv .
Parameter here7to_Adv : Adv .
Parameter here_Adv : Adv .
Parameter in_1990_Adv : VeridicalAdv .
Parameter in_1991_Adv : VeridicalAdv .
Parameter in_1992_Adv : VeridicalAdv .
Parameter in_1993_Adv : VeridicalAdv .
Parameter in_1994_Adv : VeridicalAdv .
Parameter in_a_few_weeks_Adv : Adv .
Parameter in_a_months_time_Adv : Adv .
Parameter in_july_1994_Adv : Adv .
Parameter in_march_1993_Adv : Adv .
Parameter in_march_Adv : Adv .
Parameter in_one_hour_Adv : Adv .
Parameter in_the_coming_year_Adv : Adv .
Parameter in_the_past_Adv : Adv .
Parameter in_two_hours_Adv : Adv .
Parameter last_week_Adv : Adv .
Parameter late_Adv : Adv .
Parameter long_Adv : Adv .
Parameter on_friday_Adv : Adv .
Parameter on_july_4th_1994_Adv : Adv .
Parameter on_july_8th_1994_Adv : Adv .
Parameter on_monday_Adv : Adv .
Parameter on_the_5th_of_may_1995_Adv : Adv .
Parameter on_the_7th_of_may_1995_Adv : Adv .
Parameter on_thursday_Adv : Adv .
Parameter on_time_Adv : VeridicalAdv .
Parameter on_tuesday_Adv : Adv .
Parameter on_wednesday_Adv : Adv .
Parameter over_Adv : Adv .
Parameter part_time_Adv : Adv .
Parameter saturday_july_14th_Adv : Adv .
Parameter since_1992_Adv : Adv .
Parameter somewhere_Adv : Adv .
Parameter the_15th_of_may_1995_Adv : Adv .
Parameter there7from_Adv : Adv .
Parameter there7to_Adv : Adv .
Parameter there_Adv : Adv .
Parameter together_Adv : Adv .
Parameter too_Adv : Adv .
Parameter twice_Adv : Adv .
Parameter two_years_from_now_Adv : Adv .
Parameter year_1996_Adv : Adv .
Parameter yesterday_Adv : Adv .

Parameter alan_PN : PN .
Parameter anderson_PN : PN .
Parameter apcom_PN : PN .
Parameter berlin_PN : PN .
Parameter bill_PN : PN .
Parameter birmingham_PN : PN .
Parameter bt_PN : PN .
Parameter bug_32985_PN : PN .
Parameter cambridge_PN : PN .
Parameter carl_PN : PN .
Parameter europe_PN : PN .
Parameter fido_PN : PN .
Parameter florence_PN : PN .
Parameter frank_PN : PN .
Parameter gfi_PN : PN .
Parameter helen_PN : PN .
Parameter icm_PN : PN .
Parameter itel_PN : PN .
Parameter john_PN : PN .
Parameter katmandu_PN : PN .
Parameter luxembourg_PN : PN .
Parameter mary_PN : PN .
Parameter mfi_PN : PN .
Parameter mtalk_PN : PN .
Parameter paris_PN : PN .
Parameter pavarotti_PN : PN .
Parameter peter_PN : PN .
Parameter portugal_PN : PN .
Parameter r95103_PN : PN .
Parameter scandinavia_PN : PN .
Parameter southern_europe_PN : PN .
Parameter sue_PN : PN .
Parameter sweden_PN : PN .
Parameter the_cia_PN : PN .
Parameter the_m25_PN : PN .

Parameter ambitious_A : A .
Parameter ancient_A : A .
Parameter asleep_A : A .
Parameter blue_A : A .
Parameter british_A : IntersectiveA .
Parameter broke_A : A .
Parameter canadian_A : A .
Parameter clever_A : SubsectiveA .
Parameter competent_A : SubsectiveA .
Parameter crucial_A : A .
Parameter dedicated_A : A .
Parameter different_A : A .
Parameter employed_A : A .
Parameter excellent_A : SubsectiveA .
Parameter false_A : PrivativeA.
Parameter fast_A : SubsectiveA .
Parameter fat_A : ExtensionalSubsectiveA .
Parameter female_A : IntersectiveA .
Parameter former_A : PrivativeA .
Parameter fourlegged_A : IntersectiveA .
Parameter free_A : A .
Parameter furious_A : A .
Parameter genuine_A : IntersectiveA .
Parameter german_A : IntersectiveA .
Parameter great_A : SubsectiveA .
Parameter important_A : A .
Parameter indispensable_A : SubsectiveA .
Parameter interesting_A : IntersectiveA .
Parameter irish_A : IntersectiveA .
Parameter italian_A : IntersectiveA .
Parameter known_A : A .
Parameter large_A : SubsectiveA .
Parameter leading_A : SubsectiveA .
Parameter legal_A : A .
Parameter likely_A : SubsectiveA .
Parameter major_A : SubsectiveA .
Parameter male_A : IntersectiveA .
Parameter many_A : IntersectiveA .
Parameter missing_A : A .
Parameter modest_A : A .
Parameter national_A : A .
Parameter new_A : A .
Parameter north_american_A : IntersectiveA .
Parameter noted_A : A .
Parameter own_A : A .
Parameter poor8bad_A : A .
Parameter poor8penniless_A : A .
Parameter portuguese_A : IntersectiveA .
Parameter present8attending_A : A .
Parameter present8current_A : A .
Parameter previous_A : A .
Parameter red_A : A .
Parameter resident_A : A .
Parameter scandinavian_A : A .
Parameter serious_A : A .
Parameter slow_A : SubsectiveA .
Parameter small_A : SubsectiveA .
Parameter successful_A : SubsectiveA .
Parameter swedish_A : IntersectiveA .
Parameter true_A : IntersectiveA.
Parameter unemployed_A : A .
Parameter western_A : A .

Parameter accountant_N : N .
Parameter agenda_N : N .
Parameter animal_N : N .
Parameter apcom_contract_N : N .
Parameter apcom_manager_N : N .
Parameter auditor_N : N .
Parameter authority_N : N .
Parameter board_meeting_N : N .
Parameter boss_N : N .
Parameter business_N : N .
Parameter businessman_N : N .
Parameter car_N : N .
Parameter case_N : N .
Parameter chain_N : N .
Parameter charity_N : N .
Parameter clause_N : N .
Parameter client_N : N .
Parameter colleague_N : N .
Parameter commissioner_N : N .
Parameter committee_N : N .
Parameter committee_member_N : N .
Parameter company_N : N .
Parameter company_car_N : N .
Parameter company_director_N : N .
Parameter computer_N : N .
Parameter concert_N : N .
Parameter conference_N : N .
Parameter continent_N : N .
Parameter contract_N : N .
Parameter copy_N : N .
Parameter country_N : N .
Parameter cover_page_N : N .
Parameter customer_N : N .
Parameter day_N : N .
Parameter delegate_N : N .
Parameter demonstration_N : N .
Parameter department_N : N .
Parameter desk_N : N .
Parameter diamond_N : N .
Parameter editor_N : N .
Parameter elephant_N : N .
Parameter european_N : N .
Parameter executive_N : N .
Parameter factory_N : N .
Parameter fee_N : N .
Parameter file_N : N .
Parameter greek_N : N .
Parameter hard_disk_N : N .
Parameter heart_N : N .
Parameter hour_N : N .
Parameter house_N : N .
Parameter individual_N : N .
Parameter invoice_N : N .
Parameter irishman_N : N .
Parameter italian_N : N .
Parameter itel_computer_N : N .
Parameter itelxz_N : N .
Parameter itelzx_N : N .
Parameter itelzy_N : N .
Parameter item_N : N .
Parameter job_N : N .
Parameter labour_mp_N : N .
Parameter laptop_computer_N : N .
Parameter law_lecturer_N : N .
Parameter lawyer_N : N .
Parameter line_N : N .
Parameter literature_N : N .
Parameter lobby_N : N .
Parameter loss_N : N .
Parameter machine_N : N .
Parameter mammal_N : N .
Parameter man_N : N .
Parameter meeting_N : N .
Parameter member_N : N .
Parameter member_state_N : N .
Parameter memoir_N : N .
Parameter mips_N : N .
Parameter moment_N : N .
Parameter mortgage_interest_N : N .
Parameter mouse_N : N .
Parameter newspaper_N : N .
Definition nobel_prize_N : N := fun o => exists x, nobel_prize_N2 x o.
Parameter note_N : N .
Parameter novel_N : N .
Parameter office_building_N : N .
Parameter one_N : N .
Parameter order_N : N .
Parameter paper_N : N .
Parameter payrise_N : N .
Parameter pc6082_N : N .
Parameter performance_N : N .
Parameter philosopher_N : N .
Parameter phone_N : N .
Parameter politician_N : N .
Parameter popular_music_N : N .
Parameter program_N : N .
Parameter progress_report_N : N .
Parameter project_proposal_N : N .
Parameter proposal_N : N .
Parameter report_N : N .
Parameter representative_N : N .
Parameter resident_N : N .
Parameter result_N : N .
Parameter right_N : N .
Parameter sales_department_N : N .
Parameter scandinavian_N : N .
Parameter secretary_N : N .
Parameter service_contract_N : N .
Parameter shore_N : N .
Parameter software_fault_N : N .
Parameter species_N : N .
Parameter station_N : N .
Parameter stockmarket_trader_N : N .
Parameter story_N : N .
Parameter student_N : N .
Parameter survey_N : N .
Parameter swede_N : N .
Parameter system_N : N .
Parameter system_failure_N : N .
Parameter taxi_N : N .
Parameter temper_N : N .
Parameter tenor_N : N .
Parameter time_N : N .
Parameter today_N : N .
Parameter traffic_N : N .
Parameter train_N : N .
Parameter university_graduate_N : N .
Parameter university_student_N : N .
Parameter week_N : N .
Parameter wife_N : N .
Parameter woman_N : N .
Parameter workstation_N : N .
Parameter world_N : N .
Parameter year_N : N .

Parameter MICKEY : object.
Parameter MICKEY_ANIM : animal_N MICKEY.
Definition mickey_PN := mkPN MICKEY animal_N MICKEY_ANIM  .
Parameter DUMBO : object.
Parameter DUMBO_ANIM : animal_N DUMBO.
Definition dumbo_PN := mkPN DUMBO animal_N DUMBO_ANIM .
Parameter jones : object.
Parameter jones_PERSON : person_N jones.
Definition jones_PN := mkPN jones person_N jones_PERSON.

Parameter SMITH : object.
Parameter SMITH_PERSON : person_N SMITH.
Definition smith_PN := mkPN SMITH person_N SMITH_PERSON.

Parameter KIM : object.
Parameter KIM_PERSON : person_N KIM.
Definition kim_PN := mkPN KIM person_N KIM_PERSON.

Parameter PC6082 : object.
Parameter PC6082_COMPY : computer_N PC6082.
Definition pc_6082_PN := mkPN PC6082 computer_N PC6082_COMPY.

Parameter ITEL_XZ : object.
Parameter ITEL_XZ_COMPY : computer_N ITEL_XZ.
Definition itel_xz_PN := mkPN ITEL_XZ computer_N ITEL_XZ_COMPY.
(* Syntactic replacement FIXME: it could also be possible to add environment (pc6082_N) = itel_xz_PN ; but then we also need environment to return a default class. *)
(* Definition the_pc6082_NP : NP := (DetCN (DetQuant (DefArt) (NumSg)) (UseN (pc6082_N))). *)
Definition the_pc6082_NP : NP := UsePN pc_6082_PN.

(* Definition the_itel_xz_NP : NP := (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelxz_N))). *)
Definition the_itel_xz_NP : NP := UsePN itel_xz_PN.

Parameter accept_V2 : V2 .
Parameter answer_V2 : V2 .
Parameter appoint_V2 : V2 .
Parameter arrive_in_V2 : V2 .
Parameter attend_V2 : V2 .
Parameter award_and_be_awarded_V2 : V2 .
Parameter become_V2 : V2 .
Parameter blame1_V2 : V2 .
Parameter blame2_V2 : V2 .
Parameter build_V2 : V2 .
Parameter buy_V2 : V2 .
Parameter catch_V2 : V2 .
Parameter chair_V2 : V2 .
Parameter cost_V2 : V2 .
Parameter cross_out_V2 : V2 .
Parameter deliver_V2 : V2 .
Parameter destroy_V2 : V2 .
Parameter develop_V2 : V2 .
Parameter discover_V2 : V2 .
Parameter dupe_V2 : V2 .
Parameter find_V2 : V2 .
Parameter finish_V2 : V2 .
Parameter found_V2 : V2 .
Parameter get_V2 : V2 .
Parameter hate_V2 : V2 .
Parameter have_V2 : V2 .
Parameter hurt_V2 : V2 .
Parameter last_V2 : V2 .
Parameter leave_V2 : V2 .
Parameter like_V2 : V2 .
Parameter lose_V2 : V2 .
Parameter maintain_V2 : V2 .
Parameter make8become_V2 : V2 .
Parameter make8do_V2 : V2 .
Parameter need_V2 : V2 .
Parameter open_V2 : V2 .
Parameter own_V2 : V2 .
Parameter pay_V2 : V2 .
Parameter publish_V2 : V2 .
Parameter read_V2 : V2 .
Parameter read_out_V2 : V2 .
Parameter remove_V2 : V2 .
Parameter represent_V2 : V2 .
Parameter revise_V2 : V2 .
Parameter run_V2 : V2 .
Parameter sell_V2 : V2 .
Parameter send_V2 : V2 .
Parameter sign_V2 : V2 .
Parameter sing_V2 : V2 .
Parameter speak_to_V2 : V2 .
Parameter spend_V2 : V2 .
Parameter take_V2 : V2 .
Parameter take_part_in_V2 : V2 .
Parameter update_V2 : V2 .
Parameter use_V2 : V2 .
Parameter vote_for_V2 : V2 .
Parameter win_V2 : V2 .
Parameter work_in_V2 : V2 .
Parameter write_V2 : V2 .
Parameter write_to_V2 : V2 .

(** Knowledge **)
Parameter wantCovariant_K : forall p q:VP, forall s, (forall xClass x, p xClass x -> q xClass x) -> want_VV q s -> want_VV p s.

Variable  person_K: forall x:object, chairman_N(x)-> person_N(x). 
Variable  committee_member_person_K : forall x, committee_member_N x -> person_N x.

Variable Not_stop_means_continue_K : forall x, stop_V x /\ continue_V x -> False.

Definition opposite_adjectives : A -> A -> Prop
  := fun a1 a2 =>
  forall cn o,  let (mSmall,threshSmall,_) := a1 in
                let (mLarge,threshLarge,_) := a2 in
               (   (mSmall cn o = 0 - mLarge cn o)
                /\ (1 <= threshLarge + threshSmall)).

Variable small_and_large_opposite_K : opposite_adjectives small_A large_A.
Variable fast_and_slow_opposite_K   : opposite_adjectives slow_A  fast_A.

Require Import Psatz.

Variable ineqAdd : forall {a b c d}, (a <= b) -> (c <= d) -> (a + c <= b + d).

Parameter le_trans' : forall {x y z:Z}, x <= y -> y <= z -> x <= z.

Opaque Z.le.
Lemma small_and_large_disjoint_K : forall cn o, apA small_A cn o -> apA large_A cn o -> False.
cbv.
assert (SLK := small_and_large_opposite_K).
destruct small_A as [smallness smallThres].
destruct large_A as [largeness largeThres].
intros cn o [small cno] [large _].
destruct (SLK cn o) as [neg disj].
(*rewrite -> neg in small.
assert (oops := le_trans' disj (ineqAdd large small)).
ring_simplify in oops.
*)
lia.
Qed.
(* Coq: opps -> False  *)



(** Treebank **)
Definition s_001_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (italian_N))) (ComplSlash (SlashV2a (become_V2)) (DetCN (DetQuantOrd (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (world_N)))) (NumSg) (OrdSuperl (great_A))) (UseN (tenor_N))))))).
Definition s_001_3_h := (Sentence (UseCl (Past) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumSg)) (RelCN (UseN (italian_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (become_V2)) (DetCN (DetQuantOrd (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (world_N)))) (NumSg) (OrdSuperl (great_A))) (UseN (tenor_N))))))))))).
Definition s_002_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (AdjCN (PositA (italian_A)) (UseN (man_N)))) (ComplVV (want_VV) (UseComp (CompCN (AdjCN (PositA (great_A)) (UseN (tenor_N))))))))).
Definition s_002_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (somePl_Det) (AdjCN (PositA (italian_A)) (UseN (man_N)))) (UseComp (CompCN (AdjCN (PositA (great_A)) (UseN (tenor_N)))))))).
Definition s_002_4_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (italian_A)) (UseN (man_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplVV (want_VV) (UseComp (CompNP (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (great_A)) (UseN (tenor_N)))))))))))))).
Definition s_003_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (italian_A)) (UseN (man_N))))) (ComplVV (want_VV) (UseComp (CompNP (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (great_A)) (UseN (tenor_N)))))))))).
Eval cbv in ( (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (italian_A)) (UseN (man_N))))).
Definition s_003_2_p := s_002_2_p.
Definition s_003_4_h := s_002_4_h.
Definition s_004_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det) (AdjCN (PositA (italian_A)) (UseN (tenor_N)))) (ComplVV (want_VV) (UseComp (CompAP (PositA (great_A)))))))).
Definition s_004_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (somePl_Det) (AdjCN (PositA (italian_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (great_A))))))).
Definition s_004_4_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (italian_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplVV (want_VV) (UseComp (CompAP (PositA (great_A)))))))))))).
Definition s_005_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (AdjCN (AdAP (really_AdA) (PositA (ambitious_A))) (UseN (tenor_N)))) (UseComp (CompAP (PositA (italian_A))))))).
Definition s_005_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (AdAP (really_AdA) (PositA (ambitious_A))) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (italian_A))))))))))).
Definition s_006_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumPl)) (AdjCN (AdAP (really_AdA) (PositA (great_A))) (UseN (tenor_N)))) (UseComp (CompAP (PositA (modest_A))))))).
Definition s_006_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (AdAP (really_AdA) (PositA (great_A))) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (modest_A))))))))))).
Definition s_007_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (somePl_Det) (AdjCN (PositA (great_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (swedish_A))))))).
Definition s_007_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (great_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (swedish_A))))))))))).
Definition s_008_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (many_Det) (AdjCN (PositA (great_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (german_A))))))).
Definition s_008_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (great_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (german_A))))))))))).
Definition s_009_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (several_Det) (AdjCN (PositA (great_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (british_A))))))).
Definition s_009_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (great_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (british_A))))))))))).
Definition s_010_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (great_A)) (UseN (tenor_N))))) (UseComp (CompAP (PositA (italian_A))))))).
Definition s_010_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (great_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (italian_A))))))))))).
Definition s_011_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (a_few_Det) (AdjCN (PositA (great_A)) (UseN (tenor_N)))) (ComplSlash (SlashV2a (sing_V2)) (MassNP (UseN (popular_music_N))))))).
Definition s_011_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (somePl_Det) (AdjCN (PositA (great_A)) (UseN (tenor_N)))) (ComplSlash (SlashV2a (like_V2)) (MassNP (UseN (popular_music_N))))))).
Definition s_011_4_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (great_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (sing_V2)) (MassNP (UseN (popular_music_N))))))))))).
Definition s_012_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (few_Det) (AdjCN (PositA (great_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (poor8penniless_A))))))).
Definition s_012_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (great_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (poor8penniless_A))))))))))).
Definition s_013_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (both_Det) (AdjCN (PositA (leading_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (excellent_A))))))).
Definition s_013_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (AdjCN (PositA (leading_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (excellent_A)))))))) (UseComp (CompAP (PositA (indispensable_A))))))).
Definition s_013_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (both_Det) (AdjCN (PositA (leading_A)) (UseN (tenor_N)))) (UseComp (CompAP (PositA (indispensable_A))))))).
Definition s_014_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (neither_Det) (AdjCN (PositA (leading_A)) (UseN (tenor_N)))) (come_cheap_VP)))).
Definition s_014_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (AdvNP (DetNP (DetQuant (IndefArt) (NumSg))) (PrepNP (part_Prep) (DetCN (DetQuant (DefArt) (NumPl)) (AdjCN (PositA (leading_A)) (UseN (tenor_N)))))) (UseComp (CompNP (UsePN (pavarotti_PN))))))).
Definition s_014_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (pavarotti_PN)) (UseComp (CompCN (RelCN (AdjCN (PositA (leading_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (come_cheap_VP))))))))).
Definition s_015_1_p := (Sentence (UseCl (Future) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_three)))) (UseN (tenor_N)))) (ComplSlash (SlashV2a (take_part_in_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (concert_N))))))).
Definition s_015_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (tenor_N)) (UseRCl (Future) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (take_part_in_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (concert_N))))))))))).
Definition s_016_1_p := (Sentence (UseCl (Future) (PPos) (PredVP (PredetNP (at_most_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (tenor_N)))) (ComplSlash (Slash3V3 (contribute_to_V3) (MassNP (UseN (charity_N)))) (DetCN (DetQuant (PossPron (theyRefl_Pron)) (NumPl)) (UseN (fee_N))))))).
Definition s_016_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (tenor_N)) (UseRCl (Future) (PPos) (RelVP (IdRP) (ComplSlash (Slash3V3 (contribute_to_V3) (MassNP (UseN (charity_N)))) (DetCN (DetQuant (PossPron (theyRefl_Pron)) (NumPl)) (UseN (fee_N))))))))))).
Definition s_017_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (irishman_N))) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (ComplN2 (nobel_prize_N2) (MassNP (UseN (literature_N))))))))).
Definition s_017_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (irishman_N))) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (nobel_prize_N))))))).
Definition s_018_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (european_N))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_018_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (european_N))) (UseComp (CompCN (UseN (person_N))))))).
Definition s_018_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (RelCN (UseN (person_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN)))))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_018_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (european_N))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_019_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_019_2_p := s_018_2_p.
Definition s_019_3_p := s_018_3_p.
Definition s_019_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_020_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det) (UseN (european_N))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_020_2_p := s_018_2_p.
Definition s_020_3_p := s_018_3_p.
Definition s_020_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det) (UseN (european_N))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_021_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (member_state_N))))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_021_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (member_state_N)))))) (UseComp (CompCN (UseN (individual_N))))))).
Definition s_021_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (RelCN (UseN (individual_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN)))))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_021_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (member_state_N))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_022_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumSg)) (UseN (delegate_N))) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N)))) (on_time_Adv))))).
Definition s_022_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumSg)) (UseN (delegate_N))) (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))))).
Definition s_023_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (somePl_Det) (UseN (delegate_N))) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (survey_N)))) (on_time_Adv))))).
Definition s_023_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (somePl_Det) (UseN (delegate_N))) (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (survey_N))))))).
Definition s_024_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (many_Det) (UseN (delegate_N))) (ComplSlash (Slash3V3 (obtain_from_V3) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (survey_N)))) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (interesting_A)) (UseN (result_N)))))))).
Definition s_024_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (many_Det) (UseN (delegate_N))) (ComplSlash (Slash3V3 (obtain_from_V3) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (survey_N)))) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (result_N))))))).
Definition s_025_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (several_Det) (UseN (delegate_N))) (AdvVP (ComplSlash (SlashV2a (get_V2)) (PPartNP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (result_N))) (publish_V2))) (PrepNP (in_Prep) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (major_A)) (AdjCN (PositA (national_A)) (UseN (newspaper_N)))))))))).
Definition s_025_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (several_Det) (UseN (delegate_N))) (ComplSlash (SlashV2a (get_V2)) (PPartNP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (result_N))) (publish_V2)))))).
Definition s_026_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (UseComp (CompAP (AdvAP (PositA (resident_A)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))).
Definition s_026_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (UseComp (CompCN (UseN (person_N))))))).
Definition s_026_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (AdvAP (PositA (resident_A)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_026_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_027_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (a_few_Det) (UseN (committee_member_N))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (sweden_PN)))))))).
Definition s_027_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (committee_member_N)))) (UseComp (CompCN (UseN (person_N))))))).
Definition s_027_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (sweden_PN)))))))))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (scandinavia_PN)))))))).
Definition s_027_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (a_few_Det) (UseN (committee_member_N)))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (scandinavia_PN)))))))).
Definition s_028_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (few_Det) (UseN (committee_member_N))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (portugal_PN)))))))).
Definition s_028_2_p := s_027_2_p.
Definition s_028_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (portugal_PN)))))))))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (southern_europe_PN)))))))).
Definition s_028_5_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (few_Det) (AdvCN (UseN (committee_member_N)) (PrepNP (from_Prep) (UsePN (southern_europe_PN)))))))).
Definition s_029_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (both_Det) (UseN (commissioner_N))) (ComplVV (use_VV) (UseComp (CompCN (AdjCN (PositA (leading_A)) (UseN (businessman_N))))))))).
Definition s_029_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (both_Det) (UseN (commissioner_N))) (ComplVV (use_VV) (UseComp (CompCN (UseN (businessman_N)))))))).
Definition s_030_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (neither_Det) (UseN (commissioner_N))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (DetCN (a_lot_of_Det) (UseN (time_N)))) (at_home_Adv))))).
Definition s_030_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (neither_Det) (UseN (commissioner_N))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (MassNP (UseN (time_N)))) (at_home_Adv))))).
Definition s_031_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_three)))) (UseN (commissioner_N)))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (DetCN (a_lot_of_Det) (UseN (time_N)))) (at_home_Adv))))).
Definition s_031_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_three)))) (UseN (commissioner_N)))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (MassNP (UseN (time_N)))) (at_home_Adv))))).
Definition s_032_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_most_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (UseN (commissioner_N)))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (DetCN (a_lot_of_Det) (UseN (time_N)))) (at_home_Adv))))).
Definition s_032_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_most_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (UseN (commissioner_N)))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (MassNP (UseN (time_N)))) (at_home_Adv))))).
Definition s_033_1_p := s_017_3_h.
Definition s_033_3_h := s_017_1_p.
Definition s_034_1_p := s_018_5_h.
Definition s_034_2_p := s_018_2_p.
Definition s_034_3_p := s_018_3_p.
Definition s_034_5_h := s_018_1_p.
Definition s_035_1_p := s_019_5_h.
Definition s_035_2_p := s_018_2_p.
Definition s_035_3_p := s_018_3_p.
Definition s_035_5_h := s_019_1_p.
Definition s_036_1_p := s_020_5_h.
Definition s_036_2_p := s_018_2_p.
Definition s_036_3_p := s_018_3_p.
Definition s_036_5_h := s_020_1_p.
Definition s_037_1_p := s_021_5_h.
Definition s_037_2_p := s_021_2_p.
Definition s_037_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (RelCN (UseN (individual_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (AdvVP (UseV (live_V)) (anywhere_Adv)) (PrepNP (in_Prep) (UsePN (europe_PN)))))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_037_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (member_state_N))))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (AdvVP (UseV (live_V)) (anywhere_Adv)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_038_1_p := s_022_3_h.
Definition s_038_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (someSg_Det) (UseN (delegate_N))) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N)))) (on_time_Adv))))).
Definition s_039_1_p := s_023_3_h.
Definition s_039_3_h := s_023_1_p.
Definition s_040_1_p := s_024_3_h.
Definition s_040_3_h := s_024_1_p.
Definition s_041_1_p := s_025_3_h.
Definition s_041_3_h := s_025_1_p.
Definition s_042_1_p := s_026_5_h.
Definition s_042_2_p := s_026_2_p.
Definition s_042_3_p := s_026_3_p.
Definition s_042_5_h := s_026_1_p.
Definition s_043_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (a_few_Det) (UseN (committee_member_N))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (scandinavia_PN)))))))).
Definition s_043_2_p := s_027_2_p.
Definition s_043_3_p := s_027_3_p.
Definition s_043_5_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (a_few_Det) (UseN (committee_member_N)))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (sweden_PN)))))))).
Definition s_044_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (few_Det) (UseN (committee_member_N))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (southern_europe_PN)))))))).
Definition s_044_2_p := s_027_2_p.
Definition s_044_3_p := s_028_3_p.
Definition s_044_5_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (few_Det) (AdvCN (UseN (committee_member_N)) (PrepNP (from_Prep) (UsePN (portugal_PN)))))))).
Definition s_045_1_p := s_029_3_h.
Definition s_045_3_h := s_029_1_p.
Definition s_046_1_p := s_030_3_h.
Definition s_046_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (AdvNP (DetNP (DetQuant (IndefArt) (NumSg))) (PrepNP (part_Prep) (DetCN (DetQuant (DefArt) (NumPl)) (UseN (commissioner_N))))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (DetCN (a_lot_of_Det) (UseN (time_N)))) (at_home_Adv))))).
Definition s_047_1_p := s_031_3_h.
Definition s_047_3_h := s_031_1_p.
Definition s_048_1_p := s_032_3_h.
Definition s_048_3_h := s_032_1_p.
Definition s_049_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (swede_N))) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (nobel_prize_N))))))).
Definition s_049_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (swede_N))) (UseComp (CompCN (UseN (scandinavian_N))))))).
Definition s_049_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (scandinavian_N))) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (nobel_prize_N))))))).
Definition s_050_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (AdjCN (PositA (canadian_A)) (UseN (resident_N)))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_050_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (AdjCN (PositA (canadian_A)) (UseN (resident_N)))) (UseComp (CompCN (ComplN2 (resident_on_N2) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (north_american_A)) (UseN (continent_N)))))))))).
Definition s_050_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (ComplN2 (resident_on_N2) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (north_american_A)) (UseN (continent_N)))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_051_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (canadian_A)) (UseN (resident_N))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_051_2_p := s_050_2_p.
Definition s_051_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (ComplN2 (resident_on_N2) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (north_american_A)) (UseN (continent_N))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_052_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det) (AdjCN (PositA (canadian_A)) (UseN (resident_N)))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_052_2_p := s_050_2_p.
Definition s_052_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det) (ComplN2 (resident_on_N2) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (north_american_A)) (UseN (continent_N)))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_053_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (major_A)) (AdjCN (PositA (western_A)) (UseN (country_N))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_053_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (major_A)) (AdjCN (PositA (western_A)) (UseN (country_N)))))))) (UseComp (CompCN (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (western_A)) (UseN (country_N)))))))))).
Definition s_053_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (western_A)) (UseN (country_N)))))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_054_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumSg)) (AdjCN (PositA (scandinavian_A)) (UseN (delegate_N)))) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N)))) (on_time_Adv))))).
Definition s_054_3_h := s_038_3_h.
Definition s_055_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (somePl_Det) (AdjCN (PositA (irish_A)) (UseN (delegate_N)))) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (survey_N)))) (on_time_Adv))))).
Definition s_055_3_h := s_023_1_p.
Definition s_056_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (many_Det) (AdjCN (PositA (british_A)) (UseN (delegate_N)))) (ComplSlash (Slash3V3 (obtain_from_V3) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (survey_N)))) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (interesting_A)) (UseN (result_N)))))))).
Definition s_056_3_h := s_024_1_p.
Definition s_057_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (several_Det) (AdjCN (PositA (portuguese_A)) (UseN (delegate_N)))) (AdvVP (ComplSlash (SlashV2a (get_V2)) (PPartNP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (result_N))) (publish_V2))) (PrepNP (in_Prep) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (major_A)) (AdjCN (PositA (national_A)) (UseN (newspaper_N)))))))))).
Definition s_057_3_h := s_025_1_p.
Definition s_058_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (european_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (AdvVP (UseComp (CompAP (PositA (resident_A)))) (PrepNP (in_Prep) (UsePN (europe_PN))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_058_3_h := s_026_5_h.
Definition s_059_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (a_few_Det) (AdjCN (PositA (female_A)) (UseN (committee_member_N)))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (scandinavia_PN)))))))).
Definition s_059_3_h := s_027_5_h.
Definition s_060_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (few_Det) (AdjCN (PositA (female_A)) (UseN (committee_member_N)))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (southern_europe_PN)))))))).
Definition s_060_3_h := s_044_1_p.
Definition s_061_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (both_Det) (AdjCN (PositA (female_A)) (UseN (commissioner_N)))) (ComplVV (use_VV) (UseComp (CompAdv (PrepNP (in_Prep) (MassNP (UseN (business_N)))))))))).
Definition s_061_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (both_Det) (UseN (commissioner_N))) (ComplVV (use_VV) (UseComp (CompAdv (PrepNP (in_Prep) (MassNP (UseN (business_N)))))))))).
Definition s_062_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (neither_Det) (AdjCN (PositA (female_A)) (UseN (commissioner_N)))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (DetCN (a_lot_of_Det) (UseN (time_N)))) (at_home_Adv))))).
Definition s_062_3_h := s_046_3_h.
Definition s_063_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_three)))) (AdjCN (PositA (female_A)) (UseN (commissioner_N))))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (MassNP (UseN (time_N)))) (at_home_Adv))))).
Definition s_063_3_h := s_031_3_h.
Definition s_064_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_most_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (AdjCN (PositA (female_A)) (UseN (commissioner_N))))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (MassNP (UseN (time_N)))) (at_home_Adv))))).
Definition s_064_3_h := s_032_3_h.
Definition s_065_1_p := s_049_4_h.
Definition s_065_2_p := s_049_2_p.
Definition s_065_4_h := s_049_1_p.
Definition s_066_1_p := s_050_4_h.
Definition s_066_2_p := s_050_2_p.
Definition s_066_4_h := s_050_1_p.
Definition s_067_1_p := s_051_4_h.
Definition s_067_2_p := s_050_2_p.
Definition s_067_4_h := s_051_1_p.
Definition s_068_1_p := s_052_4_h.
Definition s_068_2_p := s_050_2_p.
Definition s_068_4_h := s_052_1_p.
Definition s_069_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (western_A)) (UseN (country_N)))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_069_2_p := s_053_2_p.
Definition s_069_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (resident_in_N2) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (major_A)) (AdjCN (PositA (western_A)) (UseN (country_N))))))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_070_1_p := s_022_1_p.
Definition s_070_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (someSg_Det) (AdjCN (PositA (scandinavian_A)) (UseN (delegate_N)))) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N)))) (on_time_Adv))))).
Definition s_071_1_p := s_023_1_p.
Definition s_071_3_h := s_055_1_p.
Definition s_072_1_p := s_024_1_p.
Definition s_072_3_h := s_056_1_p.
Definition s_073_1_p := s_025_1_p.
Definition s_073_3_h := s_057_1_p.
Definition s_074_1_p := s_026_5_h.
Definition s_074_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (european_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (AdvAP (PositA (resident_A)) (PrepNP (outside_Prep) (UsePN (europe_PN))))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).
Definition s_075_1_p := s_043_1_p.
Definition s_075_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (a_few_Det) (AdjCN (PositA (female_A)) (UseN (committee_member_N))))) (UseComp (CompAdv (PrepNP (from_Prep) (UsePN (scandinavia_PN)))))))).
Definition s_076_1_p := s_044_1_p.
Definition s_076_3_h := s_060_1_p.
Definition s_077_1_p := s_061_3_h.
Definition s_077_3_h := s_061_1_p.
Definition s_078_1_p := s_030_1_p.
Definition s_078_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (AdvNP (DetNP (DetQuant (IndefArt) (NumSg))) (PrepNP (part_Prep) (DetCN (DetQuant (DefArt) (NumPl)) (AdjCN (PositA (female_A)) (UseN (commissioner_N)))))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (DetCN (a_lot_of_Det) (UseN (time_N)))) (at_home_Adv))))).
Definition s_079_1_p := s_031_3_h.
Definition s_079_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (at_least_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_three)))) (AdjCN (PositA (male_A)) (UseN (commissioner_N))))) (AdvVP (ComplSlash (SlashV2a (spend_V2)) (MassNP (UseN (time_N)))) (at_home_Adv))))).
Definition s_080_1_p := s_032_3_h.
Definition s_080_3_h := s_064_1_p.
Definition s_081_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP3 (and_Conj) (UsePN (smith_PN)) (UsePN (jones_PN)) (UsePN (anderson_PN))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_081_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_082_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP3 (and_Conj) (UsePN (smith_PN)) (UsePN (jones_PN)) (DetCN (several_Det) (UseN (lawyer_N)))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_082_3_h := s_081_3_h.
Definition s_083_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP3 (either7or_DConj) (UsePN (smith_PN)) (UsePN (jones_PN)) (UsePN (anderson_PN))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_083_3_h := s_081_3_h.
Definition s_084_1_p := s_083_1_p.
Definition s_084_3_h := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (UncNeg) (PredVP (ConjNP2 (and_Conj) (UsePN (smith_PN)) (UsePN (anderson_PN))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))))))).
Definition s_085_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (PredetNP (exactly_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (lawyer_N)))) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_three)))) (UseN (accountant_N)))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_085_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_six)))) (UseN (lawyer_N))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_086_1_p := s_085_1_p.
Definition s_086_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_six)))) (UseN (accountant_N))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_087_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (ConjCN2 (and_Conj) (UseN (representative_N)) (UseN (client_N)))) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))))).
Definition s_087_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (UseN (representative_N))) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))))).
Definition s_088_1_p := s_087_1_p.
Definition s_088_3_h := s_087_3_h.
Definition s_089_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (ConjCN2 (or_Conj) (UseN (representative_N)) (UseN (client_N)))) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))))).
Definition s_089_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP2 (andSg_Conj) (DetCN (every_Det) (UseN (representative_N))) (DetCN (every_Det) (UseN (client_N)))) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))))).
Definition s_090_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (chairman_N))) (ComplSlash (SlashV2a (read_out_V2)) (DetCN (DetQuant (DefArt) (NumPl)) (AdvCN (UseN (item_N)) (PrepNP (on_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (agenda_N)))))))))).
Definition s_090_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (chairman_N))) (ComplSlash (SlashV2a (read_out_V2)) (DetCN (every_Det) (AdvCN (UseN (item_N)) (PrepNP (on_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (agenda_N)))))))))).
Definition s_091_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N)))))))))) (ComplSlash (SlashV2a (vote_for_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (chairman_N)))))))).
Definition s_091_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (AdvNP (UsePron (everyone_Pron)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))) (ComplSlash (SlashV2a (vote_for_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (chairman_N)))))))).
Definition s_092_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))))))) (ComplSlash (SlashV2a (vote_for_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (chairman_N)))))))).
Definition s_092_3_h := s_091_3_h.
Definition s_093_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (UseComp (CompAdv (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N)))))))))) (AdVVP (all_AdV) (ComplSlash (SlashV2a (vote_for_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (chairman_N))))))))).
Definition s_093_3_h := s_091_3_h.
Definition s_094_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (ComplN2 (inhabitant_N2) (UsePN (cambridge_PN)))) (ComplSlash (SlashV2a (vote_for_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (labour_mp_N))))))).
Definition s_094_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (ComplN2 (inhabitant_N2) (UsePN (cambridge_PN)))) (ComplSlash (SlashV2a (vote_for_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (labour_mp_N))))))).
Definition s_095_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (AdjCN (PositA (ancient_A)) (UseN (greek_N)))) (UseComp (CompCN (AdjCN (PositA (noted_A)) (UseN (philosopher_N)))))))).
Definition s_095_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (AdjCN (PositA (ancient_A)) (UseN (greek_N)))) (UseComp (CompCN (AdjCN (PositA (noted_A)) (UseN (philosopher_N)))))))).
Definition s_096_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (AdjCN (PositA (ancient_A)) (UseN (greek_N)))) (AdVVP (all_AdV) (UseComp (CompCN (AdjCN (PositA (noted_A)) (UseN (philosopher_N))))))))).
Definition s_096_3_h := s_095_3_h.
Definition s_097_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (software_fault_N))) (AdvVP (PassV2s (blame1_V2)) (PrepNP (for_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_failure_N)))))))).
Definition s_097_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_failure_N))) (AdvVP (PassV2s (blame2_V2)) (PrepNP (on_Prep) (DetCN (one_or_more_Det) (UseN (software_fault_N)))))))).
Definition s_098_1_p := s_097_1_p.
Definition s_098_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bug_32985_PN)) (UseComp (CompCN (AdjCN (PositA (known_A)) (UseN (software_fault_N)))))))).
Definition s_098_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bug_32985_PN)) (AdvVP (PassV2s (blame1_V2)) (PrepNP (for_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_failure_N)))))))).
Definition s_099_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (UseN (client_N)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (demonstration_N)))))) (AdVVP (all_AdV) (UseComp (CompAP (ComplA2 (impressed_by_A2) (DetCN (DetQuant (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_N)))) (NumSg)) (UseN (performance_N)))))))))).
Definition s_099_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompCN (AdvCN (UseN (client_N)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (demonstration_N)))))))))).
Definition s_099_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompAP (ComplA2 (impressed_by_A2) (DetCN (DetQuant (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_N)))) (NumSg)) (UseN (performance_N))))))))).
Definition s_100_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (UseN (client_N)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (demonstration_N)))))) (UseComp (CompAP (ComplA2 (impressed_by_A2) (DetCN (DetQuant (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_N)))) (NumSg)) (UseN (performance_N))))))))).
Definition s_100_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (UseN (client_N)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (demonstration_N))))))) (UseComp (CompAP (ComplA2 (impressed_by_A2) (DetCN (DetQuant (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_N)))) (NumSg)) (UseN (performance_N))))))))).
Definition s_101_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (university_graduate_N))) (ComplSlash (SlashV2a (make8become_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (poor8bad_A)) (UseN (stockmarket_trader_N)))))))).
Definition s_101_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompCN (UseN (university_graduate_N))))))).
Definition s_101_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompAP (SentAP (PositA (likely_A)) (EmbedVP (ComplSlash (SlashV2a (make8become_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (poor8bad_A)) (UseN (stockmarket_trader_N)))))))))))).
Definition s_102_1_p := s_101_1_p.
Definition s_102_2_p := s_101_2_p.
Definition s_102_4_h := (Sentence (UseCl (Future) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (make8become_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (poor8bad_A)) (UseN (stockmarket_trader_N)))))))).
Definition s_103_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (apcom_manager_N)))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (company_car_N))))))).
Definition s_103_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (jones_PN)) (UseComp (CompCN (UseN (apcom_manager_N))))))).
Definition s_103_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (company_car_N))))))).
Definition s_104_1_p := s_103_1_p.
Definition s_104_2_p := s_103_2_p.
Definition s_104_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumCard (AdNum (more_than_AdN) (NumNumeral (N_one))))) (UseN (company_car_N))))))).
Definition s_105_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (PredetNP (just_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (UseN (accountant_N)))) (ComplSlash (SlashV2a (attend_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_105_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumPl)) (UseN (accountant_N))) (ComplSlash (SlashV2a (attend_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_106_1_p := s_105_1_p.
Definition s_106_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumSg)) (UseN (accountant_N))) (ComplSlash (SlashV2a (attend_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_107_1_p := s_105_1_p.
Definition s_107_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (somePl_Det) (UseN (accountant_N))) (ComplSlash (SlashV2a (attend_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_108_1_p := s_105_1_p.
Definition s_108_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (someSg_Det) (UseN (accountant_N))) (ComplSlash (SlashV2a (attend_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_109_1_p := s_105_1_p.
Definition s_109_3_h := s_107_3_h.
Definition s_110_1_p := s_105_1_p.
Definition s_110_3_h := s_108_3_h.
Definition s_111_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (UseN (contract_N))))))).
Definition s_111_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (another_Det) (UseN (contract_N))))))).
Definition s_111_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (smith_PN)) (UsePN (jones_PN))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (contract_N))))))).
Definition s_112_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (contract_N))))))).
Definition s_112_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (contract_N))))))).
Definition s_112_4_h := s_111_4_h.
Definition s_113_1_p := s_112_1_p.
Definition s_113_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdVVP (also_AdV) (ComplSlash (SlashV2a (sign_V2)) (UsePron (they_Pron))))))).
Definition s_113_4_h := s_111_4_h.
Definition s_114_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (use_V2)) (DetCN (DetQuant (PossPron (sheRefl_Pron)) (NumSg)) (UseN (workstation_N))))))).
Definition s_114_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (GenNP (UsePN (mary_PN))) (NumSg)) (UseN (workstation_N))) (PassV2s (use_V2))))).
Definition s_115_1_p := s_114_1_p.
Definition s_115_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (workstation_N))))))).
Definition s_116_1_p := s_114_1_p.
Definition s_116_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mary_PN)) (UseComp (CompAP (PositA (female_A))))))).
Definition s_117_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (UseN (student_N))) (ComplSlash (SlashV2a (use_V2)) (DetCN (DetQuant (PossPron (sheRefl_Pron)) (NumSg)) (UseN (workstation_N))))))).
Definition s_117_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mary_PN)) (UseComp (CompCN (UseN (student_N))))))).
Definition s_117_4_h := s_114_1_p.
Definition s_118_1_p := s_117_1_p.
Definition s_118_2_p := s_117_2_p.
Definition s_118_4_h := s_115_3_h.
Definition s_119_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumSg)) (UseN (student_N))) (ComplSlash (SlashV2a (use_V2)) (DetCN (DetQuant (PossPron (sheRefl_Pron)) (NumSg)) (UseN (workstation_N))))))).
Definition s_119_2_p := s_117_2_p.
Definition s_119_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (use_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (workstation_N))))))).
Definition s_120_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (attend_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_120_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (ComplSlash (SlashV2a (chair_V2)) (UsePron (it_Pron)))))).
Definition s_120_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (chair_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_121_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (deliver_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))) (PrepNP (to_Prep) (UsePN (itel_PN))))))).
Definition s_121_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (AdVVP (also_AdV) (ComplSlash (Slash2V3 (deliver_V3) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (invoice_N)))) (UsePron (they_Pron))))))).
Definition s_121_3_p := (PSentence (and_PConj) (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (ComplSlash (Slash2V3 (deliver_V3) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (project_proposal_N)))) (UsePron (they_Pron)))))).
Definition s_121_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (deliver_V2)) (ConjNP3 (and_Conj) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (invoice_N))) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (project_proposal_N))))) (PrepNP (to_Prep) (UsePN (itel_PN))))))).
Definition s_122_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (committee_N))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (chairman_N))))))).
Definition s_122_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (AdvVP (PassV2s (appoint_V2)) (PrepNP (by8agent_Prep) (DetCN (DetQuant (PossPron (it_Pron)) (NumPl)) (UseN (member_N)))))))).
Definition s_122_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (committee_N))) (ComplSlash (SlashV2a (have_V2)) (AdvNP (PPartNP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (chairman_N))) (appoint_V2)) (PrepNP (by8agent_Prep) (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (UseN (member_N)) (PrepNP (possess_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (committee_N)))))))))))).
Definition s_123_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (send_V2)) (PredetNP (most_of_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (RelCN (UseN (report_N)) (UseRCl (Present) (PPos) (EmptyRelSlash (SlashVP (UsePN (smith_PN)) (SlashV2a (need_V2)))))))))))).
Definition s_123_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePron (they_Pron)) (UseComp (CompAdv (PrepNP (on_Prep) (DetCN (DetQuant (PossPron (she_Pron)) (NumSg)) (UseN (desk_N))))))))).
Definition s_123_4_h := (Sentence (UseCl (Present) (PPos) (ExistNP (AdvNP (DetCN (somePl_Det) (AdvCN (UseN (report_N)) (PrepNP (from_Prep) (UsePN (itel_PN))))) (PrepNP (on_Prep) (DetCN (DetQuant (GenNP (UsePN (smith_PN))) (NumSg)) (UseN (desk_N)))))))).
Definition s_124_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (AdvNP (DetNP (DetQuant (IndefArt) (NumCard (NumNumeral (N_two))))) (PrepNP (out_of_Prep) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (UseN (machine_N))))) (UseComp (CompAP (PositA (missing_A))))))).
Definition s_124_2_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePron (they_Pron)) (PassV2s (remove_V2))))).
Definition s_124_4_h := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (machine_N))) (PassV2s (remove_V2))))).
Definition s_125_1_p := s_124_1_p.
Definition s_125_2_p := s_124_2_p.
Definition s_125_4_h := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_eight)))) (UseN (machine_N))) (PassV2s (remove_V2))))).
Definition s_126_1_p := s_124_1_p.
Definition s_126_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (they_Pron)) (AdvVP (AdVVP (all_AdV) (UseComp (CompAdv (here_Adv)))) (yesterday_Adv))))).
Definition s_126_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (UseN (machine_N))) (AdvVP (UseComp (CompAdv (here_Adv))) (yesterday_Adv))))).
Definition s_127_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (machine_N)))) (on_tuesday_Adv)))) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (machine_N)))) (on_wednesday_Adv)))))).
Definition s_127_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (they_Pron)) (ComplSlash (Slash3V3 (put_in_V3) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (lobby_N)))) (UsePron (they_Pron)))))).
Definition s_127_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (smith_PN)) (UsePN (jones_PN))) (ComplSlash (Slash3V3 (put_in_V3) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (lobby_N)))) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (machine_N))))))).
Definition s_128_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (john_PN)) (DetCN (DetQuant (PossPron (he_Pron)) (NumPl)) (UseN (colleague_N)))) (AdvVP (UseV (go8walk_V)) (PrepNP (to_Prep) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (meeting_N)))))))).
Definition s_128_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (they_Pron)) (ComplSlash (SlashV2a (hate_V2)) (UsePron (it_Pron)))))).
Definition s_128_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (GenNP (UsePN (john_PN))) (NumPl)) (UseN (colleague_N))) (ComplSlash (SlashV2a (hate_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_129_1_p := s_128_1_p.
Definition s_129_2_p := s_128_2_p.
Definition s_129_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (hate_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_130_1_p := s_128_1_p.
Definition s_130_2_p := s_128_2_p.
Definition s_130_4_h := s_129_4_h.
Definition s_131_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det) (UseN (department_N))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (dedicated_A)) (UseN (line_N)))))))).
Definition s_131_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePron (they_Pron)) (ComplSlash (Slash3V3 (rent_from_V3) (UsePN (bt_PN))) (UsePron (they_Pron)))))).
Definition s_131_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (department_N))) (ComplSlash (Slash3V3 (rent_from_V3) (UsePN (bt_PN))) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (line_N))))))).
Definition s_132_1_p := s_131_1_p.
Definition s_132_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (sales_department_N))) (ComplSlash (Slash3V3 (rent_from_V3) (UsePN (bt_PN))) (UsePron (it_Pron)))))).
Definition s_132_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (sales_department_N))) (ComplSlash (Slash3V3 (rent_from_V3) (UsePN (bt_PN))) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (line_N))))))).
Definition s_133_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (gfi_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (several_Det) (UseN (computer_N))))))).
Definition s_133_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (maintain_V2)) (UsePron (they_Pron)))))).
Definition s_133_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (maintain_V2)) (PredetNP (all_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (RelCN (UseN (computer_N)) (UseRCl (Present) (PPos) (RelSlash (that_RP) (SlashVP (UsePN (gfi_PN)) (SlashV2a (own_V2)))))))))))).
Definition s_134_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (RelCN (UseN (customer_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (computer_N)))))))) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (service_contract_N)))) (PrepNP (for_Prep) (UsePron (it_Pron))))))).
Definition s_134_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mfi_PN)) (UseComp (CompCN (RelCN (UseN (customer_N)) (UseRCl (Present) (PPos) (RelVP (that_RP) (ComplSlash (SlashV2a (own_V2)) (PredetNP (exactly_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (UseN (computer_N))))))))))))).
Definition s_134_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mfi_PN)) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (service_contract_N)))) (PrepNP (for_Prep) (PredetNP (all_Predet) (DetCN (DetQuant (PossPron (itRefl_Pron)) (NumPl)) (UseN (computer_N))))))))).
Definition s_135_1_p := s_134_1_p.
Definition s_135_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mfi_PN)) (UseComp (CompCN (RelCN (UseN (customer_N)) (UseRCl (Present) (PPos) (RelVP (that_RP) (ComplSlash (SlashV2a (own_V2)) (DetCN (several_Det) (UseN (computer_N)))))))))))).
Definition s_135_4_h := s_134_4_h.
Definition s_136_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (every_Det) (RelCN (UseN (executive_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (laptop_computer_N)))))))) (ComplSlash (SlashV2V (bring_V2V) (AdvVP (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (note_N)))) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N)))))) (UsePron (it_Pron)))))).
Definition s_136_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompCN (RelCN (UseN (executive_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_five)))) (AdjCN (PositA (different_A)) (UseN (laptop_computer_N))))))))))))).
Definition s_136_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_five)))) (UseN (laptop_computer_N)))) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N)))))))).
Definition s_137_1_p := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_100)))) (UseN (company_N)))))).
Definition s_137_2_p := (Sentence (PredVPS (UsePN (icm_PN)) (ConjVPS2 (and_Conj) (Present) (PPos) (UseComp (CompNP (AdvNP (DetNP (DetQuant (IndefArt) (NumCard (NumNumeral (N_one))))) (PrepNP (part_Prep) (DetCN (DetQuant (DefArt) (NumPl)) (UseN (company_N))))))) (Present) (PPos) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_150)))) (UseN (computer_N))))))).
Definition s_137_3_p := (Sentence (UseCl (Present) (UncNeg) (PredVP (UsePron (it_Pron)) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (service_contract_N)))) (PrepNP (for_Prep) (AdvNP (DetNP (anySg_Det)) (PrepNP (part_Prep) (DetCN (DetQuant (PossPron (itRefl_Pron)) (NumPl)) (UseN (computer_N)))))))))).
Definition s_137_4_p := (Sentence (UseCl (Present) (PPos) (PredVP (AdvNP (DetNP (each_Det)) (PrepNP (part_Prep) (DetCN (DetQuant (the_other_Q) (NumCard (NumNumeral (N_99)))) (UseN (company_N))))) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (UseN (computer_N))))))).
Definition s_137_5_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePron (they_Pron)) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (service_contract_N)))) (PrepNP (for_Prep) (UsePron (they_Pron))))))).
Definition s_137_7_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (company_N)) (UseRCl (Present) (PPos) (RelVP (that_RP) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (computer_N))))))))) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (service_contract_N)))) (PrepNP (for_Prep) (UsePron (it_Pron))))))).
Definition s_138_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (report_N))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (cover_page_N))))))).
Definition s_138_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (r95103_PN)) (UseComp (CompCN (UseN (report_N))))))).
Definition s_138_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (cover_page_N))))))).
Definition s_138_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (AdvCN (UseN (cover_page_N)) (PrepNP (possess_Prep) (UsePN (r95103_PN))))))))).
Definition s_139_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (company_director_N))) (ReflVP (Slash3V3 (award_V3) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (large_A)) (UseN (payrise_N))))))))).
Definition s_139_3_h := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (company_director_N))) (ComplSlash (SlashV2a (award_and_be_awarded_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (payrise_N))))))).
Definition s_140_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVSa (say_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (bill_PN)) (ReflVP (SlashV2a (hurt_V2))))))))).
Definition s_140_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVSa (say_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (bill_PN)) (PassV2s (hurt_V2)))))))).
Definition s_141_1_p := s_140_1_p.
Definition s_141_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (someone_Pron)) (ComplVSa (say_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (john_PN)) (PassV2s (hurt_V2)))))))).
Definition s_142_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN)))))).
Definition s_142_2_p := (Sentence (UseCl (Past) (PPos) (SoDoI (UsePN (bill_PN))))).
Definition s_142_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN)))))).
Definition s_143_1_p := s_142_1_p.
Definition s_143_2_p := s_142_2_p.
Definition s_143_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (at_four_oclock_Adv))))).
Definition s_143_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (at_four_oclock_Adv))))).
Definition s_144_1_p := s_143_3_p.
Definition s_144_2_p := s_142_2_p.
Definition s_144_4_h := s_143_5_h.
Definition s_145_1_p := s_143_3_p.
Definition s_145_2_p := (PSentence (and_PConj) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplVV (do_VV) (elliptic_VP)) (at_five_oclock_Adv))))).
Definition s_145_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (at_five_oclock_Adv))))).
Definition s_146_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN)))))).
Definition s_146_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ProgrVPa (ComplVV (going_to_VV) (elliptic_VP)))))).
Definition s_146_4_h := (Sentence (UseCl (Future) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN)))))).
Definition s_147_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (on_monday_Adv))))).
Definition s_147_2_p := (Sentence (UseCl (Past) (PNeg) (PredVP (UsePN (bill_PN)) (elliptic_VP)))).
Definition s_147_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (on_monday_Adv))))).
Definition s_148_1_p := (Question (UseQCl (PresentPerfect) (PPos) (QuestCl (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))))))).
Definition s_148_2_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (bill_PN)) (elliptic_VP)))).
Definition s_148_4_h := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN)))))).
Definition s_149_1_p := s_146_1_p.
Definition s_149_2_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (student_N))) (AdvVP (elliptic_VP) (too_Adv))))).
Definition s_149_4_h := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (student_N))) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN)))))).
Definition s_150_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (car_N))))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (elliptic_VP) (PrepNP (by8means_Prep) (MassNP (UseN (train_N))))))))).
Definition s_150_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (train_N)))))))).
Definition s_151_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (car_N))))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (AdvVP (elliptic_VP) (PrepNP (by8means_Prep) (MassNP (UseN (train_N))))) (PrepNP (to_Prep) (UsePN (berlin_PN)))))))).
Definition s_151_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (berlin_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (train_N)))))))).
Definition s_152_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (car_N))))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (elliptic_VP) (PrepNP (to_Prep) (UsePN (berlin_PN)))))))).
Definition s_152_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (berlin_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (car_N)))))))).
Definition s_153_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (AdvVP (ProgrVPa (UseV (go8travel_V))) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (car_N))))))) (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (student_N))) (AdvVP (elliptic_VP) (PrepNP (by8means_Prep) (MassNP (UseN (train_N))))))))).
Definition s_153_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (student_N))) (AdvVP (AdvVP (ProgrVPa (UseV (go8travel_V))) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (train_N)))))))).
Definition s_154_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (paris_PN)))) (PrepNP (by8means_Prep) (MassNP (UseN (car_N)))))))).
Definition s_154_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (elliptic_VP) (PrepNP (by8means_Prep) (MassNP (UseN (train_N)))))))).
Definition s_154_4_h := s_150_3_h.
Definition s_155_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (car_N))))))).
Definition s_155_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplSlash (SlashV2a (own_V2)) (DetNP (DetQuant (IndefArt) (NumSg)))) (too_Adv))))).
Definition s_155_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (car_N))))))).
Definition s_156_1_p := s_155_1_p.
Definition s_156_2_p := s_155_2_p.
Definition s_156_4_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumSg)) (RelCN (UseN (car_N)) (UseRCl (Present) (PPos) (RelSlash (that_RP) (SlashVP (ConjNP2 (and_Conj) (UsePN (john_PN)) (UsePN (bill_PN))) (SlashV2a (own_V2)))))))))).
Definition s_157_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (red_A)) (UseN (car_N)))))))).
Definition s_157_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (blue_A)) (UseN (one_N)))))))).
Definition s_157_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (blue_A)) (UseN (car_N)))))))).
Definition s_158_1_p := s_157_1_p.
Definition s_158_2_p := s_157_2_p.
Definition s_158_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (red_A)) (UseN (car_N)))))))).
Definition s_159_1_p := s_157_1_p.
Definition s_159_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (fast_A)) (UseN (one_N)))))))).
Definition s_159_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (fast_A)) (UseN (car_N)))))))).
Definition s_160_1_p := s_157_1_p.
Definition s_160_2_p := s_159_2_p.
Definition s_160_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (fast_A)) (AdjCN (PositA (red_A)) (UseN (car_N))))))))).
Definition s_161_1_p := s_157_1_p.
Definition s_161_2_p := s_159_2_p.
Definition s_161_4_h := s_160_4_h.
Definition s_162_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (fast_A)) (AdjCN (PositA (red_A)) (UseN (car_N))))))))).
Definition s_162_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (slow_A)) (UseN (one_N)))))))).
Definition s_162_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (slow_A)) (AdjCN (PositA (red_A)) (UseN (car_N))))))))).
Definition s_163_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (have_V2)) (PPartNP (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (paper_N))) (accept_V2)))))).
Definition s_163_2_p := (Sentence (UseCl (Present) (PNeg) (PredVP (UsePN (bill_PN)) (ComplVQ (know_VQ) (UseQCl (Past) (PPos) (QuestIAdv (why_IAdv) (elliptic_Cl))))))).
Definition s_163_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (bill_PN)) (ComplVQ (know_VQ) (UseQCl (Past) (PPos) (QuestIAdv (why_IAdv) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (have_V2)) (PPartNP (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (paper_N))) (accept_V2)))))))))).
Definition s_164_1_p := s_142_1_p.
Definition s_164_2_p := (PAdverbial (and_PConj) (PrepNP (to_Prep) (UsePN (sue_PN)))).
Definition s_164_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (sue_PN)))))).
Definition s_165_1_p := s_142_1_p.
Definition s_165_2_p := (Adverbial (on_friday_Adv)).
Definition s_165_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (on_friday_Adv))))).
Definition s_166_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (speak_to_V2)) (UsePN (mary_PN))) (on_thursday_Adv))))).
Definition s_166_2_p := (PAdverbial (and_PConj) (on_friday_Adv)).
Definition s_166_4_h := s_165_4_h.
Definition s_167_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_twenty)))) (UseN (man_N))) (ComplSlash (SlashV2a (work_in_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (sales_department_N))))))).
Definition s_167_2_p := (PNounphrase (but_PConj) (PredetNP (only_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (UseN (woman_N))))).
Definition s_167_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (woman_N))) (ComplSlash (SlashV2a (work_in_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (sales_department_N))))))).
Definition s_168_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_five)))) (UseN (man_N))) (AdvVP (UseV (work_V)) (part_time_Adv))))).
Definition s_168_2_p := (PNounphrase (and_PConj) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_fortyfive)))) (UseN (woman_N)))).
Definition s_168_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_fortyfive)))) (UseN (woman_N))) (AdvVP (UseV (work_V)) (part_time_Adv))))).
Definition s_169_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (find_V2)) (UsePN (mary_PN))) (PrepNP (before_Prep) (UsePN (bill_PN))))))).
Definition s_169_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (find_V2)) (UsePN (mary_PN))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (find_V2)) (UsePN (mary_PN)))))))))).
Definition s_170_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (find_V2)) (AdvNP (UsePN (mary_PN)) (PrepNP (before_Prep) (UsePN (bill_PN)))))))).
Definition s_170_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (AdvVP (ComplSlash (SlashV2a (find_V2)) (UsePN (mary_PN))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (find_V2)) (UsePN (bill_PN)))))))))).
Definition s_171_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplVV (want_VV) (ComplVQ (know_VQ) (UseQCl (Present) (PPos) (QuestVP (IdetCN (how8many_IDet) (UseN (man_N))) (AdvVP (UseV (work_V)) (part_time_Adv))))))))).
Definition s_171_2_p := (PNounphrase (and_PConj) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (woman_N)))).
Definition s_171_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplVV (want_VV) (ComplVQ (know_VQ) (UseQCl (Present) (PPos) (QuestVP (IdetCN (how8many_IDet) (UseN (woman_N))) (AdvVP (UseV (work_V)) (part_time_Adv))))))))).
Definition s_172_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplVV (want_VV) (ComplVQ (know_VQ) (ConjQS2 (comma_and_Conj) (UseQCl (Present) (PPos) (QuestVP (IdetCN (how8many_IDet) (UseN (man_N))) (AdvVP (UseV (work_V)) (part_time_Adv)))) (UseQCl (Present) (PPos) (QuestVP (IdetCN (IdetQuant (which_IQuant) (NumPl)) (elliptic_CN)) (elliptic_VP))))))))).
Definition s_172_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplVV (want_VV) (ComplVQ (know_VQ) (UseQCl (Present) (PPos) (QuestVP (IdetCN (IdetQuant (which_IQuant) (NumPl)) (UseN (man_N))) (AdvVP (UseV (work_V)) (part_time_Adv))))))))).
Definition s_173_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (speak_to_V2)) (RelNPa (UsePron (everyone_Pron)) (UseRCl (Past) (PPos) (StrandRelSlash (that_RP) (SlashVP (UsePN (john_PN)) (SlashVV (do_VV) (elliptic_VPSlash)))))))))).
Definition s_173_2_p := s_142_1_p.
Definition s_173_4_h := s_142_4_h.
Definition s_174_1_p := s_173_1_p.
Definition s_174_2_p := s_142_4_h.
Definition s_174_4_h := s_142_1_p.
Definition s_175_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVSa (say_VS) (UseCl (Past) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplVV (do_VV) (elliptic_VP)) (too_Adv)))))).
Definition s_175_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplVSa (say_VS) (UseCl (Past) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))).
Definition s_176_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVSa (say_VS) (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplVV (do_VV) (elliptic_VP)) (too_Adv))))))))).
Definition s_176_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVSa (say_VS) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))).
Definition s_177_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVS (say_VS) (PredVPS (UsePN (mary_PN)) (ConjVPS2 (comma_and_Conj) (Past) (PPos) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))) (Past) (PPos) (ComplVS (say_VS) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplVV (do_VV) (elliptic_VP)) (too_Adv))))))))))).
Definition s_177_3_h := s_175_3_h.
Definition s_178_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplVSa (say_VS) (UseCl (Past) (PPos) (PredVP (UsePN (peter_PN)) (ComplVV (do_VV) (elliptic_VP))))) (too_Adv)))))).
Definition s_178_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplVSa (say_VS) (UseCl (Past) (PPos) (PredVP (UsePN (peter_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))).
Definition s_179_1_p := (Sentence (ConjS2 (if_comma_then_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (AdvVP (ComplVV (do_VV) (elliptic_VP)) (too_Adv)))))).
Definition s_179_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))))).
Definition s_179_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))))).
Definition s_180_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVV (want_VV) (ComplSlash (SlashV2a (buy_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (car_N))))))) (UseCl (Past) (PPos) (PredVP (UsePron (he_Pron)) (ComplVV (do_VV) (elliptic_VP)))))).
Definition s_180_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (buy_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (car_N))))))).
Definition s_181_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (john_PN)) (ComplVV (need_VV) (ComplSlash (SlashV2a (buy_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (car_N))))))) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplVV (do_VV) (elliptic_VP)))))).
Definition s_181_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2a (buy_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (car_N))))))).
Definition s_182_1_p := (Sentence (ConjS2 (and_Conj) (UseCl (Present) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (company_N)))))) (UseCl (Present) (PPos) (SoDoI (UsePN (jones_PN)))))).
Definition s_182_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (GenNP (UsePN (jones_PN))) (NumSg)) (UseN (company_N))))))).
Definition s_183_1_p := s_182_1_p.
Definition s_183_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (GenNP (UsePN (smith_PN))) (NumSg)) (UseN (company_N))))))).
Definition s_184_1_p := s_182_1_p.
Definition s_184_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (GenNP (UsePN (jones_PN))) (NumSg)) (UseN (company_N))))))).
Definition s_185_1_p := (Sentence (ConjS2 (and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplVSa (claim_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePron (he_Pron)) (ComplSlash (SlashV2a (cost_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (proposal_N))))))))) (UseCl (Past) (PPos) (SoDoI (UsePN (jones_PN)))))).
Definition s_185_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplVSa (claim_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePron (he_Pron)) (ComplSlash (SlashV2a (cost_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (proposal_N))))))))))).
Definition s_186_1_p := s_185_1_p.
Definition s_186_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplVSa (claim_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePron (he_Pron)) (ComplSlash (SlashV2a (cost_V2)) (DetCN (DetQuant (GenNP (UsePN (smith_PN))) (NumSg)) (UseN (proposal_N)))))))))).
Definition s_187_1_p := s_185_1_p.
Definition s_187_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplVSa (claim_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (cost_V2)) (DetCN (DetQuant (GenNP (UsePN (smith_PN))) (NumSg)) (UseN (proposal_N)))))))))).
Definition s_188_1_p := s_185_1_p.
Definition s_188_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplVSa (claim_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (cost_V2)) (DetCN (DetQuant (GenNP (UsePN (jones_PN))) (NumSg)) (UseN (proposal_N)))))))))).
Definition s_189_1_p := (Sentence (ConjS2 (and_Conj) (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (UseN (man_N)))))) (UseCl (Present) (PPos) (PredVP (UsePN (mary_PN)) (UseComp (CompCN (UseN (woman_N)))))))).
Definition s_189_2_p := (Sentence (ConjS2 (and_Conj) (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (company_N)))))) (UseCl (Present) (PPos) (SoDoI (UsePN (mary_PN)))))).
Definition s_189_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (PossPron (sheRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (company_N)))))))).
Definition s_190_1_p := s_189_1_p.
Definition s_190_2_p := s_189_2_p.
Definition s_190_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mary_PN)) (ComplSlash (SlashV2a (represent_V2)) (DetCN (DetQuant (GenNP (UsePN (john_PN))) (NumSg)) (UseN (company_N))))))).
Definition s_191_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (UsePN (bill_PN)) (ComplSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (UsePron (they_Pron)) (ComplVV (shall_VV) (AdvVP (AdvVP (UseV (go8walk_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))) (together_Adv)))))) (DetCN (DetQuant (GenNP (UsePN (frank_PN))) (NumSg)) (UseN (boss_N)))))) (UseCl (Past) (PPos) (PredVP (UsePN (carl_PN)) (AdvVP (elliptic_VP) (PrepNP (to_Prep) (DetCN (DetQuant (GenNP (UsePN (alan_PN))) (NumSg)) (UseN (wife_N))))))))).
Definition s_191_3_h := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (bill_PN)) (UsePN (frank_PN))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv)))))))))) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (carl_PN)) (UsePN (alan_PN))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv))))))))))).
Definition s_192_1_p := s_191_1_p.
Definition s_192_3_h := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (bill_PN)) (UsePN (frank_PN))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv)))))))))) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (carl_PN)) (DetCN (DetQuant (GenNP (UsePN (alan_PN))) (NumSg)) (UseN (wife_N)))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv))))))))))).
Definition s_193_1_p := s_191_1_p.
Definition s_193_3_h := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (bill_PN)) (DetCN (DetQuant (GenNP (UsePN (frank_PN))) (NumSg)) (UseN (boss_N)))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv)))))))))) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (carl_PN)) (DetCN (DetQuant (GenNP (UsePN (alan_PN))) (NumSg)) (UseN (wife_N)))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv))))))))))).
Definition s_194_1_p := s_191_1_p.
Definition s_194_3_h := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (bill_PN)) (DetCN (DetQuant (GenNP (UsePN (frank_PN))) (NumSg)) (UseN (boss_N)))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv)))))))))) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (carl_PN)) (UsePN (alan_PN))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv))))))))))).
Definition s_195_1_p := s_191_1_p.
Definition s_195_3_h := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP3 (and_Conj) (UsePN (bill_PN)) (UsePN (frank_PN)) (DetCN (DetQuant (GenNP (UsePN (frank_PN))) (NumSg)) (UseN (boss_N)))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv)))))))))) (UseCl (Past) (PPos) (ImpersCl (PassVPSlash (SlashV2S (suggest_to_V2S) (UseCl (Past) (PPos) (PredVP (ConjNP3 (and_Conj) (UsePN (carl_PN)) (UsePN (alan_PN)) (DetCN (DetQuant (GenNP (UsePN (alan_PN))) (NumSg)) (UseN (wife_N)))) (ComplVV (shall_VV) (AdvVP (UseV (go8walk_V)) (together_Adv))))))))))).
Definition s_196_1_p := (Sentence (ConjS2 (comma_and_Conj) (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (lawyer_N))) (ComplSlash (SlashV2a (sign_V2)) (DetCN (every_Det) (UseN (report_N)))))) (UseCl (Past) (PPos) (SoDoI (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (auditor_N))))))).
Definition s_196_2_p := (PSentence (that_is_PConj) (UseCl (Past) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (RelCN (UseN (lawyer_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (sign_V2)) (PredetNP (all_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (UseN (report_N)))))))))))).
Definition s_196_4_h := (Sentence (UseCl (Past) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_one)))) (RelCN (UseN (auditor_N)) (UseRCl (Past) (PPos) (RelVP (IdRP) (ComplSlash (SlashV2a (sign_V2)) (PredetNP (all_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (UseN (report_N)))))))))))).
Definition s_197_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (genuine_A)) (UseN (diamond_N)))))))).
Definition s_197_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (diamond_N))))))).
Definition s_198_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (AdjCN (PositA (former_A)) (UseN (university_student_N)))))))).
Definition s_198_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (UseN (university_student_N))))))).
Definition s_199_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (AdjCN (PositA (successful_A)) (AdjCN (PositA (former_A)) (UseN (university_student_N))))))))).
Definition s_199_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompAP (PositA (successful_A))))))).
Definition s_200_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (AdjCN (PositA (former_A)) (AdjCN (PositA (successful_A)) (UseN (university_student_N))))))))).
Definition s_200_3_h := s_199_3_h.
Definition s_201_1_p := s_200_1_p.
Definition s_201_3_h := s_198_3_h.
Definition s_202_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (UseN (mammal_N))) (UseComp (CompCN (UseN (animal_N))))))).
Definition s_202_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (every_Det) (AdjCN (PositA (fourlegged_A)) (UseN (mammal_N)))) (UseComp (CompCN (AdjCN (PositA (fourlegged_A)) (UseN (animal_N)))))))).
Definition s_203_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (dumbo_PN)) (UseComp (CompCN (AdjCN (PositA (fourlegged_A)) (UseN (animal_N)))))))).
Definition s_203_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (dumbo_PN)) (UseComp (CompAP (PositA (fourlegged_A))))))).
Definition s_204_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mickey_PN)) (UseComp (CompCN (AdjCN (PositA (small_A)) (UseN (animal_N)))))))).
Definition s_204_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mickey_PN)) (UseComp (CompCN (AdjCN (PositA (large_A)) (UseN (animal_N)))))))).
Definition s_205_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (dumbo_PN)) (UseComp (CompCN (AdjCN (PositA (large_A)) (UseN (animal_N)))))))).
Definition s_205_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (dumbo_PN)) (UseComp (CompCN (AdjCN (PositA (small_A)) (UseN (animal_N)))))))).
Definition s_206_1_p := (Sentence (UseCl (Present) (UncNeg) (PredVP (UsePN (fido_PN)) (UseComp (CompCN (AdjCN (PositA (small_A)) (UseN (animal_N)))))))).
Definition s_206_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (fido_PN)) (UseComp (CompCN (AdjCN (PositA (large_A)) (UseN (animal_N)))))))).
Definition s_207_1_p := (Sentence (UseCl (Present) (UncNeg) (PredVP (UsePN (fido_PN)) (UseComp (CompCN (AdjCN (PositA (large_A)) (UseN (animal_N)))))))).
Definition s_207_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (fido_PN)) (UseComp (CompCN (AdjCN (PositA (small_A)) (UseN (animal_N)))))))).
Definition s_208_1_p := s_204_1_p.
Definition s_208_2_p := s_205_1_p.
Definition s_208_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mickey_PN)) (UseComp (CompAP (ComparA (small_A) (UsePN (dumbo_PN)))))))).
Definition s_209_1_p := s_204_1_p.
Definition s_209_2_p := s_205_1_p.
Definition s_209_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mickey_PN)) (UseComp (CompAP (ComparA (large_A) (UsePN (dumbo_PN)))))))).
Definition s_210_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (mouse_N)))) (UseComp (CompCN (AdjCN (PositA (small_A)) (UseN (animal_N)))))))).
Definition s_210_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mickey_PN)) (UseComp (CompCN (AdjCN (PositA (large_A)) (UseN (mouse_N)))))))).
Definition s_210_4_h := s_204_3_h.
Definition s_211_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (elephant_N)))) (UseComp (CompCN (AdjCN (PositA (large_A)) (UseN (animal_N)))))))).
Definition s_211_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (dumbo_PN)) (UseComp (CompCN (AdjCN (PositA (small_A)) (UseN (elephant_N)))))))).
Definition s_211_4_h := s_205_3_h.
Definition s_212_1_p := s_210_1_p.
Definition s_212_2_p := s_211_1_p.
Definition s_212_3_p := s_210_2_p.
Definition s_212_4_p := s_211_2_p.
Definition s_212_6_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (dumbo_PN)) (UseComp (CompAP (ComparA (large_A) (UsePN (mickey_PN)))))))).
Definition s_213_1_p := s_210_1_p.
Definition s_213_2_p := s_210_2_p.
Definition s_213_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (mickey_PN)) (UseComp (CompAP (PositA (small_A))))))).
Definition s_214_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (legal_A)) (UseN (authority_N))))) (UseComp (CompCN (UseN (law_lecturer_N))))))).
Definition s_214_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (law_lecturer_N)))) (UseComp (CompCN (AdjCN (PositA (legal_A)) (UseN (authority_N)))))))).
Definition s_214_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (fat_A)) (AdjCN (PositA (legal_A)) (UseN (authority_N)))))) (UseComp (CompCN (AdjCN (PositA (fat_A)) (UseN (law_lecturer_N)))))))).
Definition s_215_1_p := s_214_1_p.
Definition s_215_2_p := s_214_2_p.
Definition s_215_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (competent_A)) (AdjCN (PositA (legal_A)) (UseN (authority_N)))))) (UseComp (CompCN (AdjCN (PositA (competent_A)) (UseN (law_lecturer_N)))))))).
Definition s_216_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (AdvCN (AdjCN (UseComparA_prefix (fat_A)) (UseN (politician_N))) (PrepNP (than_Prep) (UsePN (bill_PN))))))))).
Definition s_216_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompAP (ComparA (fat_A) (UsePN (bill_PN)))))))).
Definition s_217_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompCN (AdvCN (AdjCN (UseComparA_prefix (clever_A)) (UseN (politician_N))) (PrepNP (than_Prep) (UsePN (bill_PN))))))))).
Definition s_217_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (john_PN)) (UseComp (CompAP (ComparA (clever_A) (UsePN (bill_PN)))))))).
Definition s_218_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (kim_PN)) (UseComp (CompCN (AdjCN (PositA (clever_A)) (UseN (person_N)))))))).
Definition s_218_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (kim_PN)) (UseComp (CompAP (PositA (clever_A))))))).
Definition s_219_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (kim_PN)) (UseComp (CompCN (AdjCN (PositA (clever_A)) (UseN (politician_N)))))))).
Definition s_219_3_h := s_218_3_h.


Definition s_220_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) the_itel_xz_NP)))))).
Definition s_220_2_p := (Sentence (UseCl (Present) (PPos) (PredVP the_itel_xz_NP (UseComp (CompAP (PositA (fast_A))))))).
Definition s_220_4_h := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (PositA (fast_A))))))).
Definition s_221_1_p := s_220_1_p.
Definition s_221_3_h := s_220_4_h.
Definition s_222_1_p := s_220_1_p.
Definition s_222_2_p := s_220_4_h.
Definition s_222_4_h := s_220_2_p.
Definition s_223_1_p := s_220_1_p.
Definition s_223_2_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (PositA (slow_A))))))).
Definition s_223_4_h := s_220_2_p.
Definition s_224_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparAsAs (fast_A) the_itel_xz_NP)))))).
Definition s_224_2_p := s_220_2_p.
Definition s_224_4_h := s_220_4_h.
Definition s_225_1_p := s_224_1_p.
Definition s_225_3_h := s_220_4_h.
Definition s_226_1_p := s_224_1_p.
Definition s_226_2_p := s_220_4_h.
Definition s_226_4_h := s_220_2_p.
Definition s_227_1_p := s_224_1_p.
Definition s_227_2_p := s_223_2_p.
Definition s_227_4_h := s_220_2_p.
Definition s_228_1_p := s_224_1_p.
Definition s_228_3_h := s_220_1_p.
Definition s_229_1_p := s_224_1_p.
Definition s_229_3_h := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (slow_A) the_itel_xz_NP)))))).
Definition s_230_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (AdjCN (UseComparA_prefix (many_A)) (UseN (order_N))) (SubjS (than_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplVV (do_VV) (elliptic_VP))))))))))).
Definition s_230_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (somePl_Det) (UseN (order_N))))))).
Definition s_231_1_p := s_230_1_p.
Definition s_231_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (somePl_Det) (UseN (order_N))))))).
Definition s_232_1_p := s_230_1_p.
Definition s_232_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (UseN (order_N))))))).
Definition s_232_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (PredetNP (at_least_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_eleven)))) (UseN (order_N)))))))).
Definition s_233_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (AdjCN (UseComparA_prefix (many_A)) (UseN (order_N))) (PrepNP (than_Prep) (UsePN (apcom_PN))))))))).
Definition s_233_3_h := s_230_3_h.
Definition s_234_1_p := s_233_1_p.
Definition s_234_3_h := s_231_3_h.
Definition s_235_1_p := s_233_1_p.
Definition s_235_2_p := s_232_2_p.
Definition s_235_4_h := s_232_4_h.
Definition s_236_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (AdjCN (UseComparA_prefix (many_A)) (UseN (order_N))) (PrepNP (than_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (apcom_contract_N)))))))))).
Definition s_236_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (apcom_contract_N))))))).
Definition s_237_1_p := s_236_1_p.
Definition s_237_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumCard (AdNum (more_than_AdN) (NumNumeral (N_one))))) (UseN (order_N))))))).
Definition s_238_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (twice_as_many_Det) (AdvCN (UseN (order_N)) (PrepNP (than_Prep) (UsePN (apcom_PN))))))))).
Definition s_238_2_p := s_232_2_p.
Definition s_238_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_twenty)))) (UseN (order_N))))))).
Definition s_239_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdvCN (AdjCN (UseComparA_prefix (many_A)) (UseN (order_N))) (SubjS (than_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (lose_V2)) (elliptic_NP_Pl))))))))))).
Definition s_239_3_h := s_230_3_h.
Definition s_240_1_p := s_239_1_p.
Definition s_240_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (lose_V2)) (DetCN (somePl_Det) (UseN (order_N))))))).
Definition s_241_1_p := s_239_1_p.
Definition s_241_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (lose_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_ten)))) (UseN (order_N))))))).
Definition s_241_4_h := s_232_4_h.
Definition s_242_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_500)))) (UseN (mips_N))))))))).
Definition s_242_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzx_N))) (UseComp (CompAP (ComparA (slow_A) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_500)))) (UseN (mips_N))))))))).
Definition s_242_4_h := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzx_N))))))))).
Definition s_243_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (sell_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_3000)))) (AdvCN (AdjCN (UseComparA_prefix (many_A)) (UseN (computer_N))) (PrepNP (than_Prep) (UsePN (apcom_PN))))))))).
Definition s_243_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (sell_V2)) (PredetNP (exactly_Predet) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_2500)))) (UseN (computer_N)))))))).
Definition s_243_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (sell_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_5500)))) (UseN (computer_N))))))).
Definition s_244_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (AdjCN (UseComparA_prefix (important_A)) (UseN (customer_N))) (PrepNP (than_Prep) (UsePN (itel_PN))))))))).
Definition s_244_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (AdjCN (UseComparA_prefix (important_A)) (UseN (customer_N))) (SubjS (than_Subj) (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (UseComp (CompNP (elliptic_NP_Sg)))))))))))).
Definition s_245_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (apcom_PN)) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (UseComparA_prefix (important_A)) (UseN (customer_N))))) (PrepNP (than_Prep) (UsePN (itel_PN))))))).
Definition s_245_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (apcom_PN)) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (UseComparA_prefix (important_A)) (UseN (customer_N))))) (SubjS (than_Subj) (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (elliptic_VP)))))))).
Definition s_246_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (DetCN (every_Det) (UseN (itel_computer_N))))))))).
Definition s_246_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzx_N))) (UseComp (CompCN (UseN (itel_computer_N))))))).
Definition s_246_4_h := s_242_4_h.
Definition s_247_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (DetCN (someSg_Det) (UseN (itel_computer_N))))))))).
Definition s_247_2_p := s_246_2_p.
Definition s_247_4_h := s_242_4_h.
Definition s_248_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (DetCN (anySg_Det) (UseN (itel_computer_N))))))))).
Definition s_248_2_p := s_246_2_p.
Definition s_248_4_h := s_242_4_h.
Definition s_249_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (ConjNP2 (and_Conj) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzx_N))) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzy_N)))))))))).
Definition s_249_3_h := s_242_4_h.
Definition s_250_1_p := (Sentence (UseCl (Present) (PPos) (PredVP the_pc6082_NP (UseComp (CompAP (ComparA (fast_A) (ConjNP2 (or_Conj) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzx_N))) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (itelzy_N)))))))))).
Definition s_250_3_h := s_242_4_h.
Definition s_251_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (factory_N)))) (PrepNP (in_Prep) (UsePN (birmingham_PN))))))).
Definition s_251_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (AdVVP (currently_AdV) (AdvVP (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (factory_N)))) (PrepNP (in_Prep) (UsePN (birmingham_PN)))))))).
Definition s_252_1_p := (Sentence (AdvS (since_1992_Adv) (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (UseComp (CompAdv (PrepNP (in_Prep) (UsePN (birmingham_PN))))))))).
Definition s_252_2_p := (Sentence (UseCl (Present) (PPos) (ImpersCl (AdVVP (now_AdV) (UseComp (CompAdv (year_1996_Adv))))))).
Definition s_252_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (UseComp (CompAdv (PrepNP (in_Prep) (UsePN (birmingham_PN))))) (in_1993_Adv))))).
Definition s_253_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (develop_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (editor_N))))) (since_1992_Adv))))).
Definition s_253_2_p := s_252_2_p.
Definition s_253_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (develop_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (editor_N))))) (in_1993_Adv))))).
Definition s_254_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (UseV (expand_V)) (since_1992_Adv))))).
Definition s_254_2_p := s_252_2_p.
Definition s_254_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (UseV (expand_V)) (in_1993_Adv))))).
Definition s_255_1_p := (Sentence (AdvS (since_1992_Adv) (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (make8do_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (loss_N)))))))).
Definition s_255_2_p := s_252_2_p.
Definition s_255_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (make8do_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (loss_N)))) (in_1993_Adv))))).
Definition s_256_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (make8do_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (loss_N)))) (since_1992_Adv))))).
Definition s_256_2_p := s_252_2_p.
Definition s_256_4_h := s_255_4_h.
Definition s_257_1_p := s_256_1_p.
Definition s_257_2_p := s_252_2_p.
Definition s_257_4_h := s_255_4_h.
Definition s_258_1_p := (Sentence (AdvS (in_march_1993_Adv) (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (found_V2)) (UsePN (itel_PN))))))).
Definition s_258_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (UseV (exist_V)) (in_1992_Adv))))).
Definition s_259_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (conference_N))) (AdvVP (UseV (start_V)) (on_july_4th_1994_Adv))))).
Definition s_259_2_p := (Sentence (UseCl (Past) (PPos) (ImpersCl (ComplSlash (SlashV2a (last_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_2)))) (UseN (day_N))))))).
Definition s_259_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (conference_N))) (AdvVP (UseComp (CompAdv (over_Adv))) (on_july_8th_1994_Adv))))).
Definition s_260_1_p := (Sentence (AdvS (yesterday_Adv) (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))))))).
Definition s_260_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (MassNP (UseN (today_N))) (UseComp (CompAdv (saturday_july_14th_Adv)))))).
Definition s_260_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (AdvVP (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (friday_13th_Adv))))).
Definition s_261_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (leave_V)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseV (leave_V))))))))).
Definition s_261_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (leave_V)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (anderson_PN)) (UseV (leave_V))))))))).
Definition s_261_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (leave_V)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (anderson_PN)) (UseV (leave_V))))))))).
Definition s_262_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (leave_V)) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseV (leave_V))))))))).
Definition s_262_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (leave_V)) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (anderson_PN)) (UseV (leave_V))))))))).
Definition s_262_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (leave_V)) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (anderson_PN)) (UseV (leave_V))))))))).
Definition s_263_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseComp (CompAP (PositA (present8attending_A)))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseV (leave_V))))))))).
Definition s_263_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (leave_V)) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (anderson_PN)) (UseComp (CompAP (PositA (present8attending_A))))))))))).
Definition s_263_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseComp (CompAP (PositA (present8attending_A)))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (anderson_PN)) (UseComp (CompAP (PositA (present8attending_A))))))))))).
Definition s_264_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseV (leave_V))))).
Definition s_264_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseV (leave_V))))).
Definition s_264_3_p := s_261_1_p.
Definition s_264_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (leave_V)) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseV (leave_V))))))))).
Definition s_265_1_p := s_264_1_p.
Definition s_265_2_p := s_264_2_p.
Definition s_265_3_p := s_262_1_p.
Definition s_265_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (leave_V)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseV (leave_V))))))))).
Definition s_266_1_p := s_264_1_p.
Definition s_266_2_p := s_264_2_p.
Definition s_266_3_p := s_265_5_h.
Definition s_266_5_h := s_262_1_p.
Definition s_267_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (revise_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_267_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (revise_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))).
Definition s_267_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (ComplSlash (SlashV2a (revise_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplVV (do_VV) (elliptic_VP))))))))).
Definition s_267_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (revise_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplVV (do_VV) (elliptic_VP))))))))).
Definition s_268_1_p := s_267_1_p.
Definition s_268_2_p := s_267_2_p.
Definition s_268_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (ComplSlash (SlashV2a (revise_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplVV (do_VV) (elliptic_VP))))))))).
Definition s_268_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (revise_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplVV (do_VV) (elliptic_VP))))))))).
Definition s_269_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseV (swim_V))))).
Definition s_269_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseV (swim_V))))).
Definition s_269_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (swim_V)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseV (swim_V))))))))).
Definition s_269_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (swim_V)) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseV (swim_V))))))))).
Definition s_270_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (swim_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (shore_N)))))))).
Definition s_270_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (swim_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (shore_N)))))))).
Definition s_270_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseV (swim_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (shore_N))))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseV (swim_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (shore_N)))))))))))).
Definition s_270_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (AdvVP (UseV (swim_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (shore_N))))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (swim_V)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (shore_N)))))))))))).
Definition s_271_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompAP (PositA (present8attending_A))))))).
Definition s_271_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseComp (CompAP (PositA (present8attending_A))))))).
Definition s_271_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseComp (CompAP (PositA (present8attending_A)))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseComp (CompAP (PositA (present8attending_A))))))))))).
Definition s_271_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseComp (CompAP (PositA (present8attending_A)))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompAP (PositA (present8attending_A))))))))))).
Definition s_272_1_p := s_271_1_p.
Definition s_272_2_p := s_271_2_p.
Definition s_272_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseComp (CompAP (PositA (present8attending_A)))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (UseComp (CompAP (PositA (present8attending_A))))))))))).
Definition s_272_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseComp (CompAP (PositA (present8attending_A)))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (UseComp (CompAP (PositA (present8attending_A))))))))))).
Definition s_273_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))).
Definition s_273_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))).
Definition s_273_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))))).
Definition s_273_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))))).
Definition s_274_1_p := s_273_1_p.
Definition s_274_2_p := s_273_2_p.
Definition s_274_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))) (SubjS (after_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))))).
Definition s_274_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ProgrVPa (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))))))))))).
Definition s_275_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N)))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePron (he_Pron)) (ComplSlash (SlashV2a (lose_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (temper_N))))))))))).
Definition s_275_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (lose_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (temper_N))))))).
Definition s_276_1_p := (Sentence (ExtAdvS (SubjS (when_Subj) (UseCl (Past) (PPos) (PredVP (UsePron (they_Pron)) (ComplSlash (SlashV2a (open_V2)) (UsePN (the_m25_PN)))))) (UseCl (Past) (PPos) (PredVP (MassNP (UseN (traffic_N))) (UseV (increase_V)))))).
Definition s_277_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (birmingham_PN)))) (in_1991_Adv))))).
Definition s_277_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (birmingham_PN)))) (in_1992_Adv))))).
Definition s_278_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuantOrd (PossPron (heRefl_Pron)) (NumSg) (OrdNumeral (N_one))) (UseN (novel_N)))) (in_1991_Adv))))).
Definition s_278_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuantOrd (PossPron (heRefl_Pron)) (NumSg) (OrdNumeral (N_one))) (UseN (novel_N)))) (in_1992_Adv))))).
Definition s_279_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (novel_N)))) (in_1991_Adv))))).
Definition s_279_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (UsePron (it_Pron))) (in_1992_Adv))))).
Definition s_280_1_p := s_279_1_p.
Definition s_280_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (novel_N)))) (in_1992_Adv))))).
Definition s_281_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (business_N))))) (in_1991_Adv))))).
Definition s_281_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (run_V2)) (UsePron (it_Pron)))) (in_1992_Adv))))).
Definition s_282_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (species_N))))) (in_1991_Adv))))).
Definition s_282_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (UsePron (it_Pron))) (in_1992_Adv))))).
Definition s_283_1_p := s_282_1_p.
Definition s_283_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (species_N))))) (in_1992_Adv))))).
Definition s_284_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))) (in_two_hours_Adv))))).
Definition s_284_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplVV (start_VV) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))) (at_8_am_Adv))))).
Definition s_284_4_h := (Sentence (UseCl (PastPerfect) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplVV (finish_VV) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))) (by_11_am_Adv))))).
Definition s_285_1_p := s_284_1_p.
Definition s_285_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (spend_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (AdjCN (PartVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))) (UseN (hour_N)))))))).
Definition s_286_1_p := s_284_1_p.
Definition s_286_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (spend_V2)) (DetCN (DetQuant (IndefArt) (NumCard (AdNum (more_than_AdN) (NumNumeral (N_two))))) (AdjCN (PartVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))) (UseN (hour_N)))))))).
Definition s_287_1_p := s_284_1_p.
Definition s_287_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))) (in_one_hour_Adv))))).
Definition s_288_1_p := s_284_1_p.
Definition s_288_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N))))))).
Definition s_289_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (species_N))))) (in_two_hours_Adv))))).
Definition s_289_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (spend_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (SentCN (UseN (hour_N)) (EmbedPresPart (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (species_N)))))))))))).
Definition s_290_1_p := s_289_1_p.
Definition s_290_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (species_N)))))))).
Definition s_291_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (DetCN (many_Det) (AdjCN (PositA (new_A)) (UseN (species_N))))) (in_two_hours_Adv))))).
Definition s_291_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (spend_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (SentCN (UseN (hour_N)) (EmbedPresPart (ComplSlash (SlashV2a (discover_V2)) (MassNP (AdjCN (PositA (new_A)) (UseN (species_N)))))))))))).
Definition s_292_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (business_N)))))) (PrepNP (in_Prep) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (year_N)))))))).
Definition s_292_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (spend_V2)) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (SentCN (UseN (year_N)) (EmbedPresPart (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (business_N)))))))))))).
Definition s_293_1_p := s_292_1_p.
Definition s_293_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (spend_V2)) (DetCN (DetQuant (IndefArt) (NumCard (AdNum (more_than_AdN) (NumNumeral (N_two))))) (SentCN (UseN (year_N)) (EmbedPresPart (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (business_N)))))))))))).
Definition s_294_1_p := s_292_1_p.
Definition s_294_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (business_N)))))))).
Definition s_295_1_p := (Sentence (AdvS (PrepNP (in_Prep) (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_two)))) (UseN (year_N)))) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (UseN (chain_N)) (PrepNP (part_Prep) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (business_N))))))))))).
Definition s_295_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (UseN (chain_N)) (PrepNP (part_Prep) (MassNP (UseN (business_N))))))) (for_two_years_Adv))))).
Definition s_296_1_p := s_295_1_p.
Definition s_296_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (UseN (chain_N)) (PrepNP (part_Prep) (MassNP (UseN (business_N))))))) (for_more_than_two_years_Adv))))).
Definition s_297_1_p := s_295_1_p.
Definition s_297_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (own_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (UseN (chain_N)) (PrepNP (part_Prep) (MassNP (UseN (business_N)))))))))).
Definition s_298_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (birmingham_PN)))) (for_two_years_Adv))))).
Definition s_298_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (birmingham_PN)))) (for_a_year_Adv))))).
Definition s_299_1_p := s_298_1_p.
Definition s_299_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (birmingham_PN)))) (for_exactly_a_year_Adv))))).
Definition s_300_1_p := s_298_1_p.
Definition s_300_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (birmingham_PN))))))).
Definition s_301_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (business_N))))) (for_two_years_Adv))))).
Definition s_301_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (run_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdjCN (PositA (own_A)) (UseN (business_N))))) (for_a_year_Adv))))).
Definition s_302_1_p := s_301_1_p.
Definition s_302_3_h := s_294_3_h.
Definition s_303_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))) (for_two_hours_Adv))))).
Definition s_303_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (report_N)))) (for_an_hour_Adv))))).
Definition s_304_1_p := s_303_1_p.
Definition s_304_3_h := s_288_3_h.
Definition s_305_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (new_A)) (UseN (species_N))))) (for_an_hour_Adv))))).
Definition s_306_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (new_A)) (UseN (species_N))))) (for_two_years_Adv))))).
Definition s_306_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (discover_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (new_A)) (UseN (species_N)))))))).
Definition s_307_1_p := (Sentence (AdvS (in_1994_Adv) (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (send_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (progress_report_N)))) (every_month_Adv)))))).
Definition s_307_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (send_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (progress_report_N)))) (in_july_1994_Adv))))).
Definition s_308_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (write_to_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (representative_N)))) (every_week_Adv))))).
Definition s_308_3_h := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (RelCN (UseN (representative_N)) (UseRCl (Past) (PPos) (StrandRelSlash (that_RP) (SlashVP (UsePN (smith_PN)) (SlashV2a (write_to_V2)))))) (every_week_Adv)))))).
Definition s_309_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (house_N)))) (at_a_quarter_past_five_Adv))))).
Definition s_309_2_p := (Sentence (PredVPS (UsePron (she_Pron)) (ConjVPS2 (and_Conj) (Past) (PPos) (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (UseN (taxi_N)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (station_N))))))) (Past) (PPos) (ComplSlash (SlashV2a (catch_V2)) (DetCN (DetQuantOrd (DefArt) (NumSg) (OrdNumeral (N_one))) (AdvCN (UseN (train_N)) (PrepNP (to_Prep) (UsePN (luxembourg_PN))))))))).
Definition s_310_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (lose_V2)) (DetCN (somePl_Det) (UseN (file_N))))))).
Definition s_310_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (they_Pron)) (AdvVP (PassV2s (destroy_V2)) (SubjS (when_Subj) (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (PossPron (she_Pron)) (NumSg)) (UseN (hard_disk_N))) (UseV (crash_V))))))))).
Definition s_311_1_p := (Sentence (UseCl (PastPerfect) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (house_N)))) (at_a_quarter_past_five_Adv))))).
Definition s_311_2_p := (PSentence (then_PConj) (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (AdvCN (UseN (taxi_N)) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (station_N)))))))))).
Definition s_311_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (house_N)))) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (AdvVP (ComplSlash (SlashV2a (take_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (taxi_N)))) (PrepNP (to_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (station_N)))))))))))).
Definition s_312_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (AdVVP (always_AdV) (AdvVP (ComplSlash (SlashV2a (deliver_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (report_N)))) (late_Adv)))))).
Definition s_312_2_p := (Sentence (AdvS (in_1993_Adv) (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (ComplSlash (SlashV2a (deliver_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (report_N)))))))).
Definition s_312_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (AdvVP (ComplSlash (SlashV2a (deliver_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (report_N)))) (late_Adv)) (in_1993_Adv))))).
Definition s_313_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (itel_PN)) (AdVVP (never_AdV) (AdvVP (ComplSlash (SlashV2a (deliver_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (report_N)))) (late_Adv)))))).
Definition s_313_2_p := s_312_2_p.
Definition s_313_4_h := s_312_4_h.
Definition s_314_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ComplSlash (SlashV2a arrive_in_V2) (UsePN (paris_PN))) (on_the_5th_of_may_1995_Adv))))).
Definition s_314_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (MassNP (UseN (today_N))) (UseComp (CompAdv (the_15th_of_may_1995_Adv)))))).
Definition s_314_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePron (she_Pron)) (AdVVP (still_AdV) (UseComp (CompAdv (PrepNP (in_Prep) (UsePN (paris_PN))))))))).
Definition s_314_5_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseComp (CompAdv (PrepNP (in_Prep) (UsePN (paris_PN))))) (on_the_7th_of_may_1995_Adv))))).
Definition s_315_1_p := (Sentence (AdvS (SubjS (when_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a arrive_in_V2) (UsePN (katmandu_PN)))))) (UseCl (PastPerfect) (PPos) (PredVP (UsePron (she_Pron)) (AdvVP (ProgrVPa (UseV (travel_V))) (for_three_days_Adv)))))).
Definition s_315_3_h := (Sentence (UseCl (PastPerfect) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (ProgrVPa (UseV (travel_V))) (PrepNP (on_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (AdvCN (UseN (day_N)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (ComplSlash (SlashV2a arrive_in_V2) (UsePN (katmandu_PN))))))))))))).
Definition s_316_1_p := (Sentence (PredVPS (UsePN (jones_PN)) (ConjVPS2 (and_Conj) (Past) (PPos) (AdvVP (UseV (graduate_V)) (in_march_Adv)) (PresentPerfect) (PPos) (AdvVP (UseComp (CompAP (PositA (employed_A)))) (ever_since_Adv))))).
Definition s_316_2_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (UseComp (CompAP (PositA (unemployed_A)))) (in_the_past_Adv))))).
Definition s_316_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (AdvVP (AdvVP (UseComp (CompAP (PositA (unemployed_A)))) (at_some_time_Adv)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePron (he_Pron)) (UseV (graduate_V))))))))).
Definition s_317_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (every_Det) (UseN (representative_N))) (ComplSlash (SlashV2a (read_V2)) (DetCN (DetQuant (this_Quant) (NumSg)) (UseN (report_N))))))).
Definition s_317_2_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumCard (NumNumeral (N_two)))) (UseN (representative_N))) (AdvVP (ComplSlash (SlashV2a (read_V2)) (UsePron (it_Pron))) (at_the_same_time_Adv))))).
Definition s_317_3_p := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (no_Quant) (NumSg)) (UseN (representative_N))) (ComplSlash (SlashV2V (take_V2V) (ComplSlash (SlashV2a (read_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))) (DetCN (DetQuant (IndefArt) (NumCard (AdNum (less_than_AdN) (half_a_Card)))) (UseN (day_N))))))).
Definition s_317_4_p := (Sentence (UseCl (Present) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumCard (NumNumeral (N_sixteen)))) (UseN (representative_N)))))).
Definition s_317_6_h := (Sentence (UseCl (Past) (PPos) (ImpersCl (ComplSlash (SlashV2V (take_V2V) (ComplSlash (SlashV2a (read_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (report_N))))) (DetCN (DetQuant (DefArt) (NumPl)) (AdjCN (ComparA (many_A) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (week_N)))) (UseN (representative_N)))))))).
Definition s_318_1_p := (Sentence (ExtAdvS (SubjS (while_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ProgrVPa (ComplSlash (SlashV2a (update_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (program_N)))))))) (PredVPS (UsePN (mary_PN)) (ConjVPS2 (and_Conj) (Past) (PPos) (UseV (come_in_V)) (Past) (PPos) (ComplSlash (Slash3V3 (tell_about_V3) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (board_meeting_N)))) (UsePron (he_Pron))))))).
Definition s_318_2_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePron (she_Pron)) (AdvVP (ComplVV (finish_VV) (elliptic_VP)) (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePron (he_Pron)) (ComplVV (do_VV) (elliptic_VP))))))))).
Definition s_319_1_p := (Sentence (ExtAdvS (SubjS (before_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (buy_V2)) (DetCN (DetQuant (PossPron (itRefl_Pron)) (NumSg)) (AdjCN (PositA (present8current_A)) (UseN (office_building_N)))))))) (UseCl (PastPerfect) (PPos) (ImpersCl (AdvVP (AdvVP (ProgrVPa (ComplSlash (SlashV2a (pay_V2)) (MassNP (UseN (mortgage_interest_N))))) (PrepNP (on_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (previous_A)) (UseN (one_N)))))) (for_8_years_Adv)))))).
Definition s_319_2_p := (Sentence (AdvS (SubjS (since_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (apcom_PN)) (ComplSlash (SlashV2a (buy_V2)) (DetCN (DetQuant (PossPron (itRefl_Pron)) (NumSg)) (AdjCN (PositA (present8current_A)) (UseN (office_building_N)))))))) (UseCl (PresentPerfect) (PPos) (ImpersCl (AdvVP (AdvVP (ProgrVPa (ComplSlash (SlashV2a (pay_V2)) (MassNP (UseN (mortgage_interest_N))))) (PrepNP (on_Prep) (UsePron (it_Pron)))) (for_more_than_10_years_Adv)))))).
Definition s_319_4_h := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (apcom_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (pay_V2)) (MassNP (UseN (mortgage_interest_N))))) (for_a_total_of_15_years_or_more_Adv))))).
Definition s_320_1_p := (Sentence (ExtAdvS (SubjS (when_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (get_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (AdvCN (UseN (job_N)) (PrepNP (at_Prep) (UsePN (the_cia_PN))))))))) (UseCl (Past) (PPos) (PredVP (UsePron (he_Pron)) (ComplVS (know_VS) (UseCl (Conditional) (PPos) (PredVP (UsePron (he_Pron)) (AdVVP (never_AdV) (PassVPSlash (SlashV2V (allow_V2V) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumPl)) (UseN (memoir_N)))))))))))))).
Definition s_320_3_h := (Sentence (UseCl (Present) (PPos) (ImpersCl (AdvVP (UseComp (CompNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (case_N))))) (SubjS (that_Subj) (PredVPS (UsePN (jones_PN)) (ConjVPS2 (and_Conj) (Present) (UncNeg) (PassVPSlash (elliptic_VPSlash)) (Future) (PPos) (AdVVP (never_AdV) (PassVPSlash (SlashV2V (allow_V2V) (ComplSlash (SlashV2a (write_V2)) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumPl)) (UseN (memoir_N)))))))))))))).
Definition s_321_1_p := (Sentence (UseCl (PresentPerfect) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (UseComp (CompAdv (PrepNP (to_Prep) (UsePN (florence_PN))))) (twice_Adv)) (in_the_past_Adv))))).
Definition s_321_2_p := (Sentence (UseCl (Future) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (AdvVP (AdvVP (UseV (go8travel_V)) (PrepNP (to_Prep) (UsePN (florence_PN)))) (twice_Adv)) (in_the_coming_year_Adv))))).
Definition s_321_4_h := (Sentence (AdvS (two_years_from_now_Adv) (UseCl (FuturePerfect) (PPos) (PredVP (UsePN (smith_PN)) (AdvVP (UseComp (CompAdv (PrepNP (to_Prep) (UsePN (florence_PN))))) (at_least_four_times)))))).
Definition s_322_1_p := (Sentence (AdvS (last_week_Adv) (UseCl (Past) (PPos) (PredVP (UsePron (i_Pron)) (AdVVP (already_AdV) (ComplVS (know_VS) (ExtAdvS (SubjS (when_Subj) (ExtAdvS (in_a_months_time_Adv) (UseCl (Conditional) (PPos) (PredVP (UsePN (smith_PN)) (ComplVS (discover_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePron (she_Pron)) (PassV2 (dupe_V2))))))))) (UseCl (Conditional) (PPos) (PredVP (UsePron (she_Pron)) (UseComp (CompAP (PositA (furious_A))))))))))))).
Definition s_322_3_h := (Sentence (UseCl (Future) (PPos) (ImpersCl (AdvVP (UseComp (CompNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (case_N))))) (SubjS (that_Subj) (ConjS2 (semicolon_and_Conj) (AdvS (in_a_few_weeks_Adv) (UseCl (Future) (PPos) (PredVP (UsePN (smith_PN)) (ComplVS (discover_VS) (UseCl (PresentPerfect) (PPos) (PredVP (UsePron (she_Pron)) (PassV2 (dupe_V2)))))))) (UseCl (Future) (PPos) (PredVP (UsePron (she_Pron)) (UseComp (CompAP (PositA (furious_A)))))))))))).
Definition s_323_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (RelNPa (UsePron (no_one_Pron)) (UseRCl (Present) (PPos) (RelVP (IdRP) (AdvVP (ProgrVPa (UseV (gamble_V))) (PositAdvAdj (serious_A)))))) (AdvVP (UseV (stop_V)) (SubjS (until_Subj) (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (UseComp (CompAP (PositA (broke_A))))))))))).
Definition s_323_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePron (no_one_Pron)) (ComplVV (can_VV) (AdvVP (UseV (gamble_V)) (SubjS (when_Subj) (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (UseComp (CompAP (PositA (broke_A)))))))))))).
Definition s_323_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (RelNPa (UsePron (everyone_Pron)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplVV (start_VV) (AdvVP (UseV (gamble_V)) (PositAdvAdj (serious_A))))))) (AdvVP (UseV (stop_V)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (AdvCN (UseN (moment_N)) (SubjS (when_Subj) (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (UseComp (CompAP (PositA (broke_A)))))))))))))).
Definition s_324_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (RelNPa (UsePron (no_one_Pron)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplVV (start_VV) (AdvVP (UseV (gamble_V)) (PositAdvAdj (serious_A))))))) (AdvVP (UseV (stop_V)) (SubjS (until_Subj) (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (UseComp (CompAP (PositA (broke_A))))))))))).
Definition s_324_3_h := (Sentence (UseCl (Present) (PPos) (PredVP (RelNPa (UsePron (everyone_Pron)) (UseRCl (Present) (PPos) (RelVP (IdRP) (ComplVV (start_VV) (AdvVP (UseV (gamble_V)) (PositAdvAdj (serious_A))))))) (AdvVP (UseV (continue_V)) (SubjS (until_Subj) (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (UseComp (CompAP (PositA (broke_A))))))))))).
Definition s_325_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (RelNPa (UsePron (nobody_Pron)) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (asleep_A))))))) (AdVVP (ever_AdV) (ComplVS (know_VS) (UseCl (Present) (PPos) (PredVP (UsePron (he_Pron)) (UseComp (CompAP (PositA (asleep_A))))))))))).
Definition s_325_2_p := (PSentence (but_PConj) (UseCl (Present) (PPos) (PredVP (DetCN (somePl_Det) (UseN (person_N))) (AdvVP (ComplVS (know_VS) (UseCl (PresentPerfect) (PPos) (PredVP (UsePron (they_Pron)) (UseComp (CompAP (PositA (asleep_A))))))) (SubjS (after_Subj) (UseCl (PresentPerfect) (PPos) (PredVP (UsePron (they_Pron)) (UseComp (CompAP (PositA (asleep_A))))))))))).
Definition s_325_4_h := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (somePl_Det) (UseN (person_N))) (ComplVS (discover_VS) (UseCl (PresentPerfect) (PPos) (PredVP (UsePron (they_Pron)) (UseComp (CompAP (PositA (asleep_A)))))))))).
Definition s_326_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (build_V2)) (UsePN (mtalk_PN))) (in_1993_Adv))))).
Definition s_326_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (finish_V2)) (UsePN (mtalk_PN))) (in_1993_Adv))))).
Definition s_327_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ProgrVPa (ComplSlash (SlashV2a (build_V2)) (UsePN (mtalk_PN)))) (in_1993_Adv))))).
Definition s_327_3_h := s_326_3_h.
Definition s_328_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (PrepNP (from_Prep) (UsePN (apcom_PN)))) (in_1993_Adv))))).
Definition s_328_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (contract_N)))) (in_1993_Adv))))).
Definition s_329_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (AdvVP (ProgrVPa (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (PrepNP (from_Prep) (UsePN (apcom_PN)))) (in_1993_Adv))))).
Definition s_329_3_h := s_328_3_h.
Definition s_330_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (own_V2)) (UsePN (apcom_PN))) (from_1988_to_1992_Adv))))).
Definition s_330_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (own_V2)) (UsePN (apcom_PN))) (in_1990_Adv))))).
Definition s_331_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP2 (and_Conj) (UsePN (smith_PN)) (UsePN (jones_PN))) (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_331_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_332_1_p := s_331_1_p.
Definition s_332_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (leave_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (meeting_N))))))).
Definition s_333_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (ConjNP3 (and_Conj) (UsePN (smith_PN)) (UsePN (anderson_PN)) (UsePN (jones_PN))) (UseV (meet_V))))).
Definition s_333_3_h := (Sentence (UseCl (Past) (PPos) (ExistNP (DetCN (DetQuant (IndefArt) (NumSg)) (RelCN (ComplN2 group_N2 (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (person_N)))) (UseRCl (Past) (PPos) (RelVP (that_RP) (UseV (meet_V))))))))).
Definition s_334_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplVS (know_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (in_1992_Adv)))))))).
Definition s_334_3_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (in_1992_Adv))))).
Definition s_335_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplVS (believe_VS) (UseCl (PastPerfect) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (in_1992_Adv)))))))).
Definition s_335_3_h := s_334_3_h.
Definition s_336_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplVV (manage_VV) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (in_1992_Adv))))).
Definition s_336_3_h := s_334_3_h.
Definition s_337_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplVV (try_VV) (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (in_1992_Adv))))).
Definition s_337_3_h := s_334_3_h.
Definition s_338_1_p := (Sentence (UseCl (Present) (PPos) (ImpersCl (UseComp (CompAP (SentAP (PositA (true_A)) (EmbedS (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (in_1992_Adv))))))))))).
Definition s_338_3_h := s_334_3_h.
Definition s_339_1_p := (Sentence (UseCl (Present) (PPos) (ImpersCl (UseComp (CompAP (SentAP (PositA (false_A)) (EmbedS (UseCl (Past) (PPos) (PredVP (UsePN (itel_PN)) (AdvVP (ComplSlash (SlashV2a (win_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N)))) (in_1992_Adv))))))))))).
Definition s_339_3_h := s_334_3_h.
Definition s_340_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (UsePN (jones_PN)))))).
Definition s_340_2_p := (Sentence (ExtAdvS (SubjS (if_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))) (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (PossPron (he_Pron)) (NumSg)) (UseN (heart_N))) (ProgrVPa (UseV (beat_V))))))).
Definition s_340_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2V (see_V2V) (UseV (beat_V))) (DetCN (DetQuant (GenNP (UsePN (jones_PN))) (NumSg)) (UseN (heart_N))))))).
Definition s_341_1_p := s_340_1_p.
Definition s_341_2_p := (Sentence (ExtAdvS (SubjS (when_Subj) (UseCl (Past) (PPos) (PredVP (UsePN (jones_PN)) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))))) (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (PossPron (he_Pron)) (NumSg)) (UseN (heart_N))) (ProgrVPa (UseV (beat_V))))))).
Definition s_341_4_h := s_340_4_h.
Definition s_342_1_p := s_341_1_p.
Definition s_342_3_h := s_081_3_h.
Definition s_343_1_p := s_341_1_p.
Definition s_343_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (UsePN (jones_PN)) (UseComp (CompNP (DetCN (DetQuant (DefArt) (NumSg)) (ComplN2 (chairman_N2) (UsePN (itel_PN))))))))).
Definition s_343_4_h := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (smith_PN)) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (DetCN (DetQuant (DefArt) (NumSg)) (ComplN2 (chairman_N2) (UsePN (itel_PN)))))))).
Definition s_344_1_p := (Sentence (UseCl (Past) (PPos) (PredVP (UsePN (helen_PN)) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (answer_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (phone_N))))) (DetCN (DetQuant (DefArt) (NumSg)) (ComplN2 (chairman_N2) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (department_N))))))))).
Definition s_344_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumSg)) (ComplN2 (chairman_N2) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (department_N))))) (UseComp (CompCN (UseN (person_N))))))).
Definition s_344_4_h := (Sentence (UseCl (Present) (PPos) (ExistNP (RelNPa (UsePron (someone_Pron)) (UseRCl (Past) (PPos) (StrandRelSlash (IdRP) (SlashVP (UsePN (helen_PN)) (SlashV2V (see_V2V) (ComplSlash (SlashV2a (answer_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (phone_N)))))))))))).
Definition s_345_1_p := (Sentence (PredVPS (UsePN (smith_PN)) (ConjVPS2 (and_Conj) (Past) (PPos) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (UsePN (jones_PN))) (Past) (PPos) (ComplSlash (SlashV2V (elliptic_V2V) (ComplSlash (SlashV2a (make8do_V2)) (DetCN (DetQuant (IndefArt) (NumSg)) (UseN (copy_N))))) (DetCN (DetQuant (PossPron (heRefl_Pron)) (NumSg)) (UseN (secretary_N))))))).
Definition s_345_3_h := s_340_1_p.
Definition s_346_1_p := (Sentence (PredVPS (UsePN (smith_PN)) (ConjVPS2 (or_Conj) (Past) (PPos) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (UsePN (jones_PN))) (Past) (PPos) (ComplSlash (SlashV2V (elliptic_V2V) (ComplSlash (SlashV2a (cross_out_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (crucial_A)) (UseN (clause_N)))))) (elliptic_NP_Sg))))).
Definition s_346_3_h := (Sentence (PredVPS (UsePN (smith_PN)) (ConjVPS2 (either7or_DConj) (Past) (PPos) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (sign_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (contract_N))))) (UsePN (jones_PN))) (Past) (PPos) (ComplSlash (SlashV2V (see_V2V) (ComplSlash (SlashV2a (cross_out_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (AdjCN (PositA (crucial_A)) (UseN (clause_N)))))) (UsePN (jones_PN)))))).


(** Theorems **)


Theorem FraCaS001: s_001_1_p->s_001_3_h.
cbv.
intros.
firstorder.
Qed.

Theorem FraCaS002: (s_002_1_p/\s_002_2_p)->s_002_4_h.
cbv.
destruct great_A as [greatness  greatLimit].
destruct italian_A as [italianess itLimit].
firstorder.
exists x.
firstorder.
assert (H' := H x (conj H0 H3)).
generalize H'.
apply wantCovariant_K.
intros tenor' t gt.
split.
destruct gt as [greatTenor' p].
destruct p as [p eq].
rewrite -> eq.
firstorder.
destruct gt as [greatTenor' p].
destruct p as [p eq].
rewrite -> eq.
firstorder.
Qed.


Definition s_003_1_p_fixed := (Sentence (UseCl (Present) (PPos)
   (PredVP (DetCN (all_Det) (UseN (man_N)))
           (ComplVV (want_VV) (UseComp (CompNP (DetCN (DetQuant (IndefArt) (NumSg)) (AdjCN (PositA (great_A)) (UseN (tenor_N)))))))))).

Theorem FraCaS003: (s_003_1_p_fixed/\s_003_2_p)->s_003_4_h. cbv. 
destruct great_A as [greatness thG].
destruct italian_A as [italianess thI].
firstorder.
Qed.

Theorem FraCaS004: (s_004_1_p/\s_004_2_p)->s_004_4_h. cbv. firstorder. Qed.

Theorem FraCaS005: s_005_1_p->(s_005_3_h). cbv.  firstorder. Qed.

Theorem FraCaS006: (s_006_1_p)->not(s_006_3_h). cbv. intro.  firstorder. Qed.

Theorem FraCaS007: (s_007_1_p)->(s_007_3_h). cbv. intro.  firstorder. Qed.

Theorem FraCaS008: (s_008_1_p)->(s_008_3_h). cbv. intro.  firstorder. Qed.

Theorem FraCaS009: (s_009_1_p)->(s_009_3_h). cbv. intro.  firstorder. Qed.

Theorem FraCaS010: (s_010_1_p)->(s_010_3_h). cbv. intro. firstorder. Qed.

Theorem FraCaS011: ((s_011_1_p)/\(s_011_2_p))->(s_011_4_h). cbv. firstorder. Qed.
Theorem FraCaS012: (s_012_1_p)->(s_012_3_h). cbv. firstorder. destruct great_A as [great]. firstorder. Abort All. (**this is undefined in the FraCaS, having the answer "not many". In principle, the conclusion should follow only if "few" implies existence. See the definition of a_few_Det above. **)

Definition s_013_2a_p := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (each_Det)(RelCN (AdjCN (PositA (leading_A)) (UseN (tenor_N))) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (PositA (excellent_A)))))))) (UseComp (CompAP (PositA (indispensable_A))))))).


Theorem FraCaS013: ((s_013_1_p)/\(s_013_2a_p))->(s_013_4_h).
cbv.
destruct leading_A as [leading].
destruct indispensable_A as [indispensable].
destruct excellent_A as [excellent].
firstorder. exists x. exists x0. firstorder.

(* FIXME: we're missing indispensable (excellent x) => indispensable x.
RelCN works at the CN level, not at the NP, so it is difficult to fix.
*)


Theorem FraCaS014: (s_014_1_p) -> (s_014_2_p)->not(s_014_4_h). cbv.
intros. destruct leading_A as [leading]. Abort All.
(** FIXME: Anaphora. this cannot be proven at the moment, the problem is the numeral one, "one of the" has an anaphoric existential interpretation, has to pick one of the two existentials introduced by neither. This is not what we get.**)

Lemma le_mono : forall n, forall (p q : CN), (forall x, p x -> q x) -> n <= CARD p -> n <= CARD q.
intros.
apply le_trans with (y := CARD p).
assumption.
apply CARD_monotonous.
assumption.
Qed.

Lemma le_mono' : forall n, forall (p q : CN), (forall x, q x -> p x) -> CARD p <= n -> CARD q <= n.
intros.
apply le_trans with (y := CARD p).
apply CARD_monotonous.
assumption.
assumption.
Qed.

Variable CARD_exists : forall P:(object -> Prop), 1 <= CARD P -> exists x, P x.
Theorem FraCaS015: s_015_1_p->s_015_3_h.
cbv.
intro P1.
apply CARD_exists.
apply le_trans with (y := 3).
lia.
generalize P1.
apply le_mono.
firstorder. Qed.

Theorem FraCaS016: s_016_1_p->s_016_3_h. cbv. firstorder. Abort All.
(**this has the answer "at most two" which pretty much means yes, it is one of the strangest cases, not well defined, Maccartney who did the XML marks these cases as undefined. If we were to implement this here we'd need the conclusion to be exactly the same statement as P1. **)



(* End of subsection 1.1, 12/14 *)
(* SEC 1.2*)

Theorem FraCaS017: (s_017_1_p)->(s_017_3_h). cbv. intro.  firstorder. Qed.

Theorem FraCaS018: s_018_1_p -> s_018_2_p -> s_018_3_p-> s_018_5_h. cbv.
destruct in_Prep as [inP inV inC].
destruct within_Prep as [withinP withinV withinC].
destruct europe_PN as [europe regionN].
intros P1 P2 P3.
firstorder.
Qed.

Definition s_019_1_p_fixed := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (UseN (european_N)))) (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))).
Definition s_019_5_h_fixed := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (DefArt) (NumPl)) (UseN (european_N)))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))).

Theorem FraCaS019_fixed: (s_019_1_p_fixed/\s_019_2_p/\s_019_3_p)->(s_019_5_h_fixed). cbv. intros.
firstorder. Qed.

(**all is a predeterminer and the parse tree involves an indefart
which gives an existential rather than a universal quantifier for
all. In this way, sentences with all have existential force contrary
to fact**)

Theorem FraCaS019: (s_019_1_p/\s_019_2_p/\s_019_3_p)->(s_019_5_h). cbv. intros. 
firstorder. Qed.

Theorem FraCaS020: (s_020_1_p/\s_020_2_p/\s_020_3_p)->(s_020_5_h).  cbv. firstorder. Qed.

Theorem FraCaS021: s_021_1_p -> s_021_2_p -> s_021_3_p->(s_021_5_h). cbv.
destruct in_Prep as [inP inV inC].
 destruct within_Prep as [within withinVerid withinCov].
destruct europe_PN as [europe regionN].
intros P1 P2 P3.
 firstorder.
 apply P3.
firstorder.
 Qed.

  
Theorem FraCaS022: s_022_1_p->(s_022_3_h).  cbv. intros.  firstorder. Abort All. (**UNK example**)

Theorem FraCaS023: s_023_1_p->(s_023_3_h).
cbv. intro. destruct on_time_Adv. firstorder.
Qed.


Theorem FraCaS024: s_024_1_p->(s_024_3_h).  cbv. intros. firstorder.
destruct interesting_A as [interest th].
firstorder.
generalize H0.
apply le_mono.
firstorder.
exists x2.
firstorder.
destruct interesting_A as [interest th].
firstorder.
Qed.

Theorem FraCaS025: s_025_1_p->(s_025_3_h).  cbv.
destruct major_A as [major thM] eqn:majorEq.
destruct national_A as [national thN] eqn:nationalEq.
destruct in_Prep as [inPrep inVerid inVeridCov].
intros [P1 P2].
firstorder.
exists x.
firstorder.
apply inVerid with (prepArg := (fun k : object -> Prop =>
          exists x : object,
            (thM <=
             major
               (fun x0 : object =>
                thN <= national newspaper_N x0 /\
                property newspaper_N x0) x /\
             thN <= national newspaper_N x /\
             property newspaper_N x) /\ k x)).
apply inVeridCov with (v := (fun y : object =>
          (forall x : object,
           result_N x /\ (exists subject : object, publish_V2 x subject) ->
           get_V2 x y) /\
          get_V2
            (environment
               (fun x : object =>
                result_N x /\
                (exists subject : object, publish_V2 x subject))) y /\
          result_N
            (environment
               (fun x : object =>
                result_N x /\
                (exists subject : object, publish_V2 x subject))) /\
          (exists subject : object,
             publish_V2
               (environment
                  (fun x : object =>
                   result_N x /\
                   (exists subject0 : object, publish_V2 x subject0)))
               subject))).
firstorder.
assumption.
generalize P2.
apply le_mono.
intro.
intro.
split.
firstorder.
destruct H1 as [delegx0 x0publInMNP].
split.
apply inVerid with (prepArg := (apNP1 (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (mkSubsective major thM)) (AdjCN (PositA (national_A)) (UseN (newspaper_N))))))) (subject := x0).
apply  inVeridCov with (v := ((ComplSlash (SlashV2a (get_V2)) (PPartNP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (result_N))) (publish_V2))) ) (fun x => True)).
firstorder.
cbv.
rewrite -> nationalEq.
firstorder.
firstorder.
Qed.


(* Definition s_026_1_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (most_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (UseComp (CompAP (AdvAP (PositA (resident_A)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))). *)
(* Definition s_026_2_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (UseN (european_N)))) (UseComp (CompCN (UseN (person_N))))))). *)
(* Definition s_026_3_p := (Sentence (UseCl (Present) (PPos) (PredVP (PredetNP (all_Predet) (DetCN (DetQuant (IndefArt) (NumPl)) (RelCN (UseN (person_N)) (UseRCl (Present) (PPos) (RelVP (IdRP) (UseComp (CompAP (AdvAP (PositA (resident_A)) (PrepNP (in_Prep) (UsePN (europe_PN))))))))))) (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN)))))))). *)

Definition european_travel x := european_N x /\ (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN))))) european_N x.


Theorem FraCaS026: s_026_1_p/\s_026_2_p/\s_026_3_p->s_026_5_h.
cbv.
destruct europe_PN as [europe regionN].
destruct in_Prep as [inP inVerid inCov].
destruct within_Prep as [within withinVerid withinCov].
intros [P1 P2].
cut (forall x,
         european_N x /\
         AdvAP (apA resident_A)
           (inP (fun k : object -> Prop => k europe)) european_N
           x -> european_N x /\
     can_VV
       (fun (_ : object -> Prop) (x0 : object) =>
        within (fun k : object -> Prop => k europe)
          (fun y : object => PositAdvAdj free_A (fun y0 : object => travel_V y0) y) x0) x).
intro. firstorder.
generalize H2.
apply le_mono.
firstorder.
firstorder.
Qed.

Theorem FraCaS027: s_027_1_p -> s_027_2_p -> s_027_3_p -> s_027_5_h.
cbv.
destruct from_Prep as [from fromVerid fromVeridCov].
destruct sweden_PN as [sweden countryN].
destruct scandinavia_PN as [scandinavia regionN].
intros P1 P2 P3.
firstorder.
rewrite -> H.
apply CARD_monotonous.
firstorder.
Qed.

 Theorem FraCaS028: s_028_1_p/\s_028_2_p/\s_028_3_p->s_028_5_h.
cbv. destruct from_Prep as [from fromVerid]. firstorder. (** UNK **) Abort All.


Variable usedToBeCov_K : forall (p q : VP), (forall x xClass, p xClass x -> q xClass x) -> forall x , use_VV p x -> use_VV q x.
Theorem FraCaS029: s_029_1_p->(s_029_3_h). cbv.
destruct leading_A as [leading thL].
firstorder. 
firstorder. 
exists x. exists x0. 
firstorder.
apply usedToBeCov_K with (p := (fun xClass x => thL <= leading businessman_N x /\ businessman_N x)).
firstorder. assumption.
apply usedToBeCov_K with (p := (fun xClass x => thL <= leading businessman_N x /\ businessman_N x)).
firstorder. assumption.
Qed.



Theorem FraCaS030: s_030_1_p->(s_030_3_h).  cbv. intros. destruct at_home_Adv. firstorder.
exists x0. exists x1. firstorder. apply H0. (* UNK *)  Abort All.

Theorem FraCaS031: s_031_1_p->(s_031_3_h).  cbv. firstorder.

destruct at_home_Adv as [atHome atHomeVerid].
destruct atHomeVerid as [atHomeVerid atHomeVeridCov].
generalize H. apply le_mono. firstorder.
generalize H1. apply atHomeVeridCov. firstorder.
Qed.

Theorem FraCaS032: s_032_1_p->(s_032_3_h). cbv. destruct at_home_Adv. firstorder.  (** UNK **) Abort All.
      (** End of sec 2.2 16/16  \o/ )**)

(* SEC 1.3 *)

      (* FraCaS033 -> 037 UNK *)

 Theorem FraCaS033: s_033_1_p->(s_033_3_h). cbv. 
                                            firstorder.       (**UNK**)


 Theorem FraCaS034: s_034_1_p/\ s_034_2_p/\ s_034_3_p->(s_034_5_h). cbv. 
destruct in_Prep as [inPrep inVerid].
destruct in_Prep as [within withinVerid].
firstorder. Abort all. (*UNK*)

 Theorem FraCaS035: s_035_1_p/\ s_035_2_p/\ s_035_3_p->(s_035_5_h). cbv. 
destruct in_Prep as [inPrep inVerid].
destruct in_Prep as [within withinVerid].
firstorder. Abort all. (*UNK*)

 Theorem FraCaS036: s_036_1_p/\ s_036_2_p/\ s_036_3_p->(s_036_5_h). cbv. 
destruct in_Prep as [inPrep inVerid].
destruct in_Prep as [within withinVerid].
firstorder. Abort all. (*UNK*)

  Theorem FraCaS037: s_037_1_p/\ s_037_2_p/\ s_037_3_p->(s_037_5_h). cbv. 
destruct in_Prep as [inPrep inVerid].
destruct in_Prep as [within withinVerid].
firstorder. Abort all. (*UNK*)

Theorem FraCaS038: s_038_1_p->not(s_038_3_h).  cbv. destruct on_time_Adv. firstorder. Qed.

Theorem FraCaS039: s_039_1_p->(s_039_3_h).  cbv. destruct on_time_Adv. firstorder. Abort all. (**UNK**)

Theorem FraCaS040: s_040_1_p->s_040_3_h. cbv.
firstorder.
exists x.
firstorder.
exists x0.
firstorder. (* UNK *)
Abort All.

Theorem FraCaS041: s_041_1_p->s_041_3_h. cbv.  firstorder. destruct in_Prep as [inPrep inVerid]. destruct in_Prep as [within withinVerid]. firstorder. 
(**UNK**) Abort All. 

Theorem FraCaS042: (s_042_1_p/\s_042_2_p/\s_042_3_p)->(s_042_5_h).  cbv. destruct in_Prep as [inPrep inVerid].
destruct in_Prep as [within withinVerid].

firstorder. Abort All.  (**UNK**)

Theorem FraCaS043: (s_043_1_p/\s_043_2_p/\s_043_3_p)->(s_043_5_h). cbv. destruct in_Prep as [inPrep inVerid]. destruct in_Prep as [within withinVerid]. firstorder. 
(**UNK**) Abort All.


Theorem FraCaS044: s_044_1_p -> s_044_2_p -> s_044_3_p -> s_044_5_h.
cbv.
intros P1  P2  P3.
destruct from_Prep as [from fromVerid fromVeridCov].
destruct southern_europe_PN as [southernEurope regionN].
destruct portugal_PN as [portugal countryN].
generalize P1. apply le_mono'. firstorder.
apply P3.
firstorder.
Qed.

Theorem FraCaS045: s_045_1_p->(s_045_3_h).
cbv.
destruct leading_A.
firstorder.
(* UNK *) Abort All. 

Theorem FraCaS046: s_046_1_p->not(s_046_3_h).
cbv. destruct at_home_Adv as [atHome atHomeVerid].
destruct atHomeVerid as [atHomeVerid atHomeVeridCov].  
firstorder. (**cannot prove this, FIXME: One anaphora**)Abort all. 

Theorem FraCaS047: s_047_1_p->s_047_3_h.
cbv. intros P1.
generalize P1. apply le_mono. firstorder.
(* UNK *) Abort All.

Theorem FraCaS048: s_048_1_p->(s_048_3_h). cbv. 
destruct at_home_Adv as [atHome atHomeVerid].
destruct atHomeVerid as [atHomeVerid atHomeVeridCov].
intros.
generalize H. apply le_mono'. firstorder.
generalize H1. apply atHomeVeridCov. firstorder.
Qed.
(** End of Sec 1.3 15/16 for this section**)

(* SEC 1.4 *)

Theorem FraCaS049: (s_049_1_p/\s_049_2_p)->(s_049_4_h).  cbv.
firstorder. Qed.

Theorem FraCaS050: (s_050_1_p/\s_050_2_p)->(s_050_4_h).
cbv.  destruct within_Prep as [withinPrep inVerid]. firstorder.  
(* UNK *) Abort All.


Theorem FraCaS051: (s_051_1_p/\s_051_2_p)->(s_051_4_h).
cbv. destruct within_Prep as [withinPrep inVerid].
firstorder. 
(*UNK*) Abort all. 

Theorem FraCaS052: (s_052_1_p/\s_052_2_p)->(s_052_4_h).
cbv. destruct within_Prep as [withinPrep inVerid].
firstorder. 
(*UNK*) Abort all.


Theorem FraCaS053: (s_053_1_p/\s_053_2_p)->(s_053_4_h).
cbv.
destruct in_Prep as [inPrep inVerid].
firstorder. (*UNK*)

Theorem FraCaS054: s_054_1_p->(s_054_3_h).
cbv. 
destruct on_time_Adv.
firstorder.
(*UNK*) Abort All.

Theorem FraCaS055: (s_055_1_p)->(s_055_3_h).  cbv.
destruct irish_A.
firstorder.
Qed.

Theorem FraCaS056: (s_056_1_p)->(s_056_3_h).  cbv.             
firstorder. (*UNK*) Abort All.

Theorem FraCaS057: (s_057_1_p)->(s_057_3_h).
cbv.
intro P.
destruct major_A as [major].
destruct national_A as [national].
destruct portuguese_A as [portuguese].
destruct in_Prep as [inPrep inVerid inCov].
firstorder.
generalize H0. apply le_mono. firstorder.
Qed.


Theorem FraCaS058: (s_058_1_p)->(s_058_3_h).  cbv. destruct in_Prep as [inPrep inVerid].
destruct in_Prep as [within withinVerid].
firstorder. Abort All. (* 058 UNK *)

Theorem FraCaS059: (s_059_1_p)->(s_059_3_h).
cbv.
destruct female_A as [female].
destruct from_Prep as [from fromVerid fromCov].
firstorder.
rewrite -> H.
apply CARD_monotonous.
firstorder.
Qed.

Theorem FraCaS060: (s_060_1_p)->(s_060_3_h).  cbv.
destruct from_Prep as [from fromVerid fromCov].
destruct southern_europe_PN as [southernEurope regionN].
intros P1.
generalize P1. apply le_mono'. firstorder.
Abort All. (* UNK *)

Theorem FraCaS061: (s_061_1_p)->(s_061_3_h).
cbv.
destruct female_A as [female].
firstorder.
Qed.

Theorem FraCaS062: (s_062_1_p)->not (s_062_3_h).
cbv.
destruct female_A as [female].
destruct part_Prep as [part partVerid partCov].
firstorder. (* FIXME: check the definition of 'neither' *) Abort All.


Theorem FraCaS063: (s_063_1_p)->(s_063_3_h).
cbv.
destruct female_A as [female].
intro P1.
generalize P1. apply le_mono. firstorder.
Qed.

Theorem FraCaS064: (s_064_1_p)->(s_064_3_h).  cbv.  destruct at_home_Adv. destruct at_home_Adv.  firstorder. (* UNK *)

(* End of sec. 1.4 15/15 *)

(* Sec. 1.5 *)

Theorem FraCaS065: (s_065_1_p/\s_065_2_p)->(s_065_4_h).  cbv. firstorder. (* UNK *)

Theorem FraCaS066: s_066_1_p -> s_066_2_p -> s_066_4_h.
cbv.
destruct europe_PN as [europe regionN].
destruct within_Prep as [within withinV withinC].
intros P1 P2.
firstorder.
Qed.

Theorem FraCaS067: (s_067_1_p/\s_067_2_p)->(s_067_4_h). cbv.
destruct in_Prep as [inPrep inVerid].
destruct within_Prep as [within withinVerid].
firstorder.
Qed.

Theorem FraCaS068: (s_068_1_p/\s_068_2_p)->(s_068_4_h).  cbv. firstorder. Qed.


Variable s_069_p_extra : forall cn x, (ComplVV (can_VV) (AdvVP (AdvVP (UseV (travel_V)) (PositAdvAdj (free_A))) (PrepNP (within_Prep) (UsePN (europe_PN))))) cn x -> (ComplSlash (SlashV2a (have_V2)) (DetCN (DetQuant (DefArt) (NumSg)) (SentCN (UseN (right_N)) (EmbedVP (AdvVP (UseV (live_V)) (PrepNP (in_Prep) (UsePN (europe_PN)))))))) cn x.

Theorem FraCaS069: s_069_1_p -> s_069_2_p->(s_069_4_h).
assert (P0 := s_069_p_extra).
cbv in P0.
cbv.
destruct in_Prep as [inPrep inVerid].
destruct within_Prep as [within withinVerid].
destruct major_A as [major].
destruct europe_PN as [europe countryN].
intros [P1 [P1' [co0 [wcCo0 theResidentResidesinCo0]]]] P2.
split.
intro r.
intros [co [[majorCo Co] rResidesInCo]].
apply (P0 (fun _ => True)).
apply P1.
exists co.
split.
assumption.
assumption.
split.
apply (P0 (fun _ => True)).
apply P1.
exists co0.
split.
assumption.
(* FIXME: definite plural for the conclusion means that there must exist resident of major western countries. *) Abort All.

Theorem FraCaS070: s_070_1_p->not(s_070_3_h). cbv. firstorder. Qed.

Theorem FraCaS071: (s_071_1_p)->(s_071_3_h).  cbv. destruct on_time_Adv. firstorder. (* UNK *)

Theorem FraCaS072: (s_072_1_p)->(s_072_3_h).  cbv. firstorder. (* UNK *)

Theorem FraCaS073: (s_073_1_p)->(s_073_3_h).  cbv. destruct major_A as [major].
destruct in_Prep as [inPrep inVerid inVeridCov]. firstorder. (* UNK *)

Theorem FraCaS074: s_074_1_p->not(s_074_3_h). cbv.
destruct outside_Prep as [outside outsideVerid].
destruct within_Prep as [within withinVerid].
firstorder. Abort All. (**UNK**)

Theorem FraCaS075: s_075_1_p->(s_075_3_h). cbv.
destruct from_Prep as [from fromVerid fromCov].
intro P1.
destruct P1.
rewrite -> H.
apply CARD_monotonous.
firstorder.
(* UNK *)
Abort All.

Theorem FraCaS076: s_076_1_p-> (s_076_3_h). cbv.
destruct from_Prep as [from fromVerid fromVeridCov].
destruct southern_europe_PN as [southernEurope regionN].
destruct female_A as [female].
intro P.
generalize P. apply le_mono'. firstorder.
Qed.

Theorem FraCaS077: s_077_1_p-> (s_077_3_h). cbv.
destruct in_Prep as [inPrep inVerid inVeridCov].
destruct female_A as [female].
intro.
firstorder.
exists x. exists x0.
firstorder.
Abort All.

Theorem FraCaS078: s_078_1_p-> not(s_078_3_h). cbv.
destruct part_Prep as [inPrep inVerid inVeridCov].
intro.
firstorder.
Abort All.

Theorem FraCaS079: s_079_1_p-> (s_079_3_h).
cbv.
intro P.
generalize P. apply le_mono. firstorder.
(* UNK *)
Abort All.

Theorem FraCaS080: (s_080_1_p)-> (s_080_3_h). cbv.
destruct female_A as [female].
apply le_mono'. firstorder.
Qed.

(* End of sec 1.5  13/14 in. *)
(* End of sec 1.  71/75 in. *)

(* SEC 2.1 Conjoined *)


Theorem FraCaS081: (s_081_1_p)-> (s_081_3_h). cbv.
destruct jones_PN.
destruct smith_PN as [smith person'].
destruct anderson_PN as [anderson person''].
firstorder.
Qed.

Theorem FraCaS082: (s_082_1_p)-> (s_082_3_h). cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
intro P1.
firstorder. Qed.

Theorem FraCaS083: (s_083_1_p)-> (s_083_3_h).
cbv.
destruct anderson_PN as [anderson person''].
firstorder.
Abort All. 
(* UNK *)

Theorem FraCaS084: (s_084_1_p)-> (s_084_3_h).
cbv.
destruct jones_PN.
destruct smith_PN.
destruct anderson_PN as [andersson].
intros P1 subj.
destruct P1 as [[S [nJ nA]] | H].
firstorder.
(* FIXME: The reading of 'and' in the subjunctive clause is dual to what we need. *)
Abort All.

Theorem FraCaS085: (s_085_1_p)-> not(s_085_3_h). cbv.
intros P1 H.
destruct P1 as [P].
 cut  (CARD
        (fun x : object =>
         lawyer_N x /\ sign_V2 (environment contract_N) x /\ contract_N (environment contract_N))
    <= CARD
         (fun x : object =>
          (lawyer_N x \/ accountant_N x) /\
          sign_V2 (environment contract_N) x /\ contract_N (environment contract_N))).
          intro Q.
rewrite -> H0 in Q.
rewrite -> H in Q.
Focus 2.
apply CARD_monotonous.
firstorder.
(* FIXME: Coq *)

Theorem FraCaS086: (s_086_1_p)-> not(s_086_3_h). cbv.
intros P1 H.
destruct P1 as [P].
 cut  (CARD
        (fun x : object =>
         accountant_N x /\ sign_V2 (environment contract_N) x /\ contract_N (environment contract_N))
    <= CARD
         (fun x : object =>
          (lawyer_N x \/ accountant_N x) /\
          sign_V2 (environment contract_N) x /\ contract_N (environment contract_N))).
          intro Q.
rewrite -> H0 in Q.
rewrite -> H in Q.
Focus 2.
apply CARD_monotonous.
firstorder.
(* FIXME: Coq *)

Theorem FraCaS087: (s_087_1_p)-> (s_087_3_h). cbv.
destruct at_Prep as [atPrep atVerid].
firstorder. Abort All.
(*
FIXME
Every representative and client in this reading means
"Every representative and every client"
but it seems that the parse tree says something else. Tricky.
*)

Theorem FraCaS088: (s_088_1_p)-> (s_088_3_h). cbv.
destruct at_Prep as [atPrep atVerid atCov].
intro P1.
intro x.
assert (P1' := (P1 x)).
intro isRepr.
Abort All. (* UNK *)

Theorem FraCaS089: (s_089_1_p)-> (s_089_3_h). cbv. firstorder. Qed.

(* End of sec 2.1 7/9 *)

(* SEC 2.2*)


Theorem FraCaS090: (s_090_1_p)-> (s_090_3_h). cbv. firstorder.
Qed.

Theorem FraCaS091: (s_091_1_p)-> (s_091_3_h). cbv.
destruct at_Prep as [atPrep atVerid atCov].
firstorder.
exists x0.
firstorder.
Abort All. (* UNK *)

Theorem FraCaS092: (s_092_1_p) -> (s_092_3_h). cbv.
destruct at_Prep as [atPrep atVerid atCov].
intro P1.
intros x xAtMeeting.
apply P1.
split.
generalize xAtMeeting.
apply atVerid.
apply atCov with (v := person_N).
intuition.
assumption.
Qed.

Theorem FraCaS093: (s_093_1_p) -> (s_093_3_h). cbv.
destruct at_Prep as [atPrep atVerid atCov].
intro P1.
intros x xAtMeeting.
apply P1.
split.
generalize xAtMeeting.
apply atVerid.
apply atCov with (v := person_N).
intuition.
assumption.
Qed.

Theorem FraCaS094: (s_094_1_p) -> (s_094_3_h).
cbv.
firstorder.
Qed. (* FIXME: definite plural has the wrong interpretation here. *)

Theorem FraCaS095: (s_095_1_p) -> (s_095_3_h).
cbv.
firstorder.
Qed. (* FIXME: definite plural has the wrong interpretation here. *)

Theorem FraCaS096: s_096_1_p -> s_096_3_h.
cbv.
intro P1.
firstorder.
Qed.

(* End of Sec 2.2 5/7 *)

(* SEC 2.3 *)

Theorem FraCaS097: (s_097_1_p) -> (s_097_3_h).  cbv. (* FIXME on_Prep must for_Prep be unrelated via passive voice; very hard. *) Abort All.

Theorem FraCaS098: (s_098_1_p) -> (s_098_2_p) -> (s_098_4_h).
cbv.
destruct for_Prep as [forPrep forVerid forCov].
destruct bug_32985_PN.
firstorder.
generalize H1.
Abort All. (* UNK *)

Definition s_099_1_p_fixed := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (AdvCN (UseN (client_N)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (demonstration_N)))))) (AdVVP (all_AdV) (UseComp (CompAP (ComplA2 (impressed_by_A2) (DetCN (DetQuant (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_N)))) (NumSg)) (UseN (performance_N)))))))))).

Variable Impressed_cov_K :
  forall (impressor:object) (p q:CN),
  (forall x, p x -> q x) ->
  forall x, apA (impressed_by_A2 impressor) p x -> apA (impressed_by_A2 impressor) q x.

Variable client_people_K : forall x, client_N x -> person_N x.
Theorem FraCaS099: s_099_1_p_fixed -> (s_099_2_p) -> (s_099_4_h).
cbv.
destruct at_Prep as [atPrep atVerid atCov].
destruct smith_PN.
intros [P1 P1'] P2.
assert (smithImpressed := P1 SMITH P2).
destruct smithImpressed as [[smithImpressed [ofSystem performance]] isSystem].
split.
split.
generalize smithImpressed.
apply Impressed_cov_K.
intro client.
intro clientAtDemo.
apply client_people_K.
generalize clientAtDemo.
apply atVerid.
split.
assumption.
assumption.
assumption.
Qed.

Definition s_100_1_p_fixed := (Sentence (UseCl (Past) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (AdvCN (UseN (client_N)) (PrepNP (at_Prep) (DetCN (DetQuant (DefArt) (NumSg)) (UseN (demonstration_N)))))) (UseComp (CompAP (ComplA2 (impressed_by_A2) (DetCN (DetQuant (GenNP (DetCN (DetQuant (DefArt) (NumSg)) (UseN (system_N)))) (NumSg)) (UseN (performance_N))))))))).


Theorem FraCaS100: (s_100_1_p_fixed) -> (s_100_3_h). cbv.
destruct at_Prep as [atPrep atVerid atCov].
intro P1.
destruct P1 as [clientImpressed clientAtDemo].
split.
apply most_card_mono1.
firstorder.
exists (environment
          (atPrep
             (fun k : object -> Prop =>
                k (environment demonstration_N) /\
                demonstration_N (environment demonstration_N))
             client_N)).
firstorder.
Qed.


Definition s_101_1_p_fixed := (Sentence (UseCl (Present) (PPos) (PredVP (DetCN (DetQuant (DefArt) (NumPl)) (UseN (university_graduate_N))) (ComplSlash (SlashV2a (make8become_V2)) (DetCN (DetQuant (IndefArt) (NumPl)) (AdjCN (PositA (poor8bad_A)) (UseN (stockmarket_trader_N)))))))). (* Use a definite article here. *)

Variable likely_weakening_K : forall (p:CN) (x:object), p x -> apA likely_A p x.

Theorem FraCaS101: s_101_1_p_fixed -> s_101_2_p -> (s_101_4_h).
cbv.
destruct smith_PN.
intros P1 P2.
apply likely_weakening_K.
firstorder.
exact SMITH_PERSON.
Qed.

Theorem FraCaS102: s_102_1_p -> s_102_2_p -> s_102_4_h.
cbv.
firstorder.
Abort All. (* UNK *)

(* End of Sec 2.3 5/6 *)

(* SEC 2.4 *)


Theorem FraCaS103: s_103_1_p -> s_103_2_p -> (s_103_4_h).  cbv.
destruct jones_PN as [jones person].
destruct on_Prep as [on onVerid onCov].
firstorder. Qed.

Theorem FraCaS104: s_104_1_p -> s_104_2_p -> s_104_4_h.
cbv.
destruct jones_PN as [jones person].
firstorder.
Abort All.
(* UNK *)

(* End of Sec 2.4 2/2 *)

(* SEC 2.5 *)

Theorem FraCaS105: s_105_1_p -> not s_105_3_h.
cbv. firstorder.
cut (exists x,
         accountant_N x /\
         attend_V2 (environment meeting_N) x /\ meeting_N (environment meeting_N)).
intro ex.
firstorder.
apply CARD_exists.
rewrite -> H.
intuition.
Qed.


Theorem FraCaS106: s_106_1_p -> not s_106_3_h. cbv. firstorder.
cut (exists x,
         accountant_N x /\
         attend_V2 (environment meeting_N) x /\ meeting_N (environment meeting_N)).
firstorder.
apply CARD_exists.
rewrite -> H.
intuition.
Qed.

Theorem FraCaS107: s_107_1_p -> s_107_3_h. cbv. firstorder.
apply CARD_exists.
rewrite -> H.
intuition.
Qed.

Theorem FraCaS108: s_108_1_p -> s_108_3_h. cbv. firstorder.
apply CARD_exists.
rewrite -> H.
intuition.
Qed.

Theorem FraCaS109: s_109_1_p -> s_109_3_h. cbv. firstorder.
Abort All. (* FIXME: see comment in somePl_Det *)

Theorem FraCaS110: s_110_1_p -> s_110_3_h. cbv. firstorder.
apply CARD_exists.
rewrite -> H.
intuition.
Qed.

(* End of Sec 2.5 5/6 *)

(* SEC 2.6 *)

Theorem FraCaS111: s_111_1_p -> s_111_2_p -> s_111_4_h. cbv.
(* FIXME: Anaphora: impossible *)
Abort All.

Theorem FraCaS112: s_112_1_p -> s_112_2_p -> s_112_4_h. cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
firstorder.
Qed.

(* 103 FIXME: Anaphora: impossible *)

(* End of Sec 2.6 1/3 *)
(* End of Sec 2. 25/33 *)

(* SEC 5.1 *)

Theorem FraCas197:s_197_1_p -> s_197_3_h. cbv.
destruct john_PN as [john person].
destruct genuine_A.
firstorder.
Qed.

Theorem FraCas198:s_198_1_p -> not s_198_3_h. cbv.
destruct john_PN as [john person].
destruct former_A as [former]. firstorder. Qed.

Theorem FraCas199:s_199_1_p -> s_199_3_h. cbv. destruct successful_A as [successful].  destruct former_A as [former]. firstorder. (** FIXME: This is YES in the suite, but is says "yes for a former university student", which is not what the conclusion actually says. If we were to fix the conclusion then the example becomes trivial."**) Abort All.

Theorem FraCas200:s_200_1_p -> s_200_3_h. cbv. firstorder.  destruct successful_A as [successful]. destruct former_A as [former]. firstorder. Abort All.  (**UNK**)

Theorem FraCas201:s_201_1_p -> s_201_3_h. cbv. firstorder.  destruct successful_A as [successful]. destruct former_A as [former].  Abort All. (**UNK**)

(* End of Sec 5.1 4/4, excluding 199 *)

Theorem FraCas202:s_202_1_p -> s_202_3_h. cbv.
destruct fourlegged_A.
firstorder. Qed.

Theorem FraCas203:s_203_1_p -> s_203_3_h. cbv. firstorder. Qed.

(* End of Sec 5.2 2/2 *)

Variable small_and_large_disjoint_K : forall cn o, apA small_A cn o -> apA large_A cn o -> False.
(*
cbv.
intros.
assert (SLK := small_and_large_opposite_K).
destruct small_A as [smallness smallThres].
destruct large_A as [largeness largeThres].
firstorder.
destruct (SLK cn x) as [neg disj].
rewrite -> neg in H.
assert (oops := special_trans disj (ineqAdd H0 H)).
(* Coq: opps -> False  *)
*)

Theorem FraCas204:s_204_1_p -> not s_204_3_h. cbv. intros.
assert (H' := small_and_large_opposite_K).
destruct small_A as [smallness smallThres].
destruct large_A as [largeness largeThres].
destruct (H' animal_N MICKEY) as [neg disj].
rewrite -> neg in H.
firstorder.
assert (oops := special_trans disj (ineqAdd H0 H)).
(* Coq: opps -> False  *)

Theorem FraCas205:s_205_1_p -> not s_205_3_h. cbv. intros.
assert (H' := small_and_large_opposite_K).
destruct small_A as [smallness smallThres].
destruct large_A as [largeness largeThres].
destruct (H' animal_N DUMBO) as [neg disj].
firstorder.
rewrite -> neg in H0.
assert (oops := (ineqAdd H0 H)).
(*Coq: disj and oops -> False*)

Theorem FraCas206:s_206_1_p -> s_206_3_h. cbv. intros. Abort All. (* UNK *)

Theorem FraCas207:s_207_1_p -> s_207_3_h. cbv. intros. Abort All. (* UNK *)


Theorem FraCas208:s_208_1_p -> s_208_2_p -> s_208_4_h.
assert (slK := small_and_large_opposite_K).
cbv.
destruct small_A as [small].
destruct large_A as [large].
intros P1 P2.
destruct (slK animal_N DUMBO) as [neg disj].
firstorder.
rewrite -> neg.
(* Coq : Ring tactic *)
(*Morally Qed. *)


Theorem FraCas209:s_209_1_p -> s_209_2_p -> not s_209_4_h.
assert (slK := small_and_large_opposite_K).
cbv.
destruct small_A as [small].
destruct large_A as [large].
intros P1 P2 NH.
destruct (slK animal_N DUMBO) as [neg disj].
destruct (slK animal_N MICKEY) as [neg' disj'].
firstorder.
(*
  NH : large animal_N DUMBO < large animal_N MICKEY
  neg : small animal_N DUMBO = 0 - large animal_N DUMBO
  disj : threshold0 + threshold > 0
  neg' : small animal_N MICKEY = 0 - large animal_N MICKEY
  disj' : threshold0 + threshold > 0
  H : threshold0 <= large animal_N DUMBO
  H1 : threshold <= small animal_N MICKEY
  -------------------------------------------
  NH'                   : 0 < large animal_N MICKEY - large animal_N DUMBO
  (1) = H1+H            : threshold0 + threshold <=  small animal_N MICKEY + large animal_N DUMBO
  (2) = disj ∘ (1)      : 0 <  small animal_N MICKEY + large animal_N DUMBO
  (3) = (2)+NH'         : 0 <  small animal_N MICKEY + large animal_N MICKEY
  (3) rewr. neg'        : 0 < 0
*)
(*Morally Qed. *)


(* End of Sec 5.3 6/6 *)

Theorem FraCas210:s_210_1_p -> s_210_2_p -> not s_210_4_h.
cbv.
intros.
apply small_and_large_disjoint_K with (cn := animal_N) (o := MICKEY).
destruct small_A.
destruct large_A.
firstorder.
cbv.
firstorder.
cbv.
firstorder.
Qed.

Theorem FraCas211:s_211_1_p -> s_211_2_p -> not s_211_4_h.
cbv.
intros.
apply small_and_large_disjoint_K with (cn := animal_N) (o := DUMBO).
destruct small_A.
destruct large_A.
cbv.
firstorder.
cbv.
firstorder.
destruct small_A.
destruct large_A.
firstorder.
Qed.

Theorem FraCas212:s_212_1_p -> s_212_2_p -> s_212_3_p -> s_212_4_p -> s_212_6_h.
cbv.
assert (slK := small_and_large_opposite_K).
destruct small_A as [small].
destruct large_A as [large].
intros.
destruct (slK animal_N DUMBO) as [neg disj].
destruct (slK animal_N MICKEY) as [neg' disj'].
firstorder.
destruct (H MICKEY H4 ).
destruct (H0 DUMBO H3 ).

(*
  disj' : 0 < threshold0 + threshold
  H5 : threshold <= small animal_N MICKEY
  H7 : threshold0 <= large animal_N DUMBO
*)


(*Morally Qed.*)

Theorem FraCas213:s_213_1_p -> s_213_2_p -> s_213_4_h.
cbv.
destruct small_A as [small].
destruct large_A as [large].
intros.
firstorder.
Qed.

(* End of Sec 5.4 3/3 *)

Theorem FraCas214:s_214_1_p -> s_214_2_p -> s_214_4_h.
cbv.
intros.
destruct fat_A as [fat fatP].
firstorder.
Qed.

Theorem FraCas215:s_215_1_p -> s_215_2_p -> s_215_4_h.
cbv.
intros P1 P2.
destruct competent_A as [competent].
firstorder.
(* UNK *)
Abort All.

Theorem FraCas216:s_216_1_p -> s_216_3_h.
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

Theorem FraCas217:s_217_1_p -> s_217_3_h.
cbv.
(* FIXME: syntax wrong, see 216 *)
Abort All.

(* End of Sec 5.5 3/4 *)

Theorem FraCas218:s_218_1_p -> s_218_3_h. cbv.
destruct kim_PN as [kim person].
destruct clever_A.
firstorder.
Qed.

Theorem FraCas219:s_219_1_p -> s_219_3_h. cbv.
destruct kim_PN as [kim person].
destruct clever_A.
firstorder.
Abort All. (* UNK *)

(* End of Sec 5.6 2/2 *)
(* End of Sec 5 20/21 *)


Theorem FraCas220: s_220_1_p -> s_220_2_p -> s_220_4_h.
cbv.
destruct fast_A as [fast].
firstorder.
(* Transitivity *)
(* Morally Qed. *)

Theorem FraCas221:s_221_1_p -> s_221_3_h. cbv.
destruct fast_A as [fast].
firstorder.
Abort All. (* UNK *)

Theorem FraCas222: s_222_1_p -> s_222_2_p -> s_222_4_h.
cbv.
destruct fast_A as [fast].
firstorder.
Abort All. (* UNK *)

Variable slow_and_fast_disjoint_K : forall cn o, apA slow_A cn o /\ apA fast_A cn o -> False.

Theorem FraCas223: s_223_1_p -> s_223_2_p -> not s_223_4_h.
assert (H' := fast_and_slow_opposite_K).
cbv.
destruct fast_A as [fastness fastThres].
destruct slow_A as [slowness slowThres].
destruct (H' computer_N PC6082) as [neg disj].
destruct (H' computer_N ITEL_XZ) as [neg' disj'].
intros.
firstorder.

(*
  neg : slowness computer_N PC6082 = - fastness computer_N PC6082
  disj : 0 < fastThres + slowThres
  neg' : slowness computer_N ITEL_XZ = - fastness computer_N ITEL_XZ
  H : 0 < fastness computer_N PC6082 - fastness computer_N ITEL_XZ
  H1 : fastThres <= fastness computer_N ITEL_XZ
  H0 : slowThres <= slowness computer_N PC6082
  ----------------------------------------------------
  H1+H0  : slowThres+fastThres <= slowness computer_N PC6082 + fastness computer_N ITEL_XZ
  ... ∘ disj : 0 < slowness computer_N PC6082 + fastness computer_N ITEL_XZ
  ... + H :  0 < slowness computer_N PC6082 + fastness computer_N PC6082
  ... rew. neg : 0 < 0
*)
(*Morally Qed.*)

Theorem FraCas224: s_224_1_p -> s_224_2_p -> s_224_4_h.
cbv.
destruct fast_A as [fast].
firstorder.
rewrite -> H.
firstorder.
apply PC6082_COMPY.
Qed.

Theorem FraCas225: s_225_1_p -> s_225_3_h.
cbv.
destruct fast_A as [fast].
firstorder.
Abort All. (* UNK *)

Theorem FraCas226: s_226_1_p -> s_226_2_p -> s_226_4_h.
cbv.
destruct fast_A as [fast].
firstorder.
Abort All. (* UNK *)

Theorem FraCas227: s_227_1_p -> s_227_2_p -> not s_227_4_h.
assert (H' := fast_and_slow_opposite_K).
cbv.
destruct fast_A as [fastness fastThres].
destruct slow_A as [slowness slowThres].
destruct (H' computer_N PC6082) as [neg disj].
destruct (H' computer_N ITEL_XZ) as [neg' disj'].
intros.
firstorder.
(*
  neg' : slowness computer_N ITEL_XZ = 0 - fastness computer_N ITEL_XZ
  neg : slowness computer_N PC6082 = 0 - fastness computer_N PC6082
  disj : 0 < fastThres + slowThres
  H : fastness computer_N PC6082 = fastness computer_N ITEL_XZ
  H1 : fastThres <= fastness computer_N ITEL_XZ
  H0 : slowThres <= slowness computer_N PC6082
  -----------------------------------
  H0+H1 : fastThres + slowThres <= fastness computer_N ITEL_XZ + slowness computer_N PC6082
  ... disj : 0 < fastness computer_N ITEL_XZ + slowness computer_N PC6082
  ... H  :  0 < fastness computer_N PC6082 + slowness computer_N PC6082
  ... neg :  0 < 0
*)
  
(*Morally Qed.*)

Theorem FraCas228: s_228_1_p -> s_228_3_h.
cbv.
destruct fast_A as [fast].
intro P1.
firstorder.
Abort All. (* UNK *)


Theorem FraCas229: s_229_1_p -> not s_229_3_h.
assert (H' := fast_and_slow_opposite_K).
cbv.
destruct fast_A as [fastness fastThres].
destruct slow_A as [slowness slowThres].
destruct (H' computer_N PC6082) as [neg disj].
destruct (H' computer_N ITEL_XZ) as [neg' disj'].
intros P1 H.
rewrite -> neg in H.
rewrite -> P1 in H.
rewrite -> neg' in H.
(* Coq: H -> False *)


Theorem FraCaS230: s_230_1_p -> s_230_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intro P.
destruct P as [contract wonWhat].
exists contract.
firstorder.
(*FIXME *)
Abort All.

Theorem FraCaS231: s_231_1_p -> s_231_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intro P.
(* UNK *)
Abort All.

Theorem FraCaS232: s_232_1_p -> s_232_2_p -> s_232_4_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intros P1 P2.
(*FIXME: than_Subj; elliptic_VP missing *)
Abort All.

Theorem FraCaS233: s_233_1_p -> s_233_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
destruct than_Prep as [than thanVerid thanCov].
destruct many_A.
intro P.
destruct P as [order [moreThanApcom wonWhat]].
exists order.
split.
assert (H := (thanVerid _ _ _ moreThanApcom )).
cbv in H.
destruct H.
assumption.
assumption.
Qed.

Theorem FraCaS234: s_234_1_p -> s_234_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
destruct than_Prep as [than thanVerid thanCov].
destruct many_A.
intro P.
destruct P as [order [moreThanApcom wonWhat]].
exists order.
split.
assert (H := (thanVerid _ _ _ moreThanApcom )).
cbv in H.
destruct H.
assumption.
Abort All. (* UNK *)

Theorem FraCaS235: s_235_1_p -> s_235_2_p -> s_235_4_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
destruct than_Prep as [than thanVerid thanCov].
(* FIXME: than_Prep not correctly handled *)
Abort All.

Theorem FraCaS236: s_236_1_p -> s_236_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
destruct than_Prep as [than thanVerid thanCov].
intro P.
destruct P as [order [moreThanApcom wonWhat]].
split.
(* FIXME: syntax of "more than " not precise enough *)
Abort All.

Variable exists_CARD : forall P:(object -> Prop), (exists x, P x) -> 1 <= CARD P.

Theorem FraCaS237: s_237_1_p -> s_237_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
destruct than_Prep as [than thanVerid thanCov].
destruct many_A.
intro P.
destruct P as [order [moreThanApcom wonWhat]].
assert (H := (thanVerid _ _ _ moreThanApcom )).
cbv in H.
apply exists_CARD.
firstorder.
Qed.

Theorem FraCaS238: s_238_1_p -> s_238_2_p -> s_238_4_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
destruct than_Prep as [than thanVerid thanCov].
intro.
(* FIXME: syntax of "more than " not precise enough *)
Abort All.

(* End of sec 6.1 13/19 *)

Theorem FraCaS239: s_239_1_p -> s_239_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intro P.
Abort All. (* FIXME: Than is elliptic *)

Theorem FraCaS240: s_240_1_p -> s_240_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intro P.
Abort All. (* UNK *)

Theorem FraCaS241: s_241_1_p -> s_241_2_p -> s_241_4_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intros P1 P2.
(* FIXME: We could not get the P2 to be used as an equality. But the real problem is that we do not get the implication
 CARD (fun x : object => order_N x /\ win_V2 x itel) > CARD (fun x : object => order_N x /\ lose_V2 x apcom) 
*)
Abort All.

(* End of sec 6.2 1/3 *)

Theorem FraCaS242: s_242_1_p -> s_242_2_p -> s_242_4_h.
cbv.
destruct slow_A as [slow].
destruct fast_A as [fast].
intro P1.
intro P2.
(* FIXME: Completely wrong semantics: the 500 is interpreted as a definite plural. (Then there are more real problems even if that would be fixed.) *)
Abort All.

(* End of sec 6.3 0/1 *)

Theorem FraCaS243: s_243_1_p -> s_243_2_p -> s_243_4_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intros P1 P2.
destruct than_Prep as [than].
(* FIXME: we would need a specific semantics for the prep. "than" when applied to a "many" CN. More realistic: fix the syntax. *)
Abort All.

(* End of sec 6.4 0/1 *)

Theorem FraCaS244: s_244_1_p->s_244_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intro P1.
destruct than_Prep as [than].
(* FIXME: we would need a specific semantics for the prep. "than" when applied to a "many" CN. More realistic: fix the syntax. Also more problems: than_Subj, elliptic. *)
Abort All.

Theorem FraCaS245: s_245_1_p->s_245_3_h.
cbv.
destruct itel_PN as [itel].
destruct apcom_PN as [apcom].
intro P1.
destruct than_Prep as [than].
(* FIXME: we would need a specific semantics for the prep. "than" when applied to a "many" CN. More realistic: fix the syntax. Also more problems: than_Subj, elliptic. *)
Abort All.

(* End of sec 6.5 0/2 *)

(* SEC 6.6 *)

Theorem FraCaS246: s_246_1_p -> s_246_2_p -> s_246_4_h.
cbv.
destruct fast_A as [fast] eqn:fst.
intros.
firstorder.
Qed.

Theorem FraCaS247: s_247_1_p -> s_247_2_p -> s_247_4_h.
cbv.
destruct fast_A as [fast] eqn:fst.
firstorder.
Abort All. (* UNK *)

Theorem FraCaS248: s_248_1_p -> s_248_2_p -> s_248_4_h.
cbv.
intros.
destruct fast_A as [fast] eqn:fst.
firstorder.
Qed.

Theorem FraCaS249: s_249_1_p -> s_249_3_h.
cbv.
intros.
destruct fast_A as [fast] eqn:fst.
destruct H as [zx zy].
firstorder.
Abort All.
(* FIXME: wrong semantics for 'and' in combination with 'the' *)

Theorem FraCaS250: s_250_1_p -> s_250_3_h.
cbv.
destruct fast_A as [fast] eqn:fst.
firstorder.
(* FIXME: wrong semantics for "the" *)

(* End of sec 6.6 3/5 *)
(* End of sec 6 17/31 *)

(* SEC 7
Theorem FraCaS306: s_306_1_p  -> s_306_3_h.
cbv.
destruct smith_PN as [smith person'].
destruct for_two_years_Adv. firstorder.
Qed.
*)

(* SEC 8 *)

Theorem FraCaS326: s_326_1_p -> s_326_3_h. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct in_1993_Adv as [in93].
(* FIXME: handling tense at the proposition level is difficult. Additionally, the Q has an anaphoric ellpsis (we mean finish building, not (say) finish destroying.) *)

Theorem FraCaS327: s_327_1_p -> s_327_3_h. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct in_1993_Adv as [in93].
(* Progressive prevents getting to the conclusion. *)
(* UNK *)
Abort All.

Theorem FraCaS328: s_328_1_p -> s_328_3_h. cbv.
destruct from_Prep as [from fromVerid fromCov].
destruct in_1993_Adv as [in93 [in93Verid in93Covariant]].
destruct itel_PN as [itel corpN itelIsCorp].
destruct apcom_PN as [apcom corpN' apcomIsCorp].
apply in93Covariant.
intro contract.
intro fromApcom.
assert (H := (fromVerid _ _ _ fromApcom )).
firstorder.
Qed.

Theorem FraCaS329: s_329_1_p -> s_329_3_h. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct in_1993_Adv as [in93].
destruct apcom_PN as [apcom corpN' apcomIsCorp].
destruct from_Prep as [from fromVerid fromCov].
(* Progressive prevents getting to the conclusion. *)
(* UNK *)
Abort All.


Variable year90_included_in_88_to_92_K : forall (p:object -> Prop) (x:object), from_1988_to_1992_Adv p x -> (let (a, _) := in_1990_Adv in a) p x.

Theorem FraCaS330: s_330_1_p -> s_330_3_h. cbv.
destruct itel_PN.
destruct mtalk_PN.
destruct apcom_PN as [apcom corpN' apcomIsCorp].
apply year90_included_in_88_to_92_K.
Qed.

Theorem FraCaS331: s_331_1_p -> s_331_3_h. cbv.
firstorder.
Qed.

Theorem FraCaS332: s_332_1_p -> s_332_3_h. cbv. destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
 intros. firstorder.
Qed.

Theorem FraCaS333: s_333_1_p -> s_333_3_h.
(* FIXME: no notion of group*)
Abort All.

(* End of SEC 8: 6/8 *)

(* SEC 9.1 *)

Variable know_veridical_K : forall (x:object) (xClass:CN) (p:S), know_VS p xClass x -> p.

Theorem FraCaS334: s_334_1_p -> s_334_3_h.
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corpN].
apply know_veridical_K.
Qed.

Theorem FraCaS335: s_335_1_p -> s_335_3_h.
cbv.
Abort All. (* UNK *)

Variable manageTo_veridical_K : forall (x:object) (xClass:CN) (p:VP), manage_VV p x -> p xClass x.

Theorem FraCaS336: s_336_1_p -> s_336_3_h.
cbv.
destruct in_1992_Adv as [in92].
destruct itel_PN as [itel corpN]. 
(* FIXME: adverbs not covariant. *)
Abort All.


Theorem FraCaS337: s_337_1_p -> s_337_3_h.
cbv.
destruct itel_PN as [itel corpN]. 
firstorder.
Abort all. (*UNK*)

Theorem FraCaS338: s_338_1_p -> s_338_3_h.
cbv.
destruct true_A.
destruct itel_PN as [itel corpN].
firstorder.
Qed.

Theorem FraCaS339: s_339_1_p -> not s_339_3_h.
cbv.
destruct itel_PN as [itel corpN].
destruct false_A as [false].
firstorder.
Qed.

Variable see_veridical_K : forall (dobject subject :object) (p:VP), see_V2V dobject p subject -> p (fun _ => True) dobject. (* IMPROVEMENT: not excellent because we lost the class of dobject. *)


Theorem FraCaS340: s_340_1_p/\s_340_2_p -> s_340_4_h.
 cbv.
 destruct jones_PN as [jones person].
 destruct smith_PN as [smith person'].
 firstorder.
Abort all. (*UNK*)


Theorem FraCaS341: s_341_1_p/\s_341_2_p -> s_341_4_h.
 cbv.
 destruct jones_PN as [jones person].
 destruct smith_PN as [smith person'].
 firstorder.
Abort all. (*UNK*)


Theorem FraCaS342: s_342_1_p -> s_342_3_h.
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corpN].
apply see_veridical_K.
Qed.

Theorem FraCaS343: ((s_343_1_p)/\(s_343_2_p))->(s_343_4_h).
cbv.
destruct jones_PN as [jones person].
destruct smith_PN as [smith person'].
destruct itel_PN as [itel corporation].
firstorder.
rewrite <- H0.
firstorder.
Qed.

Theorem FraCaS344: ((s_344_1_p)/\(s_344_2_p))->(s_344_4_h).
cbv.
destruct helen_PN as [helen person].
firstorder.
Qed.

Theorem FraCaS345: s_345_1_p -> s_345_3_h.
cbv.
destruct smith_PN as [smith person'].
destruct jones_PN as [jones person].
firstorder.
Qed.

Theorem FraCaS346: s_346_1_p -> s_346_3_h.
cbv.
(* FIXME: the syntax has an ellipsis, and additionally the semantics for "either" do not match the semantics for "or" *)
Abort All.

(* end of sec 9. 11/13 *)