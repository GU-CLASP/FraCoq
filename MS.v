
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
Definition A := (object -> Prop) -> (object -> Prop).
Definition A2 := object -> A.
Definition IntersectiveA := object -> Prop.
Definition wkIntersectiveA
            : IntersectiveA -> A
            := fun a cn (x:object) => a x /\ cn x.
Coercion wkIntersectiveA : IntersectiveA >-> A.

Inductive SubsectiveA : Type :=
  mkSubsective : ((object -> Prop) -> (object -> Prop)) -> SubsectiveA.
Add Printing Let SubsectiveA.

Definition apSubsectiveA
            : SubsectiveA -> A
            := fun a cn (x:object) => let (aa) := a in
                 aa cn x /\ cn x .
Definition getSubsectiveA : SubsectiveA -> A.
intro. destruct X. exact P. Defined.
Coercion apSubsectiveA : SubsectiveA >-> A.

Inductive ExtensionalSubsectiveA : Type :=
  mkExtensionalSubsective : forall (a : (object -> Prop) -> (object -> Prop)),
     (forall (p q:object -> Prop), (forall x, p x -> q x) -> (forall x, q x -> p x) ->  forall x, a p x -> a q x)
     -> ExtensionalSubsectiveA.

Add Printing Let ExtensionalSubsectiveA.

Definition apExtensionalSubsectiveA
            : ExtensionalSubsectiveA -> A
            := fun a cn (x:object) => let (aa,_) := a in
                 aa cn x /\ cn x .
Coercion apExtensionalSubsectiveA : ExtensionalSubsectiveA >-> A.

Inductive PrivativeA : Type :=
  mkPrivativeA : ((object -> Prop) -> (object -> Prop)) -> PrivativeA.
Add Printing Let PrivativeA.
Definition wkPrivativeA : PrivativeA -> A
            := fun aa cn (x:object) => let (a) := aa in a cn x /\ not (cn x).
Coercion wkPrivativeA : PrivativeA >-> A.
Definition NonCommitalA := A.


Definition AP:= A.
Definition N:= object->Prop.
Definition N2 := object -> object -> Prop.
Inductive Num : Type :=
  singular : Num |
  plural   : Num |
  unknownNum : Num |
  moreThan : Num -> Num |
  cardinal : nat -> Num.
Definition Card := Num.
Definition AdN : Type := Num -> Num.

Parameter LOTS_OF : CN -> CN. (* "lots of" is treated like an adjective *)
Parameter MANY : nat.
Parameter A_FEW : nat.
Parameter SOME : nat. (* the plural number *)
Parameter SEVERAL : nat.

Fixpoint interpAtLeast (num:Num) (x:nat) :=
  match num with
  | singular => x >= 1
  | plural   => x >= SOME
  | unknownNum => True
  | moreThan n => interpAtLeast n x
  | cardinal n => x >= n
  end.

Definition interpAtMost : Num -> nat -> Prop :=
  fun num x => match num with
  | singular => x <= 1
  | plural   => x <= SOME
  | unknownNum => True
  | moreThan _ => True
  | cardinal n => x <= n
  end.

Definition interpExactly : Num -> nat -> Prop :=
  fun num x => match num with
  | singular => x = 1
  | plural   => True
  | unknownNum => True
  | moreThan n => interpAtLeast n x
  | cardinal n => x = n
  end.

Definition Numeral := nat.
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
Definition PositA: A -> A := fun x:A=>x.

(* In GF this is PositA : A -> AP; however this type does the conversion from the adjectival subclass to generic adjectives, which is wrong *)
Definition AdAP:AdA->AP->AP:= fun ad a => ad a.

Parameter AdvAP0 : AP -> Adv -> object -> Prop . (* We want to ignore the class here *)
Definition AdvAP : AP -> Adv -> AP
  := fun adj adv cn x => AdvAP0 adj adv x.

Definition ComparA : A -> NP -> AP
 := fun a np cn x => apNP np (fun _class y =>    (a cn y -> a cn x)
                                              /\ (not (a cn x) -> not (a cn y))).
(* Remark: most of the time, the comparatives are used in a copula, and in that case the category comes from the NP.  *)
 (* x is faster than y  *)
 
Definition ComparAsAs : A -> NP -> AP
 := fun a np cn x => apNP np (fun _class y => a cn x <-> a cn y).
Definition ComplA2 : A2 -> NP -> AP := fun a2 np cn x => apNP np (fun yClass y => a2 y cn x).
Parameter PartVP : VP -> AP .
Definition SentAP : AP -> SC -> AP
  := fun ap clause cn x => ap (fun y => clause cn y /\ cn y) x.
Parameter UseComparA : A -> AP.
Definition UseComparA_prefix : A -> AP := fun adj cn x => adj cn x.
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


Parameter CARD: CN -> nat.
Parameter MOSTPART: nat -> nat.
Definition CARD_MOST := fun x => MOSTPART (CARD x).

Variable MOST_ineq : forall x, MOSTPART x <= x.
Variable CARD_monotonous : forall a b:CN, (forall x, a x -> b x) -> CARD a <= CARD b.
Parameter le_trans : forall x y z, x <= y -> y <= z -> x <= z.
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
Parameter neutral_A : IntersectiveA .
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

Variable small_and_large_disjoint_K : forall cn o, getSubsectiveA small_A cn o /\ getSubsectiveA large_A cn o -> False.

(* New combinators *)
Definition EXISTS := fun (p : object -> Prop) (q : object -> Prop) => exists x, p x /\ q x.
Definition FORALL := fun (p : object -> Prop) (q : object -> Prop) => forall x, p x -> q x.
Parameter THE : (object -> Prop) -> object.

Definition deliver_V2to := deliver_V3.
Definition NOT := not.

Definition PN2object : PN -> object.
cbv.
intros.
destruct X.
exact x.
Qed.

Definition appA : A -> (object -> Prop) -> (object -> Prop)
 := fun a cn x => a cn x.
