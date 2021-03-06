Close Scope nat_scope.
Require Import ZArith.
Open Scope Z_scope.

Opaque Z.gt.
Opaque Z.lt.
Opaque Z.add.
Opaque Z.sub.
Opaque Z.ge.
Opaque Z.le.

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
Definition VP := object -> Prop. (* subject *)
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

Definition A := (object -> Prop) -> (object -> Prop).
Definition A2 := object -> A.
Definition IntersectiveA := object -> Prop.
Definition wkIntersectiveA
            : IntersectiveA -> A
            := fun a cn (x:object) => a x /\ cn x.
Coercion wkIntersectiveA : IntersectiveA >-> A.

Inductive SubsectiveA : Type :=
  mkSubsective : forall (measure : object -> Z) (threshold : (object -> Prop) -> Z), SubsectiveA.
Add Printing Let SubsectiveA.

Definition apSubsectiveA
            : SubsectiveA -> A
            := fun a => let (measure, threshold) := a in
               fun cn x => threshold cn <= measure x /\ cn x.
Definition getSubsectiveA := apSubsectiveA.
Coercion apSubsectiveA : SubsectiveA >-> A.

Inductive ExtensionalSubsectiveA : Type :=
  mkExtensionalSubsective :
     forall
     (measure : object -> Z)
     (threshold : (object -> Prop) -> Z),
     (let a := fun cn x => (threshold cn <= measure x)
     in (forall (p q:object -> Prop), (forall x, p x -> q x) -> (forall x, q x -> p x) ->  forall x, a p x -> a q x))
     -> ExtensionalSubsectiveA.

Add Printing Let ExtensionalSubsectiveA.

Definition apExtensionalSubsectiveA
            : ExtensionalSubsectiveA -> SubsectiveA
            := fun a => let (measure,threshold,_) := a in
                 mkSubsective measure threshold.
Coercion apExtensionalSubsectiveA : ExtensionalSubsectiveA >-> SubsectiveA.

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
  cardinal : Z -> Num.
Definition Card := Num.
Definition AdN : Type := Num -> Num.

Parameter LOTS_OF : Z.
Parameter MANY : Z.
Parameter A_FEW : Z.
Parameter SOME : Z. (* the plural number *)
Parameter SEVERAL : Z.

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
Definition RelCN: CN->RS->CN:= fun cn rs x => cn x /\ rs x. (* GF FIXME: Relative clauses should apply to NPs. See 013, 027, 044.  *)

Definition AdvCN : CN -> Adv -> CN := fun cn adv => adv cn.


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

Definition EmbedVP : VP -> SC := fun vp => vp.

(* NP *)
Definition DetCN: Det->CN->NP:= fun det cn=> mkNP (fst det) (snd det) cn.

Definition   AdvNP : NP -> Adv -> NP
 := fun np adv => let (num,q,cn) := np in mkNP num (fun cn' k => q cn' (adv k)) cn. (* CHECK *)
(* Parameter ConjNP : Conj -> ListNP -> NP . *)



Definition PPartNP : NP -> V2 -> NP  (* Word of warning: in FraCas partitives always behave like intersection, which is probably not true in general *)
          := fun np v2 => let (num,q,cn) := np in
                          mkNP num q (fun x => cn x /\ exists subject, v2 x subject).
(* Parameter RelNP : NP -> RS -> NP . *)
Definition RelNPa : NP -> RS -> NP
                 := fun np rs => let (num,q,cn) := np
                                 in mkNP num q (fun x => cn x /\ rs x).
(* Parameter SelfNP : NP -> NP . *)
Definition UsePron : Pron -> NP := fun pron => pron.
(* AP *)
Definition PositA: A -> A := fun x:A=>x.

(* In GF this is PositA : A -> AP; however this type does the conversion from the adjectival subclass to generic adjectives, which is wrong *)
Definition AdAP:AdA->AP->AP:= fun ad a => ad a.

Parameter AdvAP0 : AP -> Adv -> object -> Prop . (* We want to ignore the class here *)
Definition AdvAP : AP -> Adv -> AP
  := fun adj adv cn x => AdvAP0 adj adv x.


Definition ComparA : SubsectiveA -> NP -> AP
 := fun a np cn x => let (measure,_thres) := a in
    apNP np (fun y => (1 <= measure x - measure y)).
(* Remark: most of the time, the comparatives are used in a copula, and in that case the category comes from the NP.  *)
 (* x is faster than y  *)

Definition compareGradableMore : SubsectiveA -> (object->Prop) -> object -> object -> Prop :=
fun a cn x y => let (measure,_) := a in 1 <= measure x - measure y.
Definition compareGradableEqual : SubsectiveA -> (object -> Prop) -> object -> object -> Prop :=
fun a cn x y => let (measure,_) := a in measure x = measure y.

Definition ComplA2 : A2 -> NP -> AP := fun a2 np cn x => apNP np (fun y => a2 y cn x).
Parameter PartVP : VP -> AP .
Definition SentAP : AP -> SC -> AP
  := fun ap clause cn x => ap (fun y => clause y /\ cn y) x.
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


Parameter CARD: CN -> Z.
Parameter MOSTPART: Z -> Z.
Definition CARD_MOST := fun x => MOSTPART (CARD x).

Parameter MOST_ineq : forall x, MOSTPART x <= x.
Parameter CARD_monotonous : forall a b:CN, (forall x, a x -> b x) -> CARD a <= CARD b.
Parameter le_trans : forall x y z, x <= y -> y <= z -> x <= z.
Lemma most_card_mono1 : forall a b:CN, (forall x, a x -> b x) -> MOSTPART (CARD a) <= CARD b.
intros. cbv. apply le_trans with (y := CARD a). apply MOST_ineq. apply CARD_monotonous. assumption.
Qed.



(**Definition DefArt:Quant:= fun P:CN=> fun Q:object->Prop=>exists x,  P x/\ Q x.**)
  (* JP: "exists!" fails to identify that we refer to a thing outside the current NP ??? *)

Parameter PossPron : Pron -> Quant .
Definition  no_Quant : Quant:= fun num P Q=> forall x, not (P x -> Q x) .
(* Parameter that_Quant : Quant . *)
Parameter the_other_Q : Quant .
Parameter this_Quant : Quant .

(* Det *)
Definition DetQuant: Quant -> Num -> Det:= fun (q:Quant) (n : Num) => (n,q). 
Definition DetQuantOrd: Quant->Num->Ord->Det:= fun q n o =>(n,q). (* Ignoring the ord for now *)
(* Parameter ConjDet : Conj -> ListDet -> Det . *)

(* VPSlash *)
Definition SlashV2a: V2->VPSlash:= fun v dobj  s => v dobj s.

(* Parameter AdVVPSlash : AdV -> VPSlash -> VPSlash . *)
(* Parameter AdvVPSlash : VPSlash -> Adv -> VPSlash . *)
(* Parameter SlashV2A : V2A -> AP -> VPSlash . *)
(* Parameter SlashV2Q : V2Q -> QS -> VPSlash . *)
(* Parameter SlashV2VNP : V2V -> NP -> VPSlash -> VPSlash . *)
(* Parameter VPSlashPrep : VP -> Prep -> VPSlash . *)
Definition Slash2V3 : V3 -> NP -> VPSlash
                    := fun v np indirectObject subject => apNP np (fun  directObject => v indirectObject directObject subject).
Definition Slash3V3 : V3 -> NP -> VPSlash
                    := fun v np directObject subject => apNP np (fun indirectObject => v indirectObject directObject subject).
Definition SlashV2S : V2S -> S -> VPSlash
                   := fun v2s s directObject subject => v2s directObject s subject.
Definition SlashV2V : V2V -> VP -> VPSlash
                    := fun v2v vp directObject subject => v2v directObject vp subject.
Definition SlashVV : VV -> VPSlash -> VPSlash
                   := fun vv v2 directObject subject => vv (fun x => v2 directObject x) subject.

(* AdV *)


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
Definition ComplSlash: VPSlash->NP->VP:=fun v2 dobject  subject=> apNP dobject(fun  o => v2 o subject).
Definition UseComp: Comp -> VP (* be ... *)
                  := fun p => p.
Definition ComplVV: VV -> VP -> VP
                  := fun vv vp x => vv vp x.

Definition AdVVP : AdV -> VP -> VP
                 := fun adV vp x => adV (fun y => vp y) x.
                 (* can inherit the class of x, because the new VP applies to x anyway *)



Definition  AdvVP : VP -> Adv -> VP:= fun vp adV x => adV (fun y => vp y) x.
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
                 := fun v2 subject => v2 subject subject.
(* Parameter SelfAdVVP : VP -> VP . *)
(* Parameter SelfAdvVP : VP -> VP . *)
(* Parameter UseCopula : VP . *)
Definition UseV : V -> VP
                := fun v x => v x.
Parameter elliptic_VP : VP .

(* Comp -- complement of copula*)
Definition CompCN: CN -> Comp (* be a thing given by the CN *)
                 := fun cn x => cn x.
Definition CompNP: NP -> Comp (* be the thing given by the NP *)
                 := fun np o => apNP np (fun  o' => o = o').

(* Definition CompAP: AP -> Comp (* have property given by the AP *) *)
(*                  := fun ap x => ap xClass x. *)

Definition CompAdv : Adv -> Comp := fun adv x => adv (fun _ => True) x.
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
Definition ExistNP: NP->Cl:= fun n=>apNP n (fun x => True).
Parameter IMPERSONAL : object.
Definition ImpersCl : VP -> Cl := fun vp => vp IMPERSONAL.
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
                   := fun np vp dobject => apNP np (fun subject => vp dobject subject).

(* RCl *)
Definition RelVP: RP->VP->RCl:= fun relativePronounIgnored => fun p => p.

Parameter EmptyRelSlash : ClSlash -> RCl .
(* Parameter RelCl : Cl -> RCl . *)
Definition RelSlash : RP -> ClSlash -> RCl := fun rpIgnored cl => cl. (* TODO: Check *)
Definition StrandRelSlash : RP -> ClSlash -> RCl := fun rp cl => cl.

(* RS *)
Definition UseRCl: Temp->Pol->RCl->RS:=fun t p r x => p (r x).

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

(* Parameter MkVPS : Temp -> Pol -> VP -> VPS . *)


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


(* Definition  a_lot_of_Det : Det:= (singular, fun num cn vp => (exists x, cn x /\ LOTS_OF cn x /\ vp cn x)) . (* Because this is used for "a lot of" is a mass; it's still singular. *) *)
Parameter another_Det : Det .
Parameter anyPl_Det : Det .
Parameter either_Det : Det .
Set Implicit Arguments. 



(* AdA *)
Parameter almost_AdA : AdA .
Parameter quite_Adv : AdA .
Parameter really_AdA : AdA .
Parameter so_AdA : AdA .
Parameter too_AdA : AdA .
Parameter very_AdA : AdA .

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

Parameter IMPRESSED_BY : object -> object -> Prop.
Definition impressed_by_A2 : A2 :=
   fun impressee class impressor => class impressee /\ IMPRESSED_BY impressee impressor.

Parameter can8know_VV : VV .
Parameter can_VV : VV .
Parameter finish_VV : VV .
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
Parameter on_monday_Adv : VeridicalAdv .
Parameter on_the_5th_of_may_1995_Adv : Adv .
Parameter on_the_7th_of_may_1995_Adv : Adv .
Parameter on_thursday_Adv : VeridicalAdv .
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
Parameter MARY : object.
Parameter MARY_PERSON : person_N MARY.
Definition mary_PN : PN := mkPN MARY person_N MARY_PERSON  .
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
Parameter dedicated_A : IntersectiveA .
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
Parameter modest_A : IntersectiveA .
Parameter national_A : SubsectiveA .
Parameter new_A : A .
Parameter north_american_A : IntersectiveA .
Parameter noted_A : A .
Definition own_A : A := fun cn b => True.
  (* Ok, because at the moment "own" occurs only immediately after "his" (a possesive). It does not make syntactic sense otherwise.
  Still it'd be nice to improve this --- in the GF syntax. *)
Parameter poor8bad_A : A .
Parameter poor8penniless_A : A .
Parameter portuguese_A : IntersectiveA .
Parameter present8attending_A : A .
Parameter present8current_A : A .
Parameter previous_A : A .
Parameter red_A : A .
Parameter resident_A : A .
Parameter scandinavian_A : SubsectiveA .
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
Definition itelxz_N : N := computer_N. (* hack for sec. 6 to fix comparison class *)
Definition itelzx_N : N := computer_N.
Definition itelzy_N : N := computer_N.
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
Definition nobel_prize_N : N := fun o => exists x, nobel_prize_N2 o x.
Parameter note_N : N .
Parameter novel_N : N .
Parameter office_building_N : N .
Parameter one_N : N .
Parameter order_N : N .
Parameter paper_N : N .
Parameter payrise_N : N .
Definition pc6082_N : N := computer_N.
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

Parameter accept_V2 : V2 .
Parameter answer_V2 : V2 .
Parameter appoint_V2 : V2 .
Parameter arrive_in_V2 : V2 .
Parameter attend_V2 : V2 .
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
Definition own_V2 := have_V2 . (* This is because posessives are implemented with "have", and they sometimes imply ownership. See 134.*)
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
Parameter win_V2from : object -> V2 .
Parameter work_in_V2 : V2 .
Parameter write_V2 : V2 .
Parameter write_to_V2 : V2 .

(** Knowledge **)
Parameter wantCovariant_K : forall p q:VP, forall s, (q s -> p s) -> want_VV q s -> want_VV p s.
Parameter sayCovariant_K : forall p q:S, forall s, (p -> q) -> say_VS p s -> say_VS q s.
Parameter claimCovariant_K : forall p q:S, forall s, (p -> q) -> claim_VS p s -> claim_VS q s.


Parameter  person_K: forall x:object, chairman_N(x)-> person_N(x). 
Parameter  committee_member_person_K : forall x, committee_member_N x -> person_N x.

Parameter Not_stop_means_continue_K : forall x, stop_V x /\ continue_V x -> False.

Parameter small_and_large_disjoint_K : forall cn o, getSubsectiveA small_A cn o /\ getSubsectiveA large_A cn o -> False.




(* New combinators *)
Definition EXISTS := fun (p : object -> Prop) (q : object -> Prop) => exists x, p x /\ q x.
Definition FORALL := fun (p : object -> Prop) (q : object -> Prop) => forall x, p x -> q x.
Parameter THE : (object -> Prop) -> object.
Parameter THE_sat_exact : forall (q:object -> Prop), q (THE q).
Lemma THE_sat : forall (p:object -> Prop) (q:object -> Prop), (forall x, q x -> p x) -> p (THE q).
intros.
apply H.
apply THE_sat_exact.
Qed.


Definition deliver_V2to := deliver_V3.
Definition Not := not.

Definition PN2object : PN -> object.
cbv.
intros.
destruct X.
exact x.
Defined.
Opaque PN2object.

Definition PN2Class : PN -> (object -> Prop).
cbv.
intro x.
destruct x.
exact cn.
Defined.
Opaque PN2Class.


Parameter assumedNP : object.

Definition appA : A -> (object -> Prop) -> (object -> Prop)
 := fun a cn x => a cn x.
Definition appAdv : Adv -> (object -> Prop) -> (object -> Prop)
 := fun a cn x => a cn x.


Definition appoint_V2by : V3
  := fun x y _ => appoint_V2 x y.
Definition _BE_ : VP := fun x => True.
Parameter _BE_on : object -> VP.
Parameter _BE_in  : object -> VP.
Parameter _BE_from : object -> VP.
Parameter _BE_at : object -> VP.

Parameter go8walk_Vto: object -> object -> Prop.
Parameter several: (object -> Prop) -> (object -> Prop) -> Prop.
Parameter have_V2for : object -> object -> object ->  Prop.
Parameter take_V2to : object -> object -> object  -> Prop.
Parameter take_V2at : object -> object -> object  -> Prop. 
Definition cover_page_Npossess
  := fun x: object => fun y : object => cover_page_N y /\ have_V2 y x.
Parameter go8travel_Vtoby8means : object -> object -> object -> Prop. 
Parameter go8travel_Vby8means : object -> object -> Prop. 
Parameter go8travel_Vtoby8meansto : object -> object ->  object -> object -> Prop.
Parameter go8travel_Vby8meansto :  object ->  object -> object -> Prop.
Parameter go8travel_Vto :  object -> object -> Prop.
Parameter knowVQ : VS.
Parameter WHY: Prop -> Prop.
Definition speak_to_V2to : object -> object -> object -> Prop
  := fun to _ subj => speak_to_V2 to subj.

Parameter work_Vadv : Adv -> object -> Prop.
Parameter find_V2before : object -> object -> object -> Prop.
Parameter go8walk_Vadv : Adv -> object -> Prop.
Parameter suggest_to_V2Sto : object -> V2S.
Parameter have_V2in : object -> V2.
Parameter travel_Vwithin : object -> V.
Parameter get_V2in : object -> V2.

Definition committee_member_Nfrom origin x :=
   _BE_from origin x /\ committee_member_N x.


Parameter live_Vin : object -> V.
Parameter RESIDENT_IN : object -> object -> Prop.
Definition resident_Ain : object -> A :=
  fun location pred x => RESIDENT_IN location x /\ pred x.
Parameter resident_Aoutside : object -> A.

Parameter spend_V2part : object -> V2.
Parameter item_Non : object -> N.
Parameter vote_for_V2at : object -> V2.
Parameter blame1_V2for : object -> V2.
Definition blame2_V2on : object -> V2
           := fun x y z => blame1_V2for y x z.
Parameter client_Nat : object -> N.
Definition stock_market_trader_N := stockmarket_trader_N. (* spelling *)
Parameter swim_Vto : object -> V.
Parameter run_V2in : object -> V2.
Parameter chain_Npart : object -> N.
Parameter own_V2in : object -> V2.


Definition QQ := CN -> VP -> Prop.
Definition FEWQ  := fun cn => fun vp => (CARD (fun x => cn x /\ vp x) <= A_FEW).
Definition AFEWQ  := fun cn => fun vp => A_FEW <= (CARD (fun x => cn x /\ vp x) ) /\ exists x, cn x /\ vp x.

Definition EQUAL : object -> object -> Prop := fun x y => x = y.
Definition MOSTQ := fun cn => fun vp => CARD_MOST cn <= CARD (fun x => cn x /\ vp x)  /\ exists x, cn x /\ vp x.
Definition MANYQ := fun cn => fun vp => (MANY <= CARD (fun x => cn x /\ vp x))  /\ exists x, cn x /\ vp x.
Definition LOTSQ := fun cn => fun vp => (LOTS_OF <= CARD (fun x => cn x /\ vp x))  /\ exists x, cn x /\ vp x.
Definition SEVERALQ := fun cn => fun vp => (SEVERAL <= CARD (fun x => cn x /\ vp x))  /\ exists x, cn x /\ vp x.
Definition ATLEAST:= fun n : Z => fun cn=> fun vp=>  exists x, cn x /\ vp x /\ (n <= CARD (fun x => cn x /\ vp x)).
Definition ATMOST:= fun n : Z => fun cn=> fun vp=> CARD (fun x => cn x /\ vp x) <= n.
Definition EXEXACT := fun n : Z => fun cn=> fun vp=>  exists x, cn x /\ vp x /\ (CARD (fun x => cn x /\ vp x) = n).
Definition EXACT := fun n : Z => fun cn=> fun vp=>  (CARD (fun x => cn x /\ vp x) = n).


Definition  report_Nfromon := fun source location report => report_N report /\
send_V2 report source /\ _BE_on location report.
Definition  award_and_be_awarded_V2 : V2 := fun x => fun y => award_V3 y x y .

Definition going_to_VV : VV := fun v => v. (* FIXME: Ignoring tense *)
Definition do_VV : VV := fun v => v.
Definition NOT:= not.

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

Parameter CARD_exists : forall P:(object -> Prop), 1 <= CARD P -> exists x, P x.

Definition before_PREP
  : object -> VP -> object -> Prop
  := fun arg vp subj => before_Subj (vp arg) (vp subj).

Definition le_mono_right := le_mono.
Definition le_mono_left := le_mono'.

Parameter usedToBeCov_K : forall (p q : VP), (forall x, p x -> q x) -> forall x , use_VV p x -> use_VV q x.

Parameter getInK : forall newsPaper result x, get_V2in newsPaper result x -> get_V2 result x.
(* Analysis: In "get published", published should not be intersectional. *)

Parameter client_people_K : forall x, client_N x -> person_N x.

Parameter exactEqual : forall x y (p : object -> Prop), p x -> p y -> CARD (fun x => p x) = 1 -> x = y.

Definition person_Nat : object -> CN :=
  fun location person => person_N person /\ _BE_at location person.

Parameter slow_and_fast_disjoint_K : forall cn o, getSubsectiveA slow_A cn o /\ getSubsectiveA fast_A cn o -> False.
Definition opposite_adjectives : SubsectiveA -> SubsectiveA -> Prop
  := fun a1 a2 =>
  forall cn o,  let (mSmall,threshSmall) := a1 in
                let (mLarge,threshLarge) := a2 in
               (   (mSmall o = - mLarge o)
                /\ (1 <= threshLarge cn + threshSmall cn)).
Parameter fast_and_slow_opposite_K  : opposite_adjectives slow_A  fast_A.
Parameter small_and_large_opposite_K : opposite_adjectives small_A large_A.
