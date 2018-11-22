import MS
import Bank
import LogicB
import Logic hiding (Exp(..),freeVars)
import Data.Foldable

handleProblem :: Int -> (Phr,Phr,x) -> IO ()
handleProblem n p = do
  putStrLn "=========="
  putStrLn ("== " ++ show n)
  debug (probToEff p)

probToEff :: (Phr, Phr, t) -> Effect
probToEff (premise,h,_) = phrToEff premise ==> phrToEff h

debug :: Effect -> IO ()
debug e = do
  let ps = evalDynamic e
  forM_ ps $ \p0 -> do
    putStrLn "-----------------"
    let p = (fromHOAS' p0) :: Exp Zero
    forM_ (extendAllScopesTrace p) $ \(fvs,q) -> do
      putStrLn ("extendAllScopes Step. Freevars = " ++ show fvs)
      putStrLn ("expression = " ++ show q)


testIt :: Exp Zero
testIt = Op And [Op And [Quant One Pos "x" (Con "dom") (Con "body"), Var "x" ], Con "whatever"]

tt = extendAllScopes (testIt :: Exp Zero)

-- >>> tt
-- ((EXISTS (fun x=>dom) (fun x=>body /\ x)) /\ whatever)

main :: IO ()
main = do
  -- suite handleProblem >> putStrLn "----------"
  debug (phrToEff s_135_4_h)
  -- debug (probToEff p_134)
  -- handleProblem p

-- >>> main
-- -----------------
-- extendAllScopes Step. Freevars = []
-- expression = (FORALL (fun c=>(EXISTS (fun b=>have_V2 b (PN2object mfi_PN) /\ computer_N b) (fun b=>EQUAL c b))) (fun c=>(EXISTS (fun a=>service_contract_N a) (fun a=>have_V2for c a (PN2object mfi_PN)))))
--
-- extendAllScopes Step. Freevars = []
-- expression = (FORALL (fun b=>computer_N b) (fun b=>(EXISTS (fun a=>service_contract_N a) (fun a=>have_V2for b a (PN2object mfi_PN)))))
--
-- extendAllScopes Step. Freevars = []
-- expression = ((FORALL (fun b=>customer_N b /\ (EXISTS (fun a=>computer_N a) (fun a=>own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for c c b)))) /\ customer_N (PN2object mfi_PN) /\ (EXACT (1) (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) -> (FORALL (fun f=>computer_N f) (fun f=>(EXISTS (fun e=>service_contract_N e) (fun e=>have_V2for f e (PN2object mfi_PN))))))
-- -----------------
-- extendAllScopes Step. Freevars = ["a"]
-- expression = ((FORALL (fun b=>customer_N b /\ (EXISTS (fun a=>computer_N a) (fun a=>own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for a c b)))) /\ customer_N (PN2object mfi_PN) /\ (EXACT (1) (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) -> (FORALL (fun f=>computer_N f) (fun f=>(EXISTS (fun e=>service_contract_N e) (fun e=>have_V2for f e (PN2object mfi_PN))))))
-- extendAllScopes Step. Freevars = ["a"]
-- expression = ((FORALL (fun b=>(EXISTS (fun a=>computer_N a) (fun a=>customer_N b /\ own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for a c b)))) /\ customer_N (PN2object mfi_PN) /\ (EXACT (1) (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) -> (FORALL (fun f=>computer_N f) (fun f=>(EXISTS (fun e=>service_contract_N e) (fun e=>have_V2for f e (PN2object mfi_PN))))))
-- extendAllScopes Step. Freevars = []
-- expression = ((FORALL (fun a=>computer_N a) (fun a=>(FORALL (fun b=>customer_N b /\ own_V2 a b) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for a c b)))))) /\ customer_N (PN2object mfi_PN) /\ (EXACT (1) (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) -> (FORALL (fun f=>computer_N f) (fun f=>(EXISTS (fun e=>service_contract_N e) (fun e=>have_V2for f e (PN2object mfi_PN))))))

-- Input the gender of PNs and CNs
-- Many: need to have multiple readings. Interpreted as disjunctions.

-- Many: new handling of adverbs, prepositions. See type VP'

-- Many: if ``The CN'' is not found in the environment, then forall x. cn x -> ... is introduced at the top-level.

-- ???: scope extension from domain of quantifiers: (remember that each quantifier comes with a domain, not a type but a logical formula)
   -- ∀x. (∃y. P(y) -> Q(x,y)) -> R(x,y)
   -- can be rewritten to:
   -- ∀y. P(y) -> ∀x. (TRUE -> Q(x,y)) -> R(x,y)

-- 116: Genders are given to PNs. One cannot assume that the context is empty and infer that Mary is female just from the example.

-- Analysis for 122. Conclusion (H) parse tree is wrong, it can't be fixed at the semantic level:

-- (Every committee) (has (((a chairman) appointed) (by (members of the committee))))

-- Instead, we should use:
-- (Every committee) (has (a (chairman (appointed (by (members of the committee))))))

-- The key constructions from the resource library are:
-- relA2 	RP -> A2 -> NP -> RCl    ... that is married to her
-- relCN         CN -> RS -> CN     person (married to her)

-- It appears that the omitted RP is not in GF, and that is what causes the parsing problem. (added as implicitRP below)
-- With explicit RP:
-- (Every committee) (has (a (chairman (that is (appointed (by (members of the committee)))))))

ouch122 :: IO ()
ouch122 = debug (phrToEff s_122_4_h)

-- >>> evalDbg p_122_ALT
-- ((FORALL (fun a=>committee_N a) (fun a=>(EXISTS (fun b=>chairman_N b) (fun b=>have_V2 b a)))) /\ (EXISTS (fun c=>True) (fun c=>appoint_V2by (THE (fun x1 => have_V2 a x1 /\ member_N x1)) b c)) -> (FORALL (fun d=>committee_N d) (fun d=>(EXISTS (fun e=>chairman_N e /\ appoint_V2 (THE (fun x1 => have_V2 d x1 /\ member_N x1)) e) (fun e=>have_V2 e d)))))



-- 155. Incorrect syntax (one anaphora not present, fixed now)

-- Analysis for 190. Strict identity not implemented.



-- EXTRA Anaphoric problems: 014, 016, 046, 078, 111, 113

-- 014, 046:
--   Need to interpret "the CNs" as a reference to both entities introduced with neither/both
--   Note: this should be easier by interpreting both/neither as exactly 2?
--   Need to interpret "part_Prep np" as the predicate ()
