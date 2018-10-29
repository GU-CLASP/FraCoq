Load MStest.
Section Gender.
Variable smith_PN_Male: male_A (PN2object smith_PN).

Variable smith_PN_Female: female_A (PN2object smith_PN).

Variable john_PN_Male: male_A (PN2object john_PN).

Variable itel_PN_Neutral: neutral_A (PN2object itel_PN).

Variable gfi_PN_Neutral: neutral_A (PN2object gfi_PN).

Variable bt_PN_Neutral: neutral_A (PN2object bt_PN).

Variable mary_PN_Female: female_A (PN2object mary_PN).

Definition Problem114a:= ((EXISTS (fun a=>have_V2 a (PN2object mary_PN) /\ workstation_N a) (fun a=>use_V2 a (PN2object mary_PN))) -> (EXISTS (fun b=>have_V2 b (PN2object mary_PN) /\ workstation_N b) (fun b=>(EXISTS (fun c=>True) (fun c=>use_V2 b c))))).

Theorem T114a: Problem114a. cbv. intros. destruct H. destruct H. exists x. split. exact H. exists (PN2object mary_PN). split. apply I. exact H0. Qed. 


Definition Problem115a:= ((EXISTS (fun a=>have_V2 a (PN2object mary_PN) /\ workstation_N a) (fun a=>use_V2 a (PN2object mary_PN))) -> (EXISTS (fun b=>workstation_N b) (fun b=>have_V2 b (PN2object mary_PN)))).

Theorem T115A: Problem115a. cbv. intros. destruct H. destruct H. destruct H.  exists x. split. exact H1. exact H. Qed. 


Definition Problem116a:= ((EXISTS (fun a=>have_V2 a (PN2object mary_PN) /\ workstation_N a) (fun a=>use_V2 a (PN2object mary_PN))) -> appA female_A (fun x1 => True) (PN2object mary_PN)).

Theorem T116a: Problem116a. cbv. intros.  split. apply mary_PN_Female. apply I. Qed.

Definition Problem117a:= ((FORALL (fun a=>student_N a) (fun a=>(EXISTS (fun b=>have_V2 b a /\ workstation_N b) (fun b=>use_V2 b a)))) /\ student_N (PN2object mary_PN) -> (EXISTS (fun c=>have_V2 c (PN2object mary_PN) /\ workstation_N c) (fun c=>use_V2 c (PN2object mary_PN)))).

Theorem T117a: Problem117a. cbv. intros.  elim H. intros. apply H. exact H1. Qed. 
                                                                         

Definition Problem118a:= ((FORALL (fun a=>student_N a) (fun a=>(EXISTS (fun b=>have_V2 b a /\ workstation_N b) (fun b=>use_V2 b a)))) /\ student_N (PN2object mary_PN) -> (EXISTS (fun c=>workstation_N c) (fun c=>have_V2 c (PN2object mary_PN)))).

End Gender. 


Definition Problem119a:= ((FORALL (fun a=>student_N a) (fun a=>NOT((EXISTS (fun b=>have_V2 b a /\ workstation_N b) (fun b=>use_V2 b a))))) /\ student_N (PN2object mary_PN) -> (EXISTS (fun c=>workstation_N c) (fun c=>use_V2 c (PN2object mary_PN)))).

Definition Problem120a:= ((EXISTS (fun a=>meeting_N a) (fun a=>attend_V2 a (PN2object smith_PN) /\ chair_V2 a (PN2object smith_PN))) -> (EXISTS (fun b=>meeting_N b) (fun b=>chair_V2 b (PN2object smith_PN)))).

Definition Problem121a:= ((EXISTS (fun a=>report_N a) (fun a=>deliver_V2to (PN2object itel_PN) a (PN2object smith_PN))) /\ (EXISTS (fun b=>invoice_N b) (fun b=>deliver_V3 (PN2object itel_PN) b (PN2object smith_PN))) /\ (EXISTS (fun c=>project_proposal_N c) (fun c=>deliver_V3 (PN2object itel_PN) c (PN2object smith_PN))) -> (EXISTS (fun d=>report_N d) (fun d=>deliver_V2to (PN2object itel_PN) d (PN2object smith_PN))) /\ (EXISTS (fun e=>invoice_N e) (fun e=>deliver_V2to (PN2object itel_PN) e (PN2object smith_PN))) /\ (EXISTS (fun f=>project_proposal_N f) (fun f=>deliver_V2to (PN2object itel_PN) f (PN2object smith_PN)))).

Definition Problem122a:= ((FORALL (fun a=>committee_N a) (fun a=>(EXISTS (fun b=>chairman_N b) (fun b=>have_V2 b a /\ (EXISTS (fun d=>have_V2 d a /\ member_N d) (fun d=>(EXISTS (fun c=>True) (fun c=>appoint_V2by d b c)))))))) -> (FORALL (fun e=>committee_N e) (fun e=>(EXISTS (fun g=>chairman_N g /\ (EXISTS (fun f=>have_V2 f e /\ member_N f) (fun f=>appoint_V2 f g))) (fun g=>have_V2 g e))))).

Parameter most: (object -> Prop) -> (object -> Prop) -> Prop.

Definition  MOST:= fun CN=> fun VP=>  exists x, CN x /\ VP x /\ most CN VP.

Definition Problem123a:= ((MOST (fun a=>report_N a /\ need_V2 a (PN2object smith_PN)) (fun a=>send_V2 a (PN2object itel_PN))) /\ (FORALL (fun b=>report_N b /\ need_V2 b (PN2object smith_PN) /\ send_V2 b (PN2object itel_PN)) (fun b=>True /\ (EXISTS (fun c=>have_V2 c (PN2object smith_PN) /\ desk_N c) (fun c=>_BE_ c b)))) -> (EXISTS (fun d=>have_V2 d (PN2object smith_PN) /\ desk_N d) (fun d=>(EXISTS (fun e=>report_Nfrom (PN2object itel_PN) e) (fun e=>_BE_ d e))))).

Theorem T123a: Problem123a. cbv. intros. destruct H. firstorder. Qed.                        

                           
Definition Problem123b:= ((MOST (fun a=>report_N a /\ need_V2 a (PN2object smith_PN)) (fun a=>send_V2 a (PN2object itel_PN))) /\ (FORALL (fun b=>report_N b /\ need_V2 b (PN2object smith_PN) /\ send_V2 b (PN2object itel_PN)) (fun b=>True)) /\ (EXISTS (fun c=>have_V2 c (PN2object smith_PN) /\ desk_N c) (fun c=>_BE_ c (PN2object itel_PN))) -> (EXISTS (fun d=>have_V2 d (PN2object smith_PN) /\ desk_N d) (fun d=>(EXISTS (fun e=>report_Nfrom (PN2object itel_PN) e) (fun e=>_BE_ d e))))).

Theorem T123b: Problem123b.   cbv.  intros. destruct H. Abort all.


Parameter at_least: nat -> (object -> Prop) -> (object -> Prop) -> Prop.
Definition  ATLEAST:= fun n : nat => fun CN=> fun VP=>  exists x, CN x /\ VP x /\ at_least n CN VP.


Definition Problem124a:= ((ATLEAST (2) (fun b=>True) (fun b=>(ATLEAST (10) (fun a=>machine_N a) (fun a=>appA missing_A (fun x1 => True) b)) /\ (EXISTS (fun c=>True) (fun c=>remove_V2 b c)))) -> (ATLEAST (2) (fun d=>machine_N d) (fun d=>(EXISTS (fun e=>True) (fun e=>remove_V2 d e))))).

Theorem T124a: Problem124a.
cbv. intros. elim H. intros. destruct H0. destruct H1. destruct H1. exists x.  firstorder. 
  Abort all. 
Definition Problem124b:= ((ATLEAST (10) (fun a=>machine_N a) (fun a=>(ATLEAST (2) (fun b=>True) (fun b=>appA missing_A (fun x1 => True) b)) /\ (EXISTS (fun c=>True) (fun c=>remove_V2 a c)))) -> (ATLEAST (2) (fun d=>machine_N d) (fun d=>(EXISTS (fun e=>True) (fun e=>remove_V2 d e))))).

Theorem T124b : Problem124b. 
cbv. intros. elim H.  
intros. exists x.   split. destruct H0. 
assumption. destruct H0.
destruct H1. destruct H1. elim H3. intros.  split. exists x0. exact H4. 
Theorem T124b: Problem124b. cbv. firstorder. intuition. Abort all. 

Definition Problem125a:= ((ATLEAST (2) (fun b=>True) (fun b=>(ATLEAST (10) (fun a=>machine_N a) (fun a=>appA missing_A (fun x1 => True) b)) /\ (EXISTS (fun c=>True) (fun c=>remove_V2 b c)))) -> (ATLEAST (8) (fun d=>machine_N d) (fun d=>(EXISTS (fun e=>True) (fun e=>remove_V2 d e))))).

                            

Definition Problem125b:= ((ATLEAST (10) (fun a=>machine_N a) (fun a=>(ATLEAST (2) (fun b=>True) (fun b=>appA missing_A (fun x1 => True) b)) /\ (EXISTS (fun c=>True) (fun c=>remove_V2 a c)))) -> (ATLEAST (8) (fun d=>machine_N d) (fun d=>(EXISTS (fun e=>True) (fun e=>remove_V2 d e))))).

Definition Problem126a:= ((ATLEAST (2) (fun b=>True) (fun b=>(ATLEAST (10) (fun a=>machine_N a) (fun a=>appA missing_A (fun x1 => True) b)) /\ _BE_ here_Adv b)) -> (ATLEAST (10) (fun c=>machine_N c) (fun c=>_BE_ here_Adv c))).

Definition Problem126b:= ((ATLEAST (10) (fun a=>machine_N a) (fun a=>(ATLEAST (2) (fun b=>True) (fun b=>appA missing_A (fun x1 => True) b)) /\ _BE_ here_Adv a)) -> (ATLEAST (10) (fun c=>machine_N c) (fun c=>_BE_ here_Adv c))).

Parameter take_V2adv: Adv -> object -> object -> Prop.

Definition Problem127a:= ((EXISTS (fun a=>machine_N a) (fun a=>take_V2adv on_tuesday_Adv a (PN2object smith_PN))) /\ (EXISTS (fun b=>machine_N b) (fun b=>take_V2adv on_wednesday_Adv b (PN2object jones_PN))) /\ put_in_V3 (PN2object jones_PN) (THE lobby_N) (PN2object jones_PN) -> (ATLEAST (2) (fun c=>machine_N c) (fun c=>put_in_V3 c (THE lobby_N) (PN2object smith_PN))) /\ (ATLEAST (2) (fun c=>machine_N c) (fun c=>put_in_V3 c (THE lobby_N) (PN2object jones_PN)))).

Parameter go8walk_Vto: object -> object -> Prop.

Definition Problem128a:= (FORALL (fun b=>meeting_N b) (fun b=>go8walk_Vto b (PN2object john_PN) /\ (EXISTS (fun a=>have_V2 a (PN2object john_PN) /\ colleague_N a) (fun a=>(EXISTS (fun b=>meeting_N b) (fun b=>go8walk_Vto b a)))) /\ hate_V2 b (PN2object john_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object john_PN) /\ colleague_N c) (fun c=>hate_V2 b c)) -> (EXISTS (fun d=>have_V2 d (PN2object john_PN) /\ colleague_N d) (fun d=>hate_V2 b d)))).

Definition Problem129a:= (FORALL (fun b=>meeting_N b) (fun b=>go8walk_Vto b (PN2object john_PN) /\ (EXISTS (fun a=>have_V2 a (PN2object john_PN) /\ colleague_N a) (fun a=>(EXISTS (fun b=>meeting_N b) (fun b=>go8walk_Vto b a)))) /\ hate_V2 b (PN2object john_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object john_PN) /\ colleague_N c) (fun c=>hate_V2 b c)) -> hate_V2 b (PN2object john_PN))).

Definition Problem130a:= (FORALL (fun b=>meeting_N b) (fun b=>go8walk_Vto b (PN2object john_PN) /\ (EXISTS (fun a=>have_V2 a (PN2object john_PN) /\ colleague_N a) (fun a=>(EXISTS (fun b=>meeting_N b) (fun b=>go8walk_Vto b a)))) /\ hate_V2 b (PN2object john_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object john_PN) /\ colleague_N c) (fun c=>hate_V2 b c)) -> hate_V2 b (PN2object john_PN))).

Definition Problem131a:= ((FORALL (fun a=>department_N a) (fun a=>(EXISTS (fun b=>appA dedicated_A line_N b) (fun b=>have_V2 b a)) /\ rent_from_V3 a (PN2object bt_PN) a)) -> (FORALL (fun c=>department_N c) (fun c=>(EXISTS (fun d=>line_N d) (fun d=>rent_from_V3 d (PN2object bt_PN) c))))).

Definition Problem132a:= ((FORALL (fun a=>department_N a) (fun a=>(EXISTS (fun b=>appA dedicated_A line_N b) (fun b=>have_V2 b a)))) /\ rent_from_V3 (THE sales_department_N) (PN2object bt_PN) (THE sales_department_N) -> (EXISTS (fun c=>line_N c) (fun c=>rent_from_V3 c (PN2object bt_PN) (THE sales_department_N)))).

Definition Problem132b:= ((FORALL (fun b=>appA dedicated_A line_N b) (fun b=>(FORALL (fun a=>department_N a) (fun a=>have_V2 b a)) /\ rent_from_V3 b (PN2object bt_PN) (THE sales_department_N))) -> (EXISTS (fun c=>line_N c) (fun c=>rent_from_V3 c (PN2object bt_PN) (THE sales_department_N)))).

Definition Problem132c:= ((FORALL (fun a=>department_N a) (fun a=>(EXISTS (fun b=>appA dedicated_A line_N b) (fun b=>have_V2 b a)) /\ rent_from_V3 a (PN2object bt_PN) (THE sales_department_N))) -> (EXISTS (fun c=>line_N c) (fun c=>rent_from_V3 c (PN2object bt_PN) (THE sales_department_N)))).

Parameter several: (object -> Prop) -> (object -> Prop) -> Prop.

Definition  SEVERAl:= fun CN=> fun VP=>  exists x, CN x /\ VP x /\ most CN VP.

Definition Problem133a:= ((SEVERAl (fun a=>computer_N a) (fun a=>own_V2 a (PN2object gfi_PN))) /\ (FORALL (fun b=>computer_N b /\ own_V2 b (PN2object gfi_PN)) (fun b=>True /\ maintain_V2 b (PN2object itel_PN))) -> (FORALL (fun c=>computer_N c /\ own_V2 c (PN2object gfi_PN)) (fun c=>maintain_V2 c (PN2object itel_PN)))).

Parameter have_V2for : object -> object -> object ->  Prop.
Parameter exact: nat ->  (object -> Prop) -> (object -> Prop) -> Prop.
Definition  EXACT:= fun n : nat => fun CN=> fun VP=>  exists x, CN x /\ VP x /\ exact n CN VP.

Definition Problem134a:= ((FORALL (fun b=>customer_N b /\ (EXISTS (fun a=>computer_N a) (fun a=>own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for c c b)))) /\ customer_N (PN2object mfi_PN) /\ (EXACT (1) (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) -> (FORALL (fun f=>computer_N f) (fun f=>(EXISTS (fun e=>service_contract_N e) (fun e=>have_V2for f e (PN2object mfi_PN)))))).

(**Definition Problem134b:= ((FORALL (fun b=>(EXISTS (fun a=>computer_N a) (fun a=>customer_N b /\ own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for a c b)))) /\ customer_N (PN2object mfi_PN) /\ (EXACT (1) (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) -> (FORALL (fun f=>computer_N f) (fun f=>(EXISTS (fun e=>service_contract_N e) (fun e=>have_V2for f e (PN2object mfi_PN)))))).  (**not in scope**)**)

Definition Problem135a:= ((FORALL (fun b=>customer_N b /\ (EXISTS (fun a=>computer_N a) (fun a=>own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for c c b)))) /\ customer_N (PN2object mfi_PN) /\ (SEVERAl (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) /\ (FORALL (fun e=>computer_N e /\ own_V2 e (PN2object mfi_PN)) (fun e=>True)) -> (FORALL (fun g=>computer_N g) (fun g=>(EXISTS (fun f=>service_contract_N f) (fun f=>have_V2for g f (PN2object mfi_PN)))))).

(**Definition Problem135b:= ((FORALL (fun b=>(EXISTS (fun a=>computer_N a) (fun a=>customer_N b /\ own_V2 a b))) (fun b=>(EXISTS (fun c=>service_contract_N c) (fun c=>have_V2for a c b)))) /\ customer_N (PN2object mfi_PN) /\ (SEVERAL (fun d=>computer_N d) (fun d=>own_V2 d (PN2object mfi_PN))) /\ (FORALL (fun e=>computer_N e /\ own_V2 e (PN2object mfi_PN)) (fun e=>True)) -> (FORALL (fun g=>computer_N g) (fun g=>(EXISTS (fun f=>service_contract_N f) (fun f=>have_V2for g f (PN2object mfi_PN)))))). (not in scope**)

Parameter take_V2to : object -> object -> object  -> Prop.
Parameter take_V2at :   object -> object -> (object -> Prop)  ->   Prop. 




(**Definition Problem136a:= ((FORALL (fun b=>executive_N b /\ (EXISTS (fun a=>laptop_computer_N a) (fun a=>have_V2 a b))) (fun b=>bring_V2V (THE meeting_N) (fun x1 => (EXISTS (fun c=>note_N c) (fun c=>take_V2at (THE meeting_N) c x1))) b)) /\ executive_N (PN2object smith_PN) /\ (ATLEAST (5) (fun d=>appA different_A laptop_computer_N d) (fun d=>own_V2 d (PN2object smith_PN))) -> (ATLEAST (5) (fun e=>laptop_computer_N e) (fun e=>take_V2to (THE meeting_N) e (PN2object smith_PN)))). take_V2at definition**)

(**Definition Problem136b:= ((FORALL (fun b=>executive_N b /\ (EXISTS (fun a=>laptop_computer_N a) (fun a=>have_V2 a b))) (fun b=>(EXISTS (fun c=>note_N c) (fun c=>bring_V2V c (fun x1 => take_V2at (THE meeting_N) c x1))) b)) /\ executive_N (PN2object smith_PN) /\ (ATLEAST (5) (fun d=>appA different_A laptop_computer_N d) (fun d=>own_V2 d (PN2object smith_PN))) -> (ATLEAST (5) (fun e=>laptop_computer_N e) (fun e=>take_V2to (THE meeting_N) e (PN2object smith_PN)))).**)

(**Definition Problem136c:= ((FORALL (fun b=>(EXISTS (fun a=>laptop_computer_N a) (fun a=>executive_N b /\ have_V2 a b))) (fun b=>bring_V2V a (fun x1 => (EXISTS (fun c=>note_N c) (fun c=>take_V2at (THE meeting_N) c x1))) b)) /\ executive_N (PN2object smith_PN) /\ (ATLEAST (5) (fun d=>appA different_A laptop_computer_N d) (fun d=>own_V2 d (PN2object smith_PN))) -> (ATLEAST (5) (fun e=>laptop_computer_N e) (fun e=>take_V2to (THE meeting_N) e (PN2object smith_PN)))).** not in scope**)


Parameter cover_page_Npossess: object -> object -> Prop.

Definition Problem138a:= ((FORALL (fun b=>cover_page_N b) (fun b=>(FORALL (fun a=>report_N a) (fun a=>have_V2 b a)) /\ report_N (PN2object r95103_PN) /\ sign_V2 b (PN2object smith_PN))) -> sign_V2 (THE (cover_page_Npossess (PN2object r95103_PN))) (PN2object smith_PN)).

Definition Problem139a:= ((EXISTS (fun a=>company_director_N a) (fun a=>(EXISTS (fun b=>appA large_A payrise_N b) (fun b=>award_V3 a b a)))) -> (EXISTS (fun c=>company_director_N c) (fun c=>(EXISTS (fun d=>payrise_N d) (fun d=>award_and_be_awarded_V2 d c))))).
Print VP. 

Parameter Person_N : N.
(****)Definition Problem140a:= (say_VS (hurt_V2 (PN2object bill_PN) (PN2object bill_PN)) (PN2object john_PN) -> say_VS (EXISTS (fun a=>True) (fun a=>hurt_V2 (PN2object bill_PN) a)) (PN2object john_PN)).

(**Definition Problem141a:= (say_VS (hurt_V2 (PN2object bill_PN) (PN2object bill_PN)) (PN2object john_PN) -> (EXISTS (fun a=>Person_N a) (fun a=>say_VS (EXISTS (fun b=>True) (fun b=>hurt_V2 (PN2object john_PN) b)) a))).)**)

Definition Problem142a:= (speak_to_V2 (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2 (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2 (PN2object mary_PN) (PN2object bill_PN)).

Parameter speak_to_V2adv : Adv -> object -> object -> Prop. 

Definition Problem143a:= (speak_to_V2 (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2 (PN2object mary_PN) (PN2object bill_PN) /\ speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object john_PN) -> speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem144a:= (speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem144b:= (speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2 (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object bill_PN)).


Parameter  speak_to_V2advadv :Adv ->  Adv -> object -> object -> Prop. 

Definition Problem145a:= (speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2advadv at_four_oclock_Adv at_five_oclock_Adv (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2adv at_five_oclock_Adv (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem145b:= (speak_to_V2adv at_four_oclock_Adv (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2adv at_five_oclock_Adv (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2adv at_five_oclock_Adv (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem146a:= (speak_to_V2 (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2 (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2 (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem147a:= (speak_to_V2adv on_monday_Adv (PN2object mary_PN) (PN2object john_PN) /\ NOT(speak_to_V2adv on_monday_Adv (PN2object mary_PN) (PN2object bill_PN)) -> speak_to_V2adv on_monday_Adv (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem147b:= (speak_to_V2adv on_monday_Adv (PN2object mary_PN) (PN2object john_PN) /\ NOT(speak_to_V2 (PN2object mary_PN) (PN2object bill_PN)) -> speak_to_V2adv on_monday_Adv (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem148a:= (speak_to_V2 (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2 (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem149a:= (speak_to_V2 (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2 (PN2object mary_PN) (THE student_N) -> speak_to_V2 (PN2object mary_PN) (THE student_N)).

Parameter go8travel_Vtoby8means : object -> object -> object -> Prop. 
Parameter go8travel_Vtoby8meansby8means : object -> object ->  object -> object -> Prop.
Definition Problem150a:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>(EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8meansby8means (PN2object paris_PN) b b (PN2object bill_PN))))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (PN2object bill_PN)))).

Definition Problem150b:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vtoby8means (PN2object paris_PN) b (PN2object bill_PN))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (PN2object bill_PN)))).

Parameter go8travel_Vby8means : object -> object -> Prop. 

Definition Problem150c:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vby8means b (PN2object bill_PN))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (PN2object bill_PN)))).

Parameter go8travel_Vtoby8meansby8meansto : object -> object ->  object -> object -> object -> Prop. 
Definition Problem151a:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>(EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8meansby8meansto (PN2object paris_PN) b b (PN2object berlin_PN) (PN2object bill_PN))))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object berlin_PN) c (PN2object bill_PN)))).

Parameter go8travel_Vtoby8meansto : object -> object ->  object -> object -> Prop.

Definition Problem151b:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vtoby8meansto (PN2object paris_PN) b (PN2object berlin_PN) (PN2object bill_PN))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object berlin_PN) c (PN2object bill_PN)))).

Parameter go8travel_Vby8meansto :  object ->  object -> object -> Prop.


Definition Problem151c:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vby8meansto b (PN2object berlin_PN) (PN2object bill_PN))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object berlin_PN) c (PN2object bill_PN)))).

Definition Problem152a:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8meansto (PN2object paris_PN) b (PN2object berlin_PN) (PN2object bill_PN))) -> (EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8means (PN2object berlin_PN) b (PN2object bill_PN)))).

Parameter go8travel_Vtoto :  object ->  object -> object -> Prop.

Definition Problem152b:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ go8travel_Vtoto (PN2object paris_PN) (PN2object berlin_PN) (PN2object bill_PN) -> (EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8means (PN2object berlin_PN) b (PN2object bill_PN)))).

 Parameter go8travel_Vto :  object -> object -> Prop.

Definition Problem152c:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ go8travel_Vto (PN2object berlin_PN) (PN2object bill_PN) -> (EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8means (PN2object berlin_PN) b (PN2object bill_PN)))).



Definition Problem153a:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>(EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8meansby8means (PN2object paris_PN) b b (THE student_N))))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (THE student_N)))).

Definition Problem153b:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vtoby8means (PN2object paris_PN) b (THE student_N))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (THE student_N)))).

Definition Problem153c:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vby8means b (THE student_N))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (THE student_N)))).

Definition Problem154a:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>(EXISTS (fun b=>car_N b) (fun b=>go8travel_Vtoby8meansby8means (PN2object paris_PN) b b (PN2object bill_PN))))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (PN2object bill_PN)))).

Definition Problem154b:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vtoby8means (PN2object paris_PN) b (PN2object bill_PN))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (PN2object bill_PN)))).

Definition Problem154c:= ((EXISTS (fun a=>car_N a) (fun a=>go8travel_Vtoby8means (PN2object paris_PN) a (PN2object john_PN))) /\ (EXISTS (fun b=>train_N b) (fun b=>go8travel_Vby8means b (PN2object bill_PN))) -> (EXISTS (fun c=>train_N c) (fun c=>go8travel_Vtoby8means (PN2object paris_PN) c (PN2object bill_PN)))).

Definition Problem155a:= ((EXISTS (fun a=>car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>True) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

(**Definition Problem156a:= ((EXISTS (fun a=>car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>True) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>car_N c /\ own_V2 c (PN2object john_PN) /\ own_V2 c (PN2object bill_PN)) (fun c=>_BE_ c))). **type error with _BE_**)

Definition Problem157a:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA blue_A (appA red_A car_N) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA blue_A car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem157b:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA blue_A car_N b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA blue_A car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem158a:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA blue_A (appA red_A car_N) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA red_A car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem158b:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA blue_A car_N b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA red_A car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem159a:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA fast_A (appA red_A car_N) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA fast_A car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem159b:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA fast_A car_N b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA fast_A car_N c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem160a:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA fast_A (appA red_A car_N) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA fast_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem160b:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA fast_A car_N b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA fast_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem161a:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA fast_A (appA red_A car_N) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA fast_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem161b:= ((EXISTS (fun a=>appA red_A car_N a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA fast_A car_N b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA fast_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem162a:= ((EXISTS (fun a=>appA fast_A (appA red_A car_N) a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA slow_A (appA fast_A (appA red_A car_N)) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA slow_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem162b:= ((EXISTS (fun a=>appA fast_A (appA red_A car_N) a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA slow_A (appA red_A car_N) b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA slow_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Definition Problem162c:= ((EXISTS (fun a=>appA fast_A (appA red_A car_N) a) (fun a=>own_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>appA slow_A car_N b) (fun b=>own_V2 b (PN2object bill_PN))) -> (EXISTS (fun c=>appA slow_A (appA red_A car_N) c) (fun c=>own_V2 c (PN2object bill_PN)))).

Parameter knowVQ : VS_CN.

Parameter WHY: Prop -> Prop.
Definition Problem163a:= ((EXISTS (fun b=>have_V2 b (PN2object john_PN) /\ paper_N b /\ (EXISTS (fun a=>True) (fun a=>accept_V2 b a))) (fun b=>have_V2 b (PN2object john_PN))) /\ NOT(knowVQ (WHY (EXISTS (fun d=>have_V2 d (PN2object john_PN) /\ paper_N d /\ (EXISTS (fun c=>True) (fun c=>accept_V2 d c))) (fun d=>have_V2 d (PN2object john_PN)))) (PN2object bill_PN)) -> knowVQ (WHY (EXISTS (fun f=>have_V2 f (PN2object john_PN) /\ paper_N f /\ (EXISTS (fun e=>True) (fun e=>accept_V2 f e))) (fun f=>have_V2 f (PN2object john_PN)))) (PN2object bill_PN)).

Definition Problem163b:= ((EXISTS (fun b=>have_V2 b (PN2object john_PN) /\ paper_N b /\ (EXISTS (fun a=>True) (fun a=>accept_V2 b a))) (fun b=>have_V2 b (PN2object john_PN))) /\ NOT(knowVQ (WHY (EXISTS (fun d=>have_V2 d (PN2object john_PN) /\ paper_N d /\ (EXISTS (fun c=>True) (fun c=>accept_V2 d c))) (fun d=>have_V2 d (PN2object john_PN)))) (PN2object bill_PN)) -> knowVQ (WHY (EXISTS (fun f=>have_V2 f (PN2object bill_PN) /\ paper_N f /\ (EXISTS (fun e=>True) (fun e=>accept_V2 f e))) (fun f=>have_V2 f (PN2object john_PN)))) (PN2object bill_PN)).

Definition Problem163c:= ((EXISTS (fun b=>have_V2 b (PN2object john_PN) /\ paper_N b /\ (EXISTS (fun a=>True) (fun a=>accept_V2 b a))) (fun b=>have_V2 b (PN2object john_PN))) /\ NOT(knowVQ (WHY (EXISTS (fun d=>have_V2 d (PN2object bill_PN) /\ paper_N d /\ (EXISTS (fun c=>True) (fun c=>accept_V2 d c))) (fun d=>have_V2 d (PN2object john_PN)))) (PN2object bill_PN)) -> knowVQ (WHY (EXISTS (fun f=>have_V2 f (PN2object john_PN) /\ paper_N f /\ (EXISTS (fun e=>True) (fun e=>accept_V2 f e))) (fun f=>have_V2 f (PN2object john_PN)))) (PN2object bill_PN)).

Definition Problem163d:= ((EXISTS (fun b=>have_V2 b (PN2object john_PN) /\ paper_N b /\ (EXISTS (fun a=>True) (fun a=>accept_V2 b a))) (fun b=>have_V2 b (PN2object john_PN))) /\ NOT(knowVQ (WHY (EXISTS (fun d=>have_V2 d (PN2object bill_PN) /\ paper_N d /\ (EXISTS (fun c=>True) (fun c=>accept_V2 d c))) (fun d=>have_V2 d (PN2object john_PN)))) (PN2object bill_PN)) -> knowVQ (WHY (EXISTS (fun f=>have_V2 f (PN2object bill_PN) /\ paper_N f /\ (EXISTS (fun e=>True) (fun e=>accept_V2 f e))) (fun f=>have_V2 f (PN2object john_PN)))) (PN2object bill_PN)).

 Parameter speak_to_V2to : object -> object -> object -> Prop.

Definition Problem164a:= (speak_to_V2 (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2to (PN2object sue_PN) (PN2object mary_PN) (PN2object john_PN) -> speak_to_V2 (PN2object sue_PN) (PN2object john_PN)).

Definition Problem165a:= (speak_to_V2adv on_friday_Adv (PN2object mary_PN) (PN2object john_PN) -> speak_to_V2adv on_friday_Adv (PN2object mary_PN) (PN2object john_PN)).

Definition Problem166a:= (speak_to_V2adv on_thursday_Adv (PN2object mary_PN) (PN2object john_PN) /\ speak_to_V2advadv on_thursday_Adv on_friday_Adv (PN2object mary_PN) (PN2object john_PN) -> speak_to_V2adv on_friday_Adv (PN2object mary_PN) (PN2object john_PN)).

Definition Problem167a:= ((ATLEAST (20) (fun a=>man_N a) (fun a=>work_in_V2 (THE sales_department_N) a)) /\ (EXACT (1) (fun b=>woman_N b) (fun b=>work_in_V2 (THE sales_department_N) b)) -> (ATLEAST (2) (fun c=>woman_N c) (fun c=>work_in_V2 (THE sales_department_N) c))).

Parameter work_Vadv : Adv -> object -> Prop.

Definition Problem168a:= ((ATLEAST (5) (fun a=>man_N a) (fun a=>work_Vadv part_time_Adv a)) /\ (ATLEAST (45) (fun b=>woman_N b) (fun b=>work_Vadv part_time_Adv b)) -> (ATLEAST (45) (fun c=>woman_N c) (fun c=>work_Vadv part_time_Adv c))).

Definition Problem168b:= ((ATLEAST (5) (fun a=>man_N a) (fun a=>work_Vadv part_time_Adv a)) /\ (ATLEAST (45) (fun b=>woman_N b) (fun b=>work_V b)) -> (ATLEAST (45) (fun c=>woman_N c) (fun c=>work_Vadv part_time_Adv c))).

Parameter find_V2before : object -> object -> object -> Prop.

Definition Problem169a:= (find_V2before (PN2object bill_PN) (PN2object mary_PN) (PN2object john_PN) -> find_V2 (PN2object mary_PN) (PN2object bill_PN) /\ find_V2 (PN2object mary_PN) (PN2object john_PN)).

Definition Problem170a:= (find_V2before (PN2object bill_PN) (PN2object mary_PN) (PN2object john_PN) -> find_V2 (PN2object bill_PN) (PN2object john_PN) /\ find_V2 (PN2object mary_PN) (PN2object john_PN)).

Definition Problem173a:= ((FORALL (fun a=>Person_N a /\ speak_to_V2 a (PN2object john_PN)) (fun a=>speak_to_V2 a (PN2object bill_PN))) /\ speak_to_V2 (PN2object mary_PN) (PN2object john_PN) -> speak_to_V2 (PN2object mary_PN) (PN2object bill_PN)).

Definition Problem174a:= ((FORALL (fun a=>Person_N a /\ speak_to_V2 a (PN2object john_PN)) (fun a=>speak_to_V2 a (PN2object bill_PN))) /\ speak_to_V2 (PN2object mary_PN) (PN2object bill_PN) -> speak_to_V2 (PN2object mary_PN) (PN2object john_PN)).

Definition Problem175a:= (say_VS (EXISTS (fun a=>report_N a) (fun a=>write_V2 a (PN2object mary_PN))) (PN2object john_PN) /\ say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object mary_PN))) (PN2object bill_PN) -> say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object mary_PN))) (PN2object bill_PN)).

Definition Problem175b:= (say_VS (EXISTS (fun a=>report_N a) (fun a=>write_V2 a (PN2object mary_PN))) (PN2object john_PN) /\ (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object bill_PN))) -> say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object mary_PN))) (PN2object bill_PN)).

Definition Problem176a:= (say_VS ((EXISTS (fun a=>report_N a) (fun a=>write_V2 a (PN2object mary_PN))) /\ (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object bill_PN)))) (PN2object john_PN) -> say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object bill_PN))) (PN2object john_PN)).

Definition Problem177a:= (say_VS ((EXISTS (fun a=>report_N a) (fun a=>write_V2 a (PN2object mary_PN))) /\ say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object bill_PN))) (PN2object mary_PN)) (PN2object john_PN) -> say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object mary_PN))) (PN2object bill_PN)).

Definition Problem178a:= ((EXISTS (fun a=>report_N a) (fun a=>write_V2 a (PN2object john_PN))) /\ say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object peter_PN))) (PN2object bill_PN) -> say_VS (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object peter_PN))) (PN2object bill_PN)).

Definition Problem179a:= (((EXISTS (fun a=>report_N a) (fun a=>write_V2 a (PN2object john_PN))) -> (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object bill_PN)))) /\ (EXISTS (fun b=>report_N b) (fun b=>write_V2 b (PN2object john_PN))) -> (EXISTS (fun c=>report_N c) (fun c=>write_V2 c (PN2object bill_PN)))).

Definition Problem180a:= (want_VV (fun x1 => (EXISTS (fun a=>car_N a) (fun a=>buy_V2 a x1))) (PN2object john_PN) /\ (EXISTS (fun b=>car_N b) (fun b=>buy_V2 b (PN2object john_PN))) -> (EXISTS (fun b=>car_N b) (fun b=>buy_V2 b (PN2object john_PN)))).


Definition Problem181a:= (need_VV (fun x1 => (EXISTS (fun a=>car_N a) (fun a=>buy_V2 a x1))) (PN2object john_PN) /\ (EXISTS (fun b=>car_N b) (fun b=>buy_V2 b (PN2object bill_PN))) -> (EXISTS (fun b=>car_N b) (fun b=>buy_V2 b (PN2object bill_PN)))).

Definition Problem182a:= ((EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ company_N a) (fun a=>represent_V2 a (PN2object smith_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object jones_PN))) -> (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object jones_PN)))).

Definition Problem183a:= ((EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ company_N a) (fun a=>represent_V2 a (PN2object smith_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object jones_PN))) -> (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object jones_PN)))).

Definition Problem184a:= ((EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ company_N a) (fun a=>represent_V2 a (PN2object smith_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object jones_PN))) -> (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object smith_PN)))).

Definition Problem185a:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem185b:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem185c:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem185d:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem185e:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem185f:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem185g:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem185h:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem185i:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ appA own_A proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem186a:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem186b:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem186c:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem186d:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem186e:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem186f:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem186g:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem186h:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN)).

Definition Problem186i:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem187a:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem187b:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem187c:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object smith_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem188a:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem188b:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

Definition Problem188c:= (claim_VS (EXISTS (fun a=>have_V2 a (PN2object smith_PN) /\ proposal_N a) (fun a=>cost_V2 a (PN2object smith_PN))) (PN2object smith_PN) /\ (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object jones_PN))) -> claim_VS (EXISTS (fun b=>have_V2 b (PN2object jones_PN) /\ proposal_N b) (fun b=>cost_V2 b (PN2object smith_PN))) (PN2object jones_PN)).

(**Definition Problem189a:= (man_N (PN2object john_PN) /\ woman_N (PN2object mary_PN) /\ (EXISTS (fun a=>have_V2 a (PN2object john_PN) /\ company_N a) (fun a=>represent_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>have_V2 b assumedNP /\ company_N b) (fun b=>represent_V2 b (PN2object mary_PN))) -> (EXISTS (fun b=>have_V2 b (PN2object mary_PN) /\ appA own_A company_N b) (fun b=>represent_V2 b (PN2object mary_PN)))). assumedNP**)

(** Definition Problem190a:= (man_N (PN2object john_PN) /\ woman_N (PN2object mary_PN) /\ (EXISTS (fun a=>have_V2 a (PN2object john_PN) /\ company_N a) (fun a=>represent_V2 a (PN2object john_PN))) /\ (EXISTS (fun b=>have_V2 b assumedNP /\ company_N b) (fun b=>represent_V2 b (PN2object mary_PN))) -> (EXISTS (fun b=>have_V2 b (PN2object john_PN) /\ company_N b) (fun b=>represent_V2 b (PN2object mary_PN)))). **)

Parameter go8walk_Vadv : Adv -> object -> Prop.

(**Definition Problem191a:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object frank_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) d)))). assumed**)

(**Definition Problem191b:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object bill_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) d)))).assumed**)

(**Definition Problem191c:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoadvto (THE meeting_N) together_Adv b (PN2object carl_PN))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) d)))).

Definition Problem191d:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoto (THE meeting_N) b (PN2object carl_PN))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) d)))).

Definition Problem191e:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vto b (PN2object carl_PN))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) d)))).assumed**)

(**Definition Problem192a:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object frank_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun d=>have_V2 d (PN2object alan_PN) /\ wife_N d) (fun d=>shall_VV (go8walk_Vadv together_Adv) d))) e)))). assumed**)

(**Definition Problem192b:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object bill_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun d=>have_V2 d (PN2object alan_PN) /\ wife_N d) (fun d=>shall_VV (go8walk_Vadv together_Adv) d))) e)))).assumed**)

(**Definition Problem192c:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoadvto (THE meeting_N) together_Adv b (PN2object carl_PN))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun d=>have_V2 d (PN2object alan_PN) /\ wife_N d) (fun d=>shall_VV (go8walk_Vadv together_Adv) d))) e)))).assumed**)

(**Definition Problem192d:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoto (THE meeting_N) b (PN2object carl_PN))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun d=>have_V2 d (PN2object alan_PN) /\ wife_N d) (fun d=>shall_VV (go8walk_Vadv together_Adv) d))) e)))).

Definition Problem192e:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vto b (PN2object carl_PN))) -> ((EXISTS (fun c=>True) (fun c=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN)) c)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun d=>have_V2 d (PN2object alan_PN) /\ wife_N d) (fun d=>shall_VV (go8walk_Vadv together_Adv) d))) e)))).assumed **)

(**Definition Problem193a:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object frank_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).assumed**)

(**Definition Problem193b:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object bill_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).assumed**)

(**Definition Problem193c:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoadvto (THE meeting_N) together_Adv b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).

Definition Problem193d:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoto (THE meeting_N) b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).assumed**)

(**Definition Problem193e:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vto b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))). assumed**)

(**Definition Problem194a:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object frank_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) e)))).assumed**)

(**Definition Problem194b:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object bill_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) e)))).assumed**)

(**Definition Problem194c:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoadvto (THE meeting_N) together_Adv b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) e)))). assumed**)

(**Definition Problem194d:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoto (THE meeting_N) b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) e)))).assumed**)

(**Definition Problem194e:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vto b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun e=>True) (fun e=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN)) e)))). assumed**)

(**Definition Problem195a:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object frank_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).

Definition Problem195b:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>(EXISTS (fun b=>have_V2 b (PN2object frank_PN) /\ boss_N b) (fun b=>suggest_to_V2Sto b b (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) (PN2object bill_PN)) (PN2object carl_PN))))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).assumed**)

(**Definition Problem195c:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoadvto (THE meeting_N) together_Adv b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))).assumed**)

(**Definition Problem195d:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vtoto (THE meeting_N) b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))). assumed**)

(**Definition Problem195e:= ((EXISTS (fun a=>have_V2 a (PN2object frank_PN) /\ boss_N a) (fun a=>suggest_to_V2S a (shall_VV (go8walk_Vtoadv (THE meeting_N) together_Adv) assumedNP) (PN2object bill_PN))) /\ (EXISTS (fun b=>have_V2 b (PN2object alan_PN) /\ wife_N b) (fun b=>go8walk_Vto b (PN2object carl_PN))) -> ((EXISTS (fun d=>True) (fun d=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object bill_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object frank_PN) /\ (EXISTS (fun c=>have_V2 c (PN2object frank_PN) /\ boss_N c) (fun c=>shall_VV (go8walk_Vadv together_Adv) c))) d)) -> (EXISTS (fun f=>True) (fun f=>suggest_to_V2S IMPERSONAL (shall_VV (go8walk_Vadv together_Adv) (PN2object carl_PN) /\ shall_VV (go8walk_Vadv together_Adv) (PN2object alan_PN) /\ (EXISTS (fun e=>have_V2 e (PN2object alan_PN) /\ wife_N e) (fun e=>shall_VV (go8walk_Vadv together_Adv) e))) f)))). assumed**)

(**Definition Problem196a:= ((EXISTS (fun a=>lawyer_N a) (fun a=>(FORALL (fun b=>report_N b) (fun b=>sign_V2 b a)))) /\ (EXISTS (fun c=>auditor_N c) (fun c=>(FORALL (fun d=>report_N d) (fun d=>sign_V2 d c)))) /\ (ATLEAST (1) (fun e=>lawyer_N e /\ (FORALL (fun d=>report_N d) (fun d=>sign_V2 d e))) (fun e=>_BE_ e)) -> (ATLEAST (1) (fun g=>auditor_N g /\ (FORALL (fun f=>report_N f) (fun f=>sign_V2 f g))) (fun g=>_BE_ g))). _BE_ typing**)

