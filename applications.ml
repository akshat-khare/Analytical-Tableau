#use "lab1.ml";;
let checkTrivialTauto = check_tautology (Impl(L("x"),L("x")));;
let checkTrivialContrad = check_contradiction (And(L("x"),Not(L("x"))));;
(* let prop1 = T;; *)
(* Below is the example given in class *)
(* let prop1 = Impl(Impl( Impl(L("x1"), L("x2")) ,L("x1")),L("x1"));; *)
(* Below is a trivial contradiction *)
(* let prop1 = And(F, L("x"));; *)
(* Below is R *)
(* let prop1 = Impl(Impl(Not(L("p")), Not(L("q"))) ,  Impl( Impl(Not(L("p")), L("q")) , L("p"))) *)
(* Below is S *)
(* let prop1 = Impl( Impl (L("p"), Impl(L("q"), L("r"))), Impl( Impl(L("p"), L("q")), Impl(L("p"), L("r")) ));; *)
(* Below is K *)
let prop1 = Impl ( L("p"), Impl(L("q"), L("p")));;
let node1 = Leaf(prop1, true, NotExamined, NotClosed);;
let checkTruth = check_tautology prop1;;
let checkFalse = check_contradiction prop1;;
let assignment = find_assignments node1;;
let lengthassignment = length assignment;;
let fullydevelopnode1 = fully_develop node1;;
let contradnode1 = contrad_path fullydevelopnode1;;
let assignmentsNode1 = find_assignments_after_contrad contradnode1;;
let checkValidNodeOneStep a= let selected_node = select_node a in
								(match selected_node with
								| (b,c) -> (step_develop a c))
;; 
let validTableuCheck = valid_tableau (checkValidNodeOneStep node1);;