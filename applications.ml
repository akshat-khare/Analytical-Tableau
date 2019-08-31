#use "lab1.ml";;
check_tautology (Impl(L("x"),L("x")));;
check_contradiction (Impl(L("x"),L("x")));;
(* let prop1 = Impl(Impl( Impl(L("x1"), L("x2")) ,L("x1")),L("x1"));; *)
(* let prop1 = And(F, L("x"));; *)
(* let prop1 = Impl(Impl(Not(L("p")), Not(L("q"))) ,  Impl( Impl(Not(L("p")), L("q")) , L("p"))) *)
(* let prop1 = Impl( Impl (L("p"), Impl(L("q"), L("r"))), Impl( Impl(L("p"), L("q")), Impl(L("p"), L("r")) ));; *)
(* let prop1 = Impl ( L("p"), Impl(L("q"), L("p")));; *)
let node1 = Leaf(prop1, true, NotExamined, NotClosed);;
let checkTruth = check_tautology prop1;;
let checkFalse = check_contradiction prop1;;
let assignment = find_assignments node1;;
assignment;;
length assignment;;
let fullydevelopnode1 = fully_develop node1;;
fullydevelopnode1;;
let contradnode1 = contrad_path fullydevelopnode1;;
contradnode1;;
let assignmentsNode1 = find_assignments_after_contrad contradnode1;;
assignmentsNode1;;