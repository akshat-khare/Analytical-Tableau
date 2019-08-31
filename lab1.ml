open List;;
type prop = T | F | L of string 

                  | Not of prop

                  | And of prop * prop | Or of prop * prop | Impl of prop * prop | Iff of prop * prop
              ;;
type examinationStatus = Examined | NotExamined;;
type closedPathStatus = Closed | NotClosed;;
type node = Leaf of prop * bool * examinationStatus * closedPathStatus
			| Node of prop * bool * examinationStatus * closedPathStatus * (node list)
		;;
let rec percolate a n = match n with
| Leaf (p,b,examStatus,closedStatus) -> Node(p,b,examStatus,closedStatus,a)
| Node (p,b,examStatus,closedStatus,l) -> Node(p,b,examStatus,closedStatus, map (percolate a) l )
;;

exception ExaminedOrClosed;;

let rec subList l i ans = if (i+1=0) then ans else subList (tl l) (i-1) (ans@[(hd l)]);;


let rec isUnExaminedInList l wholePath traversedPathIndex= match l with
| [] -> raise ExaminedOrClosed
| x::xs -> (match x with
			 Leaf(p,b,examStatus,closedStatus) -> if examStatus=NotExamined then (x, (subList wholePath traversedPathIndex [])) else (isUnExaminedInList xs wholePath (traversedPathIndex+1))
			| Node(p,b, examStatus, closedStatus, childr) -> if examStatus=NotExamined then (x, (subList wholePath traversedPathIndex [])) else (isUnExaminedInList xs wholePath (traversedPathIndex+1)))
;;

let rec nodeIteratorExam childr l selectNodeFn thisPath index = match childr with
| [] -> raise ExaminedOrClosed
| x::xs -> try selectNodeFn x l (thisPath@[index]) with ExaminedOrClosed -> nodeIteratorExam xs l selectNodeFn thisPath (index+1)
;;
(* The following function is selecting unexamined node from bottom *)
let rec select_node_fn a l thisPath = match a with
| Leaf (p, b, examStatus, closedStatus) -> (match closedStatus with
											| Closed -> raise ExaminedOrClosed
											| NotClosed -> let newL = l@[a] in
															isUnExaminedInList newL thisPath (-1)
										)
| Node (p, b, examStatus, closedStatus, childr)  -> (match closedStatus with
												| Closed -> raise ExaminedOrClosed
												| NotClosed -> let newL = l@[a] in
																nodeIteratorExam childr newL select_node_fn thisPath 0
										)
;;

let select_node a = select_node_fn a [] [];;



let develop_specific_node a = match a with
| Leaf (p, b, examStatus, closedStatus) -> if (examStatus=Examined || closedStatus=Closed) then a else (match (p,b) with
											| (T, true) -> Leaf (p,b, Examined,NotClosed)
											| (F, false) -> Leaf (p, b, Examined, NotClosed)
											| (T, false) -> Leaf (p, b, Examined, Closed)
											| (F, true) -> Leaf (p, b, Examined, Closed)
											| (L (c), _) -> Leaf (p, b, Examined, NotClosed)
											| (Not c, d) -> let negationD = not d in
															let child = Leaf(c, negationD, NotExamined, NotClosed) in
															Node (p, b, Examined, NotClosed, [child])
											| (And (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Node(d, true, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, NotClosed, [secondNode])
											| (Or(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, NotClosed, [secondNode])
											| (Impl(c, d), false) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, NotClosed, [secondNode])
											| (And (c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, false, NotExamined, NotClosed) in
																	Node (p, b, Examined, NotClosed, [(secondNode);(firstNode)])
											| (Or (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																	Node (p, b, Examined, NotClosed, [(secondNode);(firstNode)])
											| (Impl(c,d), true) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																	Node (p, b, Examined, NotClosed, [(secondNode);(firstNode)])
											| (Iff(c,d), false) -> let leftFirst = Leaf(c, false, NotExamined, NotClosed) in
																	let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																	let rightFirst = Leaf(c, true, NotExamined, NotClosed) in
																	let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in
																	Node (p, b, Examined, NotClosed, [(leftSecond);(rightSecond)]) 
											| (Iff(c,d), true) -> let leftFirst = Leaf(c, true, NotExamined, NotClosed) in
																	let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																	let rightFirst = Leaf(c, false, NotExamined, NotClosed) in
																	let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in
																	Node (p, b, Examined, NotClosed, [(leftSecond);(rightSecond)]) 
																)
| Node (p, b, examStatus, closedStatus, l) -> if closedStatus=Closed then Node(p,b,Examined,Closed, l) else
											(match examStatus with
											| Examined -> Node(p, b, examStatus, NotClosed, l)
											| NotExamined -> match (p,b) with
															| (T, true) -> Node(p,b,Examined, NotClosed, l)
															| (F, false) -> Node(p,b, Examined, NotClosed, l)
															| (T, false) -> Node(p,b, Examined, Closed,l)
															| (F, true) -> Node(p,b, Examined, Closed, l)
															| (L(c), _) -> Node(p, b, Examined, NotClosed, l)
															| (Not c, d) -> let negationD = not d in
																			let child = Leaf(c, negationD, NotExamined, NotClosed) in
																			let newL = map (percolate [child]) l in
																			Node(p, b, Examined, NotClosed, newL)
															| (And (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Node(d, true, NotExamined, NotClosed, [firstNode]) in
																					let newL = map (percolate [secondNode]) l in
																					Node(p, b, Examined, NotClosed, newL)
															| (Or(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																					let newL = map (percolate [secondNode]) l in
																					Node(p, b, Examined, NotClosed, newL)
															| (Impl(c,d), false) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																					let newL = map (percolate [secondNode]) l in
																					Node(p, b, Examined, NotClosed, newL)
															| (And(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, false, NotExamined, NotClosed) in
																					let newL = map (percolate [firstNode;secondNode]) l in
																					Node (p, b, Examined, NotClosed, newL)
															| (Or(c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																					let newL = map (percolate [firstNode;secondNode]) l in
																					Node (p, b, Examined, NotClosed, newL)
															| (Impl (c,d), true) ->  let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																					let newL = map (percolate [firstNode;secondNode]) l in
																					Node (p, b, Examined, NotClosed, newL)
															| (Iff (c,d), false) -> let leftFirst = Leaf(c, false, NotExamined, NotClosed) in
																					let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																					let rightFirst = Leaf(c, true, NotExamined, NotClosed) in
																					let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in	
																					let newL = map (percolate [leftSecond;rightSecond]) l in
																					Node (p, b, Examined, NotClosed, newL)	
															| (Iff (c,d), true) -> 	let leftFirst = Leaf(c, true, NotExamined, NotClosed) in
																					let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																					let rightFirst = Leaf(c, false, NotExamined, NotClosed) in
																					let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in
																					let newL = map (percolate [leftSecond;rightSecond]) l in
																					Node (p, b, Examined, NotClosed, newL)	
																				)
;;	

exception Not_Possible;;
let replace l pos fn xs = List.mapi (fun i x -> if i = pos then (fn x xs) else x) l;;
let rec step_develop a thisPath = match thisPath with
| [] -> (develop_specific_node a)
| x::xs -> (match a with
			| Leaf(p,b,examStatus,closedStatus) -> raise Not_Possible
			| Node(p,b,examStatus,closedStatus,childr) -> let newL = (replace childr x step_develop xs) in
															Node(p,b,examStatus,closedStatus,newL)
		) 
;;					
let rec contrad_path_fn rho a = match a with
| Leaf(p, b, examStatus, closedStatus) -> if closedStatus=Closed then a else 
											(match p with
											| L (c) -> (try let ans = find (fun rhoele -> match rhoele with
																							| (d,e) -> d=c) rho in
															(match ans with
															| (f,g) -> if g=b then a else Leaf(p,b,examStatus,Closed))
														with Not_found -> a)
											| _ -> a
										)
| Node(p, b, examStatus, closedStatus, childr) -> if closedStatus=Closed then a else 
													(match p with
													| L(c) -> (try let ans = find (fun rhoele -> (match rhoele with
																									| (d,e) -> d=c)) rho in
																				(match ans with
																				| (f,g) -> if g=b then (
																					Node(p,b,examStatus,closedStatus, map (contrad_path_fn rho) childr)
																				) else Node(p,b,examStatus,Closed,childr))
																			with Not_found -> (Node(p,b,examStatus,closedStatus, map (contrad_path_fn ((c,b)::rho)) childr)))
													| _ -> Node(p,b,examStatus,closedStatus, map (contrad_path_fn rho) childr))						
;;

let contrad_path a = contrad_path_fn [] a;;

let rec find_assignments_fn thisPath allPath a = match a with
| Leaf(p,b,examStatus,closedStatus) -> if closedStatus=Closed then allPath else 
										(match p with
										| L (c) -> (try let ans = find (fun rhoele -> match rhoele with
																							| (d,e) -> d=c) thisPath in
														(match ans with
														| (f,g) -> if g=b then (thisPath::allPath )else allPath)
													with Not_found -> ((c,b)::thisPath)::allPath)
										| _ -> if (length thisPath > 0) then (thisPath::allPath) else allPath
										)
| Node(p,b,examStatus,closedStatus, childr) -> if closedStatus=Closed then allPath else
										(match p with
										| L (c) -> (try let ans = find (fun rhoele -> match rhoele with
																							| (d,e) -> d=c) thisPath in
																	(match ans with
																	| (f,g) -> if g=b 
																					then fold_left (fun acc x -> find_assignments_fn thisPath acc x) allPath childr
																					else allPath
																	)
														with Not_found -> fold_left (fun acc x -> find_assignments_fn ((c,b)::thisPath) acc x) allPath childr)
										| _ -> fold_left (fun acc x -> find_assignments_fn thisPath acc x) allPath childr
										)
;;

let find_assignments_after_contrad a = find_assignments_fn [] [] a;;



let rec fully_develop a = try let selected_node = select_node a in
								(match selected_node with
								| (b,c) -> (fully_develop (step_develop a c)))
							with ExaminedOrClosed -> a
;;

let find_assignments rootNode = let developedNode = fully_develop rootNode in
								let closedNode = contrad_path developedNode in
								let assignments = find_assignments_after_contrad closedNode in
								assignments;;
(* exception NotClosed;; *)
let rec isTotallyClosed closedNode = match closedNode with
| Leaf(p,b,examStatus,closedStatus) -> (match closedStatus with
										| Closed -> true
										| NotClosed -> false)
| Node(p,b,examStatus,closedStatus,childr) -> (match closedStatus with
											| Closed -> true
											| NotClosed -> (fold_left (fun acc x -> acc && (isTotallyClosed x)) true childr) )
;;
let check_tautology a = let rootNode = Leaf(a,false,NotExamined,NotClosed) in
						let developedNode = fully_develop rootNode in
						let closedNode = contrad_path developedNode in
						let assignments = find_assignments_after_contrad closedNode in
						(match assignments with
						| [] -> if ((isTotallyClosed closedNode)=true) then (true, closedNode, assignments) else (false, closedNode, assignments)
						| _ -> (false, closedNode, assignments))
;;
let check_contradiction a = let rootNode = Leaf(a,true,NotExamined,NotClosed) in
						let developedNode = fully_develop rootNode in
						let closedNode = contrad_path developedNode in
						let assignments = find_assignments_after_contrad closedNode in
						(match assignments with
						| [] -> if ((isTotallyClosed closedNode)=true) then (true, closedNode, assignments) else (false, closedNode, assignments)
						| _ -> (false, closedNode, assignments))
;;

let rec listMatcher e1 e2 fn = match (e1,e2) with
							| ([],[]) -> true
							| (x1::xs1, x2::xs2) -> if ((fn x1 x2)=true) then (listMatcher xs1 xs2 fn) else false
							| _ -> false
;;

let rec checkIfTableauSame a b = match (a,b) with
| (Leaf(c1,d1,e1,f1), Leaf(c2,d2,e2,f2)) -> ((c1=c2) && (d1=d2) && (e1=e2) && (f1=f2))
| (Node(c1,d1,e1,f1,g1), Node(c2,d2,e2,f2,g2)) -> if ((c1=c2) && (d1=d2) && (e1=e2) && (f1=f2)) then (listMatcher g1 g2 checkIfTableauSame) else false
| _ -> false
;;

let valid_tableau a = let fully_develop_given = fully_develop a in
						let fully_develop_root = (match a with
												| Leaf(p, b, examStatus, closedStatus) -> (fully_develop (Leaf(p,b, NotExamined, NotClosed)))
												| Node(p, b, examStatus, closedStatus, childr) -> (fully_develop (Leaf(p,b,NotExamined, NotClosed)))) in 
						(checkIfTableauSame fully_develop_given fully_develop_root)
;;








(* Examples *)
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

