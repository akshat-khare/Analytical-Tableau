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



let rec isUnExaminedInList l = match l with
| [] -> raise ExaminedOrClosed
| x::xs -> (match x with
			 Leaf(p,b,examStatus,closedStatus) -> if examStatus=NotExamined then x else (isUnExaminedInList xs)
			| Node(p,b, examStatus, closedStatus, childr) -> if examStatus=NotExamined then x else (isUnExaminedInList xs))
;;

let rec nodeIteratorExam childr l selectNodeFn= match childr with
| [] -> raise ExaminedOrClosed
| x::xs -> try selectNodeFn x l with ExaminedOrClosed -> nodeIteratorExam xs l selectNodeFn
;;
(* The following function is selecting unexamined node from bottom *)
let rec select_node_fn a l= match a with
| Leaf (p, b, examStatus, closedStatus) -> (match closedStatus with
											| Closed -> raise ExaminedOrClosed
											| NotClosed -> let newL = a::l in
															isUnExaminedInList newL
										)
| Node (p, b, examStatus, closedStatus, childr)  -> (match closedStatus with
												| Closed -> raise ExaminedOrClosed
												| NotClosed -> let newL = a::l in
																nodeIteratorExam childr newL select_node_fn
										)
;;

let select_node a = select_node_fn a [];;

let rec step_develop a = match a with
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
																	Node (p, b, Examined, NotClosed, [step_develop secondNode])
											| (Or(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, NotClosed, [step_develop secondNode])
											| (Impl(c, d), false) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, NotClosed, [step_develop secondNode])
											| (And (c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, false, NotExamined, NotClosed) in
																	Node (p, b, Examined, NotClosed, [(step_develop secondNode);(step_develop firstNode)])
											| (Or (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																	Node (p, b, Examined, NotClosed, [(step_develop secondNode);(step_develop firstNode)])
											| (Impl(c,d), true) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																	Node (p, b, Examined, NotClosed, [(step_develop secondNode);(step_develop firstNode)])
											| (Iff(c,d), false) -> let leftFirst = Leaf(c, false, NotExamined, NotClosed) in
																	let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																	let rightFirst = Leaf(c, true, NotExamined, NotClosed) in
																	let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in
																	Node (p, b, Examined, NotClosed, [(step_develop leftSecond);(step_develop rightSecond)]) 
											| (Iff(c,d), true) -> let leftFirst = Leaf(c, true, NotExamined, NotClosed) in
																	let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																	let rightFirst = Leaf(c, false, NotExamined, NotClosed) in
																	let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in
																	Node (p, b, Examined, NotClosed, [(step_develop leftSecond);(step_develop rightSecond)]) 
																)
| Node (p, b, examStatus, closedStatus, l) -> if closedStatus=Closed then Node(p,b,Examined,Closed, l) else
											(match examStatus with
											| Examined -> Node(p, b, examStatus, NotClosed, map step_develop l)
											| NotExamined -> match (p,b) with
															| (T, true) -> Node(p,b,Examined, NotClosed, map step_develop l)
															| (F, false) -> Node(p,b, Examined, NotClosed, map step_develop l)
															| (T, false) -> Node(p,b, Examined, Closed,l)
															| (F, true) -> Node(p,b, Examined, Closed, l)
															| (L(c), _) -> Node(p, b, Examined, NotClosed, map step_develop l)
															| (Not c, d) -> let negationD = not d in
																			let child = Leaf(c, negationD, NotExamined, NotClosed) in
																			let newL = map (percolate [child]) l in
																			Node(p, b, Examined, NotClosed, newL)
															| (And (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Node(d, true, NotExamined, NotClosed, [firstNode]) in
																					let newL = map (percolate [secondNode]) l in
																					Node(p, b, Examined, NotClosed, map step_develop newL)
															| (Or(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																					let newL = map (percolate [secondNode]) l in
																					Node(p, b, Examined, NotClosed, map step_develop newL)
															| (Impl(c,d), false) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																					let newL = map (percolate [secondNode]) l in
																					Node(p, b, Examined, NotClosed, map step_develop newL)
															| (And(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, false, NotExamined, NotClosed) in
																					let newL = map (percolate [firstNode;secondNode]) l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)
															| (Or(c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																					let newL = map (percolate [firstNode;secondNode]) l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)
															| (Impl (c,d), true) ->  let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																					let newL = map (percolate [firstNode;secondNode]) l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)
															| (Iff (c,d), false) -> let leftFirst = Leaf(c, false, NotExamined, NotClosed) in
																					let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																					let rightFirst = Leaf(c, true, NotExamined, NotClosed) in
																					let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in	
																					let newL = map (percolate [leftSecond;rightSecond]) l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)	
															| (Iff (c,d), true) -> 	let leftFirst = Leaf(c, true, NotExamined, NotClosed) in
																					let leftSecond = Node(d, true, NotExamined, NotClosed, [leftFirst]) in
																					let rightFirst = Leaf(c, false, NotExamined, NotClosed) in
																					let rightSecond = Node(d, false, NotExamined, NotClosed, [rightFirst]) in
																					let newL = map (percolate [leftSecond;rightSecond]) l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)	
																				)
;;			
(* exception Closed;; *)
let rec contrad_path_fn rho a = match a with
| Leaf(p, b, examStatus, closedStatus) -> if closedStatus=Closed then a else 
											(match p with
											| L (c) -> try let ans = find (fun rhoele -> match rhoele with
																		| (d,e) -> d=c) rho in
														(match ans with
														| (f,g) -> if g=b then a else Leaf(p,b,examStatus,Closed))
													with Not_found -> a
											| _ -> a)
| Node(p, b, examStatus, closedStatus, childr) -> if closedStatus=Closed then a else 
													(match p with
													| L(c) -> try let ans = find (fun rhoele -> match rhoele with
																					| (d,e) -> d=c) rho in
																	(match ans with
																	| (f,g) -> if g=b then (
																		Node(p,b,examStatus,closedStatus, map (contrad_path_fn rho) childr)
																	) else Node(p,b,examStatus,Closed,childr))
																with Not_found -> Node(p,b,examStatus,closedStatus, map (contrad_path_fn ((c,b)::rho)) childr)
													| _ -> Node(p,b,examStatus,closedStatus, map (contrad_path_fn rho) childr))						
;;



