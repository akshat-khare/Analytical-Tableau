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
| Node (p,b,examStatus,closedStatus,l) -> Node(p,b,examStatus,closedStatus, map (percolate a) l );;


let rec step_develop a = match a with
| Leaf (p, b, examStatus, closedStatus) -> if (examStatus=Examined || closedStatus=NotClosed) then a else match (p,b) with
											| (T, true) -> Leaf (p,b, Examined,closedStatus)
											| (F, false) -> Leaf (p, b, Examined, closedStatus)
											| (T, false) -> Leaf (p, b, Examined, Closed)
											| (F, true) -> Leaf (p, b, Examined, Closed)
											| (L (c), _) -> Leaf (p, b, Examined, closedStatus)
											| (Not c, d) -> let negationD = not d in
															let child = Leaf(c, negationD, NotExamined, NotClosed) in
															Node (p, b, Examined, closedStatus, [child])
											| (And (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Node(d, true, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, closedStatus, [step_develop secondNode])
											| (Or(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, closedStatus, [step_develop secondNode])
											| (Impl(c, d), false) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																	Node (p, b, Examined, closedStatus, [step_develop secondNode])
											| (And (c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, false, NotExamined, NotClosed) in
																	Node (p, b, Examined, closedStatus, [(step_develop secondNode);(step_develop firstNode)])
											| (Or (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																	Node (p, b, Examined, closedStatus, [(step_develop secondNode);(step_develop firstNode)])
											| (Impl(c,d), true) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																	let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																	Node (p, b, Examined, closedStatus, [(step_develop secondNode);(step_develop firstNode)])

| Node (p, b, examStatus, closedStatus, l) -> if closedStatus=Closed then Node(p,b,Examined,Closed) else
											match examStatus with
											| Examined -> Node(p, b, examStatus, NotClosed, map step_develop l)
											| NotExamined -> match (p,b) with
															| (T, true) -> Node(p,b,Examined, NotClosed, map step_develop l)
															| (F, false) -> Node(p,b, Examined, NotClosed, map step_develop l)
															| (T, false) -> Node(p,b, Examined, Closed,l)
															| (F, true) -> Node(p,b, Examined, Closed, l)
															| (L(c), _) -> Node(p, b, Examined, NotClosed, map step_develop l)
															| (Not c, d) -> let negationD = not d in
																			let child = Leaf(c, negationD, NotExamined, NotClosed) in
																			let newL = percolate [child] l in
																			Node(p, b, Examined, NotClosed, newL)
															| (And (c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Node(d, true, NotExamined, NotClosed, [firstNode]) in
																					let newL = percolate [secondNode] l in
																					Node(p, b, Examined, NotClosed, map step_develop newL)
															| (Or(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																					let newL = percolate [secondNode] l in
																					Node(p, b, Examined, NotClosed, map step_develop newL)
															| (Impl(c,d), false) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Node(d, false, NotExamined, NotClosed, [firstNode]) in
																					let newL = percolate [secondNode] l in
																					Node(p, b, Examined, NotClosed, map step_develop newL)
															| (And(c,d), false) -> let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, false, NotExamined, NotClosed) in
																					let newL = percolate [firstNode;secondNode] l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)
															| (Or(c,d), true) -> let firstNode = Leaf(c, true, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																					let newL = percolate [firstNode;secondNode] l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)
															| (Impl (c,d), true) ->  let firstNode = Leaf(c, false, NotExamined, NotClosed) in
																					let secondNode = Leaf(d, true, NotExamined, NotClosed) in
																					let newL = percolate [firstNode;secondNode] l in
																					Node (p, b, Examined, NotClosed, map step_develop newL)
;;										




