module states
open util

sig thread_id {}

sig request {
	order_constraints : set request,
	var propagated_to : set thread_id,
  }

fun order_constraints_po[request_set : set request] : request_set -> request_set {
	refl_transitive_closure[restriction[request_set,iden].order_constraints]
}

sig system_state {
	var seen : set request,
} {
	always partial_order[seen, order_constraints_po[seen]]
}
//  -------- Constraints on signatures -----------------------------

fact order_constraints_minimal {
	all r : request | #(r.~order_constraints) <= 1
   irreflexive[order_constraints]
}

fact all_requests_seen_somewhere { all r : request | eventually r in system_state.seen}

//   ------- Auxiliary definitions for storage subsystem ----------

pred fully_propagated[s : system_state, r : request]{
	// for all requests before r in the (reflexive-transitive closure of) order-constraints order:
 	all req : r.(order_constraints_po[s.seen])
	// the request has been propagated to all threads (the set thread_id represents is all threads)
	| req.propagated_to = thread_id
}

//   ------- Sanity Check -----------

pred three_requests { #request = 3
	#system_state = 1

}
pred some_not_fully_propagated{
	some r : request, s : system_state | ! fully_propagated[s,r]
}

run fully_propagated for 4 but 1 system_state
run some_not_fully_propagated for 4 but 1 system_state

pred emptypred {}
run three_requests for 4 but 1 system_state
run emptypred for 4 but 1 system_state
