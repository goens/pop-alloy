module states
open util

sig thread_id {
	var read_response : set read
}

abstract sig request {
	//TODO: might need to make order_constraints var
	//(see propagate request to another thread, Action 2)
	order_constraints : set request,
	var propagated_to : set thread_id,
  }

sig address {}

sig write extends request { to : one address }
// TODO: sig write_exclusive extends write { }
sig read extends request { from : one address, var reads_from : lone write}
sig barrier extends request {}
//sig read_response extends request {}
// sig exclusive_write extends request {}

fun order_constraints_po : request -> request {
	refl_transitive_closure[id[request].order_constraints]
}

sig system_state {
	var seen : set request,
}
//  -------- Constraints on signatures -----------------------------

fact order_constraints_induce_po {
	partial_order[request, order_constraints_po]
}

fact order_constraints_minimal {
	// request have at most one predecessor in order-constraints
	all r : request | #(r.~order_constraints) <= 1
   irreflexive[order_constraints]
}

fact all_requests_seen_somewhere { all r : request | eventually r in system_state.seen}

fact only_seen_propagated { no (request - system_state.seen).propagated_to }

fact one_system_state {always #system_state = 1}
//   ------- Auxiliary definitions for storage subsystem ----------

pred fully_propagated[r : request]{
	// for all requests before r in the (reflexive-transitive closure of) order-constraints order:
 	all req : r.(order_constraints_po)
	// the request has been propagated to all threads (the set thread_id represents is all threads)
	| req.propagated_to = thread_id
}

fun addr[r : request] : address {
	r.(to + from)
}

//   ------- Sanity Check -----------

pred three_requests { #request = 3
	#system_state = 1

}
pred some_not_fully_propagated{
	some r : request| ! fully_propagated[r]
}

run fully_propagated for 4 but 1 system_state
run some_not_fully_propagated for 4 but 1 system_state

pred emptypred {}
run three_requests for 4 but 1 system_state
run emptypred for 4 but 1 system_state
