module pop
open util

sig thread_id {}

sig request {
	order_constraints : set request,
	propagated_to : set thread_id,
  }

sig system_state {
	//threads : set thread_id,
	seen : set request,
} {
	partial_order[seen, refl_transitive_closure[restriction[seen,iden].order_constraints]]
}

fact order_constraints_minimal {
	all r : request | #(r.~order_constraints) <= 1
   irreflexive[order_constraints]
}
fact all_requests_seen_somewhere { all r : request | one s : system_state | r in s.seen}

pred three_requests { #request = 3
		#system_state = 1
 	//some r : request, s : request, t : request | r != s and s != t and s in r.order_constraints and r in r.order_constraints and t in r.order_constraints
	//and t.order_constraints = t and t in s.order_constraints and s in s.order_constraints

}
pred emptypred {}
run three_requests for 4 but 1 system_state
run emptypred for 4 but 1 system_state
