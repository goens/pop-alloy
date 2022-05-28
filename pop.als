module pop
open states

pred init{
	no request.propagated_to
	//no system_state.seen
}

pred propagate[r : request, t : thread_id]{
	//preconditions
	no (t  & r.propagated_to) // r -> t is new
   r in system_state.seen // request has been seen

	// changes
	propagated_to' = propagated_to + (r -> t)
	all s : system_state | s.seen' = s.seen
}

pred accept_request[r : request, t : thread_id]{
	//preconditions
	not r in system_state.seen

	// changes
	system_state.seen' = system_state.seen + r
	propagated_to' = propagated_to + r->t

}

assert accept_request_always_empty_propagated_list{
 all r : request, t : thread_id | accept_request[r,t] => no r.propagated_to
}

pred trivial_transition{
	propagated_to' = propagated_to
	seen' = seen
}

pred step {
	(some r : request, t : thread_id | propagate[r,t])
 	iff not // xor
	(some r : request, t : thread_id | accept_request[r,t])
}

pred finished_execution {
	system_state.seen = request
	all r : request | fully_propagated[r]
}

fact transitions {
	init and step until (always trivial_transition)
}

assert propagate_monotone {
	always propagated_to in propagated_to'
}
check propagate_monotone for 4 but 6 steps
check accept_request_always_empty_propagated_list for 4 but 6 steps

pred some_accept_req {eventually (some r : request, t : thread_id | accept_request[r,t])}

run {#request = 2 and #thread_id = 2 } for 4..10 steps
run {} for 4 but  exactly 8 steps
run {#propagated_to = 0 until #propagated_to = 1 until #propagated_to = 4} for 4 but 10 steps
run some_not_fully_propagated for 4 but 5 steps
