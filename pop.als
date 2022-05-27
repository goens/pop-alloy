module pop
open states

// fact init{
// 	no request.propagated_to
// }

pred propagate[r : request, t : thread_id]{
	no (t  & r.propagated_to)
	propagated_to' = propagated_to + (r -> t)
	all s : system_state | s.seen' = s.seen
}

//pred accept_request[r : request]

pred trivial_transition{
	propagated_to' = propagated_to
	seen' = seen
}

pred step {
	(some r : request, t : thread_id | propagate[r,t] )
}

fact transitions {
	step until (always trivial_transition)
}

assert propagate_monotone {
	always propagated_to in propagated_to'
}
check propagate_monotone for 4 but 6 steps

run {} for 4 but  2..5 steps
run propagate for 4 but 3 steps
run {#propagated_to = 1; #propagated_to = 2} for 4 but exactly 2 steps
run some_not_fully_propagated for 4 but 5 steps
run {some t : thread_id, r : request | t in r.propagated_to} for 4 but 5 steps
