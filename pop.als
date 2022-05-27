module pop
open states

// fact init{
// 	no request.propagated_to
// }

pred propagate{
	some r : request, t : set thread_id{
	  no (t  & r.propagated_to)
	  propagated_to' = propagated_to + (r -> t)
	  all s : system_state | s.seen' = s.seen
	}
}

//pred accept_request[r : request]

pred trivial_transition{
	propagated_to' = propagated_to
	seen' = seen
}

pred step {
	propagate
}

fact transitions {
	step until (always trivial_transition)
}

assert propagate_monotone {
	always propagated_to in propagated_to'
}
check propagate_monotone for 4 but 6 steps

run {} for 4 but  2..5 steps
run {#propagated_to = 1; #propagated_to = 4} for 4 but exactly 2 steps
run some_not_fully_propagated for 4 but 5 steps
