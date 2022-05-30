module pop
open states

// -------- Auxiliary definitions -----------------

pred reorder_condition[r_old : request, r_new : request]{
  r_old not in dmb_sy
  r_new not in dmb_sy
  (r_old + r_new) in (memory_access - thread_id.read_response) => r_old.addr != r_new.addr
}

pred order_constraint_update_condition_accept_request[r_old : request, r_new : request]{
	not reorder_condition[r_old, r_new]
	r_new.thread in r_old.propagated_to
}

pred order_constraint_update_condition_propagate[r : request, r_new : request, t : thread_id] {
	not reorder_condition[r, r_new]
	//not already ordered
	r_new not in r.order_constraints_po
	r not in r_new.order_constraints_po
	//propagated constraints
	t in r_new.propagated_to
	r.thread not in r_new.propagated_to
}

pred propagate_order_constraints[r : request, t : thread_id]{
	all s : request - r | s.order_constraints' = s.order_constraints
	all r_new : request |
 		order_constraint_update_condition_propagate[r,r_new,t]
		or (r_new in r.order_constraints) <=>
			r_new in r.order_constraints'
}

pred accept_request_order_constraints[r : request]{
	all s : request - r | s.order_constraints' = s.order_constraints
	all r_new : request |
 		order_constraint_update_condition_accept_request[r,r_new]
	   or (r_new in r.order_constraints) <=>
			r_new in r.order_constraints'
}

pred po[r : request, s : request]{
	r.thread = s.thread
   (s not in system_state.seen) until (r in system_state.seen)
}

// ----------------- Execution ---------------------
pred init{
	no request.propagated_to
	no system_state.seen
	no read_response
	no reads_from
	no request.order_constraints
	no system_state.removed
}

pred propagate[r : request, t : thread_id]{
	//preconditions
	no (t  & r.propagated_to) // r -> t is new
   r in system_state.seen // request has been seen
	// every request that is before r in order_constraints has already been propagated to thread t
	all prev_req : r.order_constraints_po |  t in prev_req.propagated_to

	// changes
	propagated_to' = propagated_to + (r -> t)
	propagate_order_constraints[r,t]

	//rest unchanged
	seen' = seen
	read_response' = read_response
	reads_from' = reads_from
	removed' = removed
}

pred accept_request[r : request]{
	//preconditions
	not r in system_state.seen

	// changes
	system_state.seen' = system_state.seen + r
	propagated_to' = propagated_to + r-> r.thread
	accept_request_order_constraints[r]

	//rest unchanged
	read_response' = read_response
	reads_from' = reads_from
	removed' = removed
}

pred respond_read[r : read, w : write, t: thread_id]{
   //preconditions
	r not in thread_id.read_response // r unsatisfied yet
	r in system_state.seen
	w in system_state.seen
	r.from = w.to // same address
	r.propagated_to = w.propagated_to // propagated to exact same threads
   w in r.order_constraints_po // w before r
	// requests order_constraints_po-between w and r is fully prop and to a diff. addr.
	all req : (r.order_constraints_po - w.order_constraints_po - r) |
		fully_propagated[req] and addr[req] != r.from

	// actions
   read_response' = read_response + (t -> r)
	reads_from' = reads_from + (r -> w)
	system_state.removed' = system_state.removed + r

	//rest unchanged
	seen' = seen
	propagated_to' = propagated_to
	order_constraints' = order_constraints
}


pred trivial_transition{
	propagated_to' = propagated_to
	seen' = seen
	read_response' = read_response
	reads_from' = reads_from
	order_constraints' = order_constraints
	removed' = removed
}

pred propagate_step {some r : request, t : thread_id | propagate[r,t]}
pred accept_request_step {some r : request | accept_request[r]}
pred respond_read_step {some r : read, w : write, t : thread_id | respond_read[r,w,t]}

pred step {
	propagate_step
 	iff not // xor
	accept_request_step
	iff not
	respond_read_step
}

fact transitions {
	init and step until (always trivial_transition)
}

pred finished_execution {
	system_state.seen = request
	all r : request | fully_propagated[r]
	//all read requests have been responded to:
	read in thread_id.read_response
}


// ------------- Assertions --------------------
assert accept_request_always_empty_propagated_list{
 	all r : request| accept_request[r] => no r.propagated_to
}

assert propagate_monotone {
	always propagated_to in propagated_to'
}
assert order_constraints_always_induce_po {always order_constraints_induce_po}

assert one_request_at_a_time {
	all r : request, s : request |
		(r in (system_state.seen' - system_state.seen)) and
   	(s in (system_state.seen' - system_state.seen)) =>
			r = s
}

check propagate_monotone for 4 but 10 steps
check accept_request_always_empty_propagated_list for 4 but 10 steps
check order_constraints_always_induce_po for 4 but 10 steps
check one_request_at_a_time for 4 but 10 steps

//pred some_accept_req {eventually (some r : request, t : thread_id | accept_request[r,t])}

run {#read = 1 and #write = 1 and #thread_id = 2} for 4..10 steps
run {#request = 2 and eventually finished_execution } for 4 but 5..10 steps
run {#propagated_to = 0 until #propagated_to = 1 until #propagated_to = 4} for 4 but 10 steps
run {eventually (some r : request, s : request | reorder_condition[r,s])} for 5..10 steps
