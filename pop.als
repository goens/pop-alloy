module pop
//open arm
//open ptx
//open tso
open compound

// -------- Auxiliary definitions -----------------

pred order_constraint_update_condition_accept_request[r_old : request, r_new : request]{
   not reorder_condition[r_old, r_new]
   r_new.thread in r_old.propagated_to
}

pred order_constraint_update_condition_propagate[r : request, r_new : request, t : thread_id] {
	arch_propagate_condition[r, r_new, t]
   not reorder_condition[r, r_new]
	some s : scope | {
		min_joint_scope[r.thread,r_new.thread,s]
      r_new not in s.order_constraints_po.r
      r not in s.order_constraints_po.r_new
   }
   //propagated constraints
   t in r_new.propagated_to
   r.thread not in r_new.propagated_to
}



pred propagate_order_constraints[r : request, t : thread_id]{
   all s : scope, r_new : request - r |
 		s.order_constraints.r_new' = s.order_constraints.r_new
   all r_new : request |
      order_constraint_update_condition_propagate[r,r_new,t]
	   or arch_order_constraints_update_propagate[r,r_new,t]
	or all s : scope |
		r_new in s.order_constraints.r <=> r_new in s.order_constraints.r'
}

pred accept_request_order_constraints[r : request]{
   all s : scope, r_b : request - r | s.order_constraints.r_b' = s.order_constraints.r_b
   all r_new : request |
      order_constraint_update_condition_accept_request[r,r_new]
	or all s : scope |
		r_new in s.order_constraints.r <=> r_new in s.order_constraints.r'
}

// ----------------- Execution ---------------------
pred init{
   no request.propagated_to
   no system_state.seen
   no read_response
   no reads_from
   no system_scope.order_constraints.request
   no system_state.removed
}

pred propagate[r : request, t : thread_id]{
   //preconditions
   no (t  & r.propagated_to) // r -> t is new
   r in system_state.seen // request has been seen
   // every request that is before r in order_constraints has already been propagated to thread t
   some s : scope| {
      min_joint_scope[r.thread,t,s]
		all prev_req : (s.order_constraints_po.r - r) |  t in prev_req.propagated_to
		}
	propagate_condition[r,t]

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
	some s : scope | {
   r.propagated_to = w.propagated_to // propagated to exact same threads
   w in s.order_constraints_po.r // w before r
   // requests order_constraints_po-between w and r is fully prop and to a diff. addr.
   all req : (s.order_constraints_po.r - s.order_constraints_po.w - r) |
      fully_propagated[req,s] and addr[req] != r.from
	}

   // actions
   read_response' = read_response + (t -> r)
   reads_from' = reads_from + (r -> w)
	remove_reads[r,system_state]

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
   all r : request | fully_propagated[r,system_scope]
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


assert order_constraints_subscope {order_constraints_respect_subscope}
// ----------------- Checks ---------------------

check propagate_monotone for 4 but 10 steps
check order_constraints_subscope for 4 but 10 steps
check accept_request_always_empty_propagated_list for 4 but 10 steps
check order_constraints_always_induce_po for 4 but 10 steps
check one_request_at_a_time for 4 but 10 steps

//pred some_accept_req {eventually (some r : request, t : thread_id | accept_request[r,t])}

run {#read = 1 and # write = 1 and #thread_id = 2 and eventually respond_read_step} for 4 but exactly 2 request
run {some r1 : request, r2 : request | po[r1,r2]}
run {#read = 4 and #write = 2 and #thread_id = 4} for 4 but 6 request, 4..10 steps
run {#request = 2 and eventually finished_execution } for 4 but 5..10 steps
run {#propagated_to = 0 until #propagated_to = 1 until #propagated_to = 4} for 4 but 10 steps
run {eventually (some r : request, s : request | reorder_condition[r,s])} for 5..10 steps
