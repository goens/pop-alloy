module tso
open states

sig mov_r extends read {}
sig mov_w extends write {}
sig mfence extends barrier {}


pred reorder_condition[r_old : request, r_new : request]{
  	r_old not in mfence
  	r_new not in mfence

	//per-loc sc
  	(r_old + r_new) in (memory_access - thread_id.read_response) => r_old.addr != r_new.addr

	//tso ppo: only store -> load can be reordered
	r_old.thread = r_new.thread => r_old in write and r_new in read
}


pred arch_propagate_condition[r : request, r_new : request, t : thread_id]{
}

pred arch_order_constraints_update_propagate[r : request, r_new : request, t : thread_id]{
}

pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
	// mco: expect fully propagated
	all r_old : system_scope.order_constraints.r - r |
 		fully_propagated[r_old,system_scope]
}

fact unscoped {scope = system_scope + thread_id}
