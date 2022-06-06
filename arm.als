module arm
open states

sig ld extends read {}
sig st extends write {}
sig dmb_sy extends barrier {}


pred reorder_condition[r_old : request, r_new : request]{
  	r_old not in dmb_sy
  	r_new not in dmb_sy
  	(r_old + r_new) in (memory_access - thread_id.read_response) => r_old.addr != r_new.addr
}

pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
}

fact unscoped {#scope = 1}
