module tso
open states

sig mov_r extends read {}
sig mov_w extends write {}
sig fence extends barrier {}


pred reorder_condition[r_old : request, r_new : request]{
  	r_old not in fence
  	r_new not in fence

	//per-loc sc
  	(r_old + r_new) in (memory_access - thread_id.read_response) => r_old.addr != r_new.addr

	//tso ppo: only store -> load can be reordered
	r_old.thread = r_new.thread => r_old in write and r_new in read
}

pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
	r.propagated_to = thread_id
}

fact unscoped {#scope = 1}
