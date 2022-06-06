module ptx
open states

sig ld_weak extends read {}
abstract sig ld_strong extends read { sco : scope }
sig ld_relaxed extends ld_strong {}
sig ld_acquire extends ld_strong {}

sig st_weak extends write {}
abstract sig st_strong extends write { sco : scope }
sig st_relaed extends st_strong {}
sig st_release extends st_strong {}

sig fence_sc extends barrier { sco : scope}
sig fence_acq_rel extends barrier { sco : scope }

// ---------- Auxiliary Definitions -------------

pred strong[r : request]{
	r in ld_strong + st_strong
}

pred scope_inclusive[r1 : request, r2 : request]{
	r1.sco in r2.sco.subscopes
	r2.sco in r1.sco.subscopes
}

// ------------ Pop Definitions ---------------

pred reorder_condition[r_old : request, r_new : request]{
  	r_old not in barrier
  	r_new not in barrier
  	(r_old + r_new) in (memory_access - thread_id.read_response)
	  => r_old.addr != r_new.addr
}

pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
}
