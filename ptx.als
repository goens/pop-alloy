module ptx
open states

sig ld_weak extends read {}
abstract sig ld_strong extends read { sco : scope }
sig ld_relaxed extends ld_strong {}
sig ld_acquire extends ld_strong {}

sig st_weak extends write {}
abstract sig st_strong extends write { sco : scope }
sig st_relaxed extends st_strong {}
sig st_release extends st_strong {}

sig fence_sc extends barrier { sco : scope}
sig fence_acq_rel extends barrier { sco : scope }

// ---------- Auxiliary Definitions -------------

pred strong[r : request]{
	r in ld_strong + st_strong + barrier
}

pred scope_inclusive[r1 : request, r2 : request]{
	r1.thread in r2.sco.subscopes
	r2.thread in r1.sco.subscopes
}

// ------------ Pop Definitions ---------------

pred reorder_condition[r_old : request, r_new : request]{
  not scope_inclusive[r_old,r_new] or
  {
     // fence rel_acq : kindof like dmb_ld.
     // Reorder (w/ memory events): not allow if same thread, allowed otherwise
    	r_old + r_new in fence_acq_rel  => r_ord.thread != r_new.thread
    	r_old not in fence_sc
    	r_new not in fence_sc
    	(r_old + r_new) in (memory_access - thread_id.read_response)
  	  => r_old.addr != r_new.addr
  	r_new in ld_acquire and r_old in st_release => r_new.addr != r_old.addr
  	r_new in ld_acquire => r_new.thread != r_old.thread
  	r_new not in st_release
  }
}
pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
}

pred arch_propagate_condition[r : request, r_new : request, t : thread_id]{
}

pred arch_order_constraints_update_propagate[r : request, r_new : request, t : thread_id]{
}

pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
}
