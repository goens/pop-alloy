// TODO: look at figure 6

module compound
open states


// PTX
sig ld_weak extends read {}
abstract sig ld_strong extends read { lsco : scope }
sig ld_relaxed extends ld_strong {}
sig ld_acquire extends ld_strong {}

sig st_weak extends write {}
abstract sig st_strong extends write { wsco : scope }
sig st_relaxed extends st_strong {}
sig st_release extends st_strong {}

sig fence_sc extends barrier { scsco : scope}
sig fence_acq_rel extends barrier { rasco : scope }


// x86

sig mov_r extends ld_strong {}
sig mov_w extends st_strong {}
sig mfence extends barrier {}

// ---------- Auxiliary Definitions -------------

fun x86_request : request { mov_r + mov_w + mfence }
fun ptx_request : request { request - x86_request }

fun sco : request -> scope {
  	lsco + wsco + scsco + rasco +
	(st_weak -> system_scope) +
	(ld_weak -> system_scope) +
	(x86_request -> system_scope)
}

pred strong[r : request]{
	r in ld_strong + st_strong + barrier
}

pred scope_inclusive[r1 : request, r2 : request]{
	r1.thread in r2.sco.subscopes
	r2.thread in r1.sco.subscopes
}

// ------------ Pop Definitions ---------------

pred reorder_condition[r_old : request, r_new : request]{
  // we do the mapping manually as alloy won't allow us to convert between sigs

  // x86
	r_new in x86_request => {
	r_old.thread = r_new.thread => r_old in write and r_new in read
  	r_old not in barrier
  	r_new not in barrier
  	(r_old + r_new) in (memory_access - thread_id.read_response) => r_old.addr != r_new.addr
	r_old.thread = r_new.thread => r_old in write and r_new in read
  }

  // PTX
  r_new in ptx_request => {
    not scope_inclusive[r_old,r_new] or
    {
      	r_old + r_new in fence_acq_rel  => r_old.thread != r_new.thread
      	r_old not in fence_sc + mfence
      	r_new not in fence_sc + mfence
      	(r_old + r_new) in (memory_access - thread_id.read_response)
    	  => r_old.addr != r_new.addr
    	r_new in (ld_acquire + mov_r) and r_old in (st_release + mov_r) => r_new.addr != r_old.addr
    	r_new in (ld_acquire + mov_r) => r_new.thread != r_old.thread
    	r_new not in (st_release + mov_w)
    }
  }
}

pred remove_reads[r : request , s : system_state]{
	system_state.removed' = system_state.removed + r
}

pred propagate_condition[r : request,t : thread_id]{
	all r_old : x86_request & system_scope.order_constraints.r - r |
 		fully_propagated[r_old,system_scope]

}

pred arch_propagate_condition[r : request, r_new : request, t : thread_id]{
}

pred arch_order_constraints_update_propagate[r : request, r_new : request, t : thread_id]{
}

fact no_thread_mixing{
	all r1, r2: request | po[r1,r2] => (r1 + r2 in x86_request) or (r1 + r2 in ptx_request)
}
