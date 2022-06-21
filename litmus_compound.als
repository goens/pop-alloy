open pop
open litmus

pred IRIW_x86_reads {
 	IRIW
	pop/write in pop/st_release
	pop/read in pop/mov_r
}

pred IRIW_fence_x86_reads {
 	IRIW_fence
	pop/write in pop/st_release
	pop/read in pop/mov_r
}

pred IRIW_PTX_reads {
 	IRIW
	pop/write in pop/mov_w
	pop/read in pop/ld_acquire
}

pred IRIW_fence_PTX_reads {
 	IRIW_fence
	pop/write in  pop/mov_w
	pop/read in pop/ld_acquire
}

check {not IRIW_x86_reads} for exactly 8 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 5 scope, 25 steps
// check not IRIW_fence_x86_reads for exactly 10 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 5 scope, 25 steps
run IRIW_PTX_reads for exactly 8 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 5 scope, 25 steps
check {not IRIW_fence_PTX_reads} for exactly 10 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 5 scope, 25 steps
