open litmus

run MP for exactly 6 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 3 scope, 20 steps
run MP_fence for exactly 8 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 1 scope, 20 steps
check MP_fence_disallowed for exactly 8 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 1 scope, 20 steps
run IRIW for exactly 8 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 5 scope, 30 steps
run IRIW_fence for exactly 10 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 5 scope, 30 steps
run SB for exactly 6 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 3 scope, 30 steps
