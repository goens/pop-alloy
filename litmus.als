module litmus
open pop

pred MP {
   #thread_id = 2
   #read = 2
   #write = 4
   some t1 : thread_id, t2 : thread_id, r1 : read, r2 : read,
   w01 : write, w02 : write, w1 : write, w2 : write |
      // program
      w1.thread = t1 and w2.thread = t1
      and r1.thread = t2 and r2.thread = t2
	   and po[w01,w02] and po[w02,w1] //init
      and po[r1,r2] and po[w1,w2]
      and t1 != t2
      and w1.addr = r2.addr
      and w2.addr = r1.addr
      and w1.addr != w2.addr
      and w01.addr = w1.addr
      and w02.addr = w2.addr
      // result
      and eventually system_state.removed = read
      and eventually r1.reads_from = w2
      and always (not r2.reads_from = w1)
}


run MP for exactly 6 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 1 scope, 20 steps

pred MP_fence {
   #thread_id = 2
   and #read = 2
   and #write = 4
   and #barrier = 2
   and some t1 : thread_id, t2 : thread_id, r1 : read, r2 : read,
   w01 : write, w02 : write, w1 : write, w2 : write,
 	f1 : barrier, f2 : barrier |
      //program
      w1.thread = t1 and w2.thread = t1
      and r1.thread = t2 and r2.thread = t2
	   and po[w01,w02] and po[w02,w1] //init
      and po[w1,f1] and po[f1,w2]
      and po[r1,f2] and po[f2,r2]
      and t1 != t2
      and w1.addr = r2.addr
      and w2.addr = r1.addr
      and w1.addr != w2.addr
	   //result
      and eventually system_state.removed = read
}

assert MP_fence_disallowed{
	MP_fence => always some r1 : read, r2 : read,
	w1 : write, w2 : write |
		(po[r1,r2] and r1.reads_from = w2) => r2.reads_from = w1
}

run MP_fence for exactly 8 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 1 scope, 20 steps
check MP_fence_disallowed for exactly 8 request, exactly 2 address, exactly 2 thread_id, 1 system_state, 1 scope, 20 steps

pred IRIW {
   # pop/thread_id = 4
   # pop/read = 4
   # pop/write = 2
   some t1 : pop/thread_id, t2 : pop/thread_id, t3 : pop/thread_id, t4 : pop/thread_id,
      w1 : pop/write, w2 : pop/write, r1 : pop/read, r2 : pop/read,
      r3 : pop/read, r4 : pop/read |
        w1.thread = t1
        and r1.thread = t2 and po[r1,r2]
        and w1.thread = t3
        and r2.thread = t4 and po[r2,r3]
        and r1.addr = w1.addr and r2.addr = w2.addr
        and r3.addr = w2.addr and r4.addr = w1.addr
        and w1.addr != w2.addr
        and t1 != t2 and t1 != t3 and t1 != t4
        and t2 != t3 and t2 != t4 and t3 != t4
        //and eventually w1 in r1.reads_from and w2 in r1.reads_from
}

run IRIW for exactly 6 request, exactly 2 address, exactly 4 thread_id, 1 system_state, 1 scope, 30 steps
// pred IRIW_fences {
//    # pop/thread_id = 4
//    # pop/read = 4
//    # pop/write = 2
//    # pop/Fence = 2
//    all e : Event | e.scope = System
//    some t0 : pop/thread_id, t1 : pop/thread_id, t2 : pop/thread_id, t3 : pop/thread_id,
//    w0 : pop/write, w1 : pop/write, r0 : pop/read, r1 : pop/read,
//    r2 : pop/read, r3 : pop/read, f0 : pop/Fence, f1 : pop/Fence |
//       t0.start = w0 and
//    t1.start = r0 and r0.po = f0 and f0.po = r1 and
//    t2.start = w1 and
//    t3.start = r2 and r2.po = f1 and f1.po = r3 and
//    r0.address = w0.address and r1.address = w1.address and
//    r2.address = w1.address and r3.address = w0.address and
//    w0.address != w1.address and
//    w0.rf = r0 and w1.rf = r2
// }
