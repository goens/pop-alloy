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

pred IRIW {
   # pop/thread_id = 4
   # pop/read = 4
   # pop/write = 4
   some t1 : pop/thread_id, t2 : pop/thread_id, t3 : pop/thread_id, t4 : pop/thread_id,
        w01 : pop/write, w02 : pop/write, w1 : pop/write, w2 : pop/write,
        r1 : pop/read, r2 : pop/read, r3 : pop/read, r4 : pop/read |
       {
          //init
          po[w01,w1] and w01.addr = w1.addr
          po[w02,w2] and w02.addr = w2.addr

          //litmus
          w1.thread = t1
          r1.thread = t2 and po[r1,r2]
          w1.thread = t3
          r3.thread = t4 and po[r3,r4]
          r1.addr = w1.addr and r2.addr = w2.addr
          r3.addr = w2.addr and r4.addr = w1.addr
          w1.addr != w2.addr
          t1 != t2 and t1 != t3 and t1 != t4
          t2 != t3 and t2 != t4 and t3 != t4

          //result
          eventually w1 in r1.reads_from and w2 in r1.reads_from
        }
}

pred IRIW_fence {
   # pop/thread_id = 4
   # pop/read = 4
   # pop/write = 4
   # pop/barrier = 2
   some t1 : pop/thread_id, t2 : pop/thread_id, t3 : pop/thread_id, t4 : pop/thread_id,
   w01 : pop/write, w02: pop/write, w1 : pop/write, w2 : pop/write,
   r1 : pop/read, r2 : pop/read, r3 : pop/read, r4 : pop/read,
   b1 : pop/barrier, b2: pop/barrier |
   {
      //init
      po[w01,w1] and w01.addr = w1.addr
      po[w02,w2] and w02.addr = w2.addr

      //litmus
     w1.thread = t1
     r1.thread = t2 and po[r1,b1] and po[b1,r2]
     w1.thread = t3
     r3.thread = t4 and po[r3,b2] and po[b2,r4]
     r1.addr = w1.addr and r2.addr = w2.addr
     r3.addr = w2.addr and r4.addr = w1.addr
     w1.addr != w2.addr
     t1 != t2 and t1 != t3 and t1 != t4
     t2 != t3 and t2 != t4 and t3 != t4

     //result
     and eventually w1 in r1.reads_from and w2 in r1.reads_from
   }
}

pred SB{
   # pop/thread_id = 2
   # pop/read = 2
   # pop/write = 4
   # pop/address = 2
   some t1 : pop/thread_id, t2 : pop/thread_id,
        w01 : pop/write, w02 : pop/write,
        w1 : pop/write, w2 : pop/write,
        r1 : pop/read, r2 : pop/read |
   {
     //init
     po[w01,w1] and w01.addr = w1.addr
     po[w02,w2] and w02.addr = w1.addr
     // litmus test
     w1.thread = t1 and po[w1,r1]
     w2.thread = t2 and po[w2,r2]
     w1.addr = r2.addr
     w2.addr = r1.addr
     w1.addr != w2.addr
     // result
     eventually r1.reads_from = w01
     eventually r2.reads_from = w02
   }
}
