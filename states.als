module states
open util

// ------------------- States ---------------------


sig thread_id {
   var read_response : set read
}

abstract sig request {
   var order_constraints : set request,
   var propagated_to : set thread_id,
   thread : one thread_id
  }
abstract sig memory_access extends request {}

sig address {}

abstract sig write extends memory_access { to : one address }
abstract sig read extends memory_access { from : one address, var reads_from : lone write}
abstract sig barrier extends request {}

fun active_requests : set request { system_state.seen - system_state.removed }

fun order_constraints_po : request -> request {
   refl_transitive_closure[id[active_requests] + order_constraints]
}

sig system_state {
   var seen : set request,
   var removed : set request
}

//  -------- Constraints on signatures -----------------------------

pred order_constraints_induce_po {
   partial_order[active_requests, order_constraints_po]
}

fact all_requests_seen_somewhere { all r : request | eventually r in system_state.seen}

fact only_seen_propagated { no (request - system_state.seen).propagated_to }

fact one_system_state {always #system_state = 1}
//   ------- Auxiliary definitions for storage subsystem ----------

pred fully_propagated[r : request]{
	always(
   // for all requests before r in the (reflexive-transitive closure of) order-constraints order:
   all req : r.(order_constraints_po)
   // the request has been propagated to all threads (the set thread_id represents is all threads)
   | req.propagated_to = thread_id
			 )
}

fun addr[r : request] : address {
   r.(to + from)
}
