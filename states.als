module states
open util

// ------------------- States ---------------------

abstract sig request {
   var propagated_to : set thread_id,
   thread : one thread_id
  }
abstract sig memory_access extends request {}

sig address {}

abstract sig write extends memory_access { to : one address }
abstract sig read extends memory_access { from : one address, var reads_from : lone write}
abstract sig barrier extends request {}

fun active_requests : set request { system_state.seen - system_state.removed }

fun order_constraints_po[s : scope] : request -> request {
   refl_transitive_closure[id[active_requests] + s.order_constraints]
}

sig system_state {
   var seen : set request,
   var removed : set request,
}

sig scope{
	subscopes : set scope,
   var order_constraints : request -> set request,
}

one sig system_scope extends scope {}

sig thread_id extends scope {
   var read_response : set read,
}

//  -------- Constraints on signatures -----------------------------

fact order_constraints_respect_scope {
	all s : scope | (request.~(s.order_constraints)).thread in scope.subscopes
	all s : scope | s.order_constraints.request.thread in scope.subscopes
}

fact order_constraints_respect_subscope {
	all s : scope |
		s.order_constraints in s.subscopes.order_constraints
}

fact subscopes_po { partial_order[scope,subscopes] }

fact system_scope_root{
	tree_with_root[scope,(subscopes - iden),system_scope]
}

pred order_constraints_induce_po {
   all s : scope | partial_order[active_requests, order_constraints_po[s]]
}

fact all_requests_seen_somewhere { all r : request | eventually r in system_state.seen}

fact only_seen_propagated { no (request - system_state.seen).propagated_to }

fact one_system_state {always #system_state = 1}

fact thread_scope_minimal { all t : thread_id | t.subscopes = t }

//   ------- Auxiliary definitions for storage subsystem ----------

pred fully_propagated[r : request, s : scope]{
	always(
   // for all requests before r in the (reflexive-transitive closure of) order-constraints order:
   all req : r.(order_constraints_po[s])
   // the request has been propagated to all threads (the set thread_id represents is all threads)
   | req.propagated_to = thread_id
			 )
}

fun addr[r : request] : address {
   r.(to + from)
}

pred is_joint_scope[t1 : thread_id, t2 : thread_id, s : scope]{
	t1 in s.subscopes
	t2 in s.subscopes
}

pred min_joint_scope[t1 : thread_id, t2 : thread_id, s : scope]{
	is_joint_scope[t1,t2,s]
	all r : (s.subscopes - s) | not is_joint_scope[t1,t2,r]
}

run {} for 5
