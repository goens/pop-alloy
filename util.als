module util

fun restriction[u : univ, rel: u->u] : u->u { u <: iden :> u}
fun id[u : univ] : u->u { restriction[u, iden] }
pred transitive[u : univ, rel: u->u] { rel = ^rel }
pred reflexive[u : univ, rel: u->u] { restriction[u,iden] in rel }
pred antisymmetric[u : univ, rel: u->u] { rel & ~rel = restriction[u,iden]}
pred irreflexive[rel : univ-> univ] { no iden & rel }
pred acyclic[rel: univ -> univ]{    no x: univ | x in x.^rel }

// different from *rel, as it only includes things in the domain/range of rel
fun refl_transitive_closure[rel : univ -> univ] : univ->univ { ^(restriction[(rel.univ + univ.rel), iden] + rel) }

pred partial_order[u : univ, rel : u->u] {
	transitive[u,rel]
	antisymmetric[u,rel]
	reflexive[u,rel]
}

//see : https://stackoverflow.com/questions/41707898/is-there-a-better-alloy-model-of-a-tree
pred tree_with_root[u : univ, rel : u-> u, root : u]{
	// root has no predecessors
	no rel.root
   // can reach all nodes from root
	all n: u - root | n in root.^rel
	irreflexive[rel]
	acyclic[rel]
	// injective
	rel.~rel in iden
}

pred tree[u: univ, rel : u -> u]{
	some root : u | tree_with_root[u,rel,root]
 }
