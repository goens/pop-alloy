module util

fun restriction[u : univ, rel: u->u] : u->u { u <: iden :> u}
fun id[u : univ] : u->u { restriction[u, iden] }
pred transitive[u : univ, rel: u->u] { rel = ^rel }
pred reflexive[u : univ, rel: u->u] { restriction[u,iden] in rel }
pred antisymmetric[u : univ, rel: u->u] { rel & ~rel = restriction[u,iden]}
pred irreflexive[rel : univ-> univ] { no iden & rel }

fun refl_transitive_closure[rel : univ -> univ] : univ->univ { ^(restriction[(rel.univ + univ.rel), iden] + rel) }

pred partial_order[u : univ, rel : u->u] {
	transitive[u,rel]
	antisymmetric[u,rel]
	reflexive[u,rel]
}
