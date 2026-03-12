import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-
## Handshaking lemma: the sum of the degrees in a graph is twice the number of its edges

A *simple graph* `G = (V, E)` is defined by its set of *vertices (nodes)* `V` and
a set of *edges* `∅ ⊆ E ⊆ { e = {u, v} ∣ u ≠ v ∈ V }`. It is *finite* if `V` is
finite and its *order* denotes `#V` and *size* denotes `#E`.

The edges can also be interpreted as a relationship `~` between vertices,
where `u ~ v` if and only if `{u, v} ∈ E` (which in particular implies that
`u ≠ v`). Two vertices defining an edge are said to be *adjacent* and an edge
and any of its two vertices are said to be *incident*.

The *neighborhood* of a vertex `v` is defined as `N(v) = {u | u ~ v}`. Its
*degree* `d(v) = #N(v)` is simply the cardinality of its neighborhood.
The *incidence set* of a vertex `v` is defined as `I(v) = {e ∈ E | v ∈ e}`.

**Handshake Lemma.** Given any finite simple graph `G = (V, E)`, the sum of the
degrees of all its vertices equals twice its size, that is `Σ_v d(v) = 2 * #E`.
-/

/-
# Phase 1: Find out as much as is useful about simple graphs in `mathlib`

The two most relevant files / import should probably be
`Mathlib.Combinatorics.SimpleGraph.Basic` There we find
the definition of a simple graph `G` ...

```
structure SimpleGraph (V : Type u) where
  Adj : V → V → Prop
  symm : Symmetric Adj       := by aesop_graph
  loopless : Std.Irrefl Adj  := by aesop_graph
```

... and that we can get the edge set through `G.edgeSet`.
We can also find the definition of an incidence set ...

```
def incidenceSet (v : V) : Set (Sym2 V) :=
  { e ∈ G.edgeSet | v ∈ e }
```

... and the neighborhood set ...

```
def neighborSet (v : V) : Set V := {w | G.Adj v w}
```

... but you will not fine a notion of degree. Why? Because
this requires your graph to be finite. Luckily, we have
`Mathlib.Combinatorics.SimpleGraph.Finite`, which states

> The design for finiteness is that each definition takes the smallest finiteness assumption
necessary. For example, `SimpleGraph.neighborFinset v` only requires that `v` have
finitely many neighbors.

Working backwards, we first see that the degree is

```
def degree : ℕ := #(G.neighborFinset v)
```

... with ...

```
def neighborFinset : Finset V := (G.neighborSet v).toFinset
```

... where we recall that we have already seen `Set.toFinset`
in P06S01. Both of these get their finiteness by assuming
`Fintype ↑(G.neighborSet v)`. For us, we will need this to
hold for each `v`, so the better type class assumption to
use should be `[Fintype V]`.

There will (probably) be more importants needed once we 
understand the actual proof, but from the theorem statement
we can already infer that we might need `Finset.sum` and the
theorems about it from `Mathlib.Algebra.Order.BigOperators.Ring.Finset`
-/

#check Finset.sum_congr

/-
# Phase 2: Write down the statement of the handshake lemma in lean with `sorry`
-/

/-
# Phase 3: Find a proof of the handshake lemma that you like and flesh it out
-/

/-
# Phase 4: Find out as much as is useful for your proof in `mathlib`
-/

/-
# Phase 5: Implement your fleshed out proof as closely as possible in lean
-/
