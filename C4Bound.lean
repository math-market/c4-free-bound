/-
Copyright (c) 2026 AletheAI Inc. All rights reserved.
Released under Apache 2.0 license.

# The C4-free edge bound at n = 50 — locked statement

This file is the specification for the Problem Market task "Every C4-free graph on
50 vertices has at most 187 edges". A submission closes the `sorry` below, leaving
the statement unchanged.

`C4-free` is stated in its **local** form: no two distinct vertices have more than
one common neighbour. For a simple graph that is equivalent to containing no cycle
of length four, and it is the same condition the companion construction board's
checker enforces — so the two halves of this record are provably about the same
object.

The statement uses only Mathlib: `SimpleGraph`, `neighborFinset`, `edgeFinset`.
There are no definitions of ours to audit.
-/
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open Finset

namespace C4Bound

/-- **Every C4-free graph on 50 vertices has at most 187 edges.**

The hypothesis says no two distinct vertices share more than one neighbour, which
for a simple graph is exactly C4-freeness.

The bound is the elementary one: double-count paths of length two. Each such path
is determined by its endpoints together with its midpoint, and the hypothesis
allows at most one midpoint per pair, so `∑ v, C(deg v, 2) ≤ C(50, 2) = 1225`.
Convexity makes the left side smallest when the degrees are as equal as possible,
and integrality of the degrees then forces at most 187 edges — 188 would already
need 1232 paths. -/
theorem c4_free_fifty_edge_bound
    (G : SimpleGraph (Fin 50)) [DecidableRel G.Adj]
    (h : ∀ u v : Fin 50, u ≠ v →
      ((G.neighborFinset u) ∩ (G.neighborFinset v)).card ≤ 1) :
    G.edgeFinset.card ≤ 187 := by
  sorry

end C4Bound
