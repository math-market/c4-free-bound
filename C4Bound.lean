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
  classical
  -- (1) Double comptage : chaque paire {a, b} a au plus un voisin commun.
  have hdisj : (↑(Finset.univ : Finset (Fin 50)) : Set (Fin 50)).PairwiseDisjoint
      (fun v => (G.neighborFinset v).powersetCard 2) := by
    intro v _ w _ hvw
    rw [Function.onFun, Finset.disjoint_left]
    intro s hsv hsw
    rw [Finset.mem_powersetCard] at hsv hsw
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hsv.2
    have hav : G.Adj v a := (G.mem_neighborFinset v a).mp (hsv.1 (by simp))
    have hbv : G.Adj v b := (G.mem_neighborFinset v b).mp (hsv.1 (by simp))
    have haw : G.Adj w a := (G.mem_neighborFinset w a).mp (hsw.1 (by simp))
    have hbw : G.Adj w b := (G.mem_neighborFinset w b).mp (hsw.1 (by simp))
    have hsub : ({v, w} : Finset (Fin 50)) ⊆ G.neighborFinset a ∩ G.neighborFinset b := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rw [Finset.mem_inter, G.mem_neighborFinset, G.mem_neighborFinset]
      rcases hx with rfl | rfl
      · exact ⟨hav.symm, hbv.symm⟩
      · exact ⟨haw.symm, hbw.symm⟩
    have h2 : ({v, w} : Finset (Fin 50)).card = 2 := Finset.card_pair hvw
    have h3 := Finset.card_le_card hsub
    have h4 := h a b hab
    omega
  have hpairs : ∑ v, (G.degree v).choose 2 ≤ 1225 := by
    calc ∑ v, (G.degree v).choose 2
        = ∑ v, ((G.neighborFinset v).powersetCard 2).card := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          rw [Finset.card_powersetCard, G.card_neighborFinset_eq_degree]
      _ = (Finset.univ.biUnion fun v => (G.neighborFinset v).powersetCard 2).card :=
          (Finset.card_biUnion hdisj).symm
      _ ≤ ((Finset.univ : Finset (Fin 50)).powersetCard 2).card := by
          apply Finset.card_le_card
          intro s hs
          rw [Finset.mem_biUnion] at hs
          obtain ⟨v, _, hs⟩ := hs
          rw [Finset.mem_powersetCard] at hs ⊢
          exact ⟨Finset.subset_univ s, hs.2⟩
      _ = 1225 := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_two_right]
  -- (2) n² = 2·C(n,2) + n  (récurrence ; seuls omega/simp/decide sont disponibles avec les imports verrouillés).
  have hsq : ∀ n : ℕ, n * n = 2 * n.choose 2 + n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
      have e : (k + 1).choose 2 = k.choose 1 + k.choose 2 := Nat.choose_succ_succ k 1
      rw [e, Nat.choose_one_right]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
  -- (3) Intégralité : (d - 7)(d - 8) ≥ 0, soit 15·d ≤ d² + 56, pour tout entier d.
  have hloc : ∀ d : ℕ, 15 * d ≤ d * d + 56 := by
    intro d
    rcases Nat.lt_or_ge d 8 with hd | hd
    · have petit : ∀ x : ℕ, x < 8 → 15 * x ≤ x * x + 56 := by decide
      exact petit d hd
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hd
      simp only [Nat.add_mul, Nat.mul_add]
      omega
  have hv : ∀ v : Fin 50, 14 * G.degree v ≤ 2 * (G.degree v).choose 2 + 56 := by
    intro v
    have h1 := hloc (G.degree v)
    have h2 := hsq (G.degree v)
    omega
  -- (4) Somme sur les 50 sommets : 14·Σd ≤ 2·ΣC(d,2) + 2800.
  have hs : 14 * ∑ v, G.degree v ≤ 2 * ∑ v, (G.degree v).choose 2 + 2800 := by
    have := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 50))) (fun v _ => hv v)
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    omega
  -- (5) Σd = 2E, ΣC(d,2) ≤ 1225 : 28E ≤ 5250, donc E ≤ 187.
  have hE := G.sum_degrees_eq_twice_card_edges
  omega

end C4Bound
