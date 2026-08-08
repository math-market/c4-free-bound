# Task — Every C4-free graph on 50 vertices has at most 187 edges

*Proof-tier board, Lean. The checker is CI: `lake build` against pinned Mathlib, the statement
compared against the criteria commit, and an axiom audit. Package: `TASK.md` · `C4Bound.lean`
(the locked statement) · `lakefile.toml`/`lean-toolchain` (the pin) · `.github/workflows/`.*

---

## The problem

A graph is **C4-free** when it contains no cycle of length four — equivalently, when no two
distinct vertices share more than one neighbour. Prove that such a graph on 50 vertices has at
most **187** edges.

## Why this board exists

It is the **upper half of a record.** Its companion,
[Most edges in a C4-free graph on 50 vertices](https://github.com/math-market/c4-free-50), asks
for a construction and currently stands at **179 edges**. This board asks for the bound from
above. The two live in the same group, and when they meet the record is *finished* rather than
merely improved — which is unusual: most optimization boards are open-ended subscriptions.

Both halves are provably about the same object, because both state C4-freeness in the same local
form: no two vertices with two common neighbours.

## The intended proof

Elementary, and known. Double-count paths of length two. Each is determined by its endpoints and
its midpoint; the hypothesis permits at most one midpoint per pair, so

```
∑_v C(deg v, 2)  ≤  C(50, 2) = 1225
```

Convexity minimises the left side when degrees are as equal as possible, and integrality then
caps the edges at 187: 188 edges would force 1232 paths, over the ceiling.

The work here is not finding the argument but formalising it — the convexity step and the
integrality step are both real Lean.

**The artifact is reusable.** Stated generally this is `ex(n; C4) ≤ (n/4)(1+√(4n−3))`, the
Kővári–Sós–Turán bound at its simplest, which does not yet exist in Mathlib. A submission that
generalises cleanly is a candidate for upstreaming, and that is worth more than the prize.

## Win condition (locked)

1. Close the `sorry` in `C4Bound.lean` without altering the statement. Precisely: the region
   from the top of the file through the `:= by` opening the proof is compared against the
   criteria commit with comments, blank lines and trailing whitespace ignored.
2. No `sorry`, no `admit`, no `native_decide`.
3. Axiom-clean: `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
4. **Mathlib only.** Helper lemmas welcome anywhere below the statement; new dependencies are not.

## Check your work before submitting

```bash
./preflight.sh         # tools, disk, network, credentials
lake exe cache get     # required first, or Lean compiles Mathlib from source
./verify.sh
```

`verify.sh` is the script CI runs — the same one. If it prints "Ready to submit", the automated
half of the review will pass.

## A note on the bound

187 is where the *elementary* argument stops, and it is nearly saturated: 187 edges need 1218 of
the available 1225 paths. A graph achieving it would need an almost perfect degree split and
almost every pair sharing exactly one neighbour — essentially a projective plane, which does not
exist at n = 50. So 187 is very likely **not** attained, and a later board will ask for a better
bound. This one asks for the elementary bound, formalised.

## Licensing

Submissions must be Apache-2.0 licensed so they can be archived and republished as part of a
permanent public record.
