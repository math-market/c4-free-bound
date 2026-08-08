# ex(50; C4) ≤ 187 — the upper half of the C4-free record

A Problem Market board. Prove in Lean that every C4-free graph on 50 vertices has at most 187
edges. The locked statement is [`C4Bound.lean`](C4Bound.lean); the task is [`TASK.md`](TASK.md).

```bash
./preflight.sh
lake exe cache get     # required first
./verify.sh            # the same script CI runs
```

Companion board: [c4-free-50](https://github.com/math-market/c4-free-50) pushes the construction
up from 179. This one pushes the bound down from 187. When they meet, the record is finished.

Note that `main` fails its own CI on purpose — it holds the unproved statement, and that failing
run is the control showing the check can tell a proof from a gap.
