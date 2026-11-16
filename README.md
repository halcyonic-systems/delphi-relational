# delphi-relational

Claims from relational biology for [DELPHI](https://github.com/fractastical/delphi), with Lean 4 proofs that say exactly which reading of each claim holds.

DELPHI collects candidate laws of biology as source-cited claims, proves them in Lean where they are mathematics, and tests them against data where they are empirical. Its graph has about 2,100 claims, and its laws are about quantities: scaling, growth, geometry. None of them mentions Rosen, Louie, Rashevsky, (M,R)-systems or closure to efficient causation (checked against the public claim graph, build of 2026-11-08).

This repository adds one claim source on those topics: ten claims from Louie (2012) on Rosen's (M,R)-systems, in DELPHI's claim format and following its rules for proofs. The repository root is laid out as a DELPHI claim source, so it can be copied into `claim-sources/relational-biology/` as is.

## Why relational biology, and why Lean

Rosen's (M,R)-systems model a cell as metabolism, repair and replication, each producing the next. Rosen claimed that such a system can make all of its own machinery (it is closed to efficient causation), and that such a system has no computable model. These claims have been disputed for decades. Chu & Ho (2006) argued that Rosen's central proof fails. Mossio, Longo & Stewart (2009) gave a computable expression of closure. Cárdenas et al. (2010) re-examined the conditions for closure.

Part of the difficulty is that Rosen's proofs are in prose, so the sides often encode the same sentence differently and then prove different things. DELPHI already has a tool for this: a claim can carry several readings, each with its own status. This repository uses it on three of Louie's statements. For each one, the readings are written down and machine-checked, and the assumption on which they part is named. The pattern is the same all three times: the claim holds under a restricted reading of the hom-sets (the sets of admissible maps) and fails under another.

## Results

### 1. Replication comes "for free" exactly when evaluation is one-to-one

Rosen's simplest (M,R)-system is the chain `A --f--> B --Φ--> H(A,B)`: metabolism `f`, repair `Φ`. Rosen obtains a replication map β by inverting evaluation at a point `b` (Φ ↦ Φ b), "under stringent but not prohibitively strong conditions". `lean/RelationalLaws/Replication.lean`:

| Theorem | Statement |
|---|---|
| `replicates_iff_evalInjective` | Replication at `b` exists if and only if evaluation at `b` is one-to-one on the admissible repairs. |
| `not_replicates_full` | If every map `B → H(A,B)` counts as a repair, replication never exists, once `B` has two points and there are two metabolisms. |
| `replicates_constant` | With repairs restricted to constant maps, replication always exists. |
| `repair_is_metabolism_up` | A repair is a metabolism one level up (Louie's role relativity). An identity of bookkeeping. |

### 2. Louie's two definitions of closure come apart

Louie (2012, p. 13) defines a system as closed to efficient causation if every efficient cause is entailed within it, and calls this equivalent to every process lying on a hierarchical cycle. `lean/RelationalLaws/Closure.lean` encodes a formal system as processes with an entailment relation (g entails f when f is an output of g):

| Theorem | Statement |
|---|---|
| `clef_entailedWithin` | Every process on a cycle implies every process entailed within. |
| `entailedWithin_not_clef` | The converse fails on a fixed system: f and g entail each other, f entails h, and h lies on no cycle. |
| `clef_complex`, `complex_not_clef` | Under the cycle definition, closed systems are a proper subset of complex systems (those with at least one cycle), as Louie states. |
| `selfEntailment`, `regress` | Under the entailed-within definition the same statement fails: one process entailing itself, or an infinite regress. |
| `entailedWithin_complex_of_finite` | It holds again for finite systems in which no process entails itself. |

So whether "closed systems are a proper subset of complex systems" holds depends on which of Louie's definitions is used, and the theorems name what the weaker one needs: finiteness and no self-entailment. Louie states the equivalence through "has a model". The counterexample takes each formal system as its own model. Whether some other model always restores the equivalence depends on what counts as a model, which the paper does not fix.

### 3. Closing the loop needs a small set of replication maps

To make replication itself entailed within the system, Louie (p. 8) identifies the set `B` with the set of replication maps `H(H(A,B), H(B,H(A,B)))`, each `b` with the inverse of evaluation at `b`. Then `b` is β, and no new efficient cause is added. `lean/RelationalLaws/Loop.lean`:

| Theorem | Statement |
|---|---|
| `no_identification_full` | If every map `H(A,B) → H(B,H(A,B))` counts as a replication map, the identification is impossible once `A` is nonempty and `B` has two points. This is Cantor's diagonal argument: no map from `B` even reaches them all. |
| `boolCell`, `boolCell_closes` | With restricted hom-sets it exists: a cell on `B = Bool` with two repairs and two replication maps, in which metabolism, repair and replication close into one loop. |

## What is new here and what is not

| Result | Known before | Added here |
|---|---|---|
| 1. Replication needs one-to-one evaluation, which fails on full function spaces | Letelier et al. (2006) state this informally: evaluation must be one-to-one, so the set of admissible maps must be a proper subset of all maps and no larger than its target. They give an arithmetic example. | The condition as necessary and sufficient, machine-checked, with the counterexample |
| 2. Two definitions of closure | No statement of the gap found in the works listed below | The two separated on a fixed formal system; claim 08 shown to depend on the definition; the finite, no-self-entailment repair |
| 3. Identifying `b` with β needs small sets | Letelier et al. (2006): invertible evaluations exist "if the set S is small enough", and Rosen's full function spaces are "too big" | Cantor's obstruction stated and machine-checked (onto-ness alone fails), and a minimal cell in which the loop closes |

No formalization of (M,R)-systems in Lean, Coq, Agda or Isabelle turned up in a search on 2026-11-04. Gatherer & Galpin (2013) model them in process algebra.

## Claims

`claims.json` uses the fields of DELPHI's `docs/claims.json`, including `formalization` with its tags and readings. Two fields are added: `quote_note`, where notation in a quote was restored from the page, and `quote_check: "page-image"`, where the PDF's text layer was unusable and the quote was checked against the rendered page.

| id | claim | status |
|---|---|---|
| louie2012-01 | Postulate of Life: an organism is whatever realizes an (M,R)-system | untested (a postulate) |
| louie2012-02 | Metabolic hom-sets are a proper subset of all mappings | stipulation |
| louie2012-03 | Repair maps rebuild the metabolic components | definition |
| louie2012-04 | Replication comes for free, under conditions | proved; several readings |
| louie2012-05 | Most (M,R)-systems cannot replicate | untested ("most" needs a measure) |
| louie2012-06 | Replicability is relational, not mechanism-specific | untested |
| louie2012-07 | Metabolism, repair and replication are roles, not kinds | proved; identity |
| louie2012-08 | Closure to efficient causation is stricter than containing a causal cycle | proved under one definition, false under the other |
| louie2012-09 | Two definitions of closure, called equivalent | one direction proved, the other false on a fixed system |
| louie2012-10 | The loop closes by identifying each `b` with a replication map | false under full function spaces, satisfiable under restricted ones |

## Layout

```
claims.json                 the ten claims, DELPHI claim format
lean/RelationalLaws/        Replication.lean, Closure.lean, Loop.lean
lean/broken/                four false statements that must not compile
lean/check.sh               the proof checks
build/check-quotes.py       matches every quote to the source PDF
```

## Reproduce

```sh
cd lean && ./check.sh
python3 build/check-quotes.py <path to the Louie 2012 PDF>
```

`check.sh` applies the rules of DELPHI's law registry. The library must build. There must be no `sorry`. Every theorem and definition must use only Lean's standard axioms (propext, Classical.choice, Quot.sound). Every file in `lean/broken/` must fail to compile, with the error named on its first line (`-- expect: ...`), so a typo or a missing import cannot pass as a failure. It needs Lean 4.28.0 (`elan` installs it from `lean/lean-toolchain`) and no Mathlib, so it builds in seconds.

`check-quotes.py` needs `pdftotext` and a copy of the article, which is not included here. Each normalization of the PDF's text layer is listed in the script.

## What is not claimed

- The theorems are about formal models. Nothing here says which reading living systems realize, or that organisms are (M,R)-systems.
- Each result covers one encoding: hom-sets as predicates on function spaces, and formal systems as processes with an entailment relation. Category-theoretic, λ-calculus and process-algebra encodings are not covered.
- The claims come from Louie (2012) only. Louie's book (2009) may define these terms more carefully; it has not been checked.
- These claims have not been through DELPHI's assess and publish stages: no assessor scores, no nanopublications.

## Next

Open questions are filed as issues: Rosen's non-computability claim with its readings separated; a pre-registered test of closure on real metabolic networks; and folding these claims into DELPHI.

## References

- Louie, A. H. (2012). Anticipation in (M,R)-systems. *International Journal of General Systems* 41(1), 5-22. [doi:10.1080/03081079.2011.622088](https://doi.org/10.1080/03081079.2011.622088)
- Letelier, J.-C., Soto-Andrade, J., Guíñez Abarzúa, F., Cornish-Bowden, A., & Cárdenas, M. L. (2006). Organizational invariance and metabolic closure: Analysis in terms of (M,R) systems. *Journal of Theoretical Biology* 238(4), 949-961. [doi:10.1016/j.jtbi.2005.07.007](https://doi.org/10.1016/j.jtbi.2005.07.007)
- Chu, D., & Ho, W. K. (2006). A category theoretical argument against the possibility of artificial life: Robert Rosen's central proof revisited. *Artificial Life* 12(1), 117-134. [doi:10.1162/106454606775186392](https://doi.org/10.1162/106454606775186392)
- Mossio, M., Longo, G., & Stewart, J. (2009). A computable expression of closure to efficient causation. *Journal of Theoretical Biology* 257(3), 489-498. [doi:10.1016/j.jtbi.2008.12.012](https://doi.org/10.1016/j.jtbi.2008.12.012)
- Cárdenas, M. L., Letelier, J.-C., Gutierrez, C., Cornish-Bowden, A., & Soto-Andrade, J. (2010). Closure to efficient causation, computability and artificial life. *Journal of Theoretical Biology* 263(1), 79-92. [doi:10.1016/j.jtbi.2009.11.010](https://doi.org/10.1016/j.jtbi.2009.11.010)
- Gatherer, D., & Galpin, V. (2013). Rosen's (M,R) system in process algebra. *BMC Systems Biology* 7, 128. [doi:10.1186/1752-0509-7-128](https://doi.org/10.1186/1752-0509-7-128)
- DELPHI: [github.com/fractastical/delphi](https://github.com/fractastical/delphi), [delphibio.org](https://delphibio.org)
