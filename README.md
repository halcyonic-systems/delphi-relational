# Relational biology: Louie (2012)

One new claim source for DELPHI, from the relational biology of Rashevsky, Rosen and Louie. The public claim graph (build of 2026-11-03) has no claims mentioning Rosen, Louie, Rashevsky, (M,R)-systems or closure to efficient causation. Every law in it so far is about quantities (scaling, growth, geometry). This source adds laws about organization.

Source: Louie, A. H. (2012). Anticipation in (M,R)-systems. *International Journal of General Systems* 41(1), 5-22. [doi:10.1080/03081079.2011.622088](https://doi.org/10.1080/03081079.2011.622088)

## The result

Rosen's (M,R)-system is the chain `A --f--> B --Φ--> H(A,B)`: metabolism `f`, repair `Φ`. Rosen claimed that a replication map comes "for free" by inverting evaluation at a point `b` (Φ ↦ Φ b), "under stringent but not prohibitively strong conditions". The conditions were never stated exactly, and the disputes over Rosen's results have largely been disputes over how to encode them.

`lean/RelationalLaws/Replication.lean` states the condition exactly and separates the readings:

| Theorem | Statement |
|---|---|
| `replicates_iff_evalInjective` | Replication at `b` exists **if and only if** evaluation at `b` is one-to-one on the admissible repairs. |
| `not_replicates_full` | If every map `B → H(A,B)` counts as a repair, replication **never** exists, as soon as `B` has two points and there are two metabolisms. |
| `replicates_constant` | With repairs restricted to constant maps, replication **always** exists. |
| `repair_is_metabolism_up` | A repair is a metabolism one level up (Louie's role relativity, p. 9). An identity of bookkeeping. |

So "replication comes for free" is true under one reading of the hom-sets and false under the other. Louie insists that `H(A,B)` is a proper subset of all maps `B^A` (p. 7). These theorems show that this stipulation carries the result.

## The second result: two definitions of closure

On p. 13 Louie defines a system as closed to efficient causation if every efficient cause is entailed within it, and calls this equivalent to every process lying on a hierarchical cycle. `lean/RelationalLaws/Closure.lean` encodes a formal system as processes with an entailment relation (g entails f when f is an output of g) and separates the two:

| Theorem | Statement |
|---|---|
| `clef_entailedWithin` | Every process on a cycle implies every process entailed within. |
| `entailedWithin_not_clef` | The converse fails on a fixed system: f and g entail each other, f entails h, and h lies on no cycle. |
| `clef_complex`, `complex_not_clef` | Under the cycle definition, closed systems are a proper subset of complex ones (claim 08). |
| `selfEntailment`, `regress` | Under the entailed-within definition, claim 08 fails: one process entailing itself, or an infinite regress. |
| `entailedWithin_complex_of_finite` | It holds again for finite systems in which no process entails itself. |

So claim 08 is true under one of Louie's definitions and false under the other, and the theorems name what the weaker definition is missing: finiteness and no self-entailment. Louie phrases the equivalence through "has a model"; the counterexample takes each formal system as its own model.

## Claims

| id | claim | status |
|---|---|---|
| louie2012-01 | Postulate of Life: an organism is whatever realizes an (M,R)-system | untested (a postulate) |
| louie2012-02 | Metabolic hom-sets are a proper subset of all mappings | stipulation |
| louie2012-03 | Repair maps rebuild the metabolic components | definition |
| louie2012-04 | Replication comes for free, under conditions | **proved (Lean), several readings** |
| louie2012-05 | Most (M,R)-systems cannot replicate | untested ("most" needs a measure) |
| louie2012-06 | Replicability is relational, not mechanism-specific | untested |
| louie2012-07 | Metabolism, repair and replication are roles, not kinds | **proved (Lean), identity** |
| louie2012-08 | Closure to efficient causation is stricter than containing a causal cycle | **proved (Lean) under one definition, false under the other** |
| louie2012-09 | Two definitions of closure, called equivalent | **one direction proved (Lean), the other false on a fixed system** |

`claims.json` uses the fields of `docs/claims.json`, including the `formalization` tags and readings, plus `quote_note` where notation in a quote was restored from the page.

## Reproduce

```sh
cd lean && ./check.sh
python3 build/check-quotes.py <path to the Louie 2012 PDF>
```

`check.sh` follows the law registry's rules: the library builds, there is no `sorry`, the theorems use only Lean's standard axioms, and every file in `lean/broken/` (three false statements) fails to compile on a proof error. Lean 4.28.0, no Mathlib. `check-quotes.py` finds every quote in the PDF's text layer, with each normalization rule listed in the script; the Postulate quote and the notation in 02 were also checked against the rendered page.

## What is not claimed

- The theorems are about the model. Nothing here says which hom-set reading living systems realize, or that organisms are (M,R)-systems.
- The encoding is one reading of Louie's simplest (M,R)-system: hom-sets as predicates on function spaces, with replication at a single point `b`. Other encodings (categorical, λ-calculus, process algebra) are not covered.
- This source has not been through the assess and publish stages: no assessor scores, no nanopubs.

## Next

1. Closing the loop: when does the input `b` entail the replication map itself, so that metabolism, repair and replication form a hierarchical cycle (Louie, p. 12, diagram 21)?
2. The contested result, that systems closed to efficient causation have no computable model, as a claim with several readings. The aim is the same as here: find the assumption on which the encodings part, rather than pick a winner. Candidate sources still to be checked: Chu & Ho (2006), Mossio, Longo & Stewart (2009), Cárdenas et al. (2010), Gatherer & Galpin (2013).
