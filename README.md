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
| louie2012-08 | Closure to efficient causation is stricter than containing a causal cycle | untested, next for Lean |

`claims.json` uses the fields of `docs/claims.json`, including the `formalization` tags and readings, plus `quote_note` where notation in a quote was restored from the page.

## Reproduce

```sh
cd lean && ./check.sh
python3 build/check-quotes.py <path to the Louie 2012 PDF>
```

`check.sh` follows the law registry's rules: the library builds, there is no `sorry`, the theorems use only Lean's standard axioms, and `broken/ReplicatesFull.lean` (replication with no condition) fails to compile on a proof error. Lean 4.28.0, no Mathlib. `check-quotes.py` finds every quote in the PDF's text layer, with each normalization rule listed in the script; the Postulate quote and the notation in 02 were also checked against the rendered page.

## What is not claimed

- The theorems are about the model. Nothing here says which hom-set reading living systems realize, or that organisms are (M,R)-systems.
- The encoding is one reading of Louie's simplest (M,R)-system: hom-sets as predicates on function spaces, with replication at a single point `b`. Other encodings (categorical, λ-calculus, process algebra) are not covered.
- This source has not been through the assess and publish stages: no assessor scores, no nanopubs.

## Next

1. `louie2012-08` in Lean: on a digraph of efficient-cause entailments, every process on a cycle implies some cycle exists, and one cycle with a process off it separates the two.
2. The contested result, that systems closed to efficient causation have no computable model, as a second claim with several readings. The aim is the same as here: find the assumption on which the encodings part, rather than pick a winner. Candidate sources still to be checked: Chu & Ho (2006), Mossio, Longo & Stewart (2009), Cárdenas et al. (2010), Gatherer & Galpin (2013).
