-- expect: Type mismatch
/-
Broken variant: MUST NOT compile.

It drops the no-self-entailment hypothesis from `entailedWithin_complex_of_finite`. The
proof passes the remaining hypotheses through and has nothing to supply in its place.
`selfEntailment` proves the statement false (one process entailing itself), so no proof of
it can exist.
-/
import RelationalLaws.Closure
open RelationalLaws.Closure

theorem finite_complex_broken {α : Type} (E : α → α → Prop) (u : List α)
    (hu : ∀ x, x ∈ u) (h : EntailedWithin E) (x : α) : Complex E :=
  entailedWithin_complex_of_finite E u hu (fun f hf => hf) h x
