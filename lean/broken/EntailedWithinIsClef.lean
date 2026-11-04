-- expect: Tactic `assumption` failed
/-
Broken variant: MUST NOT compile.

It asserts Louie's "equivalently" (2012, p. 13) on a fixed formal system: that a system in
which every process is entailed within is clef. The natural proof takes each process's
entailer as the second process of its cycle and fails, because nothing entails the way back.
`entailedWithin_not_clef` proves the statement false, so no proof of it can exist.
-/
import RelationalLaws.Closure
open RelationalLaws.Closure

theorem entailedWithin_clef_broken {α : Type} (E : α → α → Prop) (h : EntailedWithin E) :
    Clef E := by
  intro f
  obtain ⟨g, hg⟩ := h f
  refine ⟨g, ?_, ?_, .single hg⟩ <;> assumption
