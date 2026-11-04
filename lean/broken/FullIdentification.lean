-- expect: Application type mismatch
/-
Broken variant: MUST NOT compile.

It asserts a closed cell on two points in which every map H(A,B) → H(B,H(A,B)) counts as a
replication map. The proof reuses `boolCell` and has to show that an arbitrary β is one of its
two replication maps, which fails. `no_identification_full` (Cantor) proves the statement false,
so no proof of it can exist.
-/
import RelationalLaws.Loop
open RelationalLaws.Loop

theorem full_cell_broken : ∃ c : Cell Unit Bool, ∀ β, c.Repl β :=
  ⟨boolCell, fun _ => ⟨true, rfl⟩⟩
