/-
Broken variant: MUST NOT compile.

It asserts the unrestricted reading of "replication comes for free": that replication exists
in the full-function-space network, with no condition on the hom-sets. The proof is the one
that works for constant repairs (`replicates_constant`), reused where its condition fails.
`not_replicates_full` proves the statement false whenever B has two points and there are two
metabolisms, so no proof of it can exist in general.
-/
import RelationalLaws.Replication
open RelationalLaws.Replication

theorem replicates_full_broken {A B : Type} (Met : (A → B) → Prop) (b : B) :
    Replicates (full Met) b := by
  rw [replicates_iff_evalInjective]
  intro Φ Ψ _ _ h
  funext x
  rw [h]
