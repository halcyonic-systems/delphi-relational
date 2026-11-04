/-!
# Replication in (M,R)-systems: when does it come "for free"?

Source: A. H. Louie (2012), "Anticipation in (M,R)-systems",
International Journal of General Systems 41(1), 5–22, pp. 7–9.
doi:10.1080/03081079.2011.622088

Louie's simplest (M,R)-system is the chain

    A --f--> B --Φ--> H(A,B)

with metabolism `f ∈ H(A,B)` and repair `Φ ∈ H(B, H(A,B))`. Rosen's replication map
`β : H(A,B) → H(B, H(A,B))` is obtained by inverting evaluation at a point `b ∈ B`
(Φ ↦ Φ b), which is possible "under stringent but not prohibitively strong conditions".

This file makes the condition exact and shows which reading of the hom-sets it holds in:

* `replicates_iff_evalInjective`: replication exists **iff** evaluation at `b` is one-to-one
  on the admissible repairs. The condition is necessary as well as sufficient.
* `not_replicates_full`: if `H(B, H(A,B))` is the **full** function space (every map counts as
  a repair), `B` has two points and there are two metabolisms, replication never exists.
* `replicates_constant`: with a **restricted** hom-set (here: constant repairs) it always does.
* `repair_is_metabolism_up`: a repair is a metabolism of the network one level up, and β has
  the type of a repair there (Louie's role relativity, p. 9). An identity of bookkeeping.

So the claim "replication comes for free" is true under one reading of `H` and false under the
other. Louie insists `H(A,B)` is a proper subset of `B^A` (p. 7); these theorems show that this
insistence is load-bearing. A proof here is about the model, not about organisms.
-/

namespace RelationalLaws.Replication

/-- An (M,R)-network in Louie's simplest form. The hom-sets are predicates:
`Met f` says `f ∈ H(A,B)`, `Rep Φ` says `Φ ∈ H(B, H(A,B))`. -/
structure Network (A B : Type) where
  Met : (A → B) → Prop
  Rep : (B → A → B) → Prop

variable {A B : Type}

/-- Replication at `b`: a map from metabolisms to repairs that recovers every admissible
repair from the metabolism it produces at `b`. -/
def Replicates (N : Network A B) (b : B) : Prop :=
  ∃ β : (A → B) → (B → A → B), ∀ Φ, N.Rep Φ → β (Φ b) = Φ

/-- Rosen's condition: evaluation at `b` (Φ ↦ Φ b) is one-to-one on admissible repairs. -/
def EvalInjective (N : Network A B) (b : B) : Prop :=
  ∀ Φ Ψ, N.Rep Φ → N.Rep Ψ → Φ b = Ψ b → Φ = Ψ

/-- Replication exists if and only if evaluation at `b` is injective on repairs. -/
theorem replicates_iff_evalInjective (N : Network A B) (b : B) :
    Replicates N b ↔ EvalInjective N b := by
  constructor
  · rintro ⟨β, hβ⟩ Φ Ψ hΦ hΨ h
    rw [← hβ Φ hΦ, ← hβ Ψ hΨ, h]
  · intro hinj
    open Classical in
    refine ⟨fun f => if h : ∃ Φ, N.Rep Φ ∧ Φ b = f then Classical.choose h else fun _ => f, ?_⟩
    intro Φ hΦ
    have h : ∃ Ψ, N.Rep Ψ ∧ Ψ b = Φ b := ⟨Φ, hΦ, rfl⟩
    simp only [dif_pos h]
    have hs := Classical.choose_spec h
    exact hinj _ _ hs.1 hΦ hs.2

/-- The full-function-space reading: every map `B → H(A,B)` counts as a repair. -/
def full (Met : (A → B) → Prop) : Network A B := ⟨Met, fun _ => True⟩

/-- Under the full reading replication never comes for free, as soon as `B` has a second
point `b'` and there are two different metabolisms `f ≠ g`. -/
theorem not_replicates_full (Met : (A → B) → Prop) (b b' : B) (hb : b' ≠ b)
    (f g : A → B) (hfg : f ≠ g) : ¬ Replicates (full Met) b := by
  rw [replicates_iff_evalInjective]
  intro hinj
  open Classical in
  let Φ₂ : B → A → B := fun x => if x = b then f else g
  have h := hinj (fun _ => f) Φ₂ trivial trivial (by simp [Φ₂])
  have h' := congrFun h b'
  simp [Φ₂, hb] at h'
  exact hfg h'

/-- A restricted reading: only constant repairs (the same enzyme rebuilt from any input). -/
def constant (Met : (A → B) → Prop) : Network A B :=
  ⟨Met, fun Φ => ∃ f, Met f ∧ Φ = fun _ => f⟩

/-- Under the constant-repair reading replication always exists, at every `b`. -/
theorem replicates_constant (Met : (A → B) → Prop) (b : B) :
    Replicates (constant Met) b := by
  rw [replicates_iff_evalInjective]
  rintro Φ Ψ ⟨f, -, rfl⟩ ⟨g, -, rfl⟩ h
  simp only at h
  rw [h]

/-- Role relativity (Louie 2012, p. 9): in the chain f, Φ, β the last two maps form an
(M,R)-system one level up, with `A' := B` and `B' := H(A,B)`. The network one level up takes
the repairs of `N` as its metabolisms; `Rβ` says which replication maps count as its repairs. -/
def up (N : Network A B) (Rβ : ((A → B) → B → A → B) → Prop) : Network B (A → B) :=
  ⟨N.Rep, Rβ⟩

/-- Every repair of `N` is a metabolism of the network one level up, and a replication map
for `N` has exactly the type of a repair there. An identity of bookkeeping, recorded as such. -/
theorem repair_is_metabolism_up (N : Network A B) (Rβ : ((A → B) → B → A → B) → Prop)
    (Φ : B → A → B) (hΦ : N.Rep Φ) : (up N Rβ).Met Φ :=
  hΦ

end RelationalLaws.Replication
