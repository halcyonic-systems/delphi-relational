/-!
# Closing the loop: identifying b with the replication map

Source: A. H. Louie (2012), "Anticipation in (M,R)-systems",
International Journal of General Systems 41(1), 5–22, p. 8 (and the general form on p. 12).

Replication (see `Replication.lean`) gives a map β from metabolisms to repairs. For the
(M,R)-system to be closed to efficient causation, β must itself be entailed within the system.
Louie closes the loop by an "isomorphic identification between the sets B and
H(H(A,B), H(B,H(A,B)))", i.e. between each point `b` and a replication map, with
β = b̂⁻¹ (the inverse of evaluation at `b`). The chain then reads

    a ↦ b        (f entails b)
    b ↦ f        (Φ entails f)
    f ↦ Φ        (b, identified with β, entails Φ)

and no new efficient cause is added: `b` *is* β.

* `no_identification_full`: if every map `H(A,B) → H(B,H(A,B))` counts as a replication map,
  the identification is impossible as soon as `A` is nonempty and `B` has two points. This is
  Cantor's diagonal argument: `B` cannot be mapped onto a set of maps out of a set that
  contains a copy of `B`.
* `boolCell` and `boolCell_closes`: with restricted hom-sets the identification exists. A cell
  with `A = Unit` and `B = Bool`, two repair maps and two replication maps, in which the whole
  loop closes and each point is identified with Rosen's inverse evaluation at that point.

The split is the one in `Replication.lean` and `Closure.lean`: the claim holds under a
restricted reading of the hom-sets and fails under the full function space.
-/

namespace RelationalLaws.Loop

variable {A B : Type}

/-- A closed (M,R)-cell in Louie's sense. `Rep` and `Repl` are the admissible repair and
replication maps. `ι` identifies points of `B` with replication maps: it is a bijection onto
`Repl`, and each `ι b` is the inverse of evaluation at `b` on admissible repairs. -/
structure Cell (A B : Type) where
  Rep : (B → A → B) → Prop
  Repl : ((A → B) → B → A → B) → Prop
  ι : B → ((A → B) → B → A → B)
  ι_mem : ∀ b, Repl (ι b)
  ι_inj : ∀ b c, ι b = ι c → b = c
  ι_onto : ∀ β, Repl β → ∃ b, ι b = β
  ι_inverts : ∀ b Φ, Rep Φ → ι b (Φ b) = Φ

/-- Cantor: with `A` nonempty and two points in `B`, no map from `B` reaches every
map `H(A,B) → H(B,H(A,B))`. -/
theorem no_surjection_full (a₀ : A) (b₁ b₂ : B) (h12 : b₁ ≠ b₂)
    (ι : B → ((A → B) → B → A → B)) : ¬ ∀ β, ∃ b, ι b = β := by
  classical
  intro honto
  -- swap moves every point of B to a different one
  let swap : B → B := fun y => if y = b₁ then b₂ else b₁
  have hswap : ∀ y, swap y ≠ y := by
    intro y
    by_cases hy : y = b₁
    · simp only [swap, if_pos hy]; rw [hy]; exact fun h => h12 h.symm
    · simp only [swap, if_neg hy]; exact fun h => hy h.symm
  -- the diagonal map differs from ι b on the constant metabolism with value b
  let d : (A → B) → B → A → B := fun f x a => swap (ι (f a₀) f x a)
  obtain ⟨b, hb⟩ := honto d
  have := congrFun (congrFun (congrFun hb (fun _ => b)) b) a₀
  exact hswap _ this.symm

/-- Under the full reading (every map is a replication map), no closed cell exists. -/
theorem no_identification_full (a₀ : A) (b₁ b₂ : B) (h12 : b₁ ≠ b₂) (c : Cell A B)
    (hfull : ∀ β, c.Repl β) : False :=
  no_surjection_full a₀ b₁ b₂ h12 c.ι (fun β => c.ι_onto β (hfull β))

/-! ### A closed cell on two points -/

/-- The metabolism with output `t`. -/
def m (t : Bool) : Unit → Bool := fun _ => t

/-- Repair that rebuilds the metabolism matching its input. -/
def idR : Bool → Unit → Bool := fun b => m b

/-- Repair that rebuilds the metabolism opposite to its input. -/
def notR : Bool → Unit → Bool := fun b => m (!b)

/-- Rosen's replication at `b`: the inverse of evaluation at `b` on `{idR, notR}`. -/
def βAt (b : Bool) : (Unit → Bool) → Bool → Unit → Bool :=
  fun f => if f () = b then idR else notR

theorem idR_ne_notR : idR ≠ notR := by
  intro h
  have := congrFun (congrFun h true) ()
  simp [idR, notR, m] at this

/-- The cell: repairs `{idR, notR}`, replication maps `{βAt true, βAt false}`, and each point
identified with the replication map at that point. -/
def boolCell : Cell Unit Bool where
  Rep Φ := Φ = idR ∨ Φ = notR
  Repl β := ∃ b, β = βAt b
  ι := βAt
  ι_mem b := ⟨b, rfl⟩
  ι_inj b c h := by
    have := congrFun h (m b)
    cases b <;> cases c <;> simp [βAt, m] at this <;> first | rfl | exact absurd this idR_ne_notR | exact absurd this.symm idR_ne_notR
  ι_onto _ := fun ⟨b, hb⟩ => ⟨b, hb.symm⟩
  ι_inverts b Φ hΦ := by
    rcases hΦ with rfl | rfl <;> cases b <;> simp [βAt, idR, notR, m]

/-- The loop closes in `boolCell`: from `a = ()`, metabolism `f` entails `b`, repair `Φ`
entails `f`, and `b`, identified with its replication map, entails `Φ`. -/
theorem boolCell_closes :
    ∃ (a : Unit) (b : Bool) (f : Unit → Bool) (Φ : Bool → Unit → Bool),
      boolCell.Rep Φ ∧ f a = b ∧ Φ b = f ∧ boolCell.ι b f = Φ :=
  ⟨(), true, m true, idR, Or.inl rfl, rfl, rfl, by simp [boolCell, βAt, m]⟩

/-- `boolCell` is not the full reading: `B` has two points and `A` is nonempty, so by
`no_identification_full` some replication map must be left out. -/
theorem boolCell_restricted : ¬ ∀ β, boolCell.Repl β :=
  fun hfull => no_identification_full () true false (by decide) boolCell hfull

end RelationalLaws.Loop
