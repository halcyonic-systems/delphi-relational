/-!
# Closure to efficient causation: two definitions that come apart

Source: A. H. Louie (2012), "Anticipation in (M,R)-systems",
International Journal of General Systems 41(1), 5–22, Sections 3–4, pp. 11–14.

## Encoding

A formal system is a type of processes (mappings) with an entailment relation `E`:
`E g f` says that `g` entails `f`, i.e. `f` is an output of `g` (Louie's hierarchical
composition `g ⊢ f`, eq. 18). This is the graph of diagram (23), `{g ⊢ f, h ⊢ g, f ⊢ h}`.

* A process lies on a *hierarchical cycle* if a closed path of entailment runs through it and
  through at least one other process (Louie: "two or more hierarchical compositions",
  "two or more processes").
* *Complex*: some process lies on a hierarchical cycle (p. 13).
* *Clef*: every process lies on a hierarchical cycle (p. 14, "a clef formal system is one that
  has all its mappings contained in hierarchical cycles").
* *Entailed within*: every process is entailed by some process of the system (p. 13, "its every
  efficient cause is entailed within the system").

On p. 13 Louie gives "entailed within" as the definition of closed to efficient causation and
calls "all processes in hierarchical cycles" equivalent, adding that the equivalence lets the
term be used on formal systems. On a fixed formal system the two are not equivalent:

* `clef_entailedWithin`: clef implies entailed within.
* `entailedWithin_not_clef`: the converse fails (a three-process counterexample).

Louie's claim that clef systems are a proper subset of complex systems (p. 13) then depends on
which definition is used:

* Clef reading: `clef_complex` and `complex_not_clef` prove it.
* Entailed-within reading: it fails for one self-entailing process (`selfEntailment`) and for an
  infinite regress (`regress`), and holds again for finite systems in which no process entails
  itself (`entailedWithin_complex_of_finite`).

So finiteness and the absence of self-entailment are exactly what the weaker definition needs.
The theorems are about formal systems; none of them says which systems organisms are.
-/

namespace RelationalLaws.Closure

open Relation

variable {α : Type}

/-- Process `f` lies on a hierarchical cycle: a closed path of entailment through `f` and
some other process `g`. -/
def OnCycle (E : α → α → Prop) (f : α) : Prop :=
  ∃ g, g ≠ f ∧ TransGen E f g ∧ TransGen E g f

/-- Complex: some process lies on a hierarchical cycle. -/
def Complex (E : α → α → Prop) : Prop := ∃ f, OnCycle E f

/-- Clef: every process lies on a hierarchical cycle. -/
def Clef (E : α → α → Prop) : Prop := ∀ f, OnCycle E f

/-- Entailed within: every process is entailed by some process of the system. -/
def EntailedWithin (E : α → α → Prop) : Prop := ∀ f, ∃ g, E g f

/-! ### Two path lemmas -/

/-- A path that ends at `b` has a last step into `b`. -/
theorem last_step {E : α → α → Prop} {a b : α} (h : TransGen E a b) :
    ∃ c, E c b := by
  cases h with
  | single h => exact ⟨_, h⟩
  | tail _ h => exact ⟨_, h⟩

/-- A path that starts at `a` has a first step out of `a`. -/
theorem first_step {E : α → α → Prop} {a b : α} (h : TransGen E a b) :
    ∃ c, E a c := by
  induction h with
  | single h => exact ⟨_, h⟩
  | tail _ _ ih => exact ih

/-! ### The two definitions -/

/-- Clef implies entailed within. -/
theorem clef_entailedWithin (E : α → α → Prop) (h : Clef E) : EntailedWithin E := by
  intro f
  obtain ⟨_, _, _, hgf⟩ := h f
  exact last_step hgf

/-- Three processes: `f` and `g` entail each other, and `f` also entails `h`. -/
inductive P3 | f | g | h
  deriving DecidableEq

/-- Entailment for `P3`: f ⊢ g, g ⊢ f, f ⊢ h. -/
def E3 : P3 → P3 → Prop
  | .f, .g | .g, .f | .f, .h => True
  | _, _ => False

/-- Entailed within does not imply clef: in `E3` every process is entailed, but `h` entails
nothing, so no cycle runs through it. Louie's "equivalently" fails on a fixed formal system. -/
theorem entailedWithin_not_clef : EntailedWithin E3 ∧ ¬ Clef E3 := by
  refine ⟨fun x => ?_, fun hc => ?_⟩
  · cases x
    · exact ⟨.g, trivial⟩
    · exact ⟨.f, trivial⟩
    · exact ⟨.f, trivial⟩
  · obtain ⟨_, _, hhg, _⟩ := hc .h
    obtain ⟨c, hc⟩ := first_step hhg
    cases c <;> exact hc

/-! ### Claim louie2012-08, clef reading: clef is a proper subset of complex -/

/-- Clef implies complex, for any system with at least one process. -/
theorem clef_complex (E : α → α → Prop) (h : Clef E) (x : α) : Complex E :=
  ⟨x, h x⟩

/-- Entailment for a complex system that is not clef: f ⊢ g, g ⊢ f, h ⊢ f.
Nothing entails `h`. -/
def E3' : P3 → P3 → Prop
  | .f, .g | .g, .f | .h, .f => True
  | _, _ => False

/-- Complex does not imply clef: `f` and `g` form a cycle, `h` lies on none. -/
theorem complex_not_clef : Complex E3' ∧ ¬ Clef E3' := by
  refine ⟨⟨.f, .g, by decide, .single trivial, .single trivial⟩, fun hc => ?_⟩
  obtain ⟨_, _, _, hgh⟩ := hc .h
  obtain ⟨c, hc⟩ := last_step hgh
  cases c <;> exact hc

/-! ### Claim louie2012-08, entailed-within reading: fails, then holds for finite systems -/

/-- One process that entails itself is entailed within but not complex: a hierarchical
cycle needs a second process. -/
theorem selfEntailment : EntailedWithin (fun (_ _ : Unit) => True) ∧
    ¬ Complex (fun (_ _ : Unit) => True) :=
  ⟨fun _ => ⟨(), trivial⟩, fun ⟨_, _, hne, _⟩ => hne rfl⟩

/-- An infinite regress (process `n + 1` entails process `n`) is entailed within but not
complex: every efficient cause has a cause, and no cycle closes. -/
theorem regress : EntailedWithin (fun m n : Nat => m = n + 1) ∧
    ¬ Complex (fun m n : Nat => m = n + 1) := by
  have down : ∀ {a b : Nat}, TransGen (fun m n : Nat => m = n + 1) a b → b < a := by
    intro a b h
    induction h with
    | single h => omega
    | tail _ h ih => omega
  exact ⟨fun n => ⟨n + 1, rfl⟩, fun ⟨_, _, _, hfg, hgf⟩ => by
    have := down hfg; have := down hgf; omega⟩

/-- Pigeonhole for lists: a list without repeats, all of whose entries occur in `u`,
is no longer than `u`. -/
theorem nodup_length_le [DecidableEq α] :
    ∀ (l u : List α), l.Nodup → (∀ x ∈ l, x ∈ u) → l.length ≤ u.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, u, hn, hs => by
    rw [List.nodup_cons] at hn
    have ha : a ∈ u := hs a (List.mem_cons_self ..)
    have hsub : ∀ x ∈ l, x ∈ u.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun h : x = a => hn.1 (h ▸ hx))).2 (hs x (List.mem_cons_of_mem _ hx))
    have ih := nodup_length_le l (u.erase a) hn.2 hsub
    rw [List.length_erase_of_mem ha] at ih
    have : 0 < u.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- Walk backwards from `x`, always to a chosen entailer. -/
def walk (pred : α → α) (x : α) : Nat → α
  | 0 => x
  | n + 1 => pred (walk pred x n)

/-- The first `n + 1` points of the backward walk, newest first. -/
def walkList (pred : α → α) (x : α) : Nat → List α
  | 0 => [x]
  | n + 1 => walk pred x (n + 1) :: walkList pred x n

theorem mem_walkList {pred : α → α} {x y : α} :
    ∀ {n}, y ∈ walkList pred x n → ∃ i, i ≤ n ∧ walk pred x i = y
  | 0, h => ⟨0, Nat.le_refl _, by simp [walkList] at h; exact h.symm⟩
  | n + 1, h => by
    simp only [walkList, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨n + 1, Nat.le_refl _, h.symm⟩
    · obtain ⟨i, hi, hy⟩ := mem_walkList h
      exact ⟨i, by omega, hy⟩

theorem length_walkList (pred : α → α) (x : α) : ∀ n, (walkList pred x n).length = n + 1
  | 0 => rfl
  | n + 1 => by simp [walkList, length_walkList pred x n]

/-- In a finite system the backward walk revisits a process. -/
theorem walk_repeats [DecidableEq α] (u : List α) (hu : ∀ x, x ∈ u) (pred : α → α) (x : α) :
    ∃ i j, i < j ∧ walk pred x j = walk pred x i := by
  apply Classical.byContradiction
  intro hno
  have hnodup : ∀ n, (walkList pred x n).Nodup := by
    intro n
    induction n with
    | zero => simp [walkList]
    | succ n ih =>
      simp only [walkList, List.nodup_cons]
      refine ⟨fun hm => ?_, ih⟩
      obtain ⟨i, hi, he⟩ := mem_walkList hm
      exact hno ⟨i, n + 1, by omega, he.symm⟩
  have := nodup_length_le _ u (hnodup u.length) (fun y _ => hu y)
  rw [length_walkList] at this
  omega

/-- Each step of the walk is an entailment, so later points entail earlier ones. -/
theorem walk_path {E : α → α → Prop} {pred : α → α} (hp : ∀ y, E (pred y) y) (x : α) :
    ∀ i d, TransGen E (walk pred x (i + d + 1)) (walk pred x i)
  | i, 0 => .single (hp _)
  | i, d + 1 => by
    have h1 : TransGen E (walk pred x (i + (d + 1) + 1)) (walk pred x (i + d + 1)) := by
      rw [show i + (d + 1) + 1 = (i + d + 1) + 1 by omega]
      exact .single (hp _)
    exact h1.trans (walk_path hp x i d)

/-- In a finite system in which no process entails itself, entailed within implies complex.
Finiteness rules out the regress and irreflexivity rules out the lone self-entailer. -/
theorem entailedWithin_complex_of_finite (E : α → α → Prop) (u : List α) (hu : ∀ x, x ∈ u)
    (hirr : ∀ f, ¬ E f f) (h : EntailedWithin E) (x : α) : Complex E := by
  classical
  let pred : α → α := fun y => Classical.choose (h y)
  have hp : ∀ y, E (pred y) y := fun y => Classical.choose_spec (h y)
  obtain ⟨i, j, hij, hji⟩ := walk_repeats u hu pred x
  -- The walk cannot repeat after one step: that step would be a self-entailment.
  have hne : walk pred x (i + 1) ≠ walk pred x i := fun he => by
    have := hp (walk pred x i)
    simp only [walk] at he
    rw [he] at this
    exact hirr _ this
  have hj : i + 1 < j := by
    rcases Nat.lt_or_eq_of_le hij with h' | h'
    · exact h'
    · subst h'
      exact absurd hji hne
  refine ⟨walk pred x i, walk pred x (i + 1), hne, ?_, .single (hp _)⟩
  obtain ⟨d, rfl⟩ : ∃ d, j = (i + 1) + d + 1 := ⟨j - i - 2, by omega⟩
  rw [← hji]
  exact walk_path hp x (i + 1) d

end RelationalLaws.Closure
