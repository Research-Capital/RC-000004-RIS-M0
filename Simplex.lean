import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Two affine images of the standard simplex

The coordinate function has length n+1. Index 0 denotes the paper's first
coordinate. 'Fin.snoc' exposes the last coordinate and 'Fin.cons' exposes
the first coordinate. Both leave the intervening coordinates in order.
-/

namespace ResearchCapital.Simplex

open scoped BigOperators

variable {n : ℕ}

/-- The solid standard simplex in dimension n+1. -/
def simplex (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ 1}

/-- The functional whose level 1 cuts the simplex. -/
def cut (x : Fin (n + 1) → ℝ) : ℝ :=
  x 0 + ∑ i, x i

/-- The two affine maps in the paper. The Boolean chooses which half to use. -/
noncomputable def affinePiece (upper : Bool) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (x (Fin.last n) / 2 + if upper then 1 - ∑ i, x i else 0)
    (fun i : Fin n => x i.castSucc)

/-- The closed half-simplex specified by the cut. -/
def half (n : ℕ) (upper : Bool) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ simplex n ∧ if upper then 1 ≤ cut x else cut x ≤ 1}

private theorem mem_simplex_cons (a : ℝ) (u : Fin n → ℝ) :
    Fin.cons a u ∈ simplex n ↔
      0 ≤ a ∧ (∀ i, 0 ≤ u i) ∧ a + ∑ i, u i ≤ 1 := by
  simp only [simplex, Set.mem_setOf_eq, Fin.sum_cons, Fin.forall_fin_succ,
    Fin.cons_zero, Fin.cons_succ]
  tauto

private theorem mem_simplex_snoc (u : Fin n → ℝ) (t : ℝ) :
    Fin.snoc u t ∈ simplex n ↔
      0 ≤ t ∧ (∀ i, 0 ≤ u i) ∧ (∑ i, u i) + t ≤ 1 := by
  simp only [simplex, Set.mem_setOf_eq, Fin.sum_snoc, Fin.forall_fin_succ',
    Fin.snoc_last, Fin.snoc_castSucc]
  tauto

/-- Exact image identity for each of the two maps, in every dimension. -/
theorem image_eq_half (upper : Bool) :
    affinePiece upper '' simplex n = half n upper := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    let u : Fin n → ℝ := fun i => y i.castSucc
    let t := y (Fin.last n)
    have hsum : (∑ i, y i) = (∑ i, u i) + t := Fin.sum_univ_castSucc y
    have ht := hy.1 (Fin.last n)
    have hu : ∀ i, 0 ≤ u i := fun i => hy.1 i.castSucc
    have htotal := hy.2
    rw [hsum] at htotal
    cases upper <;>
      simp only [half, Set.mem_setOf_eq, affinePiece, cut, Fin.cons_zero,
        Fin.sum_cons, Bool.false_eq_true, ↓reduceIte, hsum, mem_simplex_cons] <;>
      refine ⟨⟨?_, hu, ?_⟩, ?_⟩ <;> linarith
  · intro hx
    let u : Fin n → ℝ := fun i => x i.succ
    let a := x 0
    have hx' : Fin.cons a u = x := Fin.cons_self_tail x
    have hxu : Fin.cons a u ∈ simplex n := hx' ▸ hx.1
    obtain ⟨ha, hu, htotal⟩ := (mem_simplex_cons a u).mp hxu
    have hcut : cut x = a + (a + ∑ i, u i) := by
      simp only [cut, Fin.sum_univ_succ, a, u]
    cases upper
    · have hl : cut x ≤ 1 := hx.2
      rw [hcut] at hl
      refine ⟨Fin.snoc u (2 * a), (mem_simplex_snoc _ _).2 ⟨by linarith, hu, by linarith⟩, ?_⟩
      rw [← hx']
      simp only [affinePiece, Fin.snoc_last, Fin.snoc_castSucc, Bool.false_eq_true,
        ↓reduceIte, add_zero]
      congr 1
      linarith
    · have hr : 1 ≤ cut x := hx.2
      rw [hcut] at hr
      refine ⟨Fin.snoc u (2 * (1 - (a + ∑ i, u i))),
        (mem_simplex_snoc _ _).2 ⟨by linarith, hu, by linarith⟩, ?_⟩
      rw [← hx']
      simp only [affinePiece, Fin.snoc_last, Fin.snoc_castSucc, Fin.sum_snoc, ↓reduceIte]
      congr 1
      linarith

/-- The simplex is invariant under the union of the two affine images. -/
theorem image_union :
    (affinePiece false '' simplex n) ∪ (affinePiece true '' simplex n) = simplex n := by
  rw [image_eq_half, image_eq_half]
  ext x
  change ((x ∈ simplex n ∧ cut x ≤ 1) ∨ (x ∈ simplex n ∧ 1 ≤ cut x)) ↔ x ∈ simplex n
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    exact (le_total (cut x) 1).imp (And.intro h) (And.intro h)

/-- The two images meet exactly on the cutting face. -/
theorem image_inter :
    (affinePiece false '' simplex n) ∩ (affinePiece true '' simplex n) =
      {x ∈ simplex n | cut x = 1} := by
  rw [image_eq_half, image_eq_half]
  ext x
  change ((x ∈ simplex n ∧ cut x ≤ 1) ∧ (x ∈ simplex n ∧ 1 ≤ cut x)) ↔
    (x ∈ simplex n ∧ cut x = 1)
  constructor
  · exact fun h => ⟨h.1.1, le_antisymm h.1.2 h.2.2⟩
  · rintro ⟨h, he⟩
    exact ⟨⟨h, he.le⟩, ⟨h, he.ge⟩⟩

#print axioms image_eq_half
#print axioms image_union
#print axioms image_inter

end ResearchCapital.Simplex
