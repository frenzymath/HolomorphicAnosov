import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace HolomorphicAnosov.Analysis

/-- A jointly smooth family member whose topological support is compactly contained
in the test-function domain extends by zero to a global smooth compactly supported
function, hence gives a Mathlib test function. -/
theorem testFunction_of_contDiffOn_tsupport_subset
    {m k : ℕ} {U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin m))}
    {P : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin k))}
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : IsCompact K) (hKU : K ⊆ U)
    {H : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) → ℂ}
    (hH : ContDiffOn ℝ ∞ (Function.uncurry H) ((P : Set _) ×ˢ (U : Set _)))
    {p : EuclideanSpace ℝ (Fin k)} (hp : p ∈ P)
    (hSupport : tsupport (H p) ⊆ K) :
    ∃ f : TestFunction U ℂ ⊤, ∀ y, f y = H p y := by
  have hsecU : ContDiffOn ℝ ∞ (H p) (U : Set _) := by
    intro y hy
    have hh := hH (p, y) ⟨hp, hy⟩
    have hc : ContDiff ℝ ∞ (fun y : EuclideanSpace ℝ (Fin m) => (p, y)) := by
      fun_prop
    exact hh.comp y hc.contDiffWithinAt (fun z hz => ⟨hp, hz⟩)
  have hz : EqOn (H p) 0 Kᶜ := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hSupport h))
  have hsecC : ContDiffOn ℝ ∞ (H p) Kᶜ := by
    exact contDiffOn_const.congr hz
  have hun : (U : Set _) ∪ Kᶜ = Set.univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hxu : x ∈ (U : Set _)
    · exact Or.inl hxu
    · exact Or.inr (fun hk => hxu (hKU hk))
  have hglob : ContDiff ℝ ∞ (H p) :=
    contDiff_of_contDiffOn_union_of_isOpen hsecU hsecC hun U.isOpen hK.isClosed.isOpen_compl
  let f : TestFunction U ℂ ⊤ :=
    TestFunction.mk (H p) hglob (HasCompactSupport.intro hK hz) (hSupport.trans hKU)
  exact ⟨f, by intro y; rfl⟩

end HolomorphicAnosov.Analysis
