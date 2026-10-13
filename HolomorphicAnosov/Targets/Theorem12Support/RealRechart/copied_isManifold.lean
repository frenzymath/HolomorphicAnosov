import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.copiedCharts
import HolomorphicAnosov.Targets.Theorem12Support.RealRechart.Recharted
import Mathlib.Geometry.Manifold.IsManifold.Basic

/-! Postcomposing a smooth real atlas with a continuous linear equivalence gives a smooth atlas on
the type copy. (Zhang, §3, p. 11) -/

open scoped ContDiff Manifold Topology _root_.Topology
open Set
namespace HolomorphicAnosov.Theorem12SupportW2
noncomputable section
universe u

variable {d n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X]
  (B : ComplexModel d ≃L[ℝ] EuclideanSpace ℝ (Fin n))

/-- The atlas on `Recharted X` obtained by postcomposing the charts with `B` is smooth when the
original real atlas is smooth. (Zhang, §3, p. 11) -/
theorem copied_isManifold [IsManifold (realModel d) ∞ X] :
    letI := copiedCharts (X := X) B
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (Recharted X) := by
  let := copiedCharts (X := X) B
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨c, hc, rfl⟩
  rcases he' with ⟨c', hc', rfl⟩
  have h := (mem_groupoid_of_pregroupoid.mp
    ((contDiffGroupoid ∞ (realModel d)).compatible hc hc')).1
  have h0 : ContDiffOn ℝ ∞ (c.symm ≫ₕ c') (c.symm ≫ₕ c').source := by
    simpa only [contDiffPregroupoid, mfld_simps] using h
  have hcomp := B.contDiff.comp_contDiffOn
    (h0.comp B.symm.contDiff.contDiffOn (s := B.symm ⁻¹' (c.symm ≫ₕ c').source)
      (by intro z hz; exact hz))
  simp only [mfld_simps]
  convert hcomp using 1
  · rfl
  · ext z
    rfl


end
end HolomorphicAnosov.Theorem12SupportW2

