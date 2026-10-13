import HolomorphicAnosov.Analysis.BoundedContinuousInvariantSections
import HolomorphicAnosov.Analysis.Complex.LeblInjectiveHolomorphicBiholomorphism
import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Regularity.AmbientJourneRegularity
import HolomorphicAnosov.Analysis.SeparatelyHolomorphicSmooth
import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.BiholomorphToReal
import HolomorphicAnosov.Geometry.ComplexHolomorphicCompatibility
import HolomorphicAnosov.Geometry.ComplexTangent
import HolomorphicAnosov.Geometry.SmoothComplexBundleHermitianMetric
import HolomorphicAnosov.Paper.Ghys.ActualInvariantSectionFlowboxCoverG5
import HolomorphicAnosov.Paper.Ghys.StableHolonomyHolomorphic
import HolomorphicAnosov.Paper.Zhang.ComplexManifold
import HolomorphicAnosov.Paper.Zhang.Anosov
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ComplexTangentRankOne
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicTangentSubbundle

import HolomorphicAnosov.Analysis.Complex.ComplexLinearDifferentialOfSplitting

namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- The actual real derivative becomes a complex derivative with the exact
unstable kernel. Source: the scalar-restriction criterion in Demailly I §3.C,
p.23, and step 7 below. The preceding decomposition constructs the complex
operator with IDENTICAL underlying real map. Mathlib's reverse scalar-restriction
criterion then proves complex differentiability of the SAME function at the SAME
point. Injectivity on the stable summand identifies its kernel with U by the
original direct-sum decomposition; the exhibited stable vector makes it nonzero.
These are intermediate differential inputs, not new Anosov hypotheses. -/
theorem complexDerivativeOfRealSplitting
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    {q : E → ℂ} {x : E} (L : E →L[ℝ] ℂ) (hq : HasFDerivAt q L x)
    (S U : Submodule ℂ E) (hSU : IsCompl S U)
    (hU : ∀ v ∈ U, L v = 0)
    (hS : ∀ c : ℂ, ∀ v ∈ S, L (c • v) = c • L v)
    (hSinj : ∀ v ∈ S, L v = 0 → v = 0)
    (hSnonzero : ∃ v ∈ S, L v ≠ 0) :
    HasFDerivAt q (fderiv ℂ q x) x ∧
      LinearMap.ker (fderiv ℂ q x).toLinearMap = U ∧ fderiv ℂ q x ≠ 0 := by
  obtain ⟨K, hK⟩ := complexLinearDifferentialOfSplitting S U hSU L hU hS
  have hcx : HasFDerivAt q K x := hasFDerivAt_of_restrictScalars ℝ hq hK
  have hpoint : ∀ v, K v = L v := fun v ↦ congrArg
    (fun T : E →L[ℝ] ℂ ↦ T v) hK
  rw [hcx.fderiv]
  refine ⟨hcx, ?_, ?_⟩
  · apply le_antisymm
    · intro v hv
      have hall : v ∈ S ⊔ U := by rw [hSU.sup_eq_top]; trivial
      obtain ⟨s, hs, u, hu, hsum⟩ := Submodule.mem_sup.mp hall
      have hLv : L v = 0 := (hpoint v).symm.trans hv
      have hs0 : L s = 0 := by
        rw [← hsum, map_add, hU u hu, add_zero] at hLv
        exact hLv
      rw [hSinj s hs hs0, zero_add] at hsum
      exact hsum ▸ hu
    · intro v hv
      change K v = 0
      exact (hpoint v).trans (hU v hv)
  · obtain ⟨v, _, hv⟩ := hSnonzero
    intro hz
    apply hv
    rw [← hpoint, hz]
    rfl




end HolomorphicAnosov
