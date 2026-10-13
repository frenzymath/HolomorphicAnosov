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


namespace HolomorphicAnosov

universe u
open scoped Manifold ContDiff

attribute [local instance] complex_isManifold_real

/-- Step 7's Cauchy–Riemann calculation on the actual complementary complex
summands. Source: Demailly I §3.B–C, pp.22–24; this is the explicit derivative
calculation in the ambient implication recorded below. A real continuous linear
map which vanishes on the unstable summand and is complex-linear on the stable
summand is complex-linear on the entire original vector space. Decompose each
vector as s+u; both summands are stable under complex multiplication, so the
unstable contributions vanish before and after multiplication. No choice of
coordinates, replacement topology, or ambient differentiability is asserted. -/
theorem complexLinearDifferentialOfSplitting
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (S U : Submodule ℂ E) (hSU : IsCompl S U) (L : E →L[ℝ] ℂ)
    (hU : ∀ v ∈ U, L v = 0)
    (hS : ∀ c : ℂ, ∀ v ∈ S, L (c • v) = c • L v) :
    ∃ K : E →L[ℂ] ℂ, K.restrictScalars ℝ = L := by
  have hlinear : ∀ (c : ℂ) (v : E), L (c • v) = c • L v := by
    intro c v
    have hv : v ∈ S ⊔ U := by rw [hSU.sup_eq_top]; trivial
    obtain ⟨s, hs, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [smul_add, map_add, map_add, hS c s hs, hU u hu,
      hU (c • u) (U.smul_mem c hu)]
    simp
  let K : E →L[ℂ] ℂ :=
    { toFun := L
      map_add' := L.map_add
      map_smul' := hlinear
      cont := L.continuous }
  exact ⟨K, rfl⟩




end HolomorphicAnosov
