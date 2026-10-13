import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ChartSource
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ExtendedCoefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Bilinear
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.FullSourceTransition
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.SelectedRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.RestrictedTransitionGerm
import HolomorphicAnosov.Geometry.SmoothAffineConnection
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorField.Pullback
open Set Bundle IsManifold Module TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
namespace ConnectionChristoffelLocal
/-- This is the Christoffel transition formula for source-local selected coefficients. (Andrews, Exercise 8.3.2) -/
theorem localCoefficientBilinear_transition (nabla : SmoothAffineConnection E M)
    {n m : ℕ} (b : Basis (Fin n) ℝ E) (d : Basis (Fin m) ℝ E)
    (c c' : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (hc' : c' ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (p : M) (hp : p ∈ c.source) (hp' : p ∈ c'.source) (u v : E) :
    let h := c' ∘ c.symm
    coefficientBilinear d (extendedLocalChristoffel nabla d c' hc') p (fderiv ℝ h (c p) u) (fderiv ℝ h (c p) v) =
      fderiv ℝ h (c p) (coefficientBilinear b (extendedLocalChristoffel nabla b c hc) p u v) -
        fderiv ℝ (fderiv ℝ h) (c p) u v := by
  let W : Opens M := chartSource c ⊓ chartSource c'
  let pW : W := ⟨p, hp, hp'⟩
  have hW : Nonempty W := ⟨pW⟩
  let cW := c.subtypeRestr hW
  let cW' := c'.subtypeRestr hW
  have hcW := HolomorphicAnosov.maximalAtlas_subtypeRestr c hc W hW
  have hcW' := HolomorphicAnosov.maximalAtlas_subtypeRestr c' hc' W hW
  have hfull : cW.source = univ := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext q
    exact iff_of_true q.property.1 (mem_univ q)
  have hfull' : cW'.source = univ := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext q
    exact iff_of_true q.property.2 (mem_univ q)
  obtain ⟨Γ, _, hΓ⟩ :=
    ((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2 W n b cW hcW
  obtain ⟨Δ, _, hΔ⟩ :=
    ((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2 W m d cW' hcW'
  have hco (i j k : Fin n) : extendedLocalChristoffel nabla b c hc i j k p = Γ i j k pW :=
    extendedLocalChristoffel_eq_restricted nabla b c hc W hW inf_le_left Γ hΓ i j k pW
  have hco' (i j k : Fin m) : extendedLocalChristoffel nabla d c' hc' i j k p = Δ i j k pW :=
    extendedLocalChristoffel_eq_restricted nabla d c' hc' W hW inf_le_right Δ hΔ i j k pW
  have hb (a z : E) : coefficientBilinear b (extendedLocalChristoffel nabla b c hc) p a z = coefficientBilinear b Γ pW a z := by
    simp only [coefficientBilinear, hco]
  have hb' (a z : E) : coefficientBilinear d (extendedLocalChristoffel nabla d c' hc') p a z = coefficientBilinear d Δ pW a z := by
    simp only [coefficientBilinear, hco']
  have ht := fullSource_christoffel_transition nabla W b d cW cW' hcW hcW' hfull hfull'
    Γ Δ hΓ hΔ pW u v
  have heq : (cW' ∘ cW.symm) =ᶠ[𝓝 (c p)] (c' ∘ c.symm) :=
    restricted_transition_germ W hW c c' pW hp
  have hD : fderiv ℝ (cW' ∘ cW.symm) (c p) = fderiv ℝ (c' ∘ c.symm) (c p) := heq.fderiv_eq
  have hDg : fderiv ℝ (cW' ∘ cW.symm) =ᶠ[𝓝 (c p)] fderiv ℝ (c' ∘ c.symm) :=
    heq.fderiv
  have hDD : fderiv ℝ (fderiv ℝ (cW' ∘ cW.symm)) (c p) =
      fderiv ℝ (fderiv ℝ (c' ∘ c.symm)) (c p) := hDg.fderiv_eq
  dsimp only at ht ⊢
  change coefficientBilinear d Δ pW
      (fderiv ℝ (cW' ∘ cW.symm) (c p) u) (fderiv ℝ (cW' ∘ cW.symm) (c p) v) =
    fderiv ℝ (cW' ∘ cW.symm) (c p) (coefficientBilinear b Γ pW u v) -
      fderiv ℝ (fderiv ℝ (cW' ∘ cW.symm)) (c p) u v at ht
  rw [hD, hDD] at ht
  rw [hb, hb']
  exact ht

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
