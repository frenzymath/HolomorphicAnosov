import HolomorphicAnosov.Geometry.ComplexProjectiveLine
import Mathlib.LinearAlgebra.Projectivization.Action
import HolomorphicAnosov.Analysis.Complex.ProjectiveDeveloping.Helpers.ProjectiveFiniteRange

/-!
# The range of a projective transform of a complete affine coordinate

Source: Ghys, *Holomorphic Anosov systems*, §5, p.597. A complete affine
coordinate develops onto the projective line minus the image of infinity.
-/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys

/-- A projective affine expression over a surjective coordinate omits transformed infinity.
Source: Ghys §5 p.597.

Proof: finite coordinates never equal infinity, and the action of `g` is injective,
so the displayed range omits `g • infinity`. Conversely, apply `g⁻¹` to any other
point. It differs from infinity and hence has a finite coordinate `z`; surjectivity
of `a` supplies `x` with `a x = z`. Applying `g` recovers the chosen point. -/
theorem developing_projective_affine_range {L : Type*} (a : L → ℂ)
    (ha : Function.Surjective a) (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ) :
    Set.range (fun x ↦ g • complexProjectiveLineFinite (a x)) =
      {g • complexProjectiveLineInfinity}ᶜ := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩ h
    exact developing_finite_ne_infinity (a x) ((MulAction.injective g) h)
  · intro hp
    have hpre : g⁻¹ • p ∈ Set.range complexProjectiveLineFinite := by
      rw [developing_finite_range]
      intro h
      apply hp
      have := congrArg (fun q : ComplexProjectiveLine ↦ g • q) h
      simpa using this
    obtain ⟨z, hz⟩ := hpre
    obtain ⟨x, rfl⟩ := ha z
    refine ⟨x, ?_⟩
    change g • complexProjectiveLineFinite (a x) = p
    rw [hz, smul_inv_smul]


end HolomorphicAnosov.Ghys
