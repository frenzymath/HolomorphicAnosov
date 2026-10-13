import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Module.Submodule.Lattice

namespace HolomorphicAnosov

open Set Bundle
open scoped ContDiff Manifold _root_.Topology Bundle

section NormalizedFunctional
variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- On complementary fibres the form is injective on the stable summand.

Source: Zhang Lemma 4.3 p.15, normalized stable section; the elementary
complementary-kernel argument uses `Submodule.disjoint_def` in Mathlib
`Algebra/Module/Submodule/Lattice.lean`.
-/
theorem form_injective_on (S U : Submodule ℂ E) (θ : E →L[ℂ] ℂ)
    (hcompl : IsCompl S U) (hker : LinearMap.ker θ.toLinearMap = U) :
    Set.InjOn θ S := by
  intro v hv w hw heq
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp hcompl.disjoint (v - w) (S.sub_mem hv hw)
  rw [← hker]
  change θ (v - w) = 0
  simp [heq]

/-- The normalized vector exists uniquely, using only rank and complementarity.

Source: Zhang Lemma 4.3 p.15, stable-line normalization; Mathlib
`LinearAlgebra/Dimension/Finite.lean` (`Module.finrank_pos_iff_exists_ne_zero`)
supplies the nonzero vector, and complex inverse scaling gives normalization.
-/
theorem normalized_exists_unique (S U : Submodule ℂ E) [FiniteDimensional ℂ S]
    (θ : E →L[ℂ] ℂ) (hcompl : IsCompl S U)
    (hker : LinearMap.ker θ.toLinearMap = U) (hrank : Module.finrank ℂ S = 1) :
    ∃! e : E, e ∈ S ∧ θ e = 1 := by
  obtain ⟨v, hv⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℂ) (M := S)).mp
    (by rw [hrank]; decide)
  have hθv : θ (v : E) ≠ 0 := by
    intro h
    have hval : (v : E) = 0 := form_injective_on S U θ hcompl hker v.property
      (S.zero_mem) (by simpa using h)
    exact hv (Subtype.ext hval)
  refine ⟨(θ (v : E))⁻¹ • (v : E), ⟨S.smul_mem _ v.property, ?_⟩, ?_⟩
  · simp [hθv]
  · intro w hw
    apply form_injective_on S U θ hcompl hker hw.1 (S.smul_mem _ v.property)
    simpa [hθv] using hw.2




end NormalizedFunctional

end HolomorphicAnosov
