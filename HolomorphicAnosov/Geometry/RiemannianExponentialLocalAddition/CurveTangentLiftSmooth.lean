import HolomorphicAnosov.Geometry.ConnectionGeodesicSpray
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-! The tangent lift of a smooth curve is smooth on its open time domain. -/

open Set Bundle TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology

namespace HolomorphicAnosov

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] [T2Space M] in
set_option backward.isDefEq.respectTransparency false in
/-- The tangent lift of a smooth curve is smooth on its open time domain. -/
lemma curveTangentLift_contMDiffOn {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ J) :
    ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, E)).tangent ∞ (curveTangentLift (E := E) γ) J := by
  have hk : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
      (fun t : ℝ ↦ (⟨t, (tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
    apply contMDiff_vectorSpace_iff_contDiff.mpr
    change ContDiff ℝ ∞ (fun _ : ℝ ↦ (1 : ℝ))
    exact contDiff_const
  have ht := hγ.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (hJ.uniqueMDiffOn (I := 𝓘(ℝ, ℝ)))
  have hc := ht.comp hk.contMDiffOn (fun t ht ↦ ht)
  apply hc.congr
  intro t ht
  have heq := tangentMapWithin_eq_tangentMap
    (p := (⟨t, (tangentSpaceCastModel 𝓘(ℝ, ℝ) t).symm 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ))
    (hJ.uniqueMDiffWithinAt (I := 𝓘(ℝ, ℝ)) ht)
    (((hγ t ht).contMDiffAt (hJ.mem_nhds ht)).mdifferentiableAt (by simp))
  simpa [curveTangentLift, curveVelocity, tangentMap,
    tangentSpaceCastModel] using heq.symm

end
end HolomorphicAnosov
