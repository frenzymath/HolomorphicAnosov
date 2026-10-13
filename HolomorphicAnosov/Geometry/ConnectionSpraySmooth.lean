import HolomorphicAnosov.Geometry.ConnectionTangentChartInvertibleOn
import HolomorphicAnosov.Geometry.ConnectionTangentChartSmooth
import HolomorphicAnosov.Geometry.ConnectionSprayCoordinateRegularity
import Mathlib.Geometry.Manifold.VectorField.Pullback

/-!
Smoothness of vector fields with the connection spray coordinate formula. (Lee, Lemma 4.2,
pp.83–84; Andrews, p.84)
-/

open Set Bundle TopologicalSpace Module IsManifold
open scoped Manifold ContDiff Topology _root_.Topology
namespace HolomorphicAnosov
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every vector field satisfying the connection spray coordinate formula is smooth. (Lee, Lemma
4.2, pp.83–84; Andrews, p.84) -/
theorem HasConnectionSprayCoordinates.contMDiff
    (nabla : SmoothAffineConnection E M)
    {G : (z : TangentBundle 𝓘(ℝ, E) M) → TangentSpace (𝓘(ℝ, E)).tangent z}
    (hG : HasConnectionSprayCoordinates nabla G) :
    ContMDiff (𝓘(ℝ, E)).tangent ((𝓘(ℝ, E)).tangent).tangent ∞
      (fun z ↦ (⟨z, G z⟩ : TangentBundle (𝓘(ℝ, E)).tangent
        (TangentBundle 𝓘(ℝ, E) M))) := by
  intro z
  let b := Module.finBasis ℝ E
  let c := chartAt E (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  have hc := chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞)
    (⟨z.proj, mem_univ z.proj⟩ : ConnectionWhole M)
  let V (q : E × E) : TangentSpace 𝓘(ℝ, E × E) q :=
    (tangentSpaceCastModel 𝓘(ℝ, E × E) q).symm
      (q.2, -connectionChristoffelBilinear nabla b c hc (connectionChartInverse c q.1) q.2 q.2)
  have hV : ContMDiffAt 𝓘(ℝ, E × E) (𝓘(ℝ, E × E)).tangent ∞
      (fun q ↦ (⟨q, V q⟩ : TangentBundle 𝓘(ℝ, E × E) (E × E)))
      (connectionTangentChart c z) := by
    apply contMDiffAt_vectorSpace_iff_contDiffAt.mpr
    exact (connectionSprayCoordinate_contDiffOn nabla b c hc).contDiffAt
      ((c.open_target.prod isOpen_univ).mem_nhds ⟨c.map_source (mem_chart_source E _), mem_univ _⟩)
  let W := VectorField.mpullback (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E)
    (connectionTangentChart c) V
  have hW := hV.mpullback_vectorField_preimage
    (connectionTangentChart_chartAt_contMDiffAt z)
    (connectionTangentChart_chartAt_mfderiv_isInvertible z) (by simp)
  have hEq : (fun w ↦ (⟨w, G w⟩ : TangentBundle (𝓘(ℝ, E)).tangent
      (TangentBundle 𝓘(ℝ, E) M))) =ᶠ[𝓝 z]
      (fun w ↦ (⟨w, W w⟩ : TangentBundle (𝓘(ℝ, E)).tangent
        (TangentBundle 𝓘(ℝ, E) M))) := by
    filter_upwards [(FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.preimage_mem_nhds
      ((chartAt E z.proj).open_source.mem_nhds (mem_chart_source E z.proj))] with w hw
    have hwc : (⟨w.proj, mem_univ w.proj⟩ : ConnectionWhole M) ∈ c.source := by
      simpa only [c, TopologicalSpace.Opens.chartAt_eq,
        OpenPartialHomeomorph.subtypeRestr_source, mem_preimage] using hw
    have hcoords := hG (finrank ℝ E) b c hc w hwc
    have hbase : connectionChartInverse c (connectionChartMap c w.proj) = w.proj :=
      congrArg Subtype.val (c.left_inv hwc)
    have hvec : G w = W w := by
      apply (connectionTangentChart_chartAt_mfderiv_isInvertible_of_mem z w hw).injective
      change (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c) w) (G w) =
        (mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c) w)
          ((mfderiv (𝓘(ℝ, E)).tangent 𝓘(ℝ, E × E) (connectionTangentChart c) w).inverse
            (V (connectionTangentChart c w)))
      rw [(connectionTangentChart_chartAt_mfderiv_isInvertible_of_mem z w hw).self_apply_inverse]
      apply (tangentSpaceCastModel 𝓘(ℝ, E × E) (connectionTangentChart c w)).injective
      rw [hcoords]
      dsimp only [V]
      rw [ContinuousLinearEquiv.apply_symm_apply]
      change (_, -connectionChristoffelBilinear nabla b c hc w.proj _ _) =
        (_, -connectionChristoffelBilinear nabla b c hc
          (connectionChartInverse c (connectionChartMap c w.proj)) _ _)
      rw [hbase]
    rw [hvec]
  exact hW.congr_of_eventuallyEq hEq

end
end HolomorphicAnosov

