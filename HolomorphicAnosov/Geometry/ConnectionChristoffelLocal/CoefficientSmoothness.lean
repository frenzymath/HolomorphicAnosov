import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.MaximalAtlasRestriction
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ChartSource
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.Coefficients
import HolomorphicAnosov.Geometry.ConnectionChristoffelLocal.ExtendedCoefficients
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
/-- The prototype Christoffel coefficients are smooth on the chart source. (Andrews, Prop. 8.3.1) -/
theorem extendedLocalChristoffel_contMDiffOn (nabla : SmoothAffineConnection E M) {n : ℕ}
    (b : Basis (Fin n) ℝ E) (c : OpenPartialHomeomorph M E)
    (hc : c ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (i j k : Fin n) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (extendedLocalChristoffel nabla b c hc i j k) c.source := by
  classical
  intro p hp
  have hs : Nonempty (chartSource c) := ⟨⟨p, hp⟩⟩
  have hsource : (c.subtypeRestr hs).source = univ := by
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext q
    exact iff_of_true q.property (mem_univ q)
  have hd := (Classical.choose_spec
    (((isSmoothAffineConnectionOperator_iff_christoffel nabla.cov).mp nabla.laws).2
      (chartSource c) n b (c.subtypeRestr hs)
      (HolomorphicAnosov.maximalAtlas_subtypeRestr c hc (chartSource c) hs))).1 i j k
  change ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (localChristoffel nabla b c hc hs i j k)
    (c.subtypeRestr hs).source at hd
  rw [hsource, contMDiffOn_univ] at hd
  have heq : (fun q : chartSource c ↦ extendedLocalChristoffel nabla b c hc i j k q) =
      localChristoffel nabla b c hc hs i j k := by
    funext q
    unfold extendedLocalChristoffel
    split
    · rfl
    · rename_i hn
      exact False.elim (hn q.property)
  have hAt : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (fun q : chartSource c ↦ extendedLocalChristoffel nabla b c hc i j k q) ⟨p, hp⟩ := by
    rw [heq]
    exact hd.contMDiffAt
  exact ((contMDiffAt_subtype_iff (U := chartSource c) (x := ⟨p, hp⟩)).mp hAt).contMDiffWithinAt

end ConnectionChristoffelLocal
end
end HolomorphicAnosov
