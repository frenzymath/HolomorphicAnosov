import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundle
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace HolomorphicAnosov.ContinuousRealTangentSubbundle

open scoped ContDiff
open Filter Topology _root_.Topology

universe u
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {X : Type u}
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- The fibre dimension of a continuous real tangent subbundle is locally constant. -/
theorem finrank_isLocallyConstant
    (P : ContinuousRealTangentSubbundle I X) :
    IsLocallyConstant (fun z ↦ Module.finrank ℝ (P.toDistribution z)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro z
  obtain ⟨r, e, hz, he⟩ := P.locally_trivial z
  let : TopologicalSpace
      (Bundle.TotalSpace (Fin r → ℝ) (fun w : X ↦ ↥(P.toDistribution w))) :=
    TopologicalSpace.induced
      (fun v ↦ (⟨v.proj, v.snd.val⟩ : TangentBundle I X)) inferInstance
  have := he
  filter_upwards [e.open_baseSet.mem_nhds hz] with w hw
  exact (e.linearEquivAt ℝ w hw).finrank_eq.trans
    (e.linearEquivAt ℝ z hz).finrank_eq.symm

end HolomorphicAnosov.ContinuousRealTangentSubbundle
