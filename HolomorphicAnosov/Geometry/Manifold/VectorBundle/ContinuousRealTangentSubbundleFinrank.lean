import HolomorphicAnosov.Geometry.Manifold.VectorBundle.ContinuousRealTangentSubbundleLocalRankG10

/-! The rank of a continuous real tangent subbundle is constant on a preconnected base (Hatcher,
§2.1, p.39; Gallier–Quaintance, Vol. I, Prop. 13.15). -/

namespace HolomorphicAnosov.ContinuousRealTangentSubbundle

open scoped ContDiff
open Filter Topology _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} {X : Type*}
variable [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]

/-- A continuous real tangent subbundle has constant fibre dimension on a preconnected base
(Hatcher, §2.1, p.39; Gallier–Quaintance, Vol. I, Prop. 13.15). -/
theorem finrank_eq [PreconnectedSpace X]
    (P : ContinuousRealTangentSubbundle I X) (x y : X) :
    Module.finrank ℝ (P.toDistribution x) = Module.finrank ℝ (P.toDistribution y) := by
  exact P.finrank_isLocallyConstant.apply_eq_of_preconnectedSpace x y

end HolomorphicAnosov.ContinuousRealTangentSubbundle

