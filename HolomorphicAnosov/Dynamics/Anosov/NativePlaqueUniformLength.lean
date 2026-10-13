import HolomorphicAnosov.Dynamics.Anosov.Step11NativeRadialLength

noncomputable section
open Set Filter MeasureTheory Manifold Bundle
open scoped ContDiff Manifold Bundle ENNReal _root_.Topology
namespace HolomorphicAnosov
variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  {D : ∀ x : M, Submodule ℝ (TangentSpace 𝓘(ℝ,E) x)} {center : M}

/-- G17 canonical name for the verified HPS first-jet continuity provider. -/
abbrev NativePlaqueFamily.continuous_tangent
    (P : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center) :=
  NativePlaqueFamily.continuous_tangent_w04 P

/-- G17 canonical name for the verified compact tangent bound provider. -/
abbrev NativePlaqueFamily.uniform_tangent_bound_on_compact [FiniteDimensional ℝ V]
    (P : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (K : Set P.centerDomain) (hK : IsCompact K) {r : ℝ} (hr : r < P.radius) :=
  NativePlaqueFamily.uniform_tangent_bound_on_compact_w04 P g K hK hr

/-- G17 canonical name for the verified radial-length provider. -/
abbrev NativePlaqueFamily.uniform_radial_length [FiniteDimensional ℝ V]
    (P : NativePlaqueFamily 𝓘(ℝ,E) (V := V) D center)
    (g : ContMDiffRiemannianMetric 𝓘(ℝ,E) ∞ E
      (fun x : M ↦ TangentSpace 𝓘(ℝ,E) x))
    (K : Set P.centerDomain) (hK : IsCompact K) {r : ℝ}
    (hr0 : 0 < r) (hr : r < P.radius) :=
  NativePlaqueFamily.uniform_radial_length_w04 P g K hK hr0 hr

end HolomorphicAnosov
