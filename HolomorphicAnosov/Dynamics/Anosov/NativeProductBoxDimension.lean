import HolomorphicAnosov.Dynamics.Anosov.NativeSmoothLamination
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped ContDiff Manifold Topology _root_.Topology
open Set

namespace HolomorphicAnosov.HPS
universe u

/-- A native product box for a partition of constant leaf rank has that same
coordinate dimension. Source: HPS (1977), pp.115--116, native product plaques.
The connected coordinate discs are nonempty. Choose a transversal parameter
and a disc point; the differential of the given native plaque diffeomorphism
is a linear equivalence between the two coordinate tangent spaces. Equality
of their finite dimensions gives the assertion, including rank zero.
DAG node: `dynamics.native_product_box_dimension_g18`.
-/
theorem NativeProductBox.dimension_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    {D : RealTangentDistribution 𝓘(ℝ, E) M}
    {ι : Type u} {L : ι → Type u} {s d : ℕ}
    [∀ i, TopologicalSpace (L i)]
    [∀ i, ChartedSpace (Fin s → ℝ) (L i)]
    [∀ i, IsManifold 𝓘(ℝ, Fin s → ℝ) ∞ (L i)]
    {F : LeafPartition D ι L (fun _ ↦ s)}
    {T : Type u} [TopologicalSpace T] (B : NativeProductBox F d T) : d = s := by
  obtain ⟨v, hv⟩ := B.disc_connected.nonempty
  obtain ⟨w, hw⟩ := B.transverse_connected.nonempty
  let t : T := B.transverse_chart.symm ⟨w, hw⟩
  have hr := ((B.chart t).mfderivToContinuousLinearEquiv (by simp) ⟨v, hv⟩).toLinearEquiv.finrank_eq
  change Module.finrank ℝ (Fin d → ℝ) = Module.finrank ℝ (Fin s → ℝ) at hr
  simpa only [Module.finrank_fin_fun] using hr

end HolomorphicAnosov.HPS
