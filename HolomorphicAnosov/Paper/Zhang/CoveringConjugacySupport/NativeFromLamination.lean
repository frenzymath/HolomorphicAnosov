import HolomorphicAnosov.Dynamics.Anosov.GlobalLamination
import HolomorphicAnosov.Geometry.NativeAsymptoticLeaf
import HolomorphicAnosov.Paper.Zhang.CoveringConjugacySupport.NativeAsymptoticDatumOfLeaf

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- Reindex the actual source-selected HPS intrinsic leaf by its full asymptotic range equality. -/
theorem covering_conjugacy_native_from_lamination_g15
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {M : Type u} [MetricSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (D : RealTangentDistribution 𝓘(ℝ, E) M)
    (f g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞)
    (hlam : HPS.HasNativeLamination D f
      (fun F families coherent ↦ HPS.SourceBoundDistanceOutput F families coherent g edist)) :
    ∀ x, Nonempty (NativeAsymptoticLeafDatum 𝓘(ℝ, E) g.toHomeomorph D x) := by
  classical
  obtain ⟨ι, L, r, top, charts, smooth, F, _, _, families, coherent, hextra⟩ := hlam
  let := top
  let := charts
  let := smooth
  obtain ⟨label, sourceDisc, sourceMap, stages, ⟨identification, _⟩, _, _⟩ := hextra
  intro x
  have hrange : Set.range (F.leaf (identification.label x)).inclusion =
      {y | ForwardAsymptotic g.toHomeomorph x y} := by
    rw [identification.equality]
    ext y
    have heq := ENNReal.tendsto_toReal_zero_iff (fi := atTop)
      (f := fun n : ℕ ↦ edist (realIterate 𝓘(ℝ, E) g n y)
        (realIterate 𝓘(ℝ, E) g n x))
    change Tendsto (fun n : ℕ ↦ edist (realIterate 𝓘(ℝ, E) g n y)
        (realIterate 𝓘(ℝ, E) g n x)) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ ↦ dist (realIterate 𝓘(ℝ, E) g n y)
        (realIterate 𝓘(ℝ, E) g n x)) atTop (𝓝 0)
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using heq.symm
  obtain ⟨N, _⟩ := native_asymptotic_datum_of_leaf_g15 D
    (F.leaf (identification.label x)) g.toHomeomorph x hrange
  exact ⟨N⟩


end HolomorphicAnosov
