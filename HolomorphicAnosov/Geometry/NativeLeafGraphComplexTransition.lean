import HolomorphicAnosov.Geometry.LocalProjectionGraph
import HolomorphicAnosov.Geometry.ComplexLinearLeftInverse

namespace HolomorphicAnosov
open scoped ContDiff Manifold
universe u v

/-! This file proves complex smoothness of transitions between local projection graph charts.
(Demailly, I Lemma 7.15, p. 60) -/

structure NativeLeafGraphComplexTransitionData
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) where
  transition : ∀ x y : L,
    ∀ A : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x,
    ∀ B : NativeLeafLocalProjectionGraph (k := k) (d := d) inc y,
    ContDiffOn ℂ ∞ (B.chart ∘ A.chart.symm)
      (A.chart.target ∩ A.chart.symm ⁻¹' B.chart.source)

/-- The transition between any two local projection graph charts is complex-smooth on their overlap. -/
theorem native_leaf_graph_complex_transition
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin (2*k) → ℝ) ∞ L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold (complexModel d) ∞ M]
    (inc : L → M) (x y : L)
    (A : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x)
    (B : NativeLeafLocalProjectionGraph (k := k) (d := d) inc y) :
    ContDiffOn ℂ ∞ (B.chart ∘ A.chart.symm)
      (A.chart.target ∩ A.chart.symm ⁻¹' B.chart.source) := by
  obtain ⟨Q, hQ⟩ := complex_linear_left_inverse_of_injective
    B.linearModel B.linearModel_injective
  let S := A.chart.target ∩ A.chart.symm ⁻¹' B.chart.source
  have ha (z : ComplexModel k) (hz : z ∈ A.chart.target) :
      A.ambientChart (inc (A.chart.symm z)) = A.linearModel z := by
    simpa [Function.comp_def] using A.graph_equation
      (show z ∈ (A.chart.extend (complexModel k)).target by simpa using hz)
  have has (z : ComplexModel k) (hz : z ∈ A.chart.target) :
      inc (A.chart.symm z) ∈ A.ambientChart.source :=
    A.source_inside_ambient (A.chart.map_target hz)
  have hai (z : ComplexModel k) (hz : z ∈ A.chart.target) :
      A.ambientChart.symm (A.linearModel z) = inc (A.chart.symm z) := by
    rw [← ha z hz, A.ambientChart.left_inv (has z hz)]
  have hi : ContMDiffOn (complexModel k) (complexModel d) ∞
      (fun z ↦ A.ambientChart.symm (A.linearModel z)) S := by
    apply (contMDiffOn_symm_of_mem_maximalAtlas A.ambientChart_mem_complex_atlas).comp
      A.linearModel.contDiff.contMDiff.contMDiffOn
    intro z hz
    change A.linearModel z ∈ A.ambientChart.target
    rw [← ha z hz.1]
    exact A.ambientChart.map_source (has z hz.1)
  have hb : ContMDiffOn (complexModel k) (complexModel d) ∞
      (fun z ↦ B.ambientChart (A.ambientChart.symm (A.linearModel z))) S := by
    apply (contMDiffOn_of_mem_maximalAtlas B.ambientChart_mem_complex_atlas).comp hi
    intro z hz
    change A.ambientChart.symm (A.linearModel z) ∈ B.ambientChart.source
    rw [hai z hz.1]
    exact B.source_inside_ambient hz.2
  have hh := Q.contDiff.comp_contDiffOn hb.contDiffOn
  apply hh.congr
  intro z hz
  change z ∈ S at hz
  change B.chart (A.chart.symm z) =
    Q (B.ambientChart (A.ambientChart.symm (A.linearModel z)))
  rw [hai z hz.1]
  have hbg : B.ambientChart (inc (A.chart.symm z)) =
      B.linearModel (B.chart (A.chart.symm z)) := by
    have hzs : A.chart.symm z ∈ B.chart.source := hz.2
    have hg := B.graph_equation
      ((B.chart.extend (complexModel k)).map_source
        (by simpa only [B.chart.extend_source] using hzs))
    simpa [Function.comp_def, B.chart.left_inv hzs] using hg
  rw [hbg]
  exact (congrArg (fun T : ComplexModel k →L[ℂ] ComplexModel k ↦
    T (B.chart (A.chart.symm z))) hQ).symm

theorem native_leaf_graph_complex_transition_of_data
    {k d : ℕ} {L : Type u} {M : Type v}
    [TopologicalSpace L] [ChartedSpace (Fin (2*k) → ℝ) L]
    [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    (inc : L → M) (D : NativeLeafGraphComplexTransitionData (k := k) (d := d) inc)
    {x y : L} (A : NativeLeafLocalProjectionGraph (k := k) (d := d) inc x)
    (B : NativeLeafLocalProjectionGraph (k := k) (d := d) inc y) :
    ContDiffOn ℂ ∞ (B.chart ∘ A.chart.symm)
      (A.chart.target ∩ A.chart.symm ⁻¹' B.chart.source) :=
  D.transition x y A B

end HolomorphicAnosov
