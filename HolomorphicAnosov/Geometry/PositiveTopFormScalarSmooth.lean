import HolomorphicAnosov.Geometry.RealTangentTopForm
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import HolomorphicAnosov.Geometry.PositiveRealTangentTopFormNonzero
import Mathlib.LinearAlgebra.Determinant

/-! Two smooth positive tangent top forms differ by a smooth positive scalar function. (Demailly, VI
§4, pp. 296–297) -/

open scoped ContDiff
open Set
namespace HolomorphicAnosov
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Two smooth positive top forms differ by a smooth positive scalar function. (Demailly, VI §4, pp.
296–297) -/
theorem positive_topForms_exists_smooth_scalar
    {d : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel d) X]
    [IsManifold (complexModel d) ∞ X]
    (μ ν : RealTangentTopForm d X)
    (hμ : IsSmoothPositiveRealTangentTopForm μ)
    (hν : IsSmoothPositiveRealTangentTopForm ν) :
    ∃ J : X → ℝ, ContMDiff (realModel d) (modelWithCornersSelf ℝ ℝ) ∞ J ∧
      (∀ x, 0 < J x) ∧ μ = realTangentTopFormScale J ν := by
  classical
  let b : Module.Basis (ComplexPairedIndex d) ℝ (ComplexModel d) :=
    (Pi.basis (fun _ : Fin d ↦ Complex.basisOneI)).reindex
      (Equiv.sigmaEquivProd (Fin d) (Fin 2))
  have hpoint (x : X) : ∃ c : ℝ, μ x = c • ν x := by
    have hm := (μ x).toAlternatingMap.eq_smul_basis_det b
    have hn := (ν x).toAlternatingMap.eq_smul_basis_det b
    change (μ x).toAlternatingMap = μ x b • b.det at hm
    change (ν x).toAlternatingMap = ν x b • b.det at hn
    have hv : ν x b ≠ 0 := by
      intro hz
      apply positive_topForm_ne_zero ν hν x
      apply ContinuousAlternatingMap.toAlternatingMap_injective
      simpa [hz] using hn
    refine ⟨μ x b / ν x b, ?_⟩
    apply ContinuousAlternatingMap.toAlternatingMap_injective
    change (μ x).toAlternatingMap = (μ x b / ν x b) • (ν x).toAlternatingMap
    rw [hm, hn, smul_smul, div_mul_cancel₀ _ hv]
  choose J hJ using hpoint
  have heq : μ = realTangentTopFormScale J ν := funext hJ
  have hregular : ContMDiff (realModel d) (modelWithCornersSelf ℝ ℝ) ∞ J ∧
      ∀ x, 0 < J x := by
    have hJ := heq
    have hratio (e : OpenPartialHomeomorph X (ComplexModel d))
        (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X)
        (z : ComplexModel d) (hz : z ∈ e.target) :
        J (e.symm z) = realTangentTopFormChartCoefficient μ e z /
          realTangentTopFormChartCoefficient ν e z := by
      have hn := (hν e he).2 z hz
      apply (eq_div_iff (ne_of_gt hn)).mpr
      have h := congrArg (fun form : RealTangentTopForm d X ↦
        realTangentTopFormChartCoefficient form e z) hJ
      exact h.symm
    have hcharts (e : OpenPartialHomeomorph X (ComplexModel d))
        (he : e ∈ IsManifold.maximalAtlas (complexModel d) ∞ X) :
        ContDiffOn ℝ ∞ (J ∘ e.symm) e.target := by
      apply ((hμ e he).1.div (hν e he).1 (fun z hz ↦ ne_of_gt ((hν e he).2 z hz))).congr
      intro z hz
      exact hratio e he z hz
    constructor
    · intro x
      let e := chartAt (ComplexModel d) x
      have hz : e x ∈ e.target := e.map_source (mem_chart_source _ x)
      have hc := (hcharts e (IsManifold.chart_mem_maximalAtlas x)).contDiffAt
        (e.open_target.mem_nhds hz)
      apply contMDiffAt_iff_source.mpr
      simpa only [realModel, modelWithCornersSelf_coe, Set.range_id,
        contMDiffWithinAt_univ, extChartAt_coe_symm, extChartAt_coe,
        modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id] using hc.contMDiffAt
    · intro x
      let e := chartAt (ComplexModel d) x
      have hx : x ∈ e.source := mem_chart_source _ x
      have hz := e.map_source hx
      have hp := div_pos ((hμ e (IsManifold.chart_mem_maximalAtlas x)).2 (e x) hz)
        ((hν e (IsManifold.chart_mem_maximalAtlas x)).2 (e x) hz)
      rw [← hratio e (IsManifold.chart_mem_maximalAtlas x) (e x) hz, e.left_inv hx] at hp
      exact hp
  obtain ⟨hs, hp⟩ := hregular
  exact ⟨J, hs, hp, heq⟩

end HolomorphicAnosov
