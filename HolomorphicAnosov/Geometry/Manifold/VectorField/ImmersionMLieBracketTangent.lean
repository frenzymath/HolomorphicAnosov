import Mathlib.Geometry.Manifold.VectorField.LieBracket
import HolomorphicAnosov.Geometry.Manifold.VectorField.ImmersionChartBracketTangent
import HolomorphicAnosov.Geometry.Manifold.VectorField.ChartInverseMPullbackEq

/-! The Lie bracket of differentiable vector fields tangent to an immersed plaque is tangent to that
plaque. (Lee, Prop. 8.27, pp. 192–193; Cor. 8.28, p. 193; Prop. 4.16, p. 92) -/

noncomputable section
open Set Filter Function
open scoped Topology _root_.Topology ContDiff Manifold Bundle
namespace HolomorphicAnosov.Theorem12NativePlaque
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {L M : Type*} [TopologicalSpace L] [TopologicalSpace M]
  [ChartedSpace E L] [ChartedSpace H M]
variable [CompleteSpace H] [IsManifold (modelWithCornersSelf ℝ H) ∞ M]

set_option backward.isDefEq.respectTransparency false in
/-- The Lie bracket of differentiable ambient vector fields tangent along an immersed plaque belongs
to its tangent distribution. (Lee, Prop. 8.27, pp. 192–193; Cor. 8.28, p. 193; Prop. 4.16, p.
92) -/
theorem immersion_mlieBracket_tangent {f : L → M} {x : L}
    (h : Manifold.IsImmersionAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ H) ∞ f x)
    (P : M → Submodule ℝ H)
    (hP : ∀ z, LinearMap.range (mfderiv (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ H) f z).toLinearMap = P (f z))
    {V W : ∀ p : M, TangentSpace (modelWithCornersSelf ℝ H) p}
    (hV : MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% V) (f x))
    (hW : MDifferentiableAt (modelWithCornersSelf ℝ H)
      ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% W) (f x))
    (hVtan : ∀ᶠ z in 𝓝 x, V (f z) ∈ P (f z))
    (hWtan : ∀ᶠ z in 𝓝 x, W (f z) ∈ P (f z)) :
    VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W (f x) ∈ P (f x) := by
  have hsection {T : ∀ y : H, TangentSpace (modelWithCornersSelf ℝ H) y} {y : H}
      (hT : MDifferentiableAt (modelWithCornersSelf ℝ H)
        ((modelWithCornersSelf ℝ H).prod (modelWithCornersSelf ℝ H)) (T% T) y) :
      DifferentiableAt ℝ T y := by
    have hh := (mdifferentiableAt_section
      (E := TangentSpace (modelWithCornersSelf ℝ H)) (modelWithCornersSelf ℝ H) T).1 hT
    simpa only [trivializationAt_model_space_apply,
      mdifferentiableAt_iff_differentiableAt] using hh
  let c := h.codChart
  have hx := h.mem_domChart_source
  have hp := h.source_subset_preimage_source hx
  have hc : c.MDifferentiable (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H) :=
    ⟨(contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
      (by simp),
     (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).mdifferentiableOn
      (by simp)⟩
  have hci : ContMDiffAt (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
      ∞ c.symm (c (f x)) :=
    contMDiffAt_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas (c.map_source hp)
  let Vc := VectorField.mpullback (modelWithCornersSelf ℝ H)
    (modelWithCornersSelf ℝ H) c.symm V
  let Wc := VectorField.mpullback (modelWithCornersSelf ℝ H)
    (modelWithCornersSelf ℝ H) c.symm W
  have hV' : DifferentiableAt ℝ Vc (c (f x)) := by
    apply hsection
    apply MDifferentiableAt.mpullback_vectorField
    · simpa only [c.left_inv hp] using hV
    · exact hci
    · exact ⟨hc.symm.mfderiv (c.map_source hp), rfl⟩
    · simp
  have hW' : DifferentiableAt ℝ Wc (c (f x)) := by
    apply hsection
    apply MDifferentiableAt.mpullback_vectorField
    · simpa only [c.left_inv hp] using hW
    · exact hci
    · exact ⟨hc.symm.mfderiv (c.map_source hp), rfl⟩
    · simp
  have hVctan : ∀ᶠ z in 𝓝 x, Vc (c (f z)) ∈
      (P (f z)).map (mfderiv (modelWithCornersSelf ℝ H)
        (modelWithCornersSelf ℝ H) c (f z)).toLinearMap := by
    filter_upwards [hVtan, h.domChart.open_source.mem_nhds hx] with z hz hzs
    rw [show Vc (c (f z)) = _ from chart_inverse_mpullback_eq c hc
      (h.source_subset_preimage_source hzs) V]
    exact ⟨V (f z), hz, rfl⟩
  have hWctan : ∀ᶠ z in 𝓝 x, Wc (c (f z)) ∈
      (P (f z)).map (mfderiv (modelWithCornersSelf ℝ H)
        (modelWithCornersSelf ℝ H) c (f z)).toLinearMap := by
    filter_upwards [hWtan, h.domChart.open_source.mem_nhds hx] with z hz hzs
    rw [show Wc (c (f z)) = _ from chart_inverse_mpullback_eq c hc
      (h.source_subset_preimage_source hzs) W]
    exact ⟨W (f z), hz, rfl⟩
  have ht := immersion_chart_bracket_tangent h P hP hV' hW' hVctan hWctan
  let : IsManifold (modelWithCornersSelf ℝ H) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by simp)
  have hbr := VectorField.mpullback_mlieBracket
    (by simpa only [c.left_inv hp] using hV)
    (by simpa only [c.left_inv hp] using hW) hci (by simp)
  have hbr' : mfderiv (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
      c (f x) (VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W (f x)) =
      VectorField.lieBracket ℝ Vc Wc (c (f x)) := by
    calc
      _ = VectorField.mpullback (modelWithCornersSelf ℝ H) (modelWithCornersSelf ℝ H)
          c.symm (VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W)
          (c (f x)) := (chart_inverse_mpullback_eq c hc hp _).symm
      _ = VectorField.mlieBracket (modelWithCornersSelf ℝ H) Vc Wc (c (f x)) := hbr
      _ = _ := by
        rw [← VectorField.mlieBracketWithin_univ,
          VectorField.mlieBracketWithin_eq_lieBracketWithin]
        exact congrFun (VectorField.lieBracketWithin_univ
          (𝕜 := ℝ) (V := (Vc : H → H)) (W := (Wc : H → H))) (c (f x))
  rw [← hbr'] at ht
  rcases ht with ⟨a, ha, he⟩
  have hae : a = VectorField.mlieBracket (modelWithCornersSelf ℝ H) V W (f x) :=
    hc.mfderiv_injective hp he
  exact hae ▸ ha

end HolomorphicAnosov.Theorem12NativePlaque

