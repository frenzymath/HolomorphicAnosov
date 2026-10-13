import HolomorphicAnosov.Geometry.Manifold.VectorBundle.QuotientLineConnectionC0

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
universe u
namespace HolomorphicAnosov
open QuotientLineConnection

/-- Every tangent evaluation of a difference of connections is bounded by the C⁰ distance times the length in the stored metric. -/
theorem difference_eval_le_c0
    {d : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    {U : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (g : Bundle.ContMDiffRiemannianMetric (realModel d) ∞ (ComplexModel d)
      (fun x : X ↦ TangentSpace (realModel d) x)) (D E : Connection U)
    (hb : BddAbove (differenceValues g D E))
    (V : Opens X) (e : HolomorphicFrame U V) (x : X) (hx : x ∈ V)
    (v : TangentSpace (realModel d) x) :
    ‖D.form V e x v - E.form V e x v‖ ≤
      c0Distance g D E * Real.sqrt (g.inner x v v) := by
  by_cases hv : v = 0
  · simp [hv]
  have hg := g.pos x v hv
  have hs : 0 < Real.sqrt (g.inner x v v) := Real.sqrt_pos.mpr hg
  have hsq := Real.sq_sqrt hg.le
  let w := (Real.sqrt (g.inner x v v))⁻¹ • v
  have hw : g.inner x w w ≤ 1 := by
    dsimp [w]
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hne : Real.sqrt (g.inner x v v) ≠ 0 := ne_of_gt hs
    apply le_of_eq
    field_simp
    nlinarith [hsq]
  have hbound := le_csSup hb (show ‖D.form V e x w - E.form V e x w‖ ∈
      differenceValues g D E from ⟨V, e, x, hx, w, hw, rfl⟩)
  have hscale : ‖D.form V e x w - E.form V e x w‖ =
      (Real.sqrt (g.inner x v v))⁻¹ * ‖D.form V e x v - E.form V e x v‖ := by
    dsimp [w]
    rw [map_smul, map_smul, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs)]
  rw [hscale] at hbound
  calc
    ‖D.form V e x v - E.form V e x v‖ =
        (Real.sqrt (g.inner x v v)) *
          ((Real.sqrt (g.inner x v v))⁻¹ * ‖D.form V e x v - E.form V e x v‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), one_mul]
    _ ≤ (Real.sqrt (g.inner x v v)) * c0Distance g D E :=
      mul_le_mul_of_nonneg_left hbound hs.le
    _ = _ := mul_comm _ _

end HolomorphicAnosov
