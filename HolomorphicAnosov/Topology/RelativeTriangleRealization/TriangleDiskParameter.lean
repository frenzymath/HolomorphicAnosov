import Mathlib.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

noncomputable section
open Set Topology _root_.Topology Metric
namespace HolomorphicAnosov.RelativeTriangleRealization
universe u

/-- Implementation of the triangle-to-disk homeomorphism used in Hatcher's
simplex CW structure (pp.103–104). Send the simplex to the planar triangle
0 ≤ x₀, 0 ≤ x₁, x₀+x₁ ≤ 1 by retaining two barycentric coordinates.
The omitted coordinate is 1-x₀-x₁, so this is a continuous bijection from
a compact space to a Hausdorff space and hence a homeomorphism. The planar
triangle is bounded and convex; its interior consists exactly of the three
strict inequalities and contains (1/3,1/3). Mathlib's gauge-rescaling
homeomorphism sends its closure to the closed unit ball and its interior
to the open unit ball. Restriction and composition give the asserted disk
parametrization, with the exact barycentric interior condition. -/
theorem triangleDiskParameter :
    ∃ disk : Convexity.StdSimplex ℝ (Fin 3) ≃ₜ Metric.closedBall (0 : Fin 2 → ℝ) 1,
      ∀ t, (disk t).val ∈ Metric.ball (0 : Fin 2 → ℝ) 1 ↔
        ∀ j, 0 < t.weights j := by
  let S : Set (Fin 2 → ℝ) := {x | 0 ≤ x 0 ∧ 0 ≤ x 1 ∧ x 0 + x 1 ≤ 1}
  let f : Convexity.StdSimplex ℝ (Fin 3) → (Fin 2 → ℝ) :=
    fun t i ↦ t.weights i.castSucc
  have htotal (t : Convexity.StdSimplex ℝ (Fin 3)) :
      t.weights 0 + t.weights 1 + t.weights 2 = 1 := by
    simpa only [Fin.sum_univ_three] using t.total_of_fintype
  have hfS (t : Convexity.StdSimplex ℝ (Fin 3)) : f t ∈ S := by
    refine ⟨t.weights_nonneg 0,t.weights_nonneg 1,?_⟩
    have := t.weights_nonneg 2
    dsimp [f]
    linarith [htotal t]
  have hcf : Continuous f := by
    exact continuous_pi (fun i ↦ Convexity.StdSimplex.continuous_weights_apply ℝ i.castSucc)
  have hinj : Function.Injective f := by
    intro t s h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change t.weights 0 = s.weights 0 at h0
    change t.weights 1 = s.weights 1 at h1
    ext i
    fin_cases i
    · exact h0
    · exact h1
    · change t.weights 2 = s.weights 2
      have := htotal t
      have := htotal s
      linarith
  have hrange : Set.range f = S := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t,rfl⟩
      exact hfS t
    · intro x hx
      let w : Fin 3 → ℝ := ![x 0,x 1,1-x 0-x 1]
      have hw : w ∈ Set.range
          (fun t : Convexity.StdSimplex ℝ (Fin 3) ↦ (t.weights : Fin 3 → ℝ)) := by
        rw [Convexity.StdSimplex.range_toFun_comp_weights]
        refine ⟨?_,?_⟩
        · simp only [Set.mem_iInter,Set.mem_ofPred_eq]
          intro i
          fin_cases i
          · exact hx.1
          · exact hx.2.1
          · dsimp [w]
            linarith [hx.2.2]
        · simp only [Set.mem_ofPred_eq,Fin.sum_univ_three]
          dsimp [w]
          ring
      obtain ⟨t,ht⟩ := hw
      refine ⟨t,?_⟩
      funext i
      fin_cases i
      · exact congrFun ht 0
      · exact congrFun ht 1
  let e : Convexity.StdSimplex ℝ (Fin 3) ≃ S :=
    Equiv.ofBijective (fun t ↦ ⟨f t,hfS t⟩) ⟨by
      intro t s h
      exact hinj (congrArg Subtype.val h), by
      intro x
      have hx : x.val ∈ Set.range f := by rw [hrange]; exact x.property
      obtain ⟨t,ht⟩ := hx
      exact ⟨t,Subtype.ext ht⟩⟩
  let eh : Convexity.StdSimplex ℝ (Fin 3) ≃ₜ S :=
    (hcf.subtype_mk hfS).homeoOfEquivCompactToT2 (f := e)
  have hc : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    change 0 ≤ a*x 0+b*y 0 ∧ 0 ≤ a*x 1+b*y 1 ∧
      (a*x 0+b*y 0)+(a*x 1+b*y 1) ≤ 1
    refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
      add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1),?_⟩
    nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
      mul_le_mul_of_nonneg_left hy.2.2 hb]
  have hcompact : IsCompact S := hrange ▸ isCompact_range hcf
  let coordinateSum : (Fin 2 → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj 0 : (Fin 2 → ℝ) →L[ℝ] ℝ) +
      (ContinuousLinearMap.proj 1 : (Fin 2 → ℝ) →L[ℝ] ℝ)
  have hsum : IsOpenMap coordinateSum := coordinateSum.isOpenMap (by
    intro y
    exact ⟨![y,0],by simp [coordinateSum]⟩)
  have hInt : _root_.interior S = {x | 0 < x 0 ∧ 0 < x 1 ∧ x 0+x 1 < 1} := by
    change _root_.interior ((Function.eval 0 ⁻¹' Ici 0) ∩
      ((Function.eval 1 ⁻¹' Ici 0) ∩ (coordinateSum ⁻¹' Iic 1))) = _
    rw [interior_inter,interior_inter,
      ← (isOpenMap_eval 0).preimage_interior_eq_interior_preimage (continuous_apply 0),
      ← (isOpenMap_eval 1).preimage_interior_eq_interior_preimage (continuous_apply 1),
      ← hsum.preimage_interior_eq_interior_preimage coordinateSum.continuous,
      interior_Ici,interior_Iic]
    rfl
  have hne : (_root_.interior S).Nonempty := by
    rw [hInt]
    exact ⟨fun _ ↦ 1/3,by norm_num⟩
  obtain ⟨h,hi,hcl,-⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall hc hne hcompact.isBounded
  rw [hcompact.isClosed.closure_eq] at hcl
  let disk := eh.trans ((h.image S).trans (Homeomorph.setCongr hcl))
  refine ⟨disk,?_⟩
  intro t
  change h (f t) ∈ Metric.ball (0 : Fin 2 → ℝ) 1 ↔ _
  rw [← hi,Set.mem_image]
  constructor
  · rintro ⟨x,hx,hxt⟩
    have heq : x = f t := h.injective hxt
    subst x
    rw [hInt] at hx
    intro j
    fin_cases j
    · exact hx.1
    · exact hx.2.1
    · have := htotal t
      change 0 < t.weights 2
      dsimp [f] at hx
      linarith [hx.2.2]
  · intro ht
    refine ⟨f t,?_,rfl⟩
    rw [hInt]
    refine ⟨ht 0,ht 1,?_⟩
    have := htotal t
    dsimp [f]
    linarith [ht 2]

end HolomorphicAnosov.RelativeTriangleRealization
