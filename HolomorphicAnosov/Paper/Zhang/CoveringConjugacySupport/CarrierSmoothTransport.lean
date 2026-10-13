import Mathlib.Geometry.Manifold.Diffeomorph

open scoped Topology ContDiff Manifold Bundle
open Filter Set _root_.Topology

universe u v
namespace HolomorphicAnosov

/-- General intrinsic atlas transport, without any whole Euclidean parametrization. -/
theorem carrier_smooth_transport_g15 {r : ℕ} {L N : Type*}
    [TopologicalSpace L] [TopologicalSpace N] [ChartedSpace (Fin r → ℝ) L]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L] (h : N ≃ₜ L) :
    ∃ c : ChartedSpace (Fin r → ℝ) N, letI := c
      ∃ _hm : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ N,
        ∃ e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) N L ∞,
          ∀ z : N, e z = h z := by
  let c : ChartedSpace (Fin r → ℝ) N :=
    { atlas := (fun a : OpenPartialHomeomorph L (Fin r → ℝ) ↦
        h.toOpenPartialHomeomorph.trans a) '' atlas (Fin r → ℝ) L
      chartAt := fun x ↦ h.toOpenPartialHomeomorph.trans (chartAt (Fin r → ℝ) (h x))
      mem_chart_source := fun x ↦ by
        simp only [OpenPartialHomeomorph.trans_source,
          Homeomorph.toOpenPartialHomeomorph_source, Set.mem_inter_iff, Set.mem_univ,
          true_and, Homeomorph.toOpenPartialHomeomorph_apply, Set.mem_preimage]
        exact mem_chart_source _ _
      chart_mem_atlas := fun x ↦ Set.mem_image_of_mem _ (chart_mem_atlas _ _) }
  let := c
  have hm : IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ N := by
    refine { compatible := ?_ }
    rintro a a' ⟨b, hb, rfl⟩ ⟨b', hb', rfl⟩
    have heq : (h.toOpenPartialHomeomorph.trans b).symm.trans
        (h.toOpenPartialHomeomorph.trans b') = b.symm.trans b' := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        OpenPartialHomeomorph.trans_assoc,
        ← OpenPartialHomeomorph.trans_assoc h.toOpenPartialHomeomorph.symm
          h.toOpenPartialHomeomorph b',
        ← Homeomorph.symm_toOpenPartialHomeomorph,
        ← Homeomorph.trans_toOpenPartialHomeomorph, Homeomorph.symm_trans_self,
        Homeomorph.refl_toOpenPartialHomeomorph, OpenPartialHomeomorph.refl_trans]
    rw [heq]
    exact (contDiffGroupoid ∞ 𝓘(ℝ, Fin r → ℝ)).compatible hb hb'
  let := hm
  have hf : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) ∞ h := by
    intro x
    apply contMDiffWithinAt_iff'.mpr
    refine ⟨h.continuous.continuousWithinAt, ?_⟩
    apply contDiffWithinAt_id.congr_of_mem
    · intro y hy
      change (chartAt (Fin r → ℝ) (h x))
        (h (h.symm ((chartAt (Fin r → ℝ) (h x)).symm y))) = y
      rw [h.apply_symm_apply]
      apply (chartAt (Fin r → ℝ) (h x)).right_inv
      have hy' : y ∈ (chartAt (Fin r → ℝ) x).target := by
        simpa [extChartAt, OpenPartialHomeomorph.extend_target] using hy.1
      change y ∈ ((h.toOpenPartialHomeomorph.trans
        (chartAt (Fin r → ℝ) (h x))).target) at hy'
      exact hy'.1
    · refine ⟨(extChartAt 𝓘(ℝ, Fin r → ℝ) x).map_source (mem_extChartAt_source x), ?_⟩
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_univ, true_and,
        (extChartAt 𝓘(ℝ, Fin r → ℝ) x).left_inv (mem_extChartAt_source x)]
      exact mem_extChartAt_source (h x)
  have hi : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) ∞ h.symm := by
    intro y
    apply contMDiffWithinAt_iff'.mpr
    refine ⟨h.symm.continuous.continuousWithinAt, ?_⟩
    apply contDiffWithinAt_id.congr_of_mem
    · intro z hz
      change (chartAt (Fin r → ℝ) (h (h.symm y)))
        (h (h.symm ((chartAt (Fin r → ℝ) y).symm z))) = z
      simp only [h.apply_symm_apply]
      apply (chartAt (Fin r → ℝ) y).right_inv
      simpa [extChartAt, OpenPartialHomeomorph.extend_target] using hz.1
    · refine ⟨(extChartAt 𝓘(ℝ, Fin r → ℝ) y).map_source (mem_extChartAt_source y), ?_⟩
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_univ, true_and,
        (extChartAt 𝓘(ℝ, Fin r → ℝ) y).left_inv (mem_extChartAt_source y)]
      exact mem_extChartAt_source (h.symm y)
  let e : Diffeomorph 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin r → ℝ) N L ∞ :=
    { toEquiv := h.toEquiv, contMDiff_toFun := hf, contMDiff_invFun := hi }
  exact ⟨c, hm, e, fun _ ↦ rfl⟩


end HolomorphicAnosov
