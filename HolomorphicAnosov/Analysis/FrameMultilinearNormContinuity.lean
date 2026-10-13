import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Multilinear.Basic

noncomputable section
open Set _root_.Topology
open scoped BigOperators
namespace HolomorphicAnosov

/-- HPS p.8 and pp.32–35: a multilinear operator norm is the supremum of its
norm ratios on tuples of unit model vectors. Normalize each nonzero frame
preimage separately; a zero argument has zero image. Empty tuples and empty
unit spheres are included by the real supremum conventions. -/
theorem frame_multilinear_ratio_norm
    {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (j : V ≃L[ℝ] E) (L : ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E) F) :
    ‖L‖ = sSup ((fun u : Fin m → Metric.sphere (0 : V) 1 ↦
      ‖L (fun i ↦ j (u i))‖ / ∏ i, ‖j (u i)‖) '' univ) := by
  classical
  let S := (fun u : Fin m → Metric.sphere (0 : V) 1 ↦
      ‖L (fun i ↦ j (u i))‖ / ∏ i, ‖j (u i)‖) '' univ
  have hb : BddAbove S := ⟨‖L‖, by rintro _ ⟨u,_,rfl⟩; exact L.ratio_le_opNorm _⟩
  have hn : 0 ≤ sSup S := Real.sSup_nonneg (by
    rintro _ ⟨u,_,rfl⟩
    exact div_nonneg (norm_nonneg _) (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _)))
  apply le_antisymm
  · apply ContinuousMultilinearMap.opNorm_le_bound hn
    intro v
    by_cases hv : ∃ i, v i = 0
    · obtain ⟨i,hi⟩ := hv
      rw [L.map_coord_zero i hi, norm_zero]
      exact mul_nonneg hn (Finset.prod_nonneg (fun _ _ ↦ norm_nonneg _))
    have hv' : ∀ i, v i ≠ 0 := by simpa only [not_exists] using hv
    let w := fun i ↦ j.symm (v i)
    have hw : ∀ i, w i ≠ 0 := by intro i; simpa [w] using hv' i
    let u : Fin m → Metric.sphere (0 : V) 1 := fun i ↦
      ⟨‖w i‖⁻¹ • w i, by simp [norm_smul, norm_ne_zero_iff.mpr (hw i)]⟩
    have hu : ‖L (fun i ↦ j (u i))‖ / (∏ i, ‖j (u i)‖) ≤ sSup S :=
      le_csSup hb ⟨u,mem_univ _,rfl⟩
    have heq : ‖L (fun i ↦ j (u i))‖ / (∏ i, ‖j (u i)‖) =
        ‖L v‖ / (∏ i, ‖v i‖) := by
      simp only [u, map_smul, w, ContinuousLinearEquiv.apply_symm_apply,
        L.map_smul_univ, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        Finset.prod_mul_distrib]
      rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ ↦ inv_nonneg.mpr (norm_nonneg _)))]
      apply mul_div_mul_left
      exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ inv_ne_zero (norm_ne_zero_iff.mpr (hw i)))
    rw [heq] at hu
    exact (div_le_iff₀ (Finset.prod_pos (fun i _ ↦ norm_pos_iff.mpr (hv' i)))).mp hu
  · apply Real.sSup_le _ (norm_nonneg _)
    rintro _ ⟨u,_,rfl⟩
    exact L.ratio_le_opNorm _

/-- HPS pp.8,32–35: a family of multilinear operators has continuous original
operator norm when the frame norms and framed evaluation norms are jointly
continuous. Take the supremum of the continuous norm ratio on the compact
product of model unit spheres. This includes order zero and rank zero. -/
theorem continuous_multilinear_norm_of_frame
    {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {E F : X → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℝ (F x)]
    (m : ℕ) (j : ∀ x, V ≃L[ℝ] E x)
    (L : ∀ x, ContinuousMultilinearMap ℝ (fun _ : Fin m ↦ E x) (F x))
    (hden : Continuous (fun z : X × V ↦ ‖j z.1 z.2‖))
    (hnum : Continuous (fun z : X × (Fin m → V) ↦
      ‖L z.1 (fun i ↦ j z.1 (z.2 i))‖)) :
    Continuous (fun x ↦ ‖L x‖) := by
  let S := Metric.sphere (0 : V) 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hc : Continuous (fun z : X × (Fin m → S) ↦
      (z.1, fun i ↦ (z.2 i).val)) := continuous_fst.prodMk
    (continuous_pi (fun i ↦ continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
  have hd : Continuous (fun z : X × (Fin m → S) ↦ ∏ i, ‖j z.1 (z.2 i).val‖) := by
    apply continuous_finsetProd
    intro i hi
    exact hden.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp ((continuous_apply i).comp continuous_snd)))
  have hnz : ∀ z : X × (Fin m → S), (∏ i, ‖j z.1 (z.2 i).val‖) ≠ 0 := by
    intro z
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply norm_ne_zero_iff.mpr
    intro hz
    have hv : (z.2 i).val = 0 := (j z.1).injective (hz.trans (map_zero _).symm)
    have hvnorm : ‖(z.2 i).val‖ = 1 := by simp [S]
    simp [hv] at hvnorm
  have hr := (hnum.comp hc).div hd hnz
  have hsup := (isCompact_univ : IsCompact (univ : Set (Fin m → S))).continuous_sSup
    (f := fun (x : X) (u : Fin m → S) ↦
      ‖L x (fun i ↦ j x (u i).val)‖ / ∏ i, ‖j x (u i).val‖) hr
  exact hsup.congr (fun x ↦ (frame_multilinear_ratio_norm m (j x) (L x)).symm)

end HolomorphicAnosov
