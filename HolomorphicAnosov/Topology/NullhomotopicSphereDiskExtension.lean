import HolomorphicAnosov.Topology.EuclideanDiskUnitCube
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Separation.Hausdorff

/-!
# Extending a nullhomotopic sphere map to the disk

This file proves the disk extension theorem for a jointly continuous nullhomotopy.
-/

namespace HolomorphicAnosov

/-- A jointly continuous nullhomotopy of a sphere map gives a continuous extension to the closed disk. (Hatcher, Props. 0.16 and 0.17) -/
theorem nullhomotopic_sphere_disk_extension
    (d : ℕ) (hd : 1 ≤ d) {Y : Type*} [TopologicalSpace Y]
    (b : {v : Fin d → ℝ // ‖v‖ = 1} → Y) (_hb : Continuous b)
    (hnull : ∃ ystar : Y,
      ∃ H : unitInterval × {v : Fin d → ℝ // ‖v‖ = 1} → Y,
        Continuous H ∧
          (∀ s, H (0, s) = b s) ∧ (∀ s, H (1, s) = ystar)) :
    ∃ B : {v : Fin d → ℝ // ‖v‖ ≤ 1} → Y,
      Continuous B ∧ ∀ s, B ⟨s.val, le_of_eq s.property⟩ = b s := by





  obtain ⟨ystar, H, hH, hH0, hH1⟩ := hnull
  let S := {v : Fin d → ℝ // ‖v‖ = 1}
  let D := {v : Fin d → ℝ // ‖v‖ ≤ 1}
  let f : unitInterval × S → D := fun z ↦
    ⟨(z.1 : ℝ) • z.2.1, by
      rw [norm_smul, z.2.2]
      simpa [Real.norm_eq_abs, abs_of_nonneg z.1.2.1] using z.1.2.2⟩
  let g : unitInterval × S → Y := fun z ↦ H (unitInterval.symm z.1, z.2)
  have hfcont : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_fst.subtype_val.smul continuous_snd.subtype_val
  have hg : Continuous g := by
    apply hH.comp
    fun_prop
  have hfsurj : Function.Surjective f := by
    intro x
    by_cases hx : x.1 = 0
    · let i : Fin d := ⟨0, hd⟩
      let s : S := ⟨Pi.single i 1, by simp [Pi.norm_single]⟩
      refine ⟨(0, s), ?_⟩
      apply Subtype.ext
      simp [f, hx]
    · let t : unitInterval := ⟨‖x.1‖, by exact ⟨norm_nonneg _, x.2⟩⟩
      let s : S := ⟨(‖x.1‖)⁻¹ • x.1, by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩
      refine ⟨(t, s), ?_⟩
      apply Subtype.ext
      dsimp [f, t, s]
      exact smul_inv_smul₀ (norm_ne_zero_iff.mpr hx) _
  have hgf : Function.FactorsThrough g f := by
    intro z z' heq
    have hn : (z.1 : ℝ) = (z'.1 : ℝ) := by
      have he := congrArg (fun q : D ↦ ‖q.1‖) heq
      simpa [f, norm_smul, z.2.2, z'.2.2, Real.norm_eq_abs,
        abs_of_nonneg z.1.2.1, abs_of_nonneg z'.1.2.1] using he
    have ht : z.1 = z'.1 := Subtype.ext hn
    by_cases hz : (z.1 : ℝ) = 0
    · have hz0 : z.1 = 0 := Subtype.ext hz
      have hz0' : z'.1 = 0 := ht.symm.trans hz0
      simp [g, hz0, hz0', hH1]
    · have hs : z.2 = z'.2 := by
        apply Subtype.ext
        have he : (z.1 : ℝ) • z.2.1 = (z.1 : ℝ) • z'.2.1 := by
          simpa only [f, hn] using congrArg Subtype.val heq
        have hi := congrArg (fun v : Fin d → ℝ ↦ (z.1 : ℝ)⁻¹ • v) he
        simpa only [inv_smul_smul₀ hz] using hi
      simp only [g, ht, hs]
  have : CompactSpace S := by
    apply isCompact_iff_compactSpace.mp
    have hc : IsCompact (Set.pi Set.univ (fun _ : Fin d ↦ Set.Icc (-1 : ℝ) 1)) :=
      isCompact_univ_pi fun _ ↦ isCompact_Icc
    apply hc.of_isClosed_subset (isClosed_eq continuous_norm continuous_const)
    intro v hv i hi
    have h := norm_le_pi_norm v i
    rw [hv, Real.norm_eq_abs] at h
    exact abs_le.mp h
  let F : C(unitInterval × S, D) := ⟨f, hfcont⟩
  have hq : Topology.IsQuotientMap F :=
    Topology.IsQuotientMap.of_surjective_continuous hfsurj hfcont
  let G : C(D, Y) := hq.lift ⟨g, hg⟩ hgf
  refine ⟨G, G.continuous, ?_⟩
  intro s
  have hc := congrArg (fun k : C(unitInterval × S, Y) ↦ k (1, s))
    (hq.lift_comp ⟨g, hg⟩ hgf)
  change G (f (1, s)) = g (1, s) at hc
  have hf1 : f (1, s) = ⟨s.val, le_of_eq s.property⟩ := by
    apply Subtype.ext
    change (1 : ℝ) • s.val = s.val
    exact one_smul ℝ _
  have hg1 : g (1, s) = b s := by simp [g, hH0]
  rw [hf1, hg1] at hc
  exact hc


end HolomorphicAnosov

