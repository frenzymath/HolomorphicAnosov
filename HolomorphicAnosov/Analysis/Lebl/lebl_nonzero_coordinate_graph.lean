import HolomorphicAnosov.Analysis.Complex.LeblPolydiscCoordinateDerivatives
import HolomorphicAnosov.Analysis.Complex.PolydiscCauchyPowerSeries
import HolomorphicAnosov.Analysis.Complex.WindingHolomorphicZeroCount
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Connected.Basic
import HolomorphicAnosov.Analysis.Lebl.leblCoordinatePolydisc
import HolomorphicAnosov.Analysis.Lebl.leblUnpermuteGraphCoordinates
import HolomorphicAnosov.Analysis.Lebl.leblHolomorphicZeroSetGraphAt
import HolomorphicAnosov.Analysis.Lebl.lebl_product_implicit

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_nonzero_coordinate_graph {n : ℕ}
    {U : Set (Fin (n + 1) → ℂ)} {h : (Fin (n + 1) → ℂ) → ℂ}
    (hU : IsOpen U) (hh : ContDiffOn ℂ ∞ h U) {p : Fin (n + 1) → ℂ}
    (hp : p ∈ U) (hhp : h p = 0) (j : Fin (n + 1))
    (hj : HolomorphicAnosov.Analysis.Complex.LeblPolydisc.coordinateDerivative j h p ≠ 0) :
    leblHolomorphicZeroSetGraphAt U h p := by
  classical
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap j (Fin.last n)
  let l : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi fun i ↦ Fin.snoc
      (α := fun _ ↦ ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ)
      (fun k ↦ (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _))
      (ContinuousLinearMap.snd ℂ _ _) (σ.symm i)
  let pp : (Fin n → ℂ) × ℂ := (fun i ↦ p (σ i.castSucc), p (σ (Fin.last n)))
  have hl : ∀ z, l z = leblUnpermuteGraphCoordinates σ z.1 z.2 := by
    intro z
    ext i
    change (Fin.snoc
      (α := fun _ ↦ ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ)
      (fun k ↦ (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _))
      (ContinuousLinearMap.snd ℂ _ _) (σ.symm i)) z = _
    dsimp only [leblUnpermuteGraphCoordinates]
    generalize σ.symm i = k
    induction k using Fin.lastCases with
    | last => simp
    | cast k => simp
  have hlp : l pp = p := by
    rw [hl]
    ext i
    change Fin.snoc (α := fun _ ↦ ℂ) (fun k ↦ p (σ k.castSucc))
      (p (σ (Fin.last n))) (σ.symm i) = p i
    have he : Fin.snoc (α := fun _ ↦ ℂ) (fun k ↦ p (σ k.castSucc)) (p (σ (Fin.last n))) =
        fun k ↦ p (σ k) := Fin.snoc_init_self (fun k ↦ p (σ k))
    rw [he]
    exact congrArg p (σ.apply_symm_apply i)
  have hlinr : l (0, (1 : ℂ)) =
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.coordinateVector j := by
    rw [hl]
    ext i
    change Fin.snoc (α := fun _ ↦ ℂ) (0 : Fin n → ℂ) (1 : ℂ) (σ.symm i) =
      (Pi.single j 1 : Fin (n + 1) → ℂ) i
    by_cases hi : i = j
    · subst i
      simp [σ]
    · have hkl : σ.symm i ≠ Fin.last n := by
        intro he
        have he' := congrArg σ he
        simp [σ] at he'
        exact hi he'
      obtain ⟨k, hk⟩ := Fin.exists_castSucc_eq.mpr hkl
      rw [← hk, Fin.snoc_castSucc]
      simp [hi]
  let H : ((Fin n → ℂ) × ℂ) → ℂ := fun z ↦ h (l z)
  have hO : IsOpen (l ⁻¹' U) := hU.preimage l.continuous
  have hH : ContDiffOn ℂ ∞ H (l ⁻¹' U) := hh.comp l.contDiff.contDiffOn (by intro z hz; exact hz)
  have hpp : pp ∈ l ⁻¹' U := by simpa [hlp] using hp
  have hD := (hh.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hfH : fderiv ℂ H pp = (fderiv ℂ h p).comp l := by
    have hd : HasFDerivAt h (fderiv ℂ h p) (l pp) := by
      simpa [hlp] using hD.hasFDerivAt
    exact (hd.comp pp l.hasFDerivAt).fderiv
  let k : ℂ →L[ℂ] ℂ := fderiv ℂ H pp ∘L ContinuousLinearMap.inr ℂ (Fin n → ℂ) ℂ
  have hk1 : k 1 ≠ 0 := by
    simpa [k, hfH, hlinr,
      HolomorphicAnosov.Analysis.Complex.LeblPolydisc.coordinateDerivative] using hj
  have hki : k.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse
      (g := (k 1)⁻¹ • ContinuousLinearMap.id ℂ ℂ)
    · apply ContinuousLinearMap.ext
      intro z
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply, map_smul]
      have hz : k z = z • k 1 := by simpa using k.map_smul z (1 : ℂ)
      rw [hz]
      simp [smul_eq_mul, mul_left_comm, hk1]
    · apply ContinuousLinearMap.ext
      intro z
      simp only [ContinuousLinearMap.comp_apply, smul_apply,
        ContinuousLinearMap.id_apply]
      have hz : k z = z • k 1 := by simpa using k.map_smul z (1 : ℂ)
      rw [hz]
      simp [smul_eq_mul, mul_left_comm, hk1]
  obtain ⟨V, s, g, hV, hpV, hs, hgp, hg, hmaps, hinside, heq⟩ :=
    lebl_product_implicit hO hH hpp (by simpa [H, hlp] using hhp) hki
  obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp hV pp.1 hpV
  have hpoly : leblCoordinatePolydisc pp.1 (fun _ ↦ δ) = Metric.ball pp.1 δ := by
    ext y
    simp only [leblCoordinatePolydisc, mem_ofPred_eq, Metric.mem_ball, dist_eq_norm,
      pi_norm_lt_iff hδ]
    rfl
  refine ⟨⟨hp, hhp⟩, σ, pp.1, (fun _ ↦ δ), pp.2, s, g,
    (fun _ ↦ hδ), hs, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpoly]
    exact Metric.mem_ball_self hδ
  · simp [pp, hs]
  · rw [hpoly]
    exact hg.mono hδV
  · rw [hpoly]
    exact hmaps.mono_left hδV
  · intro y hy w hw
    rw [hpoly] at hy
    have hmem := hinside y (hδV hy) w hw
    simpa only [Set.mem_preimage, hl] using hmem
  · intro y hy w hw
    rw [hpoly] at hy
    simpa only [H, hl] using heq y (hδV hy) w hw

end HolomorphicAnosov.Analysis
