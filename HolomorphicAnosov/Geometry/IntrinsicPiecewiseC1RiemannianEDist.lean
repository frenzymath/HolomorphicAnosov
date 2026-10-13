import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import HolomorphicAnosov.Geometry.Riemannian.FiniteRiemannianChain

noncomputable section
open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal Bundle
namespace HolomorphicAnosov
variable {r : ℕ} {L : Type*} [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
  [∀ x : L, ENorm (TangentSpace 𝓘(ℝ, Fin r → ℝ) x)]
  [∀ x : L, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, Fin r → ℝ) x)]

/-! Comparison of piecewise C¹ and C¹ path distances. -/

/-- Finite piecewise C¹ and C¹ paths define the same length infimum for any extended homogeneous tangent norm on the original real leaf (Lee §11 pp.275–279 and the cited Mathlib path-length lemmas).-/
theorem intrinsicPiecewiseC1Path_riemannianEDist (x y : L) :
    Manifold.riemannianEDist 𝓘(ℝ, Fin r → ℝ) x y =
      ⨅ p : IntrinsicPiecewiseC1Path (r := r) x y,
        ∑ k : Fin (p.n + 1), ∫⁻ t in p.pieceInterval k, ‖p.velocity k t‖ₑ := by
  apply le_antisymm
  · apply le_iInf
    intro p
    have hj (k : Fin p.n) :
        p.piece k.castSucc (p.time k.castSucc.succ) =
          p.piece k.succ (p.time k.succ.castSucc) := by
      simpa only [Fin.castSucc_succ] using p.junction k
    have hc := riemannianEDist_le_fin_chain (I := 𝓘(ℝ, Fin r → ℝ)) p.n
      (fun k ↦ p.piece k (p.time k.castSucc))
      (fun k ↦ p.piece k (p.time k.succ)) hj
    simp only [Fin.castSucc_zero, p.time_zero, p.source,
      Fin.succ_last, p.time_one, p.target] at hc
    apply hc.trans
    apply Finset.sum_le_sum
    intro k hk
    have hb := Manifold.riemannianEDist_le_pathELength (p.piece_c1 k) rfl rfl
      (p.time_strictMono.monotone (Fin.castSucc_le_succ k))
    exact hb.trans_eq Manifold.pathELength_eq_lintegral_mfderivWithin_Icc
  · apply le_of_forall_gt
    intro a ha
    obtain ⟨c, hc0, hc1, hc, hlength⟩ := Manifold.exists_lt_of_riemannianEDist_lt ha
    let times : Fin 2 → ℝ := fun k ↦ (k : ℝ)
    let p : IntrinsicPiecewiseC1Path (r := r) x y := {
      n := 0
      time := times
      time_strictMono := by
        intro k l hkl
        simpa [times] using (show (k : ℝ) < (l : ℝ) by exact_mod_cast hkl)
      time_zero := by simp [times]
      time_one := by simp [times]
      piece := fun _ ↦ c
      piece_c1 := by
        intro k
        fin_cases k
        simpa [times] using hc
      source := hc0
      target := hc1
      junction := fun k ↦ Fin.elim0 k }
    apply (iInf_le _ p).trans_lt
    have hp : (∑ k : Fin (p.n + 1), ∫⁻ t in p.pieceInterval k, ‖p.velocity k t‖ₑ) =
        Manifold.pathELength 𝓘(ℝ, Fin r → ℝ) c 0 1 := by
      rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
      simp [p, IntrinsicPiecewiseC1Path.pieceInterval, IntrinsicPiecewiseC1Path.velocity, times]
      rfl
    exact hp.trans_lt hlength
end HolomorphicAnosov
