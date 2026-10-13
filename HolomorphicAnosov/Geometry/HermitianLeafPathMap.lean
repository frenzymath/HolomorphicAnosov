import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-! This file proves functoriality and contraction estimates for intrinsic leaf lengths. -/



open Set _root_.MeasureTheory
open scoped ContDiff Manifold ENNReal
noncomputable section
namespace HolomorphicAnosov
namespace IntrinsicPiecewiseC1Path

variable {r s d : ℕ} {L K M : Type*}
  [TopologicalSpace L] [ChartedSpace (Fin r → ℝ) L]
  [TopologicalSpace K] [ChartedSpace (Fin s → ℝ) K]
  [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]

/-- Compose the path pieces, retaining the same times and junctions. -/
def map {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (a : L → K) (ha : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) 1 a) :
    IntrinsicPiecewiseC1Path (r := s) (a x) (a y) where
  n := p.n
  time := p.time
  time_strictMono := p.time_strictMono
  time_zero := p.time_zero
  time_one := p.time_one
  piece i := a ∘ p.piece i
  piece_c1 i := ha.comp_contMDiffOn (p.piece_c1 i)
  source := by change a (p.piece 0 0) = a x; rw [p.source]
  target := by change a (p.piece (Fin.last p.n) 1) = a y; rw [p.target]
  junction i := congrArg a (p.junction i)

/-- The actual velocity transforms by the derivative of the supplied smooth map. -/
theorem map_velocity {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (a : L → K) (ha : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) 1 a)
    (i : Fin (p.n + 1)) (t : ℝ) (ht : t ∈ p.pieceInterval i) :
    (p.map a ha).velocity i t =
      mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) a (p.piece i t) (p.velocity i t) := by
  have hu : UniqueMDiffOn 𝓘(ℝ, ℝ) (p.pieceInterval i) := by
    apply uniqueMDiffOn_iff_uniqueDiffOn.mpr
    exact uniqueDiffOn_Icc (p.time_strictMono Fin.castSucc_lt_succ)
  exact congrArg
    (fun A : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ]
      TangentSpace 𝓘(ℝ, Fin s → ℝ) (a (p.piece i t)) ↦ A (1 : ℝ))
    (mfderiv_comp_mfderivWithin t (ha.mdifferentiable (by simp) _)
      ((p.piece_c1 i).mdifferentiableOn (by simp) t ht) (hu t ht))

/-- A pointwise pullback-norm bound integrates to the finite-piece length bound. -/
theorem map_length_le {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (a : L → K) (ha : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) 1 a)
    (incL : L → M) (incK : K → M) (h : HermitianTangentMetricCore d M)
    (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ z (v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z),
      leafPullbackHermitianNorm incK h (a z)
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) a z v) ≤
      c * leafPullbackHermitianNorm incL h z v) :
    (p.map a ha).length incK h ≤ ENNReal.ofReal c * p.length incL h := by
  unfold length
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  change (∫⁻ t in p.pieceInterval i, ENNReal.ofReal ((p.map a ha).speed incK h i t)) ≤ _
  calc
    _ ≤ ∫⁻ t in p.pieceInterval i, ENNReal.ofReal c * ENNReal.ofReal (p.speed incL h i t) := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      rw [← ENNReal.ofReal_mul hc]
      apply ENNReal.ofReal_le_ofReal
      change leafPullbackHermitianNorm incK h (a (p.piece i t))
        ((p.map a ha).velocity i t) ≤ c * p.speed incL h i t
      rw [map_velocity p a ha i t ht]
      exact hbound (p.piece i t) (p.velocity i t)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Taking the infimum gives contraction of the exact ENNReal intrinsic distance, including infinite distances. Strict positivity avoids the empty-infimum 0·∞ case. -/
theorem map_edist_le (a : L → K)
    (ha : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) 1 a)
    (incL : L → M) (incK : K → M) (h : HermitianTangentMetricCore d M)
    (c : ℝ) (hc : 0 < c)
    (hbound : ∀ z (v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z),
      leafPullbackHermitianNorm incK h (a z)
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) a z v) ≤
      c * leafPullbackHermitianNorm incL h z v) (x y : L) :
    intrinsicHermitianLeafEDist (r := s) incK h (a x) (a y) ≤
      ENNReal.ofReal c * intrinsicHermitianLeafEDist (r := r) incL h x y := by
  unfold intrinsicHermitianLeafEDist
  rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hc)) ENNReal.ofReal_ne_top]
  apply le_iInf
  intro p
  exact (iInf_le _ (p.map a ha)).trans (map_length_le p a ha incL incK h c hc.le hbound)

/-- Transfer the ambient tangent estimate through the inclusion chain rule. -/
theorem norm_bound_of_ambient
    (a : L → K) (ha : ContMDiff 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) 1 a)
    (incL : L → M) (incK : K → M)
    (hL : ContMDiff 𝓘(ℝ, Fin r → ℝ) (realModel d) 1 incL)
    (hK : ContMDiff 𝓘(ℝ, Fin s → ℝ) (realModel d) 1 incK)
    (g : M → M) (hg : ContMDiff (realModel d) (realModel d) 1 g)
    (heq : incK ∘ a = g ∘ incL) (h : HermitianTangentMetricCore d M) (c : ℝ)
    (hbound : ∀ z (v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z),
      Real.sqrt (hermitianTangentRealPairing h (g (incL z))
        (mfderiv (realModel d) (realModel d) g (incL z)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) incL z v))
        (mfderiv (realModel d) (realModel d) g (incL z)
          (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) incL z v))) ≤
      c * leafPullbackHermitianNorm incL h z v) :
    ∀ z (v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z),
      leafPullbackHermitianNorm incK h (a z)
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) a z v) ≤
      c * leafPullbackHermitianNorm incL h z v := by
  intro z v
  have hd : mfderiv 𝓘(ℝ, Fin s → ℝ) (realModel d) incK (a z)
      (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, Fin s → ℝ) a z v) =
      mfderiv (realModel d) (realModel d) g (incL z)
        (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) incL z v) := by
    change @Eq (ComplexModel d) _ _
    have he := congrArg (fun q : L → M ↦
      (mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) q z v : ComplexModel d)) heq
    simpa only [mfderiv_comp z (hK.mdifferentiable (by simp) _) (ha.mdifferentiable (by simp) _),
      mfderiv_comp z (hg.mdifferentiable (by simp) _) (hL.mdifferentiable (by simp) _),
      ContinuousLinearMap.comp_apply] using he
  have hp : incK (a z) = g (incL z) := congrFun heq z
  let H : M → ComplexModel d → ComplexModel d → ℝ :=
    fun x v w ↦ hermitianTangentRealPairing h x v w
  change Real.sqrt (H (incK (a z)) _ _) ≤ _
  rw [hd, hp]
  exact hbound z v

end IntrinsicPiecewiseC1Path
end HolomorphicAnosov
end
