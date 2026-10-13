import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

noncomputable section
open Set Filter
open _root_.MeasureTheory
open scoped _root_.Topology
open scoped Manifold ContDiff ENNReal
namespace HolomorphicAnosov
namespace IntrinsicPiecewiseC1Path
variable {r : ℕ} {L : Type*} [TopologicalSpace L]
  [ChartedSpace (Fin r → ℝ) L]

/-- Reverse the literal finite C¹ path, with division times reflected in 1/2 (Lee Proposition 11.20 p.278).-/
def reverse {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y) :
    IntrinsicPiecewiseC1Path (r := r) y x where
  n := p.n
  time k := 1 - p.time k.rev
  time_strictMono := by
    intro k l hkl
    have h := p.time_strictMono (Fin.rev_lt_rev.mpr hkl)
    linarith
  time_zero := by simp [p.time_one]
  time_one := by simp [p.time_zero]
  piece k t := p.piece k.rev (1 - t)
  piece_c1 k := by
    have hf : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun t : ℝ => 1 - t) := by
      rw [contMDiff_iff_contDiff]
      fun_prop
    apply (p.piece_c1 k.rev).comp hf.contMDiffOn
    intro t ht
    simp only [Set.mem_Icc, Fin.rev_castSucc, Fin.rev_succ] at ht ⊢
    constructor <;> linarith
  source := by simpa using p.target
  target := by simpa using p.source
  junction k := by
    simpa only [Fin.rev_castSucc, Fin.rev_succ, sub_sub_cancel, Fin.succ_castSucc] using (p.junction k.rev).symm

/-- Reversing a finite piece negates its literal tangent velocity (Lee Proposition 11.20 p.278; the chain rule applied to `1-t`).-/
theorem reverse_velocity [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (k : Fin (p.n + 1)) (t : ℝ) (ht : t ∈ p.reverse.pieceInterval k) :
    p.reverse.velocity k t = -p.velocity k.rev (1 - t) := by
  have hm : MapsTo (fun t : ℝ => 1 - t) (p.reverse.pieceInterval k)
      (p.pieceInterval k.rev) := by
    intro t ht
    simp only [pieceInterval, reverse, Set.mem_Icc, Fin.rev_castSucc, Fin.rev_succ] at ht ⊢
    constructor <;> linarith
  have hu : UniqueDiffOn ℝ (p.reverse.pieceInterval k) :=
    uniqueDiffOn_Icc (p.reverse.time_strictMono Fin.castSucc_lt_succ)
  have hd : HasDerivWithinAt (fun t : ℝ => 1 - t) (-1) (p.reverse.pieceInterval k) t :=
    ((hasDerivAt_id t).const_sub 1).hasDerivWithinAt
  have hf : MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => 1 - t)
      (p.reverse.pieceInterval k) t := hd.differentiableWithinAt.mdifferentiableWithinAt
  have he := mfderivWithin_comp t
    ((p.piece_c1 k.rev).mdifferentiableOn (by simp) (1-t) (hm ht)) hf hm
    (hu.uniqueMDiffOn t ht)
  change (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ)
    (p.piece k.rev ∘ (fun t : ℝ => 1-t)) (p.reverse.pieceInterval k) t) (1 : ℝ) = _
  rw [he]
  change (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) (p.piece k.rev)
    (p.pieceInterval k.rev) (1-t))
    ((mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => 1-t) (p.reverse.pieceInterval k) t) (1 : ℝ)) = _
  have hd1 : (mfderivWithin 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => 1-t)
      (p.reverse.pieceInterval k) t) (1 : ℝ) = (-1 : ℝ) := by
    rw [mfderivWithin_eq_fderivWithin]
    change (fderivWithin ℝ (fun t : ℝ => 1-t) (p.reverse.pieceInterval k) t) (1 : ℝ) = -1
    rw [hd.hasFDerivWithinAt.fderivWithin (hu t ht)]
    exact ContinuousLinearMap.toSpanSingleton_apply_one _ _
  rw [hd1]
  exact (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, Fin r → ℝ) (p.piece k.rev)
    (p.pieceInterval k.rev) (1-t)).map_neg
      (show TangentSpace 𝓘(ℝ) (1-t) from (1 : ℝ))

/-- Reflection preserves the speed integral on a reflected compact interval (Lee Proposition 11.20 p.278, reversal reparametrization).-/
theorem lintegral_reflection (F : ℝ → ℝ≥0∞) (a b : ℝ) :
    (∫⁻ t in Icc (1-b) (1-a), F (1-t)) = ∫⁻ t in Icc a b, F t := by
  have hpre : (fun t : ℝ => 1-t) ⁻¹' Icc a b = Icc (1-b) (1-a) := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [← hpre]
  exact ((volume : Measure ℝ).measurePreserving_sub_left (1 : ℝ)).setLIntegral_comp_preimage_emb
    (Homeomorph.subLeft (1 : ℝ)).measurableEmbedding F (Icc a b)

/-- Reversal preserves the given Hermitian pullback speed (Lee Proposition 11.20 p.278 and Demailly VI §4).-/
theorem reverse_hermitian_speed
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (h : HermitianTangentMetricCore d M) (j : L → M)
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    (k : Fin (p.n + 1)) (t : ℝ) (ht : t ∈ p.reverse.pieceInterval k) :
    p.reverse.speed j h k t = p.speed j h k.rev (1-t) := by
  unfold speed leafPullbackHermitianNorm leafPullbackHermitianPairing
  rw [reverse_velocity p k t ht]
  unfold hermitianTangentRealPairing hermitianTangentPairing
  change Real.sqrt ((h (j (p.piece k.rev (1-t)))).inner
    ((complexTangentToReal d (j (p.piece k.rev (1-t)))).symm
      ((mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j (p.piece k.rev (1-t)))
        (-p.velocity k.rev (1-t))))
    ((complexTangentToReal d (j (p.piece k.rev (1-t)))).symm
      ((mfderiv 𝓘(ℝ, Fin r → ℝ) (realModel d) j (p.piece k.rev (1-t)))
        (-p.velocity k.rev (1-t))))).re = _
  let : InnerProductSpace.Core ℂ (TangentSpace (complexModel d) (j (p.piece k.rev (1-t)))) :=
    h (j (p.piece k.rev (1-t)))
  simp only [map_neg, InnerProductSpace.Core.inner_neg_left,
    InnerProductSpace.Core.inner_neg_right, neg_neg]

/-- Reversal preserves the literal Hermitian length of the original finite path (Lee Proposition 11.20 p.278).-/
theorem reverse_hermitian_length
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (h : HermitianTangentMetricCore d M) (j : L → M)
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y) :
    p.reverse.length j h = p.length j h := by
  unfold length
  calc
    _ = ∑ k : Fin (p.n + 1), ∫⁻ t in p.pieceInterval k.rev,
        ENNReal.ofReal (p.speed j h k.rev t) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = ∫⁻ t in p.reverse.pieceInterval k,
            ENNReal.ofReal (p.speed j h k.rev (1-t)) := by
          apply setLIntegral_congr_fun measurableSet_Icc
          intro t ht
          exact congrArg ENNReal.ofReal (reverse_hermitian_speed h j p k t ht)
        _ = _ := by
          simp only [pieceInterval, reverse]
          convert lintegral_reflection (fun t => ENNReal.ofReal (p.speed j h k.rev t))
              (p.time k.rev.castSucc) (p.time k.rev.succ) using 1 <;>
            congr 3 <;> first | exact congrArg (fun k => 1 - p.time k) (Fin.rev_castSucc k) | exact congrArg (fun k => 1 - p.time k) (Fin.rev_succ k)
    _ = _ := by
      let F : Fin (p.n + 1) → ℝ≥0∞ := fun k =>
        ∫⁻ t in p.pieceInterval k, ENNReal.ofReal (p.speed j h k t)
      change ∑ k : Fin (p.n + 1), F (Fin.revPerm k) = ∑ k : Fin (p.n + 1), F k
      exact Equiv.sum_comp Fin.revPerm F

/-- The original Hermitian length infimum is symmetric, including infinite values (Lee Proposition 11.20 p.278).-/
theorem intrinsicHermitianLeafEDist_comm
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel d) M]
    [IsManifold 𝓘(ℝ, Fin r → ℝ) ∞ L]
    (h : HermitianTangentMetricCore d M) (j : L → M) (x y : L) :
    intrinsicHermitianLeafEDist (r := r) j h x y = intrinsicHermitianLeafEDist (r := r) j h y x := by
  have hle (x y : L) : intrinsicHermitianLeafEDist (r := r) j h x y ≤
      intrinsicHermitianLeafEDist (r := r) j h y x := by
    apply le_iInf
    intro p
    calc
      _ ≤ p.reverse.length j h := iInf_le _ p.reverse
      _ = _ := reverse_hermitian_length h j p
  exact le_antisymm (hle x y) (hle y x)

end IntrinsicPiecewiseC1Path
end HolomorphicAnosov
