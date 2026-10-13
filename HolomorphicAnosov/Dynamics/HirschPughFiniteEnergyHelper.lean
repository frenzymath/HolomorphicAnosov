import HolomorphicAnosov.Dynamics.HirschPughFactOneData
import HolomorphicAnosov.Analysis.MatherFiniteEnergyContraction

namespace HolomorphicAnosov
open Set
open scoped ContDiff Manifold Topology _root_.Topology
noncomputable section
universe u v
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {M : Type v} [TopologicalSpace M] [ChartedSpace E M]
variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The finite Mather energy associated with a hyperbolic datum and a chosen
positive integer horizon. -/
def hyperbolicFiniteEnergy
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum (E := E) (f := f) Λ) (q : ℕ)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x) : ℝ :=
  ∑ j ∈ Finset.range q,
    hyperbolicRiemannianNorm H.originalMetric
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j]) x v) ^ 2

/-- Hirsch–Pugh's finite-energy shift contracts whenever the original all-time
bound has coefficient `C * rate^n`. This is the scalar finite-sum step before
constructing or smoothing the ambient tensor. -/
theorem hyperbolicFiniteEnergy_contract
    {f : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞} {Λ : Set M}
    (H : HyperbolicSetFactOneDatum f Λ)
    {q : ℕ} (hq : 0 < q) (hsmall : H.C * H.rate ^ q < 1)
    (g : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (x : M)
    (v : TangentSpace 𝓘(ℝ, E) x)
    (hb : ∀ n : ℕ,
      hyperbolicRiemannianNorm H.originalMetric
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[n]) x v) ≤
        H.C * H.rate ^ n * hyperbolicRiemannianNorm H.originalMetric v) :
    hyperbolicFiniteEnergy H q g (g x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) ≤
      (1 - (1 - (H.C * H.rate ^ q) ^ 2) / ((q : ℝ) * H.C ^ 2)) *
        hyperbolicFiniteEnergy H q g x v := by
  let b (j : ℕ) := hyperbolicRiemannianNorm H.originalMetric
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j]) x v)
  have hz : b 0 = hyperbolicRiemannianNorm H.originalMetric v := by
    simp only [b, Function.iterate_zero, mfderiv_id]
    rfl
  have hb' (n : ℕ) : b n ≤ H.C * H.rate ^ n * b 0 := by
    rw [hz]
    exact hb n
  have hshift : hyperbolicFiniteEnergy H q g (g x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) =
      hyperbolicFiniteEnergy H q g x v - b 0 ^ 2 + b q ^ 2 := by
    have hs : hyperbolicFiniteEnergy H q g (g x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x v) =
        ∑ j ∈ Finset.range q, b (j + 1) ^ 2 := by
      dsimp [hyperbolicFiniteEnergy]
      apply Finset.sum_congr rfl
      intro j hj
      have hcomp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j + 1]) x =
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j]) (g x)).comp
            (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x) := by
        rw [Function.iterate_succ, mfderiv_comp x
          ((g.contMDiff.iterate j).mdifferentiable (by simp) (g x))
          (g.mdifferentiable (by simp) x)]
      have hv := congrArg (fun L ↦ hyperbolicRiemannianNorm H.originalMetric (L v)) hcomp
      have hv2 := congrArg (fun z : ℝ ↦ z ^ 2) hv
      change hyperbolicRiemannianNorm H.originalMetric
          ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j + 1]) x) v) ^ 2 =
        hyperbolicRiemannianNorm H.originalMetric
          ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((g : M → M)^[j]) (g x))
            ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) g x) v)) ^ 2 at hv2
      simpa only [b] using hv2.symm
    have hsum := Finset.sum_range_succ' (fun j ↦ b j ^ 2) q
    have hsum' := Finset.sum_range_succ (fun j ↦ b j ^ 2) q
    rw [hs]
    change _ = (∑ j ∈ Finset.range q, b j ^ 2) - _ + b q ^ 2
    linarith
  have hs := FactOneFiniteEnergy.scalar_energy_contraction H.C H.rate H.one_le_C
      H.rate_pos.le H.rate_lt_one.le q hq hsmall b
      (fun n ↦ Real.sqrt_nonneg _) hb'
  rw [hshift]
  simpa only [hyperbolicFiniteEnergy, b] using hs

end
end HolomorphicAnosov

