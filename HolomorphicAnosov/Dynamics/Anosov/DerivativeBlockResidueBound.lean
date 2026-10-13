import HolomorphicAnosov.Analysis.QuotientTimeToExponential
import HolomorphicAnosov.Dynamics.Anosov.RestrictedIterateDerivative
import HolomorphicAnosov.Dynamics.Anosov.IterateInvariant
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Topology.VectorBundle.Riemannian
import Mathlib.Tactic

noncomputable section
namespace HolomorphicAnosov
universe u
namespace UniformIterateBounds
open scoped Bundle ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : Type u} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
variable [Bundle.RiemannianBundle (fun x : X ↦ TangentSpace I x)]

omit [IsManifold I ∞ X] in
/-- Original derivative block composition and bounded residues give the quotient-time bound.
The derivative is literally that of the original diffeomorphism and its original invariant
subspace; all norm evaluations use the same supplied Riemannian fibre norms. -/
theorem derivative_block_residue_bound
    (f : Diffeomorph I I X X ∞) (P : RealTangentDistribution I X)
    (hP : ∀ x, (P x).map (mfderiv I I f x).toLinearMap = P (f x))
    (k : ℕ) (hk : 0 < k) (theta R : ℝ) (htheta : 0 ≤ theta) (hR : 0 ≤ R)
    (hblock : ∀ x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : X → X)^[k]) x v‖ ≤ theta * ‖v‖)
    (hresidue : ∀ r, r < k → ∀ x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : X → X)^[r]) x v‖ ≤ R * ‖v‖) :
    ∀ n x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : X → X)^[n]) x v‖ ≤ R * theta ^ (n / k) * ‖v‖ := by
  have haux : ∀ q r, r < k → ∀ x (v : TangentSpace I x), v ∈ P x →
      ‖mfderiv I I ((f : X → X)^[q * k + r]) x v‖ ≤ R * theta ^ q * ‖v‖ := by
    intro q
    induction q with
    | zero =>
      intro r hr x v hv
      rw [Nat.zero_mul, Nat.zero_add, pow_zero, mul_one]
      exact hresidue r hr x v hv
    | succ q ih =>
      intro r hr x v hv
      have hn : (q + 1) * k + r = q * k + r + k := by ring
      rw [hn, Function.iterate_add, mfderiv_comp x
        ((f.contMDiff.iterate (q * k + r)).mdifferentiableAt (by simp))
        ((f.contMDiff.iterate k).mdifferentiableAt (by simp))]
      have hw : mfderiv I I ((f : X → X)^[k]) x v ∈ P ((f : X → X)^[k] x) := by
        rw [← HolomorphicAnosov.real_distribution_iterate_invariant f P hP k x]
        exact Submodule.mem_map_of_mem hv
      calc
        ‖(mfderiv I I ((f : X → X)^[q * k + r]) ((f : X → X)^[k] x))
            (mfderiv I I ((f : X → X)^[k]) x v)‖
            ≤ R * theta ^ q * ‖mfderiv I I ((f : X → X)^[k]) x v‖ :=
          ih r hr _ _ hw
        _ ≤ R * theta ^ q * (theta * ‖v‖) :=
          mul_le_mul_of_nonneg_left (hblock x v hv) (mul_nonneg hR (pow_nonneg htheta q))
        _ = R * theta ^ (q + 1) * ‖v‖ := by rw [pow_succ]; ring
  intro n x v hv
  have h := haux (n / k) (n % k) (Nat.mod_lt n hk) x v hv
  have hn : n / k * k + n % k = n := by
    simpa only [Nat.mul_comm k (n / k)] using Nat.div_add_mod n k
  rw [hn] at h
  exact h

end UniformIterateBounds
end HolomorphicAnosov
