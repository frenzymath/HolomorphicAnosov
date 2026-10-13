import HolomorphicAnosov.Analysis.Calculus.BoundedLipschitzJetsSupport.LinearRepresentativeBound
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter _root_.Topology
namespace HolomorphicAnosov
open BoundedLipschitzJets

/-- HPS, *Invariant Manifolds*, pp.33–34: identify the invariant own jet with
the invariant linear jet. This is the final uniqueness argument, with the
local jet comparison supplied as `hstep`. It permits varying normed fibres
and any point-valued return, including a noninvertible stable return.

Write D(i) for the norm of the difference of the two jets. The uniform bound
and the local comparison give D(i) ≤ q^n M for every n by induction. Since
q<1 the right side tends to zero, so the jets coincide. Their quotient
equality says that the translated graph minus the linear map is little-o
on the punctured neighborhood of zero. Both representatives vanish at zero,
so the estimate also holds on the full neighborhood filter. The derivative
criterion identifies P(i) with the derivative at the anchor. No completeness
of the bounded-jet space or continuity of the slope section is required. -/
theorem parameter_graph_jet_identification
    {I : Type*} (X Y : I → Type*)
    [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    [∀ i, NormedAddCommGroup (Y i)] [∀ i, NormedSpace ℝ (Y i)]
    (R : I → I) (s : ∀ i, X i → Y i) (x : ∀ i, X i)
    (P : ∀ i, X i →L[ℝ] Y i) (Q : ∀ i, BoundedRepresentative (X i) (Y i))
    (hQ : ∀ i v, (Q i : X i → Y i) v = s i (x i + v) - s i (x i))
    (q : NNReal) (hq : (q : ℝ) < 1) (M : ℝ)
    (hbound : ∀ i, ‖jetClass (X i) (Y i) (Q i) - linearJet (X i) (Y i) (P i)‖ ≤ M)
    (hstep : ∀ i, ‖jetClass (X i) (Y i) (Q i) - linearJet (X i) (Y i) (P i)‖ ≤
      (q : ℝ) * ‖jetClass (X (R i)) (Y (R i)) (Q (R i)) -
        linearJet (X (R i)) (Y (R i)) (P (R i))‖) :
    ∀ i, HasFDerivAt (s i) (P i) (x i) := by
  let D : I → ℝ := fun i ↦
    ‖jetClass (X i) (Y i) (Q i) - linearJet (X i) (Y i) (P i)‖
  have hi : ∀ n : ℕ, ∀ i, D i ≤ (q : ℝ)^n * M := by
    intro n
    induction n with
    | zero => simpa only [pow_zero, one_mul] using hbound
    | succ n ih =>
      intro i
      calc
        D i ≤ (q : ℝ) * D (R i) := hstep i
        _ ≤ (q : ℝ) * ((q : ℝ)^n * M) := mul_le_mul_of_nonneg_left (ih _) q.2
        _ = (q : ℝ)^(n+1) * M := by rw [pow_succ']; exact (mul_assoc _ _ _).symm
  intro i
  have hlim : Tendsto (fun n : ℕ ↦ (q : ℝ)^n * M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one q.2 hq).mul_const M
  have hzero : D i = 0 := le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall (fun n ↦ hi n i)))
    (norm_nonneg _)
  have heq : jetClass (X i) (Y i) (Q i) = linearJet (X i) (Y i) (P i) :=
    sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have ho := (jetClass_eq_iff (X i) (Y i) (Q i)
    (linearRepresentative (X i) (Y i) (P i))).mp heq
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  rw [← nhdsNE_sup_pure (0 : X i), Filter.eventually_sup]
  constructor
  · filter_upwards [ho ε hε] with v hv
    simpa only [Pi.sub_apply, linearRepresentative, hQ] using hv
  · simp

end HolomorphicAnosov
