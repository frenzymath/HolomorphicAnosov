import HolomorphicAnosov.Dynamics.ExponentialCutoffExtension.Base

open scoped ContDiff Manifold Topology _root_.Topology Bundle ENNReal
open TopologicalSpace Set

universe u
namespace HolomorphicAnosov.HPS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Package a continuous fibrewise norm into the arbitrary continuous tangent norm interface
used by the HPS exponential-cutoff construction on the whole base.  This is the GL1-to-GL2
interface: the supplied `ν` may be an adapted finite-energy norm, while all algebraic norm laws
and continuity remain explicit assumptions. -/
def continuousRestrictedTangentNorm_univ
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    (ν : ∀ x : M, TangentSpace 𝓘(ℝ, E) x → ℝ)
    (hnonneg : ∀ x v, 0 ≤ ν x v)
    (hzero : ∀ x v, ν x v = 0 ↔ v = 0)
    (hadd : ∀ x v w, ν x (v + w) ≤ ν x v + ν x w)
    (hsmul : ∀ x (a : ℝ) v, ν x (a • v) = |a| * ν x v)
    (hcont : Continuous (fun p : TangentBundle 𝓘(ℝ, E) M ↦ ν p.proj p.2)) :
    ExponentialCutoff.ContinuousRestrictedTangentNorm
      (E := E) (Set.univ : Set M) := by
  refine {
    value := fun p v => ν (p : M) v
    nonneg := ?_
    eq_zero_iff := ?_
    add_le := ?_
    smul := ?_
    continuous := ?_ }
  · intro p v
    exact hnonneg (p : M) v
  · intro p v
    exact hzero (p : M) v
  · intro p v w
    exact hadd (p : M) v w
  · intro p a v
    exact hsmul (p : M) a v
  · exact hcont.comp continuous_subtype_val

end HolomorphicAnosov.HPS

