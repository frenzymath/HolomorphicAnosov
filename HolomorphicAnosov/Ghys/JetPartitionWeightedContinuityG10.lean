import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Constructions

/-! Continuity of guarded weighted local coefficients. Source: Demailly IV.5.11(b), equation (5.12), p.208. -/

noncomputable section
namespace HolomorphicAnosov.Ghys

open Set Filter
open scoped Topology _root_.Topology BigOperators
attribute [local instance] Classical.propDecidable

/-- The finite sum of local complex coefficients multiplied by subordinate real weights is continuous when each term is extended by zero outside its open domain. -/
theorem continuous_guarded_weighted_sum
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (U : Fin n → Set X) (hU : ∀ i, IsOpen (U i))
    (rho : Fin n → X → ℝ) (hrho : ∀ i, Continuous (rho i))
    (hsupport : ∀ i, tsupport (rho i) ⊆ U i)
    (b : ∀ i, U i → ℂ) (hb : ∀ i, Continuous (b i)) :
    Continuous (fun x ↦ ∑ i : Fin n,
      if hi : x ∈ U i then (rho i x : ℂ) * b i ⟨x, hi⟩ else 0) := by
  classical
  apply continuous_finsetSum
  intro i _
  let term : X → ℂ := fun x ↦
    if hi : x ∈ U i then (rho i x : ℂ) * b i ⟨x, hi⟩ else 0
  have hterm : ContinuousOn term (U i) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    change Continuous (fun x : U i ↦ term x)
    have hmul : Continuous (fun x : U i ↦ (rho i x : ℂ) * b i x) :=
      (Complex.continuous_ofReal.comp ((hrho i).comp continuous_subtype_val)).mul (hb i)
    simpa [term] using hmul
  apply hterm.continuous_of_tsupport_subset (hU i)
  apply Set.Subset.trans (closure_mono ?_) (hsupport i)
  intro x hx
  change term x ≠ 0 at hx
  change rho i x ≠ 0
  intro hz
  apply hx
  dsimp [term]
  split_ifs <;> simp [hz]

end HolomorphicAnosov.Ghys
