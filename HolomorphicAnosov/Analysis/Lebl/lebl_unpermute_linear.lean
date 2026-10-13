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
import HolomorphicAnosov.Analysis.Lebl.leblUnpermuteGraphCoordinates

namespace HolomorphicAnosov.Analysis

open Set
open scoped ContDiff

/-- Lebl, Tasty Bits of Several Complex Variables v3.4, §1.6 Theorem 1.6.2 p.36.
Public auxiliary result in the regular-hypersurface proof. -/
lemma lebl_unpermute_linear {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ l : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin (n + 1) → ℂ),
      ∀ z, l z = leblUnpermuteGraphCoordinates σ z.1 z.2 := by
  let l : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi fun i ↦ Fin.snoc
      (α := fun _ ↦ ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ)
      (fun k ↦ (ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℂ _ _))
      (ContinuousLinearMap.snd ℂ _ _) (σ.symm i)
  refine ⟨l, ?_⟩
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

end HolomorphicAnosov.Analysis
