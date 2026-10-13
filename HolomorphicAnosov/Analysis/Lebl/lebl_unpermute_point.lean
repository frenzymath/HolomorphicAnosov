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
lemma lebl_unpermute_point {n : ℕ} (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1) → ℂ) :
    leblUnpermuteGraphCoordinates σ (fun i ↦ p (σ i.castSucc))
      (p (σ (Fin.last n))) = p := by
  ext i
  change Fin.snoc (α := fun _ ↦ ℂ) (fun k ↦ p (σ k.castSucc))
    (p (σ (Fin.last n))) (σ.symm i) = p i
  have he : Fin.snoc (α := fun _ ↦ ℂ) (fun k ↦ p (σ k.castSucc))
      (p (σ (Fin.last n))) = fun k ↦ p (σ k) :=
    Fin.snoc_init_self (fun k ↦ p (σ k))
  rw [he]
  exact congrArg p (σ.apply_symm_apply i)

end HolomorphicAnosov.Analysis
