import Mathlib.LinearAlgebra.Basis.Basic
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleBasisIndex

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Assemble the actual degreewise circle bases, using the empty basis precisely
where the source circle profile says its cohomology is zero. Hatcher p.216. -/
def circleProfileBasis {H : ℕ → Type}
    [∀ q, AddCommGroup (H q)] [∀ q, Module ℚ (H q)]
    (B₀ : Module.Basis Unit ℚ (H 0)) (B₁ : Module.Basis Unit ℚ (H 1))
    (hz : ∀ q, 2 ≤ q → Subsingleton (H q)) (q : ℕ) :
    Module.Basis (circleBasisIndex q) ℚ (H q) := by
  cases q with
  | zero => exact B₀
  | succ q =>
    cases q with
    | zero => exact B₁
    | succ q =>
      have := hz (q + 2) (by omega)
      have hi : IsEmpty (circleBasisIndex (q + 2)) := by
        simpa [circleBasisIndex, show ¬ q + 2 ≤ 1 by omega] using (inferInstance : IsEmpty Empty)
      exact Module.Basis.empty _

end HolomorphicAnosov.TorusRationalCupBasisKronecker
