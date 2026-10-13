import Mathlib.Data.Nat.Basic

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- Circle basis indices in degrees zero and one. -/
abbrev circleBasisIndex (q : ℕ) : Type := if q ≤ 1 then Unit else Empty

end HolomorphicAnosov.TorusRationalCupBasisKronecker
