import Mathlib.Data.Finset.Card
import HolomorphicAnosov.Topology.Homology.TorusRationalCupBasisKronecker.CircleBasisIndex

noncomputable section
namespace HolomorphicAnosov.TorusRationalCupBasisKronecker

/-- The exact basis index of the native Künneth degree sum: a degree pair, a
coordinate subset in the first factor, and a circle basis index in the second.
Hatcher, Theorem 3.15 and Example 3.16, p.216. -/
abbrev circleTensorIndex (n k : ℕ) :=
  Σ i : {i : ℕ × ℕ // i.1 + i.2 = k},
    {S : Finset (Fin n) // S.card = i.val.1} × circleBasisIndex i.val.2

end HolomorphicAnosov.TorusRationalCupBasisKronecker
