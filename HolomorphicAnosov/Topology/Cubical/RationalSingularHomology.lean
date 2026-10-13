import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits

/-!
# Rational singular homology of Euclidean subsets

Source: Hatcher, *Algebraic Topology*, p.153, homology with coefficients.
This specializes the singular homology functor to the regular rational module
and the original topological subtype of a subset of real coordinate space.
-/

noncomputable section

namespace HolomorphicAnosov.Cubical

/-- Native rational singular homology of an embedded subset with its original
subtype topology. This abbreviates Mathlib's singular homology functor with the
regular rational coefficient module; no cellular proxy or chosen invariant occurs.
Source: Hatcher, coefficient chains p. 153 and §3.A, pp. 261–266. -/
abbrev rationalSingularHomology {N : ℕ} (A : Set (Fin N → ℝ)) (q : ℕ) : ModuleCat ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) q).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of A)

end HolomorphicAnosov.Cubical
