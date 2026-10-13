import HolomorphicAnosov.Topology.ZeroAugmentShortComplexMapHomologyIsIso

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `algebra.def_zero_augment_homology_iso`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- Augmentation by zero merely shifts ordinary homology, including degree
zero. Source: Hatcher p.118, via the explicit cycle/boundary comparison.
Compose the canonical isomorphism to the augmented three-term homology, the
isomorphism induced by the comparison, and the inverse canonical isomorphism
from the ordinary three-term homology. -/
def zeroAugmentHomologyIso (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)).homology (n + 1) ≅
      K.homology n := by
  have := zeroAugmentShortComplexMap_homology_isIso K n
  exact (ChainComplex.augment K (0 : K.X 0 ⟶ 0) (comp_zero)).homologyIsoSc'
      (n + 2) (n + 1) n (by simp) (by simp) ≪≫
    asIso (ShortComplex.homologyMap (zeroAugmentShortComplexMap K n)) ≪≫
    (K.homologyIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).symm

end HolomorphicAnosov.GoodPair

