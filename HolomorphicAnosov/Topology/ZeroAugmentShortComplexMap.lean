import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Source: Hatcher, *Algebraic Topology*, p.118 (augmented relative chains)
and p.124 (collapse naturality). DAG node: `algebra.def_zero_augment_short_complex_map`. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HolomorphicAnosov.GoodPair
universe u

/-- Compare the cycle/boundary short complexes after augmentation by zero.
Source: Hatcher's augmented relative sequence, p.118. Both chain components
are identities; the outgoing component at degree zero is the map from zero.
In positive degrees both squares reduce to identity laws. In degree zero the
outgoing square has zero augmentation on one side and the shape-forced zero
differential K.d 0 0 on the other. -/
def zeroAugmentShortComplexMap (K : ChainComplex (ModuleCat.{u} ℤ) ℕ) (n : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)).sc' (n + 2) (n + 1) n ⟶
      K.sc' (n + 1) n (n - 1) := by
  cases n with
  | zero =>
    exact { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 0
            comm₁₂ := by
              change 𝟙 _ ≫ K.d 1 0 = K.d 1 0 ≫ 𝟙 _
              simp
            comm₂₃ := by
              change 𝟙 _ ≫ K.d 0 0 = (0 : K.X 0 ⟶ (0 : ModuleCat.{u} ℤ)) ≫ 0
              simp }
  | succ n =>
    exact { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 𝟙 _
            comm₁₂ := by
              change 𝟙 _ ≫ K.d (n + 2) (n + 1) = K.d (n + 2) (n + 1) ≫ 𝟙 _
              simp
            comm₂₃ := by
              change 𝟙 _ ≫ K.d (n + 1) n = K.d (n + 1) n ≫ 𝟙 _
              simp }

end HolomorphicAnosov.GoodPair

