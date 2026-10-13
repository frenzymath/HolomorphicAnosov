import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.Abelian

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
noncomputable section
namespace HolomorphicAnosov
universe u v

/-- Adding a zero augmentation shifts homology by one, including ordinary
index zero, in any abelian category.

Source: Hatcher, Algebraic Topology, augmented relative sequence p.118.
Compare the cycle/boundary short complexes by identity in the first two
positions. In positive degrees the third component is identity as well.
At ordinary degree zero it is the monomorphism from the zero object; the
first component is epic and the middle component invertible, so the
short-complex homology comparison is still invertible. -/
def zeroAugmentHomologyIso {C : Type u} [Category.{v} C] [Abelian C]
    (K : ChainComplex C ℕ) (n : ℕ) :
    (ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)).homology (n + 1) ≅
      K.homology n := by
  let A := ChainComplex.augment K (0 : K.X 0 ⟶ 0) (by simp)
  let f : A.sc' (n + 2) (n + 1) n ⟶ K.sc' (n + 1) n (n - 1) := by
    cases n with
    | zero =>
      exact { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 0
              comm₁₂ := by
                change 𝟙 _ ≫ K.d 1 0 = K.d 1 0 ≫ 𝟙 _
                simp
              comm₂₃ := by
                change 𝟙 _ ≫ K.d 0 0 = (0 : K.X 0 ⟶ (0 : C)) ≫ 0
                simp }
    | succ n =>
      exact { τ₁ := 𝟙 _, τ₂ := 𝟙 _, τ₃ := 𝟙 _
              comm₁₂ := by
                change 𝟙 _ ≫ K.d (n + 2) (n + 1) = K.d (n + 2) (n + 1) ≫ 𝟙 _
                simp
              comm₂₃ := by
                change 𝟙 _ ≫ K.d (n + 1) n = K.d (n + 1) n ≫ 𝟙 _
                simp }
  have : IsIso (ShortComplex.homologyMap f) := by
    apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
    · cases n <;> change Epi (𝟙 _) <;> infer_instance
    · cases n <;> change IsIso (𝟙 _) <;> infer_instance
    · cases n with
      | zero => change Mono (0 : (0 : C) ⟶ K.X 0); infer_instance
      | succ n => change Mono (𝟙 (K.X n)); infer_instance
  exact A.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp) ≪≫
    asIso (ShortComplex.homologyMap f) ≪≫
    (K.homologyIsoSc' (n + 1) n (n - 1) (by simp) (by cases n <;> simp)).symm

end HolomorphicAnosov
