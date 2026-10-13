import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Relative
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.CommSq
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
namespace HolomorphicAnosov.Topology
universe u

variable {X : SSet.{u}} (A B : X.Subcomplex) (R : ModuleCat.{u} ℤ)

/-- The chain square of the intersection and union of simplicial subcomplexes.
Source: Hatcher, Algebraic Topology, §2.1, pp.120–121. -/
theorem subcomplexChainSquare : CommSq
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R) where
  w := by rw [← Functor.map_comp, ← Functor.map_comp]; rfl

/-- Chains preserve the pushout square of two simplicial subcomplexes.
In each degree the square of simplex sets is a pushout, and the coproduct of
copies of the coefficient module preserves that pushout. Colimits of chain
complexes are detected degreewise. Source: Hatcher §2.1, pp.120–121. -/
theorem subcomplexChainSquare_isPushout : IsPushout
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_left : A ≤ A ⊔ B)) R)
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (le_sup_right : B ≤ A ⊔ B)) R) := by
  let h : SSet.Subcomplex.BicartSq (A ⊓ B) A B (A ⊔ B) := ⟨rfl, rfl⟩
  refine ⟨subcomplexChainSquare A B R, ⟨?_⟩⟩
  apply HomologicalComplex.isColimitOfEval
  intro n
  refine (PushoutCocone.isColimitMapCoconeEquiv _ _).symm ?_
  exact ((h.isPushout.map ((evaluation _ _).obj (op ⦋n⦌))).map
    (sigmaConst.obj R)).isColimit

/-- The signed diagonal and sum form the short exact simplicial-chain sequence.
The last map is the cokernel supplied by the pushout square; the first map is
monic because its first component is an inclusion of simplicial chains.
Source: Hatcher §2.1, pp.120–121. -/
theorem subcomplexChainSquare_shortExact : (subcomplexChainSquare A B R).shortComplex.ShortExact := by
  have h := subcomplexChainSquare_isPushout A B R
  refine { exact := h.exact_shortComplex, mono_f := ?_, epi_g := h.epi_shortComplex_g }
  let i := SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)
  have : Mono (SSet.chainComplexMap
      (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R) :=
    inferInstanceAs (Mono (SSet.chainComplexMap (SSetPair.of i).hom R))
  apply mono_of_mono_fac (biprod.lift_fst
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_left : A ⊓ B ≤ A)) R)
    (-SSet.chainComplexMap (SSet.Subcomplex.homOfLE (inf_le_right : A ⊓ B ≤ B)) R))

end HolomorphicAnosov.Topology
