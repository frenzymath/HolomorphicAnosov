import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import HolomorphicAnosov.AlgebraicTopology.SingularCochainCohomologyDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairPullbackDefinition
import HolomorphicAnosov.AlgebraicTopology.SingularCochainPairShortExact
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientExactness
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingExactness
import HolomorphicAnosov.AlgebraicTopology.CochainQuotientConnectingNaturality
import Mathlib.Algebra.FiveLemma

/-!
# Relative comparison for maps inducing absolute cohomology isomorphisms

Source: Hatcher, Algebraic Topology, pp.199–201 (the natural exact sequence
of a pair), and Proposition 3.17 p.217 (the five-lemma comparison).
DAG: topo.singular_relative_cohomology_comparison_g5.
The proof uses the public short-exact and quotient-connecting lemmas directly,
never the bundled relative_cohomology_pair_theorems or the excision admission.
-/
open CategoryTheory CategoryTheory.Limits Opposite
universe u
noncomputable section
namespace HolomorphicAnosov.SingularCochain
set_option backward.isDefEq.respectTransparency false

/-- A map of arbitrary pairs inducing cohomology isomorphisms on both ambient
spaces and subspaces induces isomorphisms on relative cohomology in every degree.

Proof: restriction of singular cochains is degreewise surjective, so its kernel
sequence is short exact. The pair pullback gives a map between these two rows.
Pass to the literal cohomology quotients and their natural connecting maps.
For degree n+1 apply the five lemma to Hⁿ(Y) → Hⁿ(B) → Hⁿ⁺¹(Y,B) →
Hⁿ⁺¹(Y) → Hⁿ⁺¹(B) and the row for (X,A). At degree zero there is no incoming
differential, so both relative-forget maps are injective; the left-exact
three-term comparison proves the result. No nonempty-space, field, finite-type,
or positive-degree hypothesis is required. -/
theorem relative_cohomology_pullback_bijective_of_absolute
    (R : Type u) [CommRing R] {X Y : TopCat.{u}} {A : Set X} {B : Set Y}
    (f : X ⟶ Y) (hf : Set.MapsTo f A B)
    (hambient : ∀ n, Function.Bijective (cohomologyPullback R f n))
    (hsubspace : ∀ n,
      Function.Bijective (cohomologyPullback R (pairSubspaceMap f hf) n)) (k : ℕ) :
    Function.Bijective (relativeCohomologyPullback R f hf k) := by
  let inc (Z : TopCat.{u}) (C : Set Z) : relativeComplex R Z C ⟶ complex R Z :=
    kernel.ι (pullback R (subspaceInclusion Z C))
  let forget (Z : TopCat.{u}) (C : Set Z) (n : ℕ) := quotientMap R (inc Z C) n
  have qcomp {Q Q' Q'' : CochainComplex (ModuleCat.{u} R) ℕ}
      (a : Q ⟶ Q') (b : Q' ⟶ Q'') (n : ℕ) :
      quotientMap R (a ≫ b) n = quotientMap R a n ≫ quotientMap R b n := by
    dsimp [quotientMap]
    rw [HomologicalComplex.homologyMap_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have forgetSquare (n : ℕ) :
      (forget X A n).hom.comp (relativeCohomologyPullback R f hf n).hom =
        (cohomologyPullback R f n).hom.comp (forget Y B n).hom := by
    apply congrArg ModuleCat.Hom.hom
    change relativeCohomologyPullback R f hf n ≫ forget X A n =
      forget Y B n ≫ cohomologyPullback R f n
    unfold relativeCohomologyPullback forget cohomologyPullback
    rw [← qcomp, ← qcomp]
    congr 1
    dsimp only [relativePullback, inc, kernel.map]
    simp only [kernel.lift_ι]
  have restrictionSquare (n : ℕ) :
      (cohomologyPullback R (subspaceInclusion X A) n).hom.comp
          (cohomologyPullback R f n).hom =
        (cohomologyPullback R (pairSubspaceMap f hf) n).hom.comp
          (cohomologyPullback R (subspaceInclusion Y B) n).hom := by
    apply congrArg ModuleCat.Hom.hom
    change cohomologyPullback R f n ≫ cohomologyPullback R (subspaceInclusion X A) n =
      cohomologyPullback R (subspaceInclusion Y B) n ≫
        cohomologyPullback R (pairSubspaceMap f hf) n
    unfold cohomologyPullback
    rw [← qcomp, ← qcomp, pairRestrictionSquare]
  have exactRow (Z : TopCat.{u}) (C : Set Z) (n : ℕ) :
      Function.Exact (forget Z C n).hom
        (cohomologyPullback R (subspaceInclusion Z C) n).hom :=
    LinearMap.exact_iff.mpr (cochain_quotient_exact_of_shortExact R _
      (singular_cochain_pair_shortExact R Z C) n).symm
  cases k with
  | zero =>
    have firstInjective (Z : TopCat.{u}) (C : Set Z) :
        Function.Injective (forget Z C 0).hom := by
      apply (ModuleCat.mono_iff_injective _).mp
      unfold forget quotientMap
      have : Mono (inc Z C) := by
        dsimp [inc]
        infer_instance
      have hnot : ∀ i : ℕ, ¬ (ComplexShape.up ℕ).Rel i 0 := by
        intro i hi
        simp at hi
      have : Mono (HomologicalComplex.homologyMap (inc Z C) 0) :=
        HomologicalComplex.mono_homologyMap_of_mono_of_not_rel
          (inc Z C) 0 hnot
      infer_instance
    exact LinearMap.bijective_of_bijective_of_injective_of_left_exact
      (forget Y B 0).hom
      (cohomologyPullback R (subspaceInclusion Y B) 0).hom
      (forget X A 0).hom
      (cohomologyPullback R (subspaceInclusion X A) 0).hom
      (relativeCohomologyPullback R f hf 0).hom
      (cohomologyPullback R f 0).hom
      (cohomologyPullback R (pairSubspaceMap f hf) 0).hom
      (forgetSquare 0) (restrictionSquare 0) (exactRow Y B 0) (exactRow X A 0)
      (hambient 0) (hsubspace 0).1 (firstInjective Y B) (firstInjective X A)
  | succ n =>
    let δX := quotientConnecting R (singular_cochain_pair_shortExact R X A) n
    let δY := quotientConnecting R (singular_cochain_pair_shortExact R Y B) n
    have hX := cochain_quotient_connecting_exact R _
      (singular_cochain_pair_shortExact R X A) n
    have hY := cochain_quotient_connecting_exact R _
      (singular_cochain_pair_shortExact R Y B) n
    let φ : ShortComplex.kernelSequence (pullback R (subspaceInclusion Y B)) ⟶
        ShortComplex.kernelSequence (pullback R (subspaceInclusion X A)) :=
      { τ₁ := relativePullback R f hf
        τ₂ := pullback R f
        τ₃ := pullback R (pairSubspaceMap f hf)
        comm₁₂ := by
          dsimp [relativePullback, ShortComplex.kernelSequence]
          simp
        comm₂₃ := (pairRestrictionSquare R f hf).symm }
    have hδ : δX.hom.comp (cohomologyPullback R (pairSubspaceMap f hf) n).hom =
        (relativeCohomologyPullback R f hf (n + 1)).hom.comp δY.hom :=
      (congrArg ModuleCat.Hom.hom (cochain_quotient_connecting_naturality R φ
        (singular_cochain_pair_shortExact R Y B)
        (singular_cochain_pair_shortExact R X A) n)).symm
    exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (cohomologyPullback R (subspaceInclusion Y B) n).hom δY.hom
      (forget Y B (n + 1)).hom
      (cohomologyPullback R (subspaceInclusion Y B) (n + 1)).hom
      (cohomologyPullback R (subspaceInclusion X A) n).hom δX.hom
      (forget X A (n + 1)).hom
      (cohomologyPullback R (subspaceInclusion X A) (n + 1)).hom
      (cohomologyPullback R f n).hom
      (cohomologyPullback R (pairSubspaceMap f hf) n).hom
      (relativeCohomologyPullback R f hf (n + 1)).hom
      (cohomologyPullback R f (n + 1)).hom
      (cohomologyPullback R (pairSubspaceMap f hf) (n + 1)).hom
      (restrictionSquare n) hδ (forgetSquare (n + 1)) (restrictionSquare (n + 1))
      (LinearMap.exact_iff.mpr hY.1.symm) (LinearMap.exact_iff.mpr hY.2.symm)
      (exactRow Y B (n + 1))
      (LinearMap.exact_iff.mpr hX.1.symm) (LinearMap.exact_iff.mpr hX.2.symm)
      (exactRow X A (n + 1))
      (hambient n).2 (hsubspace n) (hambient (n + 1)) (hsubspace (n + 1)).1

end HolomorphicAnosov.SingularCochain
