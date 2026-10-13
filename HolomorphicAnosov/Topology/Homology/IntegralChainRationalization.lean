import HolomorphicAnosov.Topology.Homology.SingularChainSignedExpansion
import HolomorphicAnosov.Topology.Homology.SignedShufflePositiveBoundary
import HolomorphicAnosov.Topology.SignedCrossProductUnitGenerators
import HolomorphicAnosov.Topology.Homology.IntegralRelativeProductData

/-!
Coefficient inclusion from integral to rational singular chains.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.IntegralChainRationalization
universe u
open SignedSingularCrossProduct HolomorphicAnosov.Topology _root_.Topology
set_option backward.isDefEq.respectTransparency false

/-- Canonical rational simplex coefficients, using the native coproduct. -/
def rationalCoefficients (X : TopCat.{u}) (n : ℕ) :
    SignedShuffle.Chain X n ≃ₗ[ℚ] (Simplex X n →₀ ULift.{u} ℚ) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
      (ModuleCat.of ℚ (ULift.{u} ℚ)) n).coconePointUniqueUpToIso
    (ModuleCat.finsuppCoconeIsColimit ℚ (ULift.{u} ℚ) (Simplex X n)) |>.toLinearEquiv

/-- The rational coefficient equivalence preserves each simplex summand. -/
theorem rationalCoefficients_ι (X : TopCat.{u}) (n : ℕ)
    (σ : Simplex X n) (z : ULift.{u} ℚ) :
    rationalCoefficients X n (((TopCat.toSSet.obj X).ιChainComplex
      (R := ModuleCat.of ℚ (ULift.{u} ℚ)) σ).hom z) = Finsupp.single σ z := by
  have h := ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℚ (ULift.{u} ℚ)) n).comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit ℚ (ULift.{u} ℚ) (Simplex X n)) (Discrete.mk σ)
  exact congrArg (fun k ↦ k.hom z) h

/-- The coefficient inclusion with the native universe lifts. -/
def coefficientInclusion : ULift.{u} ℤ →+ ULift.{u} ℚ where
  toFun z := ULift.up (z.down : ℚ)
  map_zero' := by rfl
  map_add' a b := by ext; exact Int.cast_add _ _

/-- The additive inclusion of native integral chains into native rational chains. -/
def toRational (X : TopCat.{u}) (n : ℕ) : Chain X n →+ SignedShuffle.Chain X n :=
  (rationalCoefficients X n).symm.toAddEquiv.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom coefficientInclusion).comp
      (integralSingularChainCoefficients X n).toAddEquiv.toAddMonoidHom)

/-- Integral singular chains inject into rational chains: the coefficient map is injective at every simplex, and both native coefficient comparisons are equivalences. (Hatcher) -/
theorem toRational_injective (X : TopCat.{u}) (n : ℕ) :
    Function.Injective (toRational X n) := by
  intro a b h
  apply (integralSingularChainCoefficients X n).injective
  apply Finsupp.ext
  intro σ
  have hc := congrArg (fun c ↦ (rationalCoefficients X n c) σ) h
  simp [toRational] at hc
  change ULift.up (((integralSingularChainCoefficients X n a) σ).down : ℚ) =
    ULift.up (((integralSingularChainCoefficients X n b) σ).down : ℚ) at hc
  have hd := congrArg ULift.down hc
  exact ULift.ext (Int.cast_injective hd)

/-- Coefficient inclusion preserves the unit generator. -/
theorem toRational_generator (X : TopCat.{u}) {n : ℕ} (σ : Simplex X n) :
    toRational X n (((TopCat.toSSet.obj X).ιChainComplex
      (R := singularIntegralCoefficients) σ).hom (ULift.up 1)) =
      SignedShuffle.generator X σ := by
  apply (rationalCoefficients X n).injective
  change rationalCoefficients X n ((rationalCoefficients X n).symm
    (Finsupp.mapRange coefficientInclusion coefficientInclusion.map_zero
      (integralSingularChainCoefficients X n _))) = _
  rw [LinearEquiv.apply_symm_apply, integralSingularChainCoefficients_ι,
    SignedShuffle.generator, rationalCoefficients_ι]
  simp [Finsupp.mapRange_single, coefficientInclusion]
  rfl

/-- Coefficient inclusion commutes with a change of degree by equality. -/
theorem toRational_cast (X : TopCat.{u}) {m n : ℕ} (h : m = n) (c : Chain X m) :
    toRational X n (castChain X h c) = SignedShuffle.regrade X h (toRational X m c) := by
  subst n
  rfl

/-- The prescribed integral staircase sum maps to the prescribed rational sum. -/
theorem toRational_simplexProduct (X Y : TopCat.{u}) {p q : ℕ}
    (σ : Simplex X p) (τ : Simplex Y q) :
    toRational (TopCat.of (X × Y)) (p + q) (simplexProduct X Y σ τ) =
      SignedShuffle.shuffleGenerator X Y σ τ := by
  simp only [simplexProduct, SignedShuffle.shuffleGenerator, map_sum, map_zsmul,
    Int.cast_smul_eq_zsmul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [toRational_generator]

/-- The integral generator differential is its alternating sum of faces. -/
theorem integral_d_generator (X : TopCat.{u}) (n : ℕ) (σ : Simplex X (n + 1)) :
    (((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (n + 1) n).hom
      (((TopCat.toSSet.obj X).ιChainComplex
        (R := singularIntegralCoefficients) σ).hom (ULift.up 1)) =
    ∑ i : Fin (n + 2), (-1 : ℤ)^i.val •
      (((TopCat.toSSet.obj X).ιChainComplex
        (R := singularIntegralCoefficients) ((TopCat.toSSet.obj X).δ i σ)).hom
        (ULift.up 1)) := by
  have hδ := congrArg (fun f ↦ f.hom (ULift.up (1 : ℤ)))
    (SSet.ιChainComplex_d (TopCat.toSSet.obj X)
      (R := singularIntegralCoefficients) σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_zsmul] at hδ
  refine hδ.trans ?_
  apply Finset.sum_congr rfl
  intro i hi
  exact map_zsmul (LinearMap.applyₗ (R := ℤ) (ULift.up 1)) _ _

/-- Coefficient inclusion commutes with the differential in positive degrees. -/
theorem toRational_boundary (X : TopCat.{u}) (n : ℕ) (hn : 0 < n) (c : Chain X n) :
    toRational X (n - 1)
      ((((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d n (n - 1)).hom c) =
    SignedShuffle.boundary X n (toRational X n c) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  obtain ⟨m, σ, ε, _, rfl⟩ := integralSingularChainSignedExpansion X (k + 1) c
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  change toRational X k
    ((((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (k + 1) k).hom _) = _
  rw [integral_d_generator, toRational_generator,
    SignedShuffle.boundary_generator_succ]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [toRational_generator]

/-- Successor-degree form of differential compatibility. -/
theorem toRational_boundary_succ (X : TopCat.{u}) (n : ℕ) (c : Chain X (n + 1)) :
    toRational X n
      ((((TopCat.toSSet.obj X).chainComplex singularIntegralCoefficients).d (n + 1) n).hom c) =
    SignedShuffle.boundary X (n + 1) (toRational X (n + 1) c) := by
  simpa [SignedShuffle.boundary] using toRational_boundary X (n + 1) (by omega) c

/-- Coefficient inclusion respects the bilinear signed staircase product. (Bredon, IV §16.1) -/
theorem toRational_crossProduct (X Y : TopCat.{u}) (p q : ℕ)
    (a : Chain X p) (b : Chain Y q) :
    toRational (TopCat.of (X × Y)) (p + q) (signedSingularCrossProduct X Y p q a b) =
    SignedShuffle.shuffleBilinear X Y p q (toRational X p a) (toRational Y q b) := by
  classical
  obtain ⟨ma, σ, ε, _, ha⟩ := integralSingularChainSignedExpansion X p a
  obtain ⟨mb, τ, η, _, hb⟩ := integralSingularChainSignedExpansion Y q b
  rw [ha, hb]
  have eval_zsmul (f : Chain Y q →ₗ[ℤ] Chain (TopCat.of (X × Y)) (p + q))
      (r : ℤ) (c : Chain Y q) : (r • f) c = r • f c :=
    map_zsmul (LinearMap.applyₗ (R := ℤ) c) r f
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, eval_zsmul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [toRational_generator, toRational_generator,
    signedSingularCrossProduct_unit_generators, SignedShuffle.shuffleBilinear_generators,
    toRational_simplexProduct]


end HolomorphicAnosov.IntegralChainRationalization
