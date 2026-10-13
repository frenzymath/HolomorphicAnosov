import HolomorphicAnosov.Topology.EuclideanOpenDimensionInvariance
import HolomorphicAnosov.Topology.Homology.EmptySingularHomology

/-!
Integral point-local homology of Euclidean spaces. (Hatcher, Thm. 2.26)
-/

open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov

/-- Zero-dimensional relative point homology vanishes in every positive degree. -/
theorem euclidean_zero_dimension_local_positive_isZero (q : ℕ) :
    IsZero ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin 0))) {0}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} (q + 1)) := by
  let E := EuclideanSpace ℝ (Fin 0)
  let P := singularSubspacePair (TopCat.of E) ({0}ᶜ : Set E)
  have : IsEmpty ↥({0}ᶜ : Set E) := ⟨fun z ↦ z.property (Subsingleton.elim z.val 0)⟩
  have hleft : IsZero ((P.left.chainComplex reducedSingularIntegralCoefficients.{0}).homology q) :=
    singular_homology_isZero_of_isEmpty (TopCat.of ↥({0}ᶜ : Set E))
      reducedSingularIntegralCoefficients.{0} q
  have hright : IsZero ((P.right.chainComplex reducedSingularIntegralCoefficients.{0}).homology (q + 1)) :=
    normedSpace_positive_integral_homology_isZero (E := E) (q + 1) (by omega)
  exact (P.homology_exact₃ reducedSingularIntegralCoefficients.{0} (q + 1) q rfl).isZero_of_both_isZero
    hright hleft

/-- Dimension one uses positive reduced homology of the discrete zero-sphere. -/
theorem euclidean_one_dimension_local_above_isZero (q : ℕ) :
    IsZero ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin 1))) {0}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} (q + 2)) :=
  (HolomorphicAnosov.Topology.Homology.zeroSphere_positive q).of_iso
    (normedSpacePuncturedRelativeSphereIso (E := EuclideanSpace ℝ (Fin 1)) (q + 1))

/-- Dimension one's top group is the augmentation kernel of S⁰, hence one Z. -/
noncomputable def euclideanOneDimensionLocalTopIso :
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin 1))) {0}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} 1 ≅ reducedSingularIntegralCoefficients.{0} :=
  normedSpacePuncturedRelativeSphereIso (E := EuclideanSpace ℝ (Fin 1)) 0 ≪≫
    HolomorphicAnosov.Topology.Homology.zeroSphere_degreeZeroIso


/-- In dimension zero the local degree-zero group is ordinary H₀(point), one Z. -/
noncomputable def euclideanZeroDimensionLocalTopIso :
    (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin 0))) {0}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} 0 ≅ reducedSingularIntegralCoefficients.{0} := by
  let E := EuclideanSpace ℝ (Fin 0)
  let P := singularSubspacePair (TopCat.of E) ({0}ᶜ : Set E)
  let R := reducedSingularIntegralCoefficients.{0}
  have : IsEmpty ↥({0}ᶜ : Set E) := ⟨fun z ↦ z.property (Subsingleton.elim z.val 0)⟩
  have hleft : IsZero ((P.left.chainComplex R).homology 0) :=
    singular_homology_isZero_of_isEmpty (TopCat.of ↥({0}ᶜ : Set E)) R 0
  have hmono : Mono (P.homologyπ R 0) :=
    (P.homology_exact₂ R 0).mono_g (hleft.eq_of_src _ _)
  have hiso : IsIso (P.homologyπ R 0) := isIso_of_mono_of_epi _
  have haug : IsIso (ordinaryIntegralH0Augmentation.{0,0} (TopCat.of E)) :=
    ordinaryIntegralH0Augmentation_isIso _
  exact (asIso (P.homologyπ R 0)).symm ≪≫ @asIso _ _ _ _ (ordinaryIntegralH0Augmentation.{0,0} (TopCat.of E)) haug

/-- The Euclidean local profile through degree one includes the zero-dimensional point and the degree-one edge. -/
theorem euclidean_zero_local_above_dimension_isZero (n i : ℕ) (hi : n < i) :
    IsZero ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ).homology
      reducedSingularIntegralCoefficients i) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  cases n with
  | zero =>
    let E := EuclideanSpace ℝ (Fin 0)
    let P := singularSubspacePair (TopCat.of E) ({0}ᶜ : Set E)
    have : IsEmpty ↥({0}ᶜ : Set E) := ⟨fun z ↦ z.property (Subsingleton.elim z.val 0)⟩
    have hleft : IsZero ((P.left.chainComplex reducedSingularIntegralCoefficients).homology q) :=
      singular_homology_isZero_of_isEmpty (TopCat.of ↥({0}ᶜ : Set E))
        reducedSingularIntegralCoefficients q
    have hright : IsZero ((P.right.chainComplex reducedSingularIntegralCoefficients).homology (q + 1)) :=
      normedSpace_positive_integral_homology_isZero (E := E) (q + 1) (by omega)
    exact (P.homology_exact₃ reducedSingularIntegralCoefficients (q + 1) q rfl).isZero_of_both_isZero
      hright hleft
  | succ k =>
    have hq : q ≠ k := by omega
    have hs := (HolomorphicAnosov.Topology.Homology.reduced_sphere_homology k).2.1 q hq
    exact hs.of_iso (normedSpacePuncturedRelativeSphereIso
      (E := EuclideanSpace ℝ (Fin (k + 1))) q)


/-- Translation of the puncture gives vanishing above dimension at every point. (Hatcher, Thm. 2.26) -/
theorem euclidean_point_local_above_dimension_isZero (n i : ℕ) (hi : n < i)
    (x : EuclideanSpace ℝ (Fin n)) :
    IsZero ((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
      reducedSingularIntegralCoefficients i) := by
  let e := Homeomorph.addLeft (-x)
  have he : e x = 0 := by simp [e]
  have eqv := puncturedRelativeHomologyIso e x reducedSingularIntegralCoefficients i
  rw [he, singularPairFunctor_punctured_eq, singularPairFunctor_punctured_eq] at eqv
  exact (euclidean_zero_local_above_dimension_isZero n i hi).of_iso eqv

/-- Hatcher's local Euclidean homology calculation in its top degree. -/
theorem euclidean_point_local_top_iso (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Nonempty (((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} n) ≅ reducedSingularIntegralCoefficients.{0}) := by
  let e := Homeomorph.addLeft (-x)
  have he : e x = 0 := by simp [e]
  have eqv := puncturedRelativeHomologyIso e x reducedSingularIntegralCoefficients n
  rw [he, singularPairFunctor_punctured_eq, singularPairFunctor_punctured_eq] at eqv
  suffices h : Nonempty (((singularSubspacePair
      (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} n) ≅ reducedSingularIntegralCoefficients.{0}) from
    h.map (fun f ↦ eqv ≪≫ f)
  cases n with
  | zero => exact ⟨euclideanZeroDimensionLocalTopIso⟩
  | succ k =>
    obtain ⟨f⟩ := (HolomorphicAnosov.Topology.Homology.reduced_sphere_homology k).1
    exact ⟨normedSpacePuncturedRelativeSphereIso (E := EuclideanSpace ℝ (Fin (k+1))) k ≪≫ f⟩

/-- The part of the local Euclidean profile needed for compact-support orientation: top degree is Z and every degree above dimension is zero. (Hatcher, Thm. 2.26) -/
theorem euclidean_point_local_homology_profile (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∀ i : ℕ, n < i → IsZero ((singularSubspacePair
      (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
        reducedSingularIntegralCoefficients.{0} i)) ∧
    Nonempty (((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} n) ≅ reducedSingularIntegralCoefficients.{0}) :=
  ⟨fun i hi ↦ euclidean_point_local_above_dimension_isZero n i hi x,
    euclidean_point_local_top_iso n x⟩

/-- The zero- and one-dimensional profile without the higher-sphere theorem. (Hatcher) -/
theorem euclidean_point_local_small_dimension_profile (n : ℕ) (hn : n = 0 ∨ n = 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∀ i : ℕ, n < i → IsZero ((singularSubspacePair
      (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
        reducedSingularIntegralCoefficients.{0} i)) ∧
    Nonempty (((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
      reducedSingularIntegralCoefficients.{0} n) ≅ reducedSingularIntegralCoefficients.{0}) := by
  have hz :
      (∀ i : ℕ, n < i → IsZero ((singularSubspacePair
        (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ).homology
          reducedSingularIntegralCoefficients.{0} i)) ∧
      Nonempty (((singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ).homology
        reducedSingularIntegralCoefficients.{0} n) ≅ reducedSingularIntegralCoefficients.{0}) := by
    rcases hn with rfl | rfl
    · refine ⟨?_, ⟨euclideanZeroDimensionLocalTopIso⟩⟩
      intro i hi
      obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact euclidean_zero_dimension_local_positive_isZero q
    · refine ⟨?_, ⟨euclideanOneDimensionLocalTopIso⟩⟩
      intro i hi
      obtain ⟨q, hq⟩ : ∃ q, i = q + 2 := ⟨i - 2, by omega⟩
      rw [hq]
      exact euclidean_one_dimension_local_above_isZero q
  let e := Homeomorph.addLeft (-x)
  have he : e x = 0 := by simp [e]
  have eqv (i : ℕ) :
      (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {x}ᶜ).homology
        reducedSingularIntegralCoefficients.{0} i ≅
      (singularSubspacePair (TopCat.of (EuclideanSpace ℝ (Fin n))) {0}ᶜ).homology
        reducedSingularIntegralCoefficients.{0} i := by
    have f := puncturedRelativeHomologyIso e x reducedSingularIntegralCoefficients i
    rw [he, singularPairFunctor_punctured_eq, singularPairFunctor_punctured_eq] at f
    exact f
  exact ⟨fun i hi ↦ (hz.1 i hi).of_iso (eqv i),
    hz.2.map (fun f ↦ eqv n ≪≫ f)⟩

end HolomorphicAnosov


