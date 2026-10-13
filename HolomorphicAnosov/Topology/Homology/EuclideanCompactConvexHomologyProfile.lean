import HolomorphicAnosov.Topology.Homology.ConvexSupportRestrictionIso
import HolomorphicAnosov.Topology.Homology.EuclideanLocalHomologyProfile

/-!
Integral support homology of nonempty compact convex Euclidean sets. (Hatcher, Lemma 3.27)
-/

open CategoryTheory CategoryTheory.Limits HolomorphicAnosov.Topology _root_.Topology
namespace HolomorphicAnosov

/-- A nonempty compact convex support has integral relative homology `ℤ` in its Euclidean dimension and zero above it; restriction to any chosen point is an isomorphism. (Hatcher, Lemma 3.27) -/
theorem euclidean_compact_convex_homology_profile (n : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : Convex ℝ K) (hcK : IsCompact K)
    (hnK : K.Nonempty) :
    (∀ i : ℕ, n < i → IsZero ((supportSingularPair
      (TopCat.of (EuclideanSpace ℝ (Fin n))) K).homology
        reducedSingularIntegralCoefficients.{0} i)) ∧
    Nonempty (((supportSingularPair (TopCat.of (EuclideanSpace ℝ (Fin n))) K).homology
      reducedSingularIntegralCoefficients.{0} n) ≅ reducedSingularIntegralCoefficients.{0}) := by
  obtain ⟨x, hx⟩ := hnK
  let f := supportSingularPairMap (X := TopCat.of (EuclideanSpace ℝ (Fin n)))
    (Y := TopCat.of (EuclideanSpace ℝ (Fin n))) K {x} (𝟙 _)
    (fun z hz hm ↦ hz ((show z = x from hm) ▸ hx))
  have hf (i : ℕ) : IsIso (SSetPair.homologyMap f reducedSingularIntegralCoefficients.{0} i) :=
    convex_compact_support_restriction_isIso K hK hcK x hx i
  constructor
  · intro i hi
    have : IsIso (SSetPair.homologyMap f reducedSingularIntegralCoefficients.{0} i) := hf i
    exact (euclidean_point_local_above_dimension_isZero n i hi x).of_iso
      (@asIso _ _ _ _ (SSetPair.homologyMap f reducedSingularIntegralCoefficients.{0} i) (hf i))
  · have : IsIso (SSetPair.homologyMap f reducedSingularIntegralCoefficients.{0} n) := hf n
    obtain ⟨e⟩ := euclidean_point_local_top_iso n x
    exact ⟨@asIso _ _ _ _ (SSetPair.homologyMap f reducedSingularIntegralCoefficients.{0} n) (hf n) ≪≫ e⟩

end HolomorphicAnosov

