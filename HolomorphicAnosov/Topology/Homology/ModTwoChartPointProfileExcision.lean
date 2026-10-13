import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.SupportNeighborhoodExcisionCoefficients
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chart and excision transport for a mod-two point profile

Source: Hatcher, *Algebraic Topology*, pp.115--118 and 233--237.  The
support-neighborhood excision maps identify the literal pair in an ambient
space with its pair in an open chart.  A chart homeomorphism then identifies
the chart point pair with the Euclidean point pair; all maps retain the
coefficient object `ULift (ZMod 2)`.

This is an agent-written Stage 3 bridge.  Its purpose is to isolate the
remaining carrier-level construction: commuting the two excision squares,
extracting the induced linear equivalences in every degree, and transporting
the degree-n generator and off-degree `Subsingleton` instances.  The bridge
includes the arbitrary point and the zero-dimensional case; it makes no
orientation or boundary regularity assumption.
-/

universe u
noncomputable section
namespace HolomorphicAnosov.Topology.Homology

open Set CategoryTheory

/-- A point profile in an open chart transports to the original ambient point
profile through the literal support-pair excision maps.

The proof is the chart/excision comparison from Hatcher Lemma 3.27, with the
actual `modTwoSupportHomology` carriers.  This named handoff records the
remaining relative-pair map calculation so that downstream profile statements
depend on a precise proposition rather than an unnamed gap. -/
theorem modTwo_chart_point_profile_excision
    (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U)
    (_e : U ≃ₜ EuclideanSpace ℝ (Fin n))
    (A : Set M) (_hAcompact : IsCompact A) (hAU : A ⊆ U)
    (hpoint : ∀ x : A,
      Nonempty (modTwoSupportHomology U {z : U | z.val = x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        (∀ k : ℕ, k ≠ n →
          Subsingleton (modTwoSupportHomology U {z : U | z.val = x.val} k))) :
    ∀ x : A,
      Nonempty (modTwoSupportHomology M {x.val} n ≃ₗ[ZMod 2] ZMod 2) ∧
        (∀ k : ℕ, k ≠ n → Subsingleton (modTwoSupportHomology M {x.val} k)) := by
  classical
  intro x
  let ix := HolomorphicAnosov.singularExcisionInclusion
    (TopCat.of M) ({x.val} : Set M)ᶜ U
  let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
  have hix (k : ℕ) : IsIso (SSetPair.homologyMap ix V k) := by
    apply HolomorphicAnosov.support_neighborhood_excision_isIso_coefficients
      (TopCat.of M) {x.val} U hU
    simpa only [isClosed_singleton.closure_eq] using
      (Set.singleton_subset_iff.mpr (hAU x.property))
  have hsource : HolomorphicAnosov.singularExcisionSource
      (TopCat.of M) ({x.val} : Set M)ᶜ U =
      singularSubspacePair (TopCat.of U)
        ({z : U | z.val = x.val} : Set U)ᶜ := by
    apply congrArg (fun B : Set U ↦ singularSubspacePair (TopCat.of U) B)
    ext z
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  have hmap (k : ℕ) : IsIso
      (SSetPair.homologyMap ix V k) := hix k
  let E (k : ℕ) : modTwoSupportHomology U {z : U | z.val = x.val} k ≃ₗ[ZMod 2]
      modTwoSupportHomology M {x.val} k := by
    let f₀ := SSetPair.homologyMap ix V k
    let f := eqToHom (congrArg (fun P : SSetPair => P.homology V k) hsource.symm) ≫ f₀
    have hf₀ : IsIso f₀ := hix k
    have hf : IsIso f := by
      dsimp [f]
      infer_instance
    let := hf
    exact LinearEquiv.ofBijective (ModuleCat.Hom.hom f)
      (ConcreteCategory.bijective_of_isIso f)
  rcases hpoint x with ⟨hn, hrest⟩
  refine ⟨?_, ?_⟩
  · rcases hn with ⟨q⟩
    exact ⟨(E n).symm.trans q⟩
  · intro k hk
    let hsub : Subsingleton (modTwoSupportHomology U {z : U | z.val = x.val} k) := hrest k hk
    constructor
    intro a b
    apply (E k).symm.injective
    exact hsub.elim _ _

end HolomorphicAnosov.Topology.Homology
