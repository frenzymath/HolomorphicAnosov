import HolomorphicAnosov.Topology.Homology.ModTwoPositiveUnitSphereProfile
import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomotopyEquivIso
import HolomorphicAnosov.Topology.Homology.ModTwoPositivePuncturedSphereScale
import HolomorphicAnosov.Topology.Homology.ModTwoSupportProfileHomeomorphTransport
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# Positive-dimensional Euclidean point homology over mod two

Hatcher, Algebraic Topology, pp.110–118 and p.153. The contractible ambient
pair shifts local homology to reduced homology of the punctured complement.
Radial deformation identifies that complement with the unit sphere. The
zero-sphere calculation handles dimension one; the positive-sphere profile
handles all higher dimensions. Translation carries the result to any point.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov.Topology.Homology
universe u
noncomputable section
private theorem augmentation_w (X : TopCat.{0}) :
    ((TopCat.toSSet.obj X).chainComplex modTwoCoefficients).d 1 0 ≫
      modTwoSingularAugmentation X = 0 := by
  apply SSet.chainComplex_hom_ext
  intro σ
  rw [← Category.assoc, SSet.ιChainComplex_d]
  simp [modTwoSingularAugmentation, SSet.ιChainComplex, Fin.sum_univ_two]

private theorem native_sphere_profile (d : ℕ) :
    let S := {x : EuclideanSpace ℝ (Fin (d + 1)) // ‖x‖ = 1}
    Nonempty ((modTwoAugmentedSingularChains (TopCat.of S)).homology (d + 1) ≅
      modTwoCoefficients.{0}) ∧
    ∀ q : ℕ, q ≠ d → IsZero
      ((modTwoAugmentedSingularChains (TopCat.of S)).homology (q + 1)) := by
  cases d with
  | zero =>
    obtain ⟨h, hz⟩ := HolomorphicAnosov.modTwoZeroSphereProfile
      (augmentation_w (TopCat.of {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}))
    refine ⟨h, ?_⟩
    intro q hq
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
    exact hz q
  | succ d =>
    exact HolomorphicAnosov.modTwoPositiveUnitSphereProfile d
      (augmentation_w (TopCat.of {x : EuclideanSpace ℝ (Fin (d + 1 + 1)) // ‖x‖ = 1}))

private theorem native_positive_point_profile (d : ℕ) :
    Nonempty (modTwoSupportHomology (EuclideanSpace ℝ (Fin (d + 1))) {0}
      (d + 1) ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ q : ℕ, q ≠ d + 1 → Subsingleton
        (modTwoSupportHomology (EuclideanSpace ℝ (Fin (d + 1))) {0} q) := by
  let E := EuclideanSpace ℝ (Fin (d + 1))
  let A : Set E := {0}ᶜ
  let S := {x : E // ‖x‖ = 1}
  have : Nonempty A := by
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    exact ⟨⟨z, hz⟩⟩
  have hshift := HolomorphicAnosov.modTwoContractibleAmbientShift (TopCat.of E) A
    (augmentation_w (TopCat.of A)) (augmentation_w (TopCat.of E))
  let e : ContinuousMap.HomotopyEquiv A S :=
    positivePuncturedSphereHomotopyEquiv 1 zero_lt_one
  have he (q : ℕ) := modTwoAugmentedHomologyIso e q
  have hi (q : ℕ) : Nonempty (modTwoSupportHomology E {0} (q + 1) ≅
      (modTwoAugmentedSingularChains (TopCat.of S)).homology (q + 1)) := by
    obtain ⟨a⟩ := hshift.2 q
    obtain ⟨b⟩ := he (q + 1)
    exact ⟨a ≪≫ b⟩
  obtain ⟨ht, hz⟩ := native_sphere_profile d
  obtain ⟨t⟩ := ht
  obtain ⟨i⟩ := hi d
  refine ⟨⟨(i ≪≫ t).toLinearEquiv.trans ULift.moduleEquiv⟩, ?_⟩
  intro q hq
  cases q with
  | zero => exact ModuleCat.isZero_iff_subsingleton.mp hshift.1
  | succ q =>
    obtain ⟨i⟩ := hi q
    exact ModuleCat.isZero_iff_subsingleton.mp
      ((hz q (by omega)).of_iso i)

/-- A point of Euclidean space of dimension d+1 has one mod-two local
homology generator in degree d+1 and zero local homology in every other degree.
Source: Hatcher pp.110–118 and p.153, the radial deformation and the augmented
pair exact sequence. Degree zero vanishes because the complement is nonempty;
the connecting map identifies each positive relative group with the reduced
sphere group one degree lower, including reduced H₀ of the zero-sphere. -/
theorem modTwo_euclidean_point_positive_profile (d : ℕ)
    (x : EuclideanSpace ℝ (Fin (d + 1))) :
    Nonempty (modTwoSupportHomology (EuclideanSpace ℝ (Fin (d + 1))) {x}
      (d + 1) ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ q : ℕ, q ≠ d + 1 → Subsingleton
        (modTwoSupportHomology (EuclideanSpace ℝ (Fin (d + 1))) {x} q) := by
  let e := Homeomorph.addLeft (-x)
  apply modTwo_support_profile_homeomorph_transport (d + 1) e x
  have he : e x = 0 := by simp [e]
  rw [he]
  exact native_positive_point_profile d

end
end HolomorphicAnosov.Topology.Homology
