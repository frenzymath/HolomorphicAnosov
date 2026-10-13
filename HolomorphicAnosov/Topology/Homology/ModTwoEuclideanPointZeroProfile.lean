import Mathlib.Analysis.Convex.Contractible
import HolomorphicAnosov.Topology.Homology.ModTwoSingularSupportHomology
import HolomorphicAnosov.Topology.Homology.EmptySingularHomology
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Mod-two local homology in Euclidean dimension zero

Source: Hatcher, Algebraic Topology, §2.1 pp.109–110 and coefficients p.153.
The space has one point and its punctured complement is empty. The relative
long exact sequence identifies degree zero with the ordinary augmentation and
makes every positive relative homology group zero.
-/

open CategoryTheory CategoryTheory.Limits
namespace HolomorphicAnosov.Topology.Homology
noncomputable section

/-- The native zero-dimensional Euclidean point has one copy of ZMod 2 in
local degree zero and zero local homology in every other natural degree.

Source: Hatcher pp.109–110,153. The complement of the point is empty. Its
homology vanishes in every degree, so the degree-zero relative projection
is an isomorphism and the coefficient-sum augmentation identifies its source
with the coefficient module. In positive degrees use the relative long exact
sequence and the ordinary totally disconnected-space calculation. -/
theorem modTwo_euclidean_point_zero_profile
    (x : EuclideanSpace ℝ (Fin 0)) :
    Nonempty (modTwoSupportHomology (EuclideanSpace ℝ (Fin 0)) {x} 0 ≃ₗ[ZMod 2] ZMod 2) ∧
      ∀ k : ℕ, k ≠ 0 →
        Subsingleton (modTwoSupportHomology (EuclideanSpace ℝ (Fin 0)) {x} k) := by
  let E := EuclideanSpace ℝ (Fin 0)
  let P := singularSubspacePair E ({x}ᶜ : Set E)
  let R := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let : Subsingleton E := inferInstance
  let : PathConnectedSpace E := by infer_instance
  have : IsEmpty ↥({x}ᶜ : Set E) := ⟨fun z ↦ z.property (Subsingleton.elim z.val x)⟩
  have hleft (q : ℕ) : IsZero ((P.left.chainComplex R).homology q) :=
    HolomorphicAnosov.singular_homology_isZero_of_isEmpty
      (TopCat.of ↥({x}ᶜ : Set E)) R q
  constructor
  · have : Mono (P.homologyπ R 0) :=
      (P.homology_exact₂ R 0).mono_g ((hleft 0).eq_of_src _ _)
    have : IsIso (P.homologyπ R 0) := isIso_of_mono_of_epi _
    have : PathConnectedSpace (TopCat.of E) := inferInstance
    have : (TopCat.toSSet.obj (TopCat.of E)).IsConnected := inferInstance
    have haug : IsIso ((TopCat.of E).singularHomology₀ε R) := by
      change IsIso ((TopCat.toSSet.obj (TopCat.of E)).homology₀ε R)
      infer_instance
    let h := (asIso (P.homologyπ R 0)).symm ≪≫
      @asIso _ _ _ _ ((TopCat.of E).singularHomology₀ε R) haug
    exact ⟨h.toLinearEquiv.trans ULift.moduleEquiv⟩
  · intro k hk
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have hright : IsZero ((P.right.chainComplex R).homology (q + 1)) :=
      AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
        (ModuleCat (ZMod 2)) (q + 1) R (TopCat.of E) (by omega)
    exact ModuleCat.subsingleton_of_isZero
      ((P.homology_exact₃ R (q + 1) q rfl).isZero_of_both_isZero hright (hleft q))

end
end HolomorphicAnosov.Topology.Homology
