import HolomorphicAnosov.Topology.Homology.CompactSupportMayerVietoris
import HolomorphicAnosov.Topology.Homology.ModTwoLocalHomologyCompatibleFamily
import HolomorphicAnosov.Topology.Homology.SSetPairRestrictScalarsHomologyNaturality
open CategoryTheory
open HolomorphicAnosov.Topology _root_.Topology HolomorphicAnosov.Topology.Homology
open HolomorphicAnosov.HatcherCompactSupport
universe u
namespace HolomorphicAnosov.HatcherCompactSupport
/-- Naturality of support restriction under coefficient comparison.
Source: Hatcher, Algebraic Topology, maps of pairs p.118, coefficients p.153 and support pp.233–235.
Apply relative homology comparison naturality to the complement inclusion. Simplify the
identity coefficient map in the integer support restriction and evaluate the commuting square.
DAG node: `topo.mod_two_support_restriction_comparison_g18`. -/
theorem modTwoSupportRestriction_comparison (M : Type u) [TopologicalSpace M] (A B : Set M) (h : B ⊆ A) (k : ℕ) :
    let f := Int.castRingHom (ZMod 2)
    let F := ModuleCat.restrictScalars.{u} f
    let V := ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))
    let W := F.obj V
    let e (K : Set M) :=
      (ssetPairRestrictScalarsHomologyIso f (supportSingularPair (TopCat.of M) K) V k).toLinearEquiv.toAddEquiv
    ∀ x : SupportHomology A k,
      e B (supportRestriction h k x) = supportSingularHomologyRestrict (TopCat.of M) W h k (e A x) := by
  dsimp only
  intro x
  have hn := ssetPairRestrictScalarsHomologyIso_naturality
    (Int.castRingHom (ZMod 2))
    (HolomorphicAnosov.Topology.Homology.singularSupportRestrictionPair M A B h)
    (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2))) k
  have hx := congrArg (fun g ↦ g x) hn
  have hr : supportSingularHomologyRestrict (TopCat.of M)
      ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj
        (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))) h k =
      (SSetPair.homologyMap
        (supportSingularPairMap A B (𝟙 (TopCat.of M)) (fun _ hx hB ↦ hx (h hB)))
        ((ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))).obj
          (ModuleCat.of (ZMod 2) (ULift.{u} (ZMod 2)))) k).hom.toAddMonoidHom := by
    simp [supportSingularHomologyRestrict, supportSingularHomologyMap, supportSingularPairMap]
  rw [hr]
  exact hx

end HolomorphicAnosov.HatcherCompactSupport
