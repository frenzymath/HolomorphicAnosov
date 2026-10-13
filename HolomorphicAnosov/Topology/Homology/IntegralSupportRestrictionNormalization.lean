import HolomorphicAnosov.Topology.Homology.SupportHomeomorphism
noncomputable section
namespace HolomorphicAnosov
open CategoryTheory HolomorphicAnosov.Topology _root_.Topology
universe u

/-- The compact-support restriction is definitionally the native relative homology map
of the identity-induced support pair map. -/
theorem integral_support_restrict_native_apply
    (X : TopCat.{u}) (R : ModuleCat.{u} ℤ)
    {A B : Set X} (h : B ⊆ A) (q : ℕ)
    (a : supportSingularHomology X A R q) :
    supportSingularHomologyRestrict X R h q a =
      SSetPair.homologyMap
        (SSetPair.homMk (X := supportSingularPair X A) (Y := supportSingularPair X B)
          (TopCat.toSSet.map (TopCat.ofHom
            ⟨fun z : ↥(Aᶜ) ↦ (⟨z.val, fun hz ↦ z.property (h hz)⟩ : ↥(Bᶜ)),
              continuous_subtype_val.subtype_mk _⟩))
          (𝟙 _) (by rfl)) R q a := by
  simp [supportSingularHomologyRestrict, supportSingularHomologyMap,
    supportSingularPairMap]
  congr 3

end HolomorphicAnosov
