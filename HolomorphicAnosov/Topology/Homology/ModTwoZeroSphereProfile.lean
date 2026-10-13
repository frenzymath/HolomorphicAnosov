import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedDiscreteHomology
import HolomorphicAnosov.Topology.Homology.ModTwoTwoPointAugmentationKernel
import HolomorphicAnosov.Topology.Homology.ReducedSphereHomology.ZeroSphereBoolHomeomorph

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

/-- The Euclidean zero-sphere has reduced mod-two homology R0 in degree zero,
and zero in every positive degree, for the literal coefficient-sum augmentation.

Source: Hatcher, Algebraic Topology, Propositions 2.6–2.8 pp.109–110 and p.153.
The zero-sphere is homeomorphic to the discrete two-point space Bool. Singular
simplices there are constant. Its augmented degree-one homology is the kernel
of the sum map R0⊕R0→R0, isomorphic to R0 by a↦(a,-a); its higher homology
vanishes by the alternating zero/identity differentials. Transport these groups
through the genuine augmented chain isomorphism of the two-point homeomorphism.
The chosen augmentation witness makes no difference by proof irrelevance. -/
theorem modTwoZeroSphereProfile :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let S := {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}
    let L := TopCat.toSSet.obj (TopCat.of S)
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∀ w : K.d 1 0 ≫ ε = 0,
      Nonempty ((ChainComplex.augment K ε w).homology 1 ≅ R0) ∧
      ∀ n : ℕ, IsZero ((ChainComplex.augment K ε w).homology (n + 2)) := by
  dsimp only
  intro w
  obtain ⟨_, hk, hz⟩ := modTwoAugmentedDiscreteHomology (TopCat.of Bool)
  obtain ⟨ib⟩ := hk
  obtain ⟨ik⟩ := modTwoTwoPointAugmentationKernel
  obtain ⟨_, _, b, _, _⟩ := modTwoAugmentedHomeomorphism
    (TopCat.of {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}) (TopCat.of Bool)
    Topology.Homology.zeroSphereBoolHomeomorph
  refine ⟨⟨(HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2))
    (ComplexShape.down ℕ) 1).mapIso b ≪≫ ib ≪≫ ik⟩, ?_⟩
  intro n
  exact IsZero.of_iso (hz n)
    ((HomologicalComplex.homologyFunctor (ModuleCat (ZMod 2))
      (ComplexShape.down ℕ) (n + 2)).mapIso b)

end HolomorphicAnosov
