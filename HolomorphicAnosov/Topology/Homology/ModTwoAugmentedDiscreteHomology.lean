import HolomorphicAnosov.Topology.Homology.ModTwoAugmentedHomeomorphism
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Reduced mod-two homology of totally disconnected spaces

Source: Hatcher, Algebraic Topology, Propositions 2.6 and 2.8 pp.109–110,
coefficient-sum augmentation p.110, and coefficient extension p.153.
Singular simplices in a totally disconnected space are constant. The resulting
alternating differential is zero in odd degrees and identity in positive even
degrees. Augmentation affects only reduced degree zero, where the answer is
the kernel of literal coefficient sum. The fixed coefficient object is retained.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- For a totally disconnected space, the reduced modulus-two degree-zero group
is the augmentation kernel, and every positive reduced group is zero.

Source: Hatcher pp.109–110,153. The constant-simplex chain isomorphism gives a
zero first differential. The short complex in augmented degrees 2,1,0 therefore
has homology equal to the kernel of its outgoing coefficient-sum map. In each
augmented degree n+2 its incoming and outgoing differentials are exactly those
of the ordinary singular complex at n+1. The identity isomorphism of these
three-term complexes identifies their homology. Mathlib's alternating-constant
calculation makes the latter homology zero. The augmentation witness comes from
the coefficient-preserving identity-homeomorphism comparison. This argument
includes the empty space and makes no claim that degree-minus-one homology vanishes. -/
theorem modTwoAugmentedDiscreteHomology (X : TopCat.{0}) [TotallyDisconnectedSpace X] :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let L := TopCat.toSSet.obj X
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∃ w : K.d 1 0 ≫ ε = 0,
      Nonempty ((ChainComplex.augment K ε w).homology 1 ≅ kernel ε) ∧
      ∀ n : ℕ, IsZero ((ChainComplex.augment K ε w).homology (n + 2)) := by
  dsimp only
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let K := (TopCat.toSSet.obj X).chainComplex R0
  let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  obtain ⟨w, _, _, _, _⟩ := modTwoAugmentedHomeomorphism X X (Homeomorph.refl X)
  let A := ChainComplex.augment K ε w
  have hd : K.d 1 0 = 0 := by
    let e := AlgebraicTopology.singularChainComplexFunctorIsoOfTotallyDisconnectedSpace
      (ModuleCat (ZMod 2)) R0 X
    have h := e.hom.comm 1 0
    have hz : (ChainComplex.alternatingConst.obj (∐ fun _ : X ↦ R0)).d 1 0 = 0 := by
      simp [ChainComplex.alternatingConst, HomologicalComplex.alternatingConst]
    rw [hz, CategoryTheory.Limits.comp_zero] at h
    apply (cancel_mono (e.hom.f 0)).mp
    rw [CategoryTheory.Limits.zero_comp]
    exact h.symm
  refine ⟨w, ⟨?_⟩, ?_⟩
  · let S := A.sc' 2 1 0
    have hf : S.f = 0 := hd
    exact A.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
      (ShortComplex.HomologyData.ofIsLimitKernelFork S hf _ (kernelIsKernel S.g)).left.homologyIso
  · intro n
    let e : A.homology (n + 2) ≅ K.homology (n + 1) :=
      A.homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp) ≪≫
        ShortComplex.homologyMapIso
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by simp [A, Category.id_comp, Category.comp_id])
            (by simp [A, Category.id_comp, Category.comp_id])) ≪≫
        (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm
    apply IsZero.of_iso ?_ e
    exact AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat (ZMod 2)) (n + 1) R0 X (by omega)

end
end HolomorphicAnosov
