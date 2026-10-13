import HolomorphicAnosov.Topology.Homology.ContractibleSingularHomology
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Algebra.Homology.Augment
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

set_option backward.isDefEq.respectTransparency false in
/-- Every reduced mod-two homology group of a contractible space vanishes for
the literal singular coefficient-sum augmentation.

Source: Hatcher, Algebraic Topology, Corollary 2.11 p.111, the reduced sequence
p.118 and the coefficient extension p.153. In positive reduced degrees the
augmented cycle/boundary short complex is the ordinary short complex shifted
once, so ordinary contractible acyclicity applies. In reduced degree zero,
the cokernel of the first boundary is the direct sum of coefficients over path
components. A contractible space has one component, and coefficient sum is the
isomorphism from this one-summand coproduct to R0. Thus the first boundary and
augmentation are exact. Contractibility includes nonemptiness; no assertion
about the reduced homology of an empty space is made. -/
theorem modTwoAugmentedContractibleAcyclic (X : TopCat.{0}) [ContractibleSpace X] :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let L := TopCat.toSSet.obj X
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∀ (w : K.d 1 0 ≫ ε = 0) (q : ℕ),
      IsZero ((ChainComplex.augment K ε w).homology (q + 1)) := by
  dsimp only
  intro w q
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let L := TopCat.toSSet.obj X
  let K := L.chainComplex R0
  let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let A := ChainComplex.augment K ε w
  cases q with
  | zero =>
    let p := SSet.π₀.fromChainComplexXZero L R0
    let S := ShortComplex.mk (K.d 1 0) p (SSet.π₀.d_fromChainComplexXZero L R0 1)
    have hex : S.Exact := S.exact_of_g_is_cokernel
      (SSet.isColimitCokernelCoforkChainComplexDOneZero L R0)
    let s : (∐ fun _ : SSet.π₀ L ↦ R0) ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
    have hs : IsIso s := by
      have h : IsIso (L.homology₀ε R0) := inferInstance
      simpa only [SSet.homology₀ε, isIso_comp_left_iff] using h
    have hε : p ≫ s = ε := by
      apply SSet.chainComplex_hom_ext
      intro σ
      dsimp only [p]
      rw [← Category.assoc, SSet.π₀.comp_fromChainComplexXZero]
      simp [s, ε, SSet.ιChainComplex]
    let e : S ≅ A.sc' 2 1 0 :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (asIso s)
        (by simp [S, A, ChainComplex.augment]) (by simpa [S, A] using hε.symm)
    exact IsZero.of_iso (S.exact_iff_isZero_homology.mp hex)
      (A.homologyIsoSc' 2 1 0 (by simp) (by simp) ≪≫
        (ShortComplex.homologyMapIso e).symm)
  | succ n =>
    let e : A.homology (n + 2) ≅ K.homology (n + 1) :=
      A.homologyIsoSc' (n + 3) (n + 2) (n + 1) (by simp) (by simp) ≪≫
        ShortComplex.homologyMapIso
          (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
            (by simp [A]) (by simp [A])) ≪≫
        (K.homologyIsoSc' (n + 2) (n + 1) n (by simp) (by simp)).symm
    exact IsZero.of_iso (singular_homology_isZero_of_contractible X R0 (n + 1)
      (by omega)) e

end HolomorphicAnosov
