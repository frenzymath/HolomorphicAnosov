import HolomorphicAnosov.Topology.SingularSubspaceSubcomplex
import Mathlib.Algebra.Homology.Augment
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

open CategoryTheory CategoryTheory.Limits
open scoped Simplicial ZeroObject
namespace HolomorphicAnosov

/-- The augmented singular-chain sequence of a subspace is short exact over
mod-two coefficients, with identity on the added coefficient object and the
native inclusion and relative quotient maps in all higher degrees.

Source: Hatcher, Algebraic Topology, the augmented pair sequence p.118 and
coefficient extension p.153. Postcomposition preserves coefficient sum, so the
inclusion extends by identity in index zero. The quotient extends by zero in
that index. Their composite vanishes by the relative quotient equation.
In index zero the sequence is R0 → R0 → 0 with identity first map, hence short
exact; every successor index is the native singular-pair short exact sequence.
Degreewise short exactness gives short exactness of chain complexes. Empty
subspaces and empty ambient spaces are allowed: the added coefficient sequence
remains identity followed by zero. No reduced acyclicity is assumed. -/
theorem modTwoAugmentedPairShortExact (X : TopCat.{0}) (A : Set X) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let P := singularSubspacePair X A
    let KA := P.left.chainComplex R0
    let KX := P.right.chainComplex R0
    let εA : KA.X 0 ⟶ R0 := Sigma.desc (fun _ : P.left _⦋0⦌ ↦ 𝟙 R0)
    let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ : P.right _⦋0⦌ ↦ 𝟙 R0)
    ∀ (wA : KA.d 1 0 ≫ εA = 0) (wX : KX.d 1 0 ≫ εX = 0),
    let RA := ChainComplex.augment KA εA wA
    let RX := ChainComplex.augment KX εX wX
    let Q := ChainComplex.augment (P.chainComplex R0)
      (0 : (P.chainComplex R0).X 0 ⟶ (0 : ModuleCat (ZMod 2))) (by simp)
    ∃ (i : RA ⟶ RX) (π : RX ⟶ Q) (h : i ≫ π = 0),
      (ShortComplex.mk i π h).ShortExact ∧
      i.f 0 = 𝟙 R0 ∧ π.f 0 = 0 ∧
      (∀ n, i.f (n + 1) = (SSet.chainComplexMap P.hom R0).f n) ∧
      (∀ n, π.f (n + 1) = (P.chainComplexπ R0).f n) := by
  dsimp only
  intro wA wX
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let P := singularSubspacePair X A
  let KA := P.left.chainComplex R0
  let KX := P.right.chainComplex R0
  let εA : KA.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let εX : KX.X 0 ⟶ R0 := Sigma.desc (fun _ ↦ 𝟙 R0)
  let RA := ChainComplex.augment KA εA wA
  let RX := ChainComplex.augment KX εX wX
  let Q := ChainComplex.augment (P.chainComplex R0)
    (0 : (P.chainComplex R0).X 0 ⟶ (0 : ModuleCat (ZMod 2))) (by simp)
  let i : RA ⟶ RX := ChainComplex.ofHom
    (fun n ↦ match n with
      | 0 => 𝟙 R0
      | n + 1 => (SSet.chainComplexMap P.hom R0).f n)
    (fun n ↦ by
      cases n with
      | zero =>
        change (SSet.chainComplexMap P.hom R0).f 0 ≫ εX = εA ≫ 𝟙 R0
        apply SSet.chainComplex_hom_ext
        intro σ
        rw [← Category.assoc, SSet.ι_chainComplexMap_f]
        simp [εX, εA, SSet.ιChainComplex]
      | succ n => exact (SSet.chainComplexMap P.hom R0).comm (n + 1) n)
  let π : RX ⟶ Q := ChainComplex.ofHom
    (fun n ↦ match n with
      | 0 => 0
      | n + 1 => (P.chainComplexπ R0).f n)
    (fun n ↦ by
      cases n with
      | zero => exact comp_zero.trans comp_zero.symm
      | succ n => exact (P.chainComplexπ R0).comm (n + 1) n)
  have hiπ : i ≫ π = 0 := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero => exact comp_zero
    | succ n => exact P.chainComplex_condition_f R0 n
  refine ⟨i, π, hiπ, ?_, rfl, rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  cases n with
  | zero =>
    have : Mono (((ShortComplex.mk i π hiπ).map
        (HomologicalComplex.eval (ModuleCat (ZMod 2)) (.down ℕ) 0)).f) := by
      change Mono (𝟙 R0)
      infer_instance
    have : Epi (((ShortComplex.mk i π hiπ).map
        (HomologicalComplex.eval (ModuleCat (ZMod 2)) (.down ℕ) 0)).g) := by
      change Epi (0 : R0 ⟶ (0 : ModuleCat (ZMod 2)))
      infer_instance
    refine ⟨?_⟩
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨x, rfl⟩
  | succ n =>
    exact (P.shortExact_chainComplexShortComplex R0).map
      (HomologicalComplex.eval (ModuleCat (ZMod 2)) (.down ℕ) n)

end HolomorphicAnosov
