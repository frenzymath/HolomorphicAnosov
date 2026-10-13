import HolomorphicAnosov.Topology.Homology.ModTwoSphereSuccessor
import HolomorphicAnosov.Topology.Homology.ModTwoZeroSphereProfile
import HolomorphicAnosov.Topology.Homology.ModTwoPositiveSphereReducedH0
import Mathlib.Analysis.InnerProductSpace.PiL2
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

/-- Base transport from the augmented two-point calculation to the first
positive-dimensional native sphere.

Source: Hatcher, Algebraic Topology, Corollary 2.14 p.114 and coefficient
extension p.153. -/
theorem modTwoPositiveSphereProfileBase :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let S := {x : EuclideanSpace ℝ (Fin (0 + 1 + 1)) // ‖x‖ = 1}
    let L := TopCat.toSSet.obj (TopCat.of S)
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∀ w : K.d 1 0 ≫ ε = 0,
      Nonempty ((ChainComplex.augment K ε w).homology (0 + 1 + 1) ≅ R0) ∧
      ∀ q : ℕ, q ≠ 0 + 1 → IsZero ((ChainComplex.augment K ε w).homology (q + 1)) := by
  dsimp only
  intro wU
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let SL := {x : EuclideanSpace ℝ (Fin 1) // ‖x‖ = 1}
  let LL := TopCat.toSSet.obj (TopCat.of SL)
  let KL := LL.chainComplex R0
  let εL : KL.X 0 ⟶ R0 := Sigma.desc (fun _ : LL _⦋0⦌ ↦ 𝟙 R0)
  have wL : KL.d 1 0 ≫ εL = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [εL, SSet.ιChainComplex, Fin.sum_univ_two]
  have hzero := modTwoZeroSphereProfile
  dsimp only at hzero
  have hzero' := hzero wL
  obtain ⟨hTop, hOff⟩ := hzero'
  obtain ⟨hTop⟩ := hTop
  have hsucc0 := modTwoSphereSuccessor 0 0 wU wL
  obtain ⟨hIso0⟩ := hsucc0
  have hH0 := modTwoPositiveSphereReducedH0 0 wU
  constructor
  · exact ⟨hIso0 ≪≫ hTop⟩
  · intro q hq
    cases q with
    | zero => exact hH0
    | succ q =>
      cases q with
      | zero =>
        exfalso
        exact hq rfl
      | succ n =>
        have hsucc := modTwoSphereSuccessor 0 (Nat.succ n) wU wL
        obtain ⟨hIso⟩ := hsucc
        apply IsZero.of_iso (hOff n)
        simpa [Nat.add_assoc] using hIso

end HolomorphicAnosov
