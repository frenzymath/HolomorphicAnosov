import HolomorphicAnosov.Topology.Homology.ModTwoSphereSuccessor
import HolomorphicAnosov.Topology.Homology.ModTwoPositiveSphereReducedH0
import Mathlib.Analysis.InnerProductSpace.PiL2
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

/-- Induction transport for positive native spheres. It combines the successor
isomorphism with the lower profile and new-sphere reduced H₀ vanishing.

Source: Hatcher, Algebraic Topology, Theorem 2.13 and Corollary 2.14 p.114,
with arbitrary coefficients p.153. -/
theorem modTwoPositiveSphereProfileStep (k : ℕ) :
    (let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
     let SU := {x : EuclideanSpace ℝ (Fin (k + 1 + 1 + 1)) // ‖x‖ = 1}
     let LU := TopCat.toSSet.obj (TopCat.of SU)
     let KU := LU.chainComplex R0
     let εU : KU.X 0 ⟶ R0 := Sigma.desc (fun _ : LU _⦋0⦌ ↦ 𝟙 R0)
     ∀ wU : KU.d 1 0 ≫ εU = 0,
       IsZero ((ChainComplex.augment KU εU wU).homology 1)) →
    (let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
     let SL := {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}
     let LL := TopCat.toSSet.obj (TopCat.of SL)
     let KL := LL.chainComplex R0
     let εL : KL.X 0 ⟶ R0 := Sigma.desc (fun _ : LL _⦋0⦌ ↦ 𝟙 R0)
     ∀ wL : KL.d 1 0 ≫ εL = 0,
       Nonempty ((ChainComplex.augment KL εL wL).homology (k + 1 + 1) ≅ R0) ∧
       ∀ q : ℕ, q ≠ k + 1 → IsZero ((ChainComplex.augment KL εL wL).homology (q + 1))) →
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let SU := {x : EuclideanSpace ℝ (Fin (k + 1 + 1 + 1)) // ‖x‖ = 1}
    let LU := TopCat.toSSet.obj (TopCat.of SU)
    let KU := LU.chainComplex R0
    let εU : KU.X 0 ⟶ R0 := Sigma.desc (fun _ : LU _⦋0⦌ ↦ 𝟙 R0)
    ∀ wU : KU.d 1 0 ≫ εU = 0,
      Nonempty ((ChainComplex.augment KU εU wU).homology (k + 1 + 1 + 1) ≅ R0) ∧
      ∀ q : ℕ, q ≠ k + 1 + 1 → IsZero ((ChainComplex.augment KU εU wU).homology (q + 1)) := by
  dsimp only
  intro hH0 hLower wU
  let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
  let SL := {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}
  let LL := TopCat.toSSet.obj (TopCat.of SL)
  let KL := LL.chainComplex R0
  let εL : KL.X 0 ⟶ R0 := Sigma.desc (fun _ : LL _⦋0⦌ ↦ 𝟙 R0)
  have wL : KL.d 1 0 ≫ εL = 0 := by
    apply SSet.chainComplex_hom_ext
    intro σ
    rw [← Category.assoc, SSet.ιChainComplex_d]
    simp [εL, SSet.ιChainComplex, Fin.sum_univ_two]
  obtain ⟨hTopL, hOffL⟩ := hLower wL
  obtain ⟨hTopL⟩ := hTopL
  constructor
  · have hs := modTwoSphereSuccessor (k + 1) (k + 1) wU wL
    obtain ⟨hs⟩ := hs
    exact ⟨hs ≪≫ hTopL⟩
  · intro q hq
    cases q with
    | zero => exact hH0 wU
    | succ q =>
      by_cases hqk : q = k + 1
      · subst q
        exfalso
        exact hq rfl
      · have hs := modTwoSphereSuccessor (k + 1) q wU wL
        obtain ⟨hs⟩ := hs
        exact IsZero.of_iso (hOffL q (by simpa using hqk)) hs

end HolomorphicAnosov
