import HolomorphicAnosov.Topology.Homology.ModTwoConnectedReducedH0
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
namespace HolomorphicAnosov

/-- The reduced degree-zero group of every positive-dimensional native sphere
vanishes for the literal coefficient-sum augmentation.

Source: Hatcher, Algebraic Topology, Proposition 2.7 p.110 and coefficient
extension p.153. The sphere is connected in positive dimension, so ordinary H₀
augmentation is an isomorphism and augmented H₁ is its kernel. The generic
cycle/cokernel bridge is represented by the public mod-two H₀ interfaces. -/
theorem modTwoPositiveSphereReducedH0 (k : ℕ) :
    let R0 : ModuleCat.{0} (ZMod 2) := ModuleCat.of (ZMod 2) (ULift.{0} (ZMod 2))
    let S := {x : EuclideanSpace ℝ (Fin (k + 1 + 1)) // ‖x‖ = 1}
    let L := TopCat.toSSet.obj (TopCat.of S)
    let K := L.chainComplex R0
    let ε : K.X 0 ⟶ R0 := Sigma.desc (fun _ : L _⦋0⦌ ↦ 𝟙 R0)
    ∀ w : K.d 1 0 ≫ ε = 0,
      IsZero ((ChainComplex.augment K ε w).homology 1) := by
  dsimp only
  intro w
  let E := EuclideanSpace ℝ (Fin (k + 1 + 1))
  let S := {x : E // ‖x‖ = 1}
  have hrank : 1 < Module.rank ℝ E := by
    apply Module.one_lt_rank_of_one_lt_finrank
    dsimp [E]
    simp
  have hp : IsPathConnected (Metric.sphere (0 : E) 1) :=
    isPathConnected_sphere hrank 0 (by norm_num)
  have hset : Metric.sphere (0 : E) 1 = Set.ofPred (fun x : E => ‖x‖ = 1) := by
    ext x
    simp [Metric.sphere, dist_zero_right]
  have hp' : IsPathConnected (Set.ofPred (fun x : E => ‖x‖ = 1)) := by
    rw [← hset]
    exact hp
  let : PathConnectedSpace S :=
    isPathConnected_iff_pathConnectedSpace.mp hp'
  let : SSet.IsConnected (TopCat.toSSet.obj (TopCat.of S)) := inferInstance
  exact modTwoConnectedReducedH0 (TopCat.of S) w

end HolomorphicAnosov
