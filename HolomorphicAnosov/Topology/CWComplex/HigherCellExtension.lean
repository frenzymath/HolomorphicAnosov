import HolomorphicAnosov.Topology.NullhomotopicSphereDiskExtension
import HolomorphicAnosov.Topology.UnitSphereSimplyConnected
import Mathlib.Topology.CWComplex.Classical.Basic
import Mathlib.Topology.Homotopy.Lifting

/-!
# Extending maps over higher-dimensional characteristic disks

Source: Hatcher, *Algebraic Topology*, Proposition 1B.9, printed p. 91 (PDF p. 100).
The nullhomotopy-to-disk extension uses Hatcher pp. 14–15; the boundary-preserving
round-disk/max-norm adapter uses Bredon, *Topology and Geometry*, I16.2–16.4, pp. 56–57.

This module states DAG node `topo.cw_realization_higher_cell_extension_g8` on Mathlib's
actual characteristic maps, maximum-norm disks and skeleton subspaces. The two theorem
proofs are postponed in Stage 2. The attaching maps themselves use Mathlib alone.
-/

open Metric Set _root_.Topology

namespace HolomorphicAnosov

universe u v w

variable {K : Type u} [TopologicalSpace K] [T2Space K] [CWComplex (univ : Set K)]
variable {E : Type v} [TopologicalSpace E] {Y : Type w} [TopologicalSpace Y]

/-- The literal characteristic boundary map into the lower skeleton.

Mathlib `RelCWComplex.map`, `continuousOn` and `cellFrontier_subset_skeletonLT`
in `Topology/CWComplex/Classical/Basic.lean`, with the original maximum-norm sphere.
The data and its continuity are constructed directly from these Mathlib fields.
-/
def cwAttachingMap (d : ℕ) (i : RelCWComplex.cell (univ : Set K) d) :
    C(sphere (0 : Fin d → ℝ) 1, ↥(RelCWComplex.skeletonLT (univ : Set K) d)) where
  toFun s := ⟨RelCWComplex.map d i s,
    RelCWComplex.cellFrontier_subset_skeletonLT d i ⟨s, s.property, rfl⟩⟩
  continuous_toFun :=
    ((RelCWComplex.continuousOn d i).mono sphere_subset_closedBall).domRestrict.subtype_mk _

/-- The same literal attaching map in successor-skeleton notation.

Source: Mathlib `RelCWComplex.cellFrontier_subset_skeleton`; `skeleton C n` is
`skeletonLT C (n + 1)`. No new CW structure or boundary parametrization is selected.
-/
def cwAttachingMapSucc (n : ℕ) (i : RelCWComplex.cell (univ : Set K) (n + 1)) :
    C(sphere (0 : Fin (n + 1) → ℝ) 1, ↥(RelCWComplex.skeleton (univ : Set K) n)) where
  toFun s := ⟨RelCWComplex.map (n + 1) i s,
    RelCWComplex.cellFrontier_subset_skeleton n i ⟨s, s.property, rfl⟩⟩
  continuous_toFun :=
    ((RelCWComplex.continuousOn (n + 1) i).mono sphere_subset_closedBall).domRestrict.subtype_mk _

/-- Every map on the lower skeleton extends on each characteristic disk of dimension at least 3.

Source: Hatcher Proposition 1B.9, p. 91, higher-cell paragraph; Hatcher pp. 14–15
and Bredon I16.2–16.4, pp. 56–57, supply the native disk-filling step as recorded in
`topo.nullhomotopic_sphere_disk_extension`. Natural-language proof:

The CW field gives continuity of the characteristic map on the original closed unit
ball. Restricting to the sphere and using the frontier-in-lower-skeleton theorem gives
exactly `cwAttachingMap d i`. Compose it with `f`. Since d ≥ 3, its source sphere has
dimension d − 1 ≥ 2 and is simply connected and locally path connected. These are
the original maximum-norm subspace topologies, via the boundary-preserving sphere
adapter. Choose a sphere point (for example the first coordinate unit vector), and
use surjectivity of p to choose an initial point over its image. The covering lift
theorem lifts this composite to a continuous map into E. Contractibility of E gives
a homotopy of its identity to a constant; composing that contraction with the lift
and then p yields a nullhomotopy of the original boundary map. The nullhomotopic
sphere-to-disk extension theorem supplies a continuous F on this very closed ball
with the displayed literal boundary equation. Its Hatcher closed-bottom/side pasting
and disk-prism retraction proof, with the Bredon boundary-preserving adapter, needs
no separation property of Y. This proof uses no prism in the conclusion, finite CW
assumption, regularity or injectivity of the boundary characteristic map. When two
boundary points have the same characteristic image, their prescribed f-values agree.
If there are no d-cells, the cell-indexed assertion is vacuous.
-/
theorem cw_realization_higher_cell_extension
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    [ContractibleSpace E] (d : ℕ) (hd : 3 ≤ d)
    (i : RelCWComplex.cell (univ : Set K) d)
    (f : C(↥(RelCWComplex.skeletonLT (univ : Set K) d), Y)) :
    ∃ F : C(closedBall (0 : Fin d → ℝ) 1, Y),
      ∀ s : sphere (0 : Fin d → ℝ) 1,
        F ⟨s.val, sphere_subset_closedBall s.property⟩ = f (cwAttachingMap d i s) := by
  have hdim : d - 1 + 1 = d := by omega
  have htop := unit_sphere_simply_connected (d - 1) (by omega)
  rw [hdim] at htop
  have : SimplyConnectedSpace {v : Fin d → ℝ // ‖v‖ = 1} := htop.2.2.1
  have : LocallyPathConnectedSpace {v : Fin d → ℝ // ‖v‖ = 1} := htop.2.2.2.1
  have hsphere : sphere (0 : Fin d → ℝ) 1 = {v : Fin d → ℝ | ‖v‖ = 1} := by
    ext v
    simp
  let es : sphere (0 : Fin d → ℝ) 1 ≃ₜ {v : Fin d → ℝ // ‖v‖ = 1} :=
    Homeomorph.setCongr hsphere
  let b : C({v : Fin d → ℝ // ‖v‖ = 1}, Y) :=
    { toFun := fun s ↦ f (cwAttachingMap d i (es.symm s))
      continuous_toFun := f.continuous.comp ((cwAttachingMap d i).continuous.comp es.symm.continuous) }
  have hfill : ∃ B : {v : Fin d → ℝ // ‖v‖ ≤ 1} → Y, Continuous B ∧
      ∀ s : {v : Fin d → ℝ // ‖v‖ = 1}, B ⟨s.val, le_of_eq s.property⟩ = b s := by
    let z₀ : {v : Fin d → ℝ // ‖v‖ = 1} :=
      ⟨fun _ ↦ 1, by
        have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
        simp⟩
    obtain ⟨e₀, he₀⟩ := hsurj (b z₀)
    obtain ⟨L, hL, _⟩ := hp.existsUnique_continuousMap_lifts b z₀ e₀ he₀
    obtain ⟨estar, ⟨C⟩⟩ := id_nullhomotopic E
    apply nullhomotopic_sphere_disk_extension d (by omega) b b.continuous
    refine ⟨p estar, fun q ↦ p (C (q.1, L q.2)), ?_, ?_, ?_⟩
    · exact hp.continuous.comp (C.continuous.comp
        (continuous_fst.prodMk (L.continuous.comp continuous_snd)))
    · intro s
      simpa only [C.apply_zero, ContinuousMap.id_apply, Function.comp_apply] using congrFun hL.2 s
    · intro s
      simp only [C.apply_one, ContinuousMap.const_apply]
  rcases hfill with ⟨B, hB, hBb⟩
  have hball : closedBall (0 : Fin d → ℝ) 1 = {v : Fin d → ℝ | ‖v‖ ≤ 1} := by
    ext v
    simp
  let ed : closedBall (0 : Fin d → ℝ) 1 ≃ₜ {v : Fin d → ℝ // ‖v‖ ≤ 1} :=
    Homeomorph.setCongr hball
  let edC : C(closedBall (0 : Fin d → ℝ) 1, {v : Fin d → ℝ // ‖v‖ ≤ 1}) :=
    { toFun := ed
      continuous_toFun := ed.continuous }
  let F : C(closedBall (0 : Fin d → ℝ) 1, Y) :=
    { toFun := B ∘ edC
      continuous_toFun := hB.comp edC.continuous }
  refine ⟨F, ?_⟩
  intro s
  have hs := hBb (es s)
  have he : edC ⟨s.val, sphere_subset_closedBall s.property⟩ =
      (⟨(es s).val, le_of_eq (es s).property⟩ : {v : Fin d → ℝ // ‖v‖ ≤ 1}) := by
    apply Subtype.ext
    rfl
  change B (edC ⟨s.val, sphere_subset_closedBall s.property⟩) = f (cwAttachingMap d i s)
  rw [he]
  exact hs

/-- The equivalent successor form of the same higher-cell extension theorem.

Source and proof: Hatcher Proposition 1B.9, p. 91, and the preceding theorem's full
proof. Put d = n + 1. Then n ≥ 2 implies d ≥ 3, and `skeleton univ n` is the same
subspace as `skeletonLT univ (n + 1)`. Transport along this equality; the characteristic
map, sphere-to-disk inclusion and prescribed boundary points stay unchanged.
No global skeletal descent or homotopy-uniqueness conclusion is asserted.
-/
theorem cw_realization_higher_cell_extension_succ
    (p : E → Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    [ContractibleSpace E] (n : ℕ) (hn : 2 ≤ n)
    (i : RelCWComplex.cell (univ : Set K) (n + 1))
    (f : C(↥(RelCWComplex.skeleton (univ : Set K) n), Y)) :
    ∃ F : C(closedBall (0 : Fin (n + 1) → ℝ) 1, Y),
      ∀ s : sphere (0 : Fin (n + 1) → ℝ) 1,
        F ⟨s.val, sphere_subset_closedBall s.property⟩ = f (cwAttachingMapSucc n i s) := by
  obtain ⟨F, hF⟩ :=
    cw_realization_higher_cell_extension p hp hsurj (n + 1) (by omega) i f
  refine ⟨F, ?_⟩
  intro s
  convert hF s using 1
  rfl

end HolomorphicAnosov

