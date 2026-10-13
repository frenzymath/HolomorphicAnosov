import HolomorphicAnosov.Topology.OpenCoverPathReplacement
import HolomorphicAnosov.Topology.SingleCellPuncturedRetraction
import HolomorphicAnosov.Topology.SingleCellInteriorChart
import HolomorphicAnosov.Topology.PushoutSumQuotient
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Path

open CategoryTheory CategoryTheory.Limits
open Topology _root_.Topology
namespace HolomorphicAnosov
universe u

/-- Attaching one cell of dimension at least two preserves path connectedness
and every based loop is homotopic relative endpoints to an old-space loop.

Source: Hatcher, Algebraic Topology, Proposition 1.26(a),(b), pp.50–51,
and Lemma 1.15 p.35. The conclusion uses only the surjectivity part in
dimension two; no injectivity assertion is made there.

Proof. The categorical pushout is homeomorphic, compatibly with both given
maps, to the adjunction quotient of X and the closed disk. Every disk point
joins a boundary point by a disk path, so this quotient is path connected.
For a basepoint x choose a boundary point θ and a path in X from x to its
attaching image. Attach a square strip to the quotient along its bottom edge
using this path and along its right edge using the radial arc from θ to the
disk centre. The strip retracts onto bottom union right, so the enlarged
space Z deformation retracts onto the original pushout fixing X. Choose an
interior disk point off the radial arc. The complement U of that point in Z
deformation retracts onto X by radial projection from the omitted point,
with the strip contracted compatibly. The complement V of X in Z is
contractible: retract the open disk onto the radial arc and then collapse
the remaining strip. The open sets U,V cover Z and U∩V is path connected,
since a punctured n-disk is path connected for n≥2 and its attached strip
meets it. Lemma 1.15 subdivides each loop into U and V pieces and connects
their switching points to a common point of U∩V. The resulting V loops are
null homotopic, so all loop classes come from U. Change basepoint along the
strip's left edge, retract U to X and Z to the original pushout. These maps
fix x and compose to the given inclusion, yielding the stated based path
homotopy. Quotient continuity and compatibility on the attached edges
justify each deformation; no Hausdorff assumption on X or injectivity of
the attaching map is needed. Universe lifts of the standard disk and sphere
are transported by their canonical homeomorphisms.
-/
theorem single_higher_cell_attachment_pathConnected_loop
    {X Y : TopCat.{u}} [PathConnectedSpace X]
    (n : ℕ) (hn : 2 ≤ n)
    (φ : TopCat.diskBoundary.{u} n ⟶ X)
    (f : X ⟶ Y) (χ : TopCat.disk.{u} n ⟶ Y)
    (hpush : IsPushout φ (TopCat.diskBoundaryInclusion.{u} n) f χ) :
    PathConnectedSpace Y ∧
      ∀ (x : X) (γ : Path (f.hom x) (f.hom x)), ∃ δ : Path x x,
        Path.Homotopic (δ.map f.hom.continuous) γ := by
  refine ⟨?_, ?_⟩
  · classical
    obtain ⟨x₀⟩ := PathConnectedSpace.nonempty (X := X)
    have hjoin : ∀ y : Y, Joined (f x₀) y := by
      intro y
      obtain ⟨x, rfl⟩ | ⟨z, rfl⟩ :=
        Types.eq_or_eq_of_isPushout (hpush.map (forget TopCat)) y
      · exact (PathConnectedSpace.joined x₀ x).map f.hom.continuous
      · change ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) at z
        obtain ⟨z'⟩ := z
        have hn0 : 0 < n := by omega
        let q : TopCat.diskBoundary n :=
          ⟨⟨EuclideanSpace.single ⟨0, hn0⟩ (1 : ℝ), by simp⟩⟩
        let q' : TopCat.disk n := TopCat.diskBoundaryInclusion n q
        have hq : f (φ q) = χ q' := by
          exact congrArg (fun h : TopCat.diskBoundary n ⟶ Y => h q) hpush.w
        let : PathConnectedSpace (Metric.closedBall
            (0 : EuclideanSpace ℝ (Fin n)) 1) :=
          isPathConnected_iff_pathConnectedSpace.mp
            (Metric.isPathConnected_closedBall (by norm_num))
        have hto : PathConnectedSpace (TopCat.disk n) :=
          Homeomorph.ulift.symm.pathConnectedSpace
        have hjdisk : Joined (ULift.up z') q' := hto.joined _ _
        have hbase : Joined (f x₀) (χ q') := by
          rw [← hq]
          exact (PathConnectedSpace.joined x₀ (φ q)).map f.hom.continuous
        exact hbase.trans (hjdisk.symm.map χ.hom.continuous)
    exact ⟨⟨f x₀⟩, fun y z ↦ (hjoin y).symm.trans (hjoin z)⟩
  · intro x γ
    classical
    let : T1Space (TopCat.disk n) := by
      change T1Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
      infer_instance
    have hboundary_closed :
        IsClosed (Set.range (TopCat.diskBoundaryInclusion n).hom) := by
      let : T2Space (TopCat.disk n) := by
        change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
        infer_instance
      exact (isCompact_range (TopCat.diskBoundaryInclusion n).hom.continuous).isClosed
    have hold_closed : IsClosed (Set.range f.hom) :=
      pushout_left_range_isClosed hpush hboundary_closed
    let p : TopCat.disk n := ⟨⟨0, by simp⟩⟩
    have hp : ‖p.down.val‖ < 1 := by simp [p]
    have hpboundary : p ∉ Set.range (TopCat.diskBoundaryInclusion n).hom := by
      rintro ⟨a, ha⟩
      have hnorm : ‖(TopCat.diskBoundaryInclusion n a).down.val‖ = 1 := by
        change ‖a.down.val‖ = 1
        simpa only [Metric.mem_sphere, dist_zero_right] using a.down.property
      rw [ha] at hnorm
      exact (ne_of_lt hp) hnorm
    have hcross := pushout_left_ne_right_off_left_range hpush hpboundary
    obtain ⟨R, K, hRfixed, hKzero, hKone, hKfixed⟩ :=
      single_cell_punctured_deformation n φ f χ hpush p hp
    obtain ⟨hcell_sc, hpunct_pc⟩ :=
      single_cell_open_cover_topology n hn φ f χ hpush
    have hA : IsOpen ({χ.hom p}ᶜ : Set Y) := pushout_singleton_compl_isOpen_of_right_off_range hpush hpboundary
    have hB : IsOpen ((Set.range f.hom)ᶜ : Set Y) := hold_closed.isOpen_compl
    have hcover : {χ.hom p}ᶜ ∪ (Set.range f.hom)ᶜ = (Set.univ : Set Y) := by
      ext y
      simp only [Set.mem_univ, iff_true]
      by_cases hy : y = χ.hom p
      · right
        subst y
        rintro ⟨z, hz⟩
        exact hcross z hz
      · left
        exact hy
    obtain ⟨δ, hδA, hδhom⟩ := openCover_path_replacement hA hB hcover hpunct_pc hcell_sc
      (hcross x) (hcross x) γ
    let δA : Path (⟨f.hom x, hcross x⟩ : {y : Y // y ≠ χ.hom p})
        ⟨f.hom x, hcross x⟩ :=
      { toFun := fun t ↦ ⟨δ t, hδA t⟩
        continuous_toFun := δ.continuous.subtype_mk _
        source' := Subtype.ext δ.source
        target' := Subtype.ext δ.target }
    let rpath : Path x x :=
      { toFun := fun t ↦ R ⟨δ t, hδA t⟩
        continuous_toFun := R.continuous.comp (δ.continuous.subtype_mk _)
        source' := by
          have heq : (⟨δ 0, hδA 0⟩ : {y : Y // y ≠ χ.hom p}) =
              ⟨f.hom x, hcross x⟩ := Subtype.ext δ.source
          change R ⟨δ 0, hδA 0⟩ = x
          rw [heq]
          exact hRfixed x (hcross x)
        target' := by
          have heq : (⟨δ 1, hδA 1⟩ : {y : Y // y ≠ χ.hom p}) =
              ⟨f.hom x, hcross x⟩ := Subtype.ext δ.target
          change R ⟨δ 1, hδA 1⟩ = x
          rw [heq]
          exact hRfixed x (hcross x) }
    let Hδ : δ.Homotopy (rpath.map f.hom.continuous) :=
      { toFun := fun z ↦ K (z.1, δA z.2)
        continuous_toFun := K.continuous.comp
          (continuous_fst.prodMk (δA.continuous.comp continuous_snd))
        map_zero_left := by intro t; exact hKzero (δA t)
        map_one_left := by intro t; exact hKone (δA t)
        prop' := by
          intro t z hz
          rcases hz with hz | hz
          · subst z
            change K (t, δA 0) = δ 0
            rw [δA.source, δ.source]
            exact hKfixed t x (hcross x)
          · have hz' : z = 1 := hz
            subst z
            change K (t, δA 1) = δ 1
            rw [δA.target, δ.target]
            exact hKfixed t x (hcross x) }
    exact ⟨rpath, (show δ.Homotopic (rpath.map f.hom.continuous) from ⟨Hδ⟩).symm.trans hδhom⟩

end HolomorphicAnosov

