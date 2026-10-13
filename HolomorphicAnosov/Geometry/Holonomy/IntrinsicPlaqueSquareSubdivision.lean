import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation
import HolomorphicAnosov.Topology.OpenCoverSquareSubdivision

/-! # Intrinsic plaque grids for leaf homotopies  Nisoli, Theorem 1.3.8, pp.24–25: subdivide the homotopy in the intrinsic leaf topology.    Every closed cell then lies in a single original plaque. -/

namespace HolomorphicAnosov
open Set

universe u v

/-- Every continuous square in an intrinsic S leaf admits a strict finite grid whose closed cells are contained in individual S plaques of the original boxes. (Nisoli, Theorem 1.3.8) -/
theorem intrinsic_plaque_square_subdivision
    {s t : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [ChartedSpace (Fin (s + t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M)
    (q : Quotient F.stablePartition)
    (H : unitInterval × unitInterval → IntrinsicFoliationLeaf F.stablePartition q)
    (hH : Continuous H) :
    ∃ n : ℕ, ∃ a : Fin (n + 2) → unitInterval,
      StrictMono a ∧ a 0 = 0 ∧ a (Fin.last (n + 1)) = 1 ∧
      ∀ j k : Fin (n + 1), ∃ b : F.boxIndex, ∃ w : FoliationCoordinateDisk t,
        F.stableLabel b w = q ∧
        ∀ z ∈ Icc (a j.castSucc) (a j.succ) ×ˢ Icc (a k.castSucc) (a k.succ),
          ∃ r : FoliationCoordinateDisk s,
            ((F.box b).chart (r, w)).val = (H z).val := by
  let J := {bw : (Σ _ : F.boxIndex, FoliationCoordinateDisk t) //
    F.stableLabel bw.1 bw.2 = q}
  let plaque (i : J) : FoliationCoordinateDisk s →
      IntrinsicFoliationLeaf F.stablePartition q := fun r ↦
    ⟨((F.box i.val.1).chart (r, i.val.2)).val,
      (F.stable_label i.val.1 r i.val.2).trans i.property⟩
  have hopen (i : J) : IsOpen (range (plaque i)) := by
    rcases i with ⟨⟨b,w⟩,h⟩
    subst q
    exact (F.stable_plaque b w).isOpen_range
  have hcover (z : unitInterval × unitInterval) : ∃ i : J, H z ∈ range (plaque i) := by
    obtain ⟨b,hb⟩ := F.cover (H z).val
    let rw := (F.box b).chart.symm ⟨(H z).val,hb⟩
    have he : ((F.box b).chart rw).val = (H z).val :=
      congrArg Subtype.val ((F.box b).chart.apply_symm_apply ⟨(H z).val,hb⟩)
    have hl : F.stableLabel b rw.2 = q :=
      (F.stable_label b rw.1 rw.2).symm.trans
        ((congrArg (Quotient.mk F.stablePartition) he).trans (H z).property)
    exact ⟨⟨⟨b,rw.2⟩,hl⟩,rw.1,Subtype.ext he⟩
  obtain ⟨n,a,ha,h0,h1,hcells⟩ := exists_openCover_squareSubdivision H hH
    (fun i : J ↦ range (plaque i)) hopen hcover
  refine ⟨n,a,ha,h0,h1,?_⟩
  intro j k
  obtain ⟨i,hi⟩ := hcells j k
  refine ⟨i.val.1,i.val.2,i.property,?_⟩
  intro z hz
  obtain ⟨r,hr⟩ := hi hz
  exact ⟨r,congrArg Subtype.val hr⟩

end HolomorphicAnosov
