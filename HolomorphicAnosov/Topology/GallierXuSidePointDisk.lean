import HolomorphicAnosov.Topology.GallierXuEdgeIdentificationBoundary
import HolomorphicAnosov.Topology.GallierXuSidePointContinuity

noncomputable section
open Set Topology _root_.Topology
namespace HolomorphicAnosov.Topology.GallierXu

/-- A prescribed circular side point is in the closed parameter disk. -/
lemma sidePoint_mem_disk {P : Presentation} (f : Fin P.length)
    (i : Fin (P.get f).length) (t : ℝ) : sidePoint P f i t ∈ Disk := by
  change dist (sidePoint P f i t) (0 : ℂ) ≤ 1
  rw [dist_zero_right, sidePoint_norm]

/-- Canonical closed-disk representative of a prescribed circular side point. -/
def sidePointDisk {P : Presentation} (f : Fin P.length)
    (i : Fin (P.get f).length) (t : ℝ) : Disk :=
  ⟨sidePoint P f i t, sidePoint_mem_disk f i t⟩

@[simp] lemma coe_sidePointDisk {P : Presentation} (f : Fin P.length)
    (i : Fin (P.get f).length) (t : ℝ) :
    (sidePointDisk f i t : ℂ) = sidePoint P f i t := rfl

/-- The canonical disk-side representative varies continuously with its parameter. -/
lemma continuous_sidePointDisk {P : Presentation} (f : Fin P.length)
    (i : Fin (P.get f).length) : Continuous (sidePointDisk f i) :=
  (continuous_sidePoint f i).subtype_mk _

/-- Equal edge labels at the same parameter give equal quotient representatives. -/
lemma project_sidePointDisk_eq {P : Presentation} (f g : Fin P.length)
    (i : Fin (P.get f).length) (j : Fin (P.get g).length) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (hl : ((P.get f).get i).1 = ((P.get g).get j).1) :
    project P (f, sidePointDisk f i t) = project P (g, sidePointDisk g j t) := by
  apply Quotient.sound
  exact Relation.EqvGen.rel _ _ ⟨i, j, t, ht, hl, rfl, rfl⟩

end HolomorphicAnosov.Topology.GallierXu
