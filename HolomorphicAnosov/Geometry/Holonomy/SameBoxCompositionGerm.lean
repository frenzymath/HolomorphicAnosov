import HolomorphicAnosov.Geometry.LocalHolonomyPathContinuation

/-! # Composition of original one-box holonomy germs  The existing proof from GlobalUnstableHolonomy is exposed here for the cellwise homotopy comparison; its intrinsic carriers and domains are unchanged. -/

noncomputable section
open scoped _root_.Topology
open Set Filter
universe u v
namespace HolomorphicAnosov

/-- Composing two consecutive correspondences in the SAME box gives the direct correspondence as a germ. (Nisoli) -/
theorem same_box_composition_germ {s t : ℕ} {M : Type u}
    [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (Fin (s+t) → ℝ) M]
    (F : TransverseContinuousFoliations.{u,v} s t M) {x y z : M}
    (e : LocalPlaqueTransport F x z) (l : LocalPlaqueTransport F x y)
    (r : LocalPlaqueTransport F y z)
    (hlb : l.box = e.box) (hrb : r.box = e.box)
    (hlf : l.first = e.first) (hmid : l.second = r.first) (hrs : r.second = e.second) :
    (Filter.Germ.ofFun (r.map ∘ l.map) : Filter.Germ (𝓝 (F.uPoint x)) (F.ULeaf z)) =
      Filter.Germ.ofFun e.map := by
  have hrt : r.map.source ∈ 𝓝 (F.uPoint y) := r.map.open_source.mem_nhds r.source_point
  have ht : Tendsto l.map (𝓝 (F.uPoint x)) (𝓝 (F.uPoint y)) := by
    simpa only [l.map_point] using (l.map.continuousAt l.source_point).tendsto
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [ht.eventually hrt,l.map.open_source.mem_nhds l.source_point,
    e.map.open_source.mem_nhds e.source_point] with u hur hul hue
  obtain ⟨v,hv⟩ := l.source_in_plaque u hul
  have hchartl (p : FoliationCoordinateDisk s × FoliationCoordinateDisk t) :
      ((F.box l.box).chart p).val = ((F.box e.box).chart p).val :=
    congrArg (fun b ↦ ((F.box b).chart p).val) hlb
  have hchartr (p : FoliationCoordinateDisk s × FoliationCoordinateDisk t) :
      ((F.box r.box).chart p).val = ((F.box e.box).chart p).val :=
    congrArg (fun b ↦ ((F.box b).chart p).val) hrb
  have hve : ((F.box e.box).chart (e.first,v)).val = u.val := by
    rw [← hlf,← hchartl]
    exact hv
  have hvr : ((F.box r.box).chart (r.first,v)).val = (l.map u).val := by
    rw [hchartr,← hmid,← hchartl,l.coordinate_map u v hul hv]
  apply Subtype.ext
  change (r.map (l.map u)).val = (e.map u).val
  rw [r.coordinate_map (l.map u) v hur hvr,e.coordinate_map u v hue hve,hchartr,hrs]


end HolomorphicAnosov
