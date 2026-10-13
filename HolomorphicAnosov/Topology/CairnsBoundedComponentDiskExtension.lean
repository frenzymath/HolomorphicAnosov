import HolomorphicAnosov.Topology.CairnsRadialPatchConvexControl
import Mathlib.Data.Set.UnionLift
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.UniformSpace.HeineCantor
import HolomorphicAnosov.Topology.BoundedOpenRealInterval
import HolomorphicAnosov.Topology.FrontierConnectedComponentIn
import HolomorphicAnosov.Topology.CairnsResidualChordRefinementShrinking
import HolomorphicAnosov.Topology.Plane.CairnsChordSectorSeparation
import HolomorphicAnosov.Topology.Plane.CairnsConvexStarSectorExtension
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Prescribed boundary extension over a given bounded complementary component

Source: S. S. Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§3--§4, printed pp.861--865, especially Theorem 4.1 on p.864 and Lemma 4.1 on p.865;
`literature/cairns-jordan-schoenflies-1951.pdf` and its obtained text.
DAG node: `topo.cairns_bounded_component_disk_extension`.

The standard circle is Mathlib's `Circle` in the complex plane. The complementary
component is expressed by `connectedComponentIn`; nonemptiness excludes its empty
value at a point outside the complement. No existence or uniqueness of a bounded
complementary component is asserted. All domains have their subspace topologies.
-/

namespace HolomorphicAnosov

open Set

/--
Every prescribed homeomorphism of an embedded standard circle onto `Circle` extends
over the closure of the given nonempty bounded complementary component, with the
stated boundary and exact interior image.

Source: Cairns (1951), Lemma 3.1 and corollary, pp.861--862; star-sector construction
§3(D,E), pp.862--863; radial extension §4(A), Theorem 4.1 and recurrence (4.3), p.864;
Lemma 4.1, exhaustion and continuity argument, p.865. The proof below is the DAG's
one-level source proof relative to `topo.cairns_chord_sector_separation_g10`,
`topo.cairns_convex_star_sector_extension_g10`, and
`topo.cairns_residual_chord_refinement_shrinking_g10`. Compact uniform continuity and
the compact-to-Hausdorff closed-map/homeomorphism criteria supply the remaining
named prerequisites. This Stage2 declaration postpones its proof with one `sorry`.

Natural-language proof:

1. The embedded circle c is compact. Its complementary components are open and polygonally
connected: balls disjoint from c form a basis, and finite ball chains give an open-and-closed
reachable class in each component. Since a is bounded, its closure is compact. Every frontier
point of a lies in c: if it were outside c, a small connected ball disjoint from c meeting a would
be wholly in a, contradicting its being a frontier point. These facts do not yet assert
c⊆closure(a).

2. Choose Q∈a and a line through Q. In each direction let its first exit from a be D1,D2.
Boundedness gives finite exit distances, openness makes them positive, and the preceding boundary
containment gives D1,D2∈c. The entire open segment d between them lies in a. The chord-sector
theorem divides a into two nonempty sectors with boundaries contained in d plus the corresponding
curve arcs.

3. Apply the convex-star extension to both sectors using the originally prescribed h, with affine
values on their shared chord. The radial extension preserves that h at every original boundary
contact and agrees on the chord. Use the refinement theorem to obtain the increasing filled cells
a_j and K_j, closed nested contact sets S_j⊂c, and compatible H_j on closure(a_j)∪c. It also
supplies the residual-sector decomposition, uniform shrinking in both planes, and exhaustions
⋃a_j=a and ⋃K_j=ball(0,1). This is the exact source recurrence, including finite termination;
countable pasting and planar seams are the open mathematical content of that prerequisite.

4. Every S_j lies on frontier(a_j) and hence in closure(a), since a_j⊂a. Their union is dense in c
by refinement, so closedness of closure(a) gives c⊆closure(a). Together with frontier(a)⊆c and
a∩c=∅ this proves frontier(a)=c and closure(a)=a∪c. Thus no independent Jordan boundary-equality
theorem has been imported.

5. Define F on a∪c by F|c=h and F(x)=H_j(x) whenever x∈a_j. Compatibility makes this independent
of j. Every interior point lies in some open a_j, so F agrees with the continuous H_j on a
neighborhood. If x is on frontier(a_j)∩a, it lies in a later filled open cell; compatibility
ensures F(x)=H_j(x) also there. Each H_j maps a_j bijectively onto K_j, and h maps c bijectively
onto S1. For two interior points choose a common stage to get injectivity; their images cannot be
on S1. Target exhaustion gives surjectivity onto the entire closed disk.

6. For continuity at p∈c and ε>0, choose a source distance δ>0 such that q∈c and |q−p|<2δ imply
|h(q)−h(p)|<ε/2, using uniform continuity of h on compact c. Choose j for which every residual
source sector has diameter <δ and every corresponding target sector has diameter <ε/2. Continuity
of H_j at p on closure(a_j)∪c supplies a neighborhood in which points of this domain map within ε
of h(p). Reduce its radius below δ. Any remaining nearby x∈a lies in a residual sector β. Select
an endpoint q∈c of its boundary chord. Since q∈closure(β), |q−x|<δ (enlarge the strict mesh margin
if necessary), so |q−p|<2δ. All later filled pieces within β map into its corresponding target
sector: the refinement respects the chord-side subdivision and only fills within that sector.
Hence F(x) is within ε/2 of its boundary value h(q), and within ε of h(p). Points of c itself are
handled by h. This proves boundary continuity without claiming countable pasting is automatic.

7. F is now a continuous bijection from compact closure(a) to the Hausdorff closed unit disk. It
is closed and therefore has continuous inverse, yielding the required homeomorphism. Its
restriction is exactly the original h, irrespective of orientation or wild curve/chord
accumulations, and its image of a is the open unit disk.

This parent is complete only one level down. The three source children remain open at exact
substantive polygonal, convex-star, and countable refinement gaps; this does not certify the
Jordan–Schoenflies theorem down to Mathlib.
-/
theorem cairns_bounded_component_disk_extension
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (a : Set ℂ) (ha_nonempty : a.Nonempty)
    (ha_component : ∃ z : ℂ, a = connectedComponentIn (Set.range γ)ᶜ z)
    (ha_bounded : Bornology.IsBounded a) (h : (Set.range γ) ≃ₜ Circle) :
    frontier a = Set.range γ ∧ closure a = a ∪ Set.range γ ∧
      ∃ F : closure a ≃ₜ Metric.closedBall (0 : ℂ) 1,
        (∀ (z : closure a) (hz : z.val ∈ Set.range γ),
          (F z).val = (h ⟨z.val, hz⟩ : ℂ)) ∧
        (fun z : closure a ↦ (F z).val) '' {z : closure a | z.val ∈ a} =
          Metric.ball (0 : ℂ) 1 := by
  have hc : IsClosed (Set.range γ) := (isCompact_range hγ.continuous).isClosed
  obtain ⟨x, hax⟩ := ha_component
  have haopen : IsOpen a := hax ▸ hc.isOpen_compl.connectedComponentIn
  have hasub : a ⊆ (Set.range γ)ᶜ := hax ▸ connectedComponentIn_subset _ _
  have hfront : frontier a ⊆ Set.range γ := by
    rw [hax]
    simpa only [compl_compl] using
      frontier_connectedComponentIn_subset_compl hc.isOpen_compl x
  obtain ⟨z, hz⟩ := ha_nonempty
  let line : ℝ → ℂ := fun t ↦ z + t
  have hline : Isometry line := Isometry.of_dist_eq fun t s ↦ by
    simpa only [line, dist_add_left] using Complex.isometry_ofReal.dist_eq t s
  have hopen : IsOpen (line ⁻¹' a) := haopen.preimage hline.continuous
  have hzero : (0 : ℝ) ∈ line ⁻¹' a := by simpa [line] using hz
  let U := connectedComponentIn (line ⁻¹' a) 0
  have hUopen : IsOpen U := hopen.connectedComponentIn
  have hUconn : IsConnected U := isConnected_connectedComponentIn_iff.mpr hzero
  have hUsub : U ⊆ line ⁻¹' a := connectedComponentIn_subset _ _
  have hUbdd : Bornology.IsBounded U :=
    (hline.antilipschitzWith.isBounded_preimage ha_bounded).subset hUsub
  obtain ⟨u, v, huv, hUeq, hucl, hvcl⟩ :=
    bounded_open_connected_real_interval hUopen hUconn hUbdd
  have hend (t : ℝ) (htcl : t ∈ closure U) (htout : t ∉ U) :
      line t ∈ frontier a := by
    have htfront : t ∈ frontier U := ⟨htcl, by simpa only [hUopen.interior_eq] using htout⟩
    have hta : line t ∉ a := frontier_connectedComponentIn_subset_compl hopen 0 htfront
    refine ⟨closure_mono (image_subset_iff.mpr hUsub)
      (mem_closure_image hline.continuous.continuousAt htcl), ?_⟩
    simpa only [haopen.interior_eq] using hta
  have huch : line u ∈ range γ := hfront (hend u hucl (by simp [hUeq]))
  have hvch : line v ∈ range γ := hfront (hend v hvcl (by simp [hUeq]))
  obtain ⟨p, hp⟩ := huch
  obtain ⟨q, hq⟩ := hvch
  have hpq : p ≠ q := by
    intro heq
    have : line u = line v := hp.symm.trans (heq ▸ hq)
    exact huv.ne (hline.injective this)
  have hchord : openSegment ℝ (γ p) (γ q) ⊆ a := by
    rw [hp, hq, openSegment_eq_image_lineMap]
    rintro w ⟨t, ht, rfl⟩
    have hin : (1 - t) * u + t * v ∈ U := by
      rw [hUeq]
      constructor <;> nlinarith [ht.1, ht.2, huv]
    have hmem : line ((1 - t) * u + t * v) ∈ a := hUsub hin
    convert hmem using 1
    simp only [AffineMap.lineMap_apply_module, line, Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have hcomponent : ∃ w ∈ a, connectedComponentIn (range γ)ᶜ w = a := by
    refine ⟨z, hz, ?_⟩
    rw [hax] at hz ⊢
    exact (connectedComponentIn_eq hz).symm
  obtain ⟨d, βt, hregions, hmonoA, hmonoK, hmonoT, hclosedT, hdense,
      hcontactclosure, hcount, hfrontstage, hremaining⟩ :=
    HolomorphicAnosov.Topology.Plane.cairns_residual_chord_refinement_shrinking
      γ hγ a ⟨z, hz⟩ ha_bounded hcomponent h p q hpq hchord
  have hcontacts : (⋃ j, γ '' (d.stages j).contacts γ) ⊆ closure a := by
    intro w hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    apply closure_mono (hregions j).2.2.1
    apply frontier_subset_closure
    rw [(hfrontstage j).2.1]
    exact Or.inl hj
  have hcover : range γ ⊆ closure a := by
    rw [← hcontactclosure]
    exact closure_minimal hcontacts isClosed_closure
  classical
  have hboundary : frontier a = Set.range γ := by
    apply Subset.antisymm hfront
    intro z hz
    refine ⟨hcover hz, ?_⟩
    rw [haopen.interior_eq]
    exact fun hza ↦ hasub hza hz
  have hclosure : closure a = a ∪ range γ := by
    rw [closure_eq_self_union_frontier, hboundary]
  rcases hremaining with ⟨hH, hstep, hlinear, hTsucc, hKsucc, hres, hrestarget,
    hdisj, hsector, hterm, hmax, hmesh, hshrink, hAunion, hKunion⟩
  let S : ℕ → Set ℂ := fun j ↦ closure (d.stages j).region ∪ range γ
  let f : ℕ → ℂ → ℂ := fun j ↦ (d.stages j).map
  have hSmono : Monotone S := fun i j hij ↦
    union_subset_union (closure_mono (hmonoA hij)) Subset.rfl
  have hScover : closure a ⊆ ⋃ j, S j := by
    intro x hx
    rw [hclosure] at hx
    rcases hx with hx | hx
    · rw [← hAunion] at hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨j, Or.inl (subset_closure hj)⟩
    · exact mem_iUnion.mpr ⟨0, Or.inr hx⟩
  have hSsub (j : ℕ) : S j ⊆ closure a :=
    union_subset (closure_mono (hregions j).2.2.1) hcover
  have hstable (i j : ℕ) (hij : i ≤ j) (x : ℂ) (hx : x ∈ S i) :
      f j x = f i x := by
    induction j, hij using Nat.le_induction with
    | base => rfl
    | succ j hij ih => exact (hstep j x (hSmono hij hx)).trans ih
  have hagree (i j : ℕ) (x : ℂ) (hi : x ∈ S i) (hj : x ∈ S j) :
      f i x = f j x := by
    exact (hstable i (max i j) (le_max_left _ _) x hi).symm.trans
      (hstable j (max i j) (le_max_right _ _) x hj)
  let g : closure a → ℂ := Set.iUnionLift S (fun j x ↦ f j x) hagree _ hScover
  have hgrestrict (j : ℕ) (x : closure a) (hx : (x : ℂ) ∈ S j) :
      g x = f j x := Set.iUnionLift_of_mem x hx
  have hgcont (x : closure a) (hx : (x : ℂ) ∈ a) : ContinuousAt g x := by
    obtain ⟨j, hj⟩ := mem_iUnion.mp
      (show (x : ℂ) ∈ ⋃ j, (d.stages j).region by rwa [hAunion])
    obtain ⟨H, hHmap, hHbdry⟩ := hH j
    have hfj : ContinuousOn (f j) (S j) := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (continuous_subtype_val.comp H.continuous).congr hHmap
    have hfjx : ContinuousAt (f j) (x : ℂ) := hfj.continuousAt
      (Filter.mem_of_superset ((hregions j).2.1.mem_nhds hj)
        (fun _ ht ↦ Or.inl (subset_closure ht)))
    apply (hfjx.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq
    have hevent : ∀ᶠ y : closure a in nhds x, (y : ℂ) ∈ (d.stages j).region :=
      (continuous_subtype_val.isOpen_preimage _ (hregions j).2.1).mem_nhds hj
    filter_upwards [hevent] with y hy
    exact hgrestrict j y (Or.inl (subset_closure hy))
  have hinj : Function.Injective g := by
    intro x y hxy
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hScover x.property)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hScover y.property)
    let n := max i j
    have hxn : (x : ℂ) ∈ S n := hSmono (le_max_left _ _) hi
    have hyn : (y : ℂ) ∈ S n := hSmono (le_max_right _ _) hj
    obtain ⟨H, hHmap, hHbdry⟩ := hH n
    apply Subtype.ext
    have heq : H ⟨x, hxn⟩ = H ⟨y, hyn⟩ := by
      apply Subtype.ext
      rw [hHmap, hHmap]
      change f n x = f n y
      rw [← hgrestrict n x hxn, ← hgrestrict n y hyn]
      exact hxy
    exact congrArg (fun z : S n ↦ (z : ℂ)) (H.injective heq)
  have hgbdry (x : closure a) (hx : (x : ℂ) ∈ range γ) :
      g x = (h ⟨x, hx⟩ : ℂ) := by
    obtain ⟨H, hHmap, hHbdry⟩ := hH 0
    rw [hgrestrict 0 x (Or.inr hx)]
    change (d.stages 0).map x = _
    rw [← hHmap ⟨x, Or.inr hx⟩]
    exact hHbdry _ hx
  have hgimage : g '' {x : closure a | (x : ℂ) ∈ a} = Metric.ball (0 : ℂ) 1 := by
    apply Subset.antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := mem_iUnion.mp (show (x : ℂ) ∈ ⋃ j, (d.stages j).region by rwa [hAunion])
      rw [hgrestrict j x (Or.inl (subset_closure hj))]
      exact (hregions j).2.2.2.2.2.2 ⟨x, hj, rfl⟩
    · intro y hy
      obtain ⟨j, hj⟩ := mem_iUnion.mp (show y ∈ ⋃ j, (d.stages j).target by rwa [hKunion])
      obtain ⟨x, hx, hxy⟩ := hj
      refine ⟨⟨x, subset_closure ((hregions j).2.2.1 hx)⟩,
        (hregions j).2.2.1 hx, ?_⟩
      exact (hgrestrict j _ (Or.inl (subset_closure hx))).trans hxy
  have hgrange : Set.range g = Metric.closedBall (0 : ℂ) 1 := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (x : ℂ) ∈ a ∪ range γ := hclosure.subset x.property
      rcases hx with hx | hx
      · exact Metric.ball_subset_closedBall (hgimage ▸ mem_image_of_mem g hx)
      · rw [hgbdry x hx, Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]
    · intro hy
      rw [← Metric.ball_union_sphere] at hy
      rcases hy with hy | hy
      · obtain ⟨x, _, hx⟩ := (show y ∈ g '' {x : closure a | (x : ℂ) ∈ a} by rwa [hgimage])
        exact ⟨x, hx⟩
      · let t : Circle := ⟨y, hy⟩
        let x := h.symm t
        refine ⟨⟨x, hcover x.property⟩, ?_⟩
        rw [hgbdry _ x.property]
        exact congrArg (fun t : Circle ↦ (t : ℂ)) (h.apply_symm_apply t)
  let G : closure a → Metric.closedBall (0 : ℂ) 1 :=
    fun x ↦ ⟨g x, hgrange ▸ mem_range_self x⟩
  have hGbij : Function.Bijective G := by
    refine ⟨fun x y hxy ↦ hinj (congrArg Subtype.val hxy), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := (show (y : ℂ) ∈ Set.range g by rw [hgrange]; exact y.property)
    exact ⟨x, Subtype.ext hx⟩
  have hsourcecontact (j : ℕ)
      (i : Topology.Plane.CairnsRefinement.ResidualComponent ((d.stages j).contacts γ)) :
      ((d.steps j).star i).contact ∈ closure ((d.steps j).star i).sector := by
    let b := (d.steps j).star i
    let ray : ℝ → ℂ := fun t ↦
      (γ ((d.steps j).gap i).first + γ ((d.steps j).gap i).last) / 2 +
        t • (b.sign • (Complex.I *
          (γ ((d.steps j).gap i).last - γ ((d.steps j).gap i).first)))
    have hray : Continuous ray := continuous_const.add (continuous_id.smul continuous_const)
    have hradius : b.radius ∈ closure (Ioo (0 : ℝ) b.radius) := by
      rw [closure_Ioo b.radius_pos.ne]
      exact ⟨le_of_lt b.radius_pos, le_rfl⟩
    have hcontact := hray.continuousAt.continuousWithinAt.mem_closure hradius b.ray_inside
    change ray b.radius ∈ closure b.sector at hcontact
    change b.contact ∈ closure b.sector
    simpa only [ray, b.first_contact, Topology.Plane.CairnsRefinement.StarChoice.contact] using hcontact
  have htargetcontrol : ∀ j
      (i : Topology.Plane.CairnsRefinement.ResidualComponent ((d.stages j).contacts γ)),
      let q : range γ := ⟨((d.steps j).star i).contact,
        ⟨((d.steps j).gap i).parameter ((d.steps j).star i).contactParameter, rfl⟩⟩
      (h q : ℂ) ∈ closure (βt j i) ∧
        ∀ y : closure a, (y : ℂ) ∈ ((d.steps j).star i).sector →
          g y ∈ closure (βt j i) := by
    intro j i
    let b := (d.steps j).star i
    have hsec := hsector j i
    rcases hsec with ⟨hβne, hβopen, hβconn, hβcomp, hβfront, hβball,
      htne, htopen, htconn, htcomp, htfront, htball, htarc, htmap⟩
    have hcontact : (h (⟨b.contact,
        ⟨((d.steps j).gap i).parameter b.contactParameter, rfl⟩⟩ : range γ) : ℂ) ∈
        closure (βt j i) := by
      apply htarc
      refine ⟨((d.steps j).gap i).parameter b.contactParameter, ?_, rfl⟩
      rw [Topology.Plane.CairnsCircleGap.closedArc]
      change Circle.exp (((d.steps j).gap i).start +
          (((d.steps j).gap i).stop - ((d.steps j).gap i).start) *
            (b.contactParameter : ℝ)) ∈
        Circle.exp '' Set.Icc ((d.steps j).gap i).start ((d.steps j).gap i).stop
      refine ⟨((d.steps j).gap i).start +
          (((d.steps j).gap i).stop - ((d.steps j).gap i).start) *
            (b.contactParameter : ℝ), ?_, rfl⟩
      constructor <;> nlinarith [((d.steps j).gap i).start_lt_stop,
        b.contactParameter.property.1, b.contactParameter.property.2]
    refine ⟨hcontact, ?_⟩
    intro y hy
    have hyβ : (y : ℂ) ∈ b.sector := hy
    have hya : (y : ℂ) ∈ a := by
      rcases hβcomp with ⟨xβ, hxβ, hxeq⟩
      have hsubset := connectedComponentIn_subset (a \ closure (d.stages j).region) xβ
      have : (y : ℂ) ∈ connectedComponentIn (a \ closure (d.stages j).region) xβ := by
        rw [hxeq]
        exact hyβ
      exact (hsubset this).1
    obtain ⟨n, hyn⟩ := mem_iUnion.mp (show (y : ℂ) ∈ ⋃ n, (d.stages n).region by rwa [hAunion])
    let m := max j n
    have hym : (y : ℂ) ∈ (d.stages m).region :=
      hmonoA (le_max_right j n) hyn
    have hymβ : (y : ℂ) ∈ (d.stages m).region ∩ b.sector := ⟨hym, hyβ⟩
    have hmap := htmap m (le_max_left j n) hymβ
    rw [hgrestrict m y (Or.inl (subset_closure hym))]
    exact hmap
  have hsectorcontrol : ∀ j
      (i : Topology.Plane.CairnsRefinement.ResidualComponent ((d.stages j).contacts γ)),
      ∃ q : range γ, (q : ℂ) ∈ closure ((d.steps j).star i).sector ∧
        (h q : ℂ) ∈ closure (βt j i) ∧
        ∀ y : closure a, (y : ℂ) ∈ ((d.steps j).star i).sector →
          g y ∈ closure (βt j i) := by
    intro j i
    exact ⟨⟨((d.steps j).star i).contact,
      ⟨((d.steps j).gap i).parameter ((d.steps j).star i).contactParameter, rfl⟩⟩,
      hsourcecontact j i, htargetcontrol j i⟩
  -- Cairns p.865: the final boundary estimate follows from sector correspondence.
  suffices hGcont : Continuous G by
    have : CompactSpace (closure a) := isCompact_iff_compactSpace.mp ha_bounded.isCompact_closure
    let F := (Equiv.ofBijective G hGbij).toHomeomorphOfContinuousClosed
      hGcont hGcont.isClosedMap
    exact ⟨hboundary, hclosure, F, hgbdry, hgimage⟩
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx : (x : ℂ) ∈ a ∪ range γ := hclosure.subset x.property
  rcases hx with hx | hx
  · exact (hgcont x hx).codRestrict (fun x ↦ hgrange ▸ mem_range_self x)
  · apply ContinuousAt.codRestrict (fun x ↦ hgrange ▸ mem_range_self x)
    have : CompactSpace (range γ) :=
      isCompact_iff_compactSpace.mp (isCompact_range hγ.continuous)
    have hhuc : UniformContinuous (fun q : range γ ↦ (h q : ℂ)) :=
      CompactSpace.uniformContinuous_of_continuous (continuous_subtype_val.comp h.continuous)
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hhδ⟩ := Metric.uniformContinuous_iff.mp hhuc (ε / 2) (half_pos hε)
    obtain ⟨j, hj⟩ := hshrink (min (δ / 2) (ε / 2))
      (lt_min (half_pos hδ) (half_pos hε))
    obtain ⟨H, hHmap, hHbdry⟩ := hH j
    let pS : S j := ⟨x, Or.inr hx⟩
    have hHcontinuous : Continuous (fun y : S j ↦ (H y : ℂ)) :=
      continuous_subtype_val.comp H.continuous
    obtain ⟨η, hη, hhη⟩ := Metric.continuousAt_iff.mp hHcontinuous.continuousAt ε hε
    refine ⟨min η (δ / 2), lt_min hη (half_pos hδ), ?_⟩
    intro y hy
    have hyd : dist (y : ℂ) (x : ℂ) < δ / 2 := lt_of_lt_of_le hy (min_le_right _ _)
    by_cases hys : (y : ℂ) ∈ S j
    · have hdist : dist (⟨y, hys⟩ : S j) pS < η := lt_of_lt_of_le hy (min_le_left _ _)
      have hbound := hhη hdist
      rw [hHmap, hHmap] at hbound
      change dist (f j y) (f j x) < ε at hbound
      rwa [← hgrestrict j y hys, ← hgrestrict j x (Or.inr hx)] at hbound
    · have hya : (y : ℂ) ∈ a := (hclosure.subset y.property).resolve_right
        (fun hyc ↦ hys (Or.inr hyc))
      have hyres : (y : ℂ) ∈ a \ closure (d.stages j).region :=
        ⟨hya, fun hycl ↦ hys (Or.inl hycl)⟩
      rw [hres j] at hyres
      obtain ⟨i, hi⟩ := mem_iUnion.mp hyres
      obtain ⟨q, hqsource, hqtarget, hmapsector⟩ := hsectorcontrol j i
      have hbsource : Bornology.IsBounded (closure ((d.steps j).star i).sector) := by
        apply ha_bounded.closure.subset
        apply closure_mono
        intro w hw
        have hwa : w ∈ a \ closure (d.stages j).region := by
          rw [hres j]
          exact mem_iUnion.mpr ⟨i, hw⟩
        exact hwa.1
      have hbtarget : Bornology.IsBounded (closure (βt j i)) := by
        apply Metric.isBounded_ball.closure.subset
        apply closure_mono
        intro w hw
        have hwa : w ∈ Metric.ball (0 : ℂ) 1 \ closure (d.stages j).target := by
          rw [hrestarget j]
          exact mem_iUnion.mpr ⟨i, hw⟩
        exact hwa.1
      have hqydist : dist (q : ℂ) (y : ℂ) < δ / 2 :=
        lt_of_le_of_lt (Metric.dist_le_diam_of_mem hbsource hqsource (subset_closure hi))
          (lt_of_lt_of_le (hj j le_rfl i).1 (min_le_left _ _))
      have hqxdist : dist q (⟨x, hx⟩ : range γ) < δ := by
        change dist (q : ℂ) (x : ℂ) < δ
        have ht := dist_triangle (q : ℂ) (y : ℂ) (x : ℂ)
        linarith
      have htargetdist : dist (g y) (h q : ℂ) < ε / 2 :=
        lt_of_le_of_lt (Metric.dist_le_diam_of_mem hbtarget (hmapsector y hi) hqtarget)
          (lt_of_lt_of_le (hj j le_rfl i).2 (min_le_right _ _))
      have hboundarydist := hhδ hqxdist
      rw [hgbdry x hx]
      have ht := dist_triangle (g y) (h q : ℂ) (h ⟨x, hx⟩ : ℂ)
      linarith

end HolomorphicAnosov
