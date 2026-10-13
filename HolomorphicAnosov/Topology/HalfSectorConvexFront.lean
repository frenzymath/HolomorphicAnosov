import HolomorphicAnosov.Topology.EmbeddedArcGapComponentsG2
import HolomorphicAnosov.Topology.ArcContactOrderG2
import HolomorphicAnosov.Topology.ChordShadowOppositeArcG2
import HolomorphicAnosov.Topology.ArcContactFaceGapsG2
import HolomorphicAnosov.Topology.TriangleVisibleContactFaceG2
import HolomorphicAnosov.Topology.ConvexTriangleInteriorBase
import HolomorphicAnosov.Topology.HalfSectorRadialSweepUnique
import HolomorphicAnosov.Topology.TwoTriangleSeamGeometryG2
import HolomorphicAnosov.Topology.ConvexConeVisibleSweepClosureG2
import HolomorphicAnosov.Topology.TriangleHullEndpointVisibilityG2
import HolomorphicAnosov.Topology.ConvexConeComplementConnectedG2
import HolomorphicAnosov.Topology.HalfSectorVisibleFrontier
import HolomorphicAnosov.Topology.HalfSectorVisibleRadialImage
import HolomorphicAnosov.Topology.CompactConvexHullFiniteDimensional
import HolomorphicAnosov.Topology.HalfSectorPerpendicularBaseExclusion
import HolomorphicAnosov.Topology.HalfSectorHullApexExclusion
import HolomorphicAnosov.Topology.HalfSectorVisibleRadialInjectivity
import HolomorphicAnosov.Topology.HalfSectorRadialHomeomorph
import HolomorphicAnosov.Topology.HalfSectorConvexFrontRayTail

/-!
# Cairns' two half-sector convex fronts

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
§3, Cases I/II and (D,E), printed pp.862--863, and §4, (4.1),(4.2),(A),
printed pp.863--864; `literature/cairns-jordan-schoenflies-1951.pdf`.
The complete construction and expanded proof are recorded in
`topo.cairns_half_sector_convex_front_geometry_g2`. Its retained-contact order
uses the original-circle chord-shadow consequence and the agent-written gap-filling lemma
`topo.closed_contact_interval_affine_gap_order_g5`; it is not a written Cairns proof.

The real plane is the underlying real normed space of `ℂ`. The circle, paths,
connected components, convex hulls, straight segments, visibility, closures,
frontiers and homeomorphisms below are genuine Mathlib objects. The two sides
are indexed by `Bool`: `false` has endpoint D1 and `true` has endpoint D2.
No independently postulated sector, star or contact-order predicate is used.
-/

namespace HolomorphicAnosov

open Set
open scoped Classical

/--
The original two half-sector constructions have simple visible fronts, their
precise radial shadows, ordered retained contacts and countably many straight gaps.

Source: Cairns (1951), §3 Cases I/II and (D,E), pp.862--863, with §4 pp.863--864;
Gallier--Quaintance, *Aspects of Convex Geometry*, author notes dated October 9,
2025, Chapter 3 §3.3, Theorem 3.2 pp.65--66 and Proposition 3.3 pp.66--67,
and Proposition 4.19 p.99; Rockafellar, *Convex Analysis* (1970), §§7,9,10,18,
Theorems 7.1 pp.51--52, 9.1 pp.73--74, 9.2 pp.75--76, 10.2 pp.84--85,
18.1 p.163 and 18.3/Corollary 18.3.1 p.165; Boyd--Vandenberghe,
*Convex Optimization* (2004), §2.3.3 pp.39--42. The global order step is the
explicitly agent-written omission expansion in
`topo.closed_contact_interval_affine_gap_order_g5`, applied exactly as in this
node's full natural proof. No whole published proof of that omitted step is claimed.

The component hypotheses encode the given complementary component, sector and
half-sectors. The first-contact hypotheses say only that the perpendicular ray
avoids the curve before P and initially enters the sector. Membership of the
entire open MP segment in the sector is a conclusion of component maximality,
not an input. The local half-sector hypotheses select the component containing
the near-M part of its triangle. Case I uses the stated whole-triangle inclusion;
Case II uses the ordinary hull of the actual retained curve contacts and base.

In Case II the front is exactly the points of K visible from M. The selected
open region consists of points in intΔ\K whose connected component has M in
its closure; the conclusion identifies it as one nonempty component. The angular
interval is the normalization image of the opposite triangle edge. All parameter
intervals in the gap assertion belong to the original Di-to-P curve subpath.

Natural-language proof.

C1. The chord midpoint M lies in the complementary component and hence off the curve. The first-contact segment MP avoids the curve and the original chord and initially meets β; connected-component maximality puts its entire open segment in β. Perpendicularity gives two nondegenerate triangles. Their apex edges have no curve contacts except their far endpoints. The hull generators are compact, contain their opposite bases and omit M; the hulls are compact convex subsets of their triangles. Nonnegative affine coordinates and their singleton zero fibers show both base endpoints are visible from M.

C2. In triangle coordinates (u,v), apply the shear (u,v)↦(u,u+v) and positive perspective (x,y)↦(x/y,1/y). The compact convex hull image projects onto [0,1], and its upper boundary is the continuous concave graph of an attained height H≥1. Compactness controls endpoint limits, while concavity supplies the lower chord bound. Inverse perspective gives the compact visible front. Radial visibility gives injectivity of normalization, and the apex-to-base ray decomposition gives its exact angular image. Compact-to-Hausdorff bijectivity yields a radial homeomorphism. Composing with the base interval parametrization gives an interval homeomorphism with the prescribed endpoints. Case I instead uses the base itself; all these conclusions follow by its affine parametrization.

C3. Put V=int(Δ) minus K. Every component of V approaches M. Since K is closed and misses M, a small ball at M misses K; its intersection with int(Δ) is convex and meets every component, so V is connected. It is nonempty because M lies in the closure of the nonempty triangle interior. The asserted half-sector frontier does not meet V: its curve part belongs to K, and its two apex edges miss the triangle interior. The near-M hypothesis selects the half-sector side of this frontier, so connectedness gives V⊆βhalf. Thus the Case II definition B equals V and every indicated component equals B. In Case I, B is the open triangle. Both cases give nonempty open connected shadows.

C4. A point outside K in the cone lies strictly before its first visible hull point, by closedness and convexity. Conversely strict radial points before a visible point avoid K. Convexity and nonempty triangle interior make these radial points limits of int(Δ) minus K. Compactness of the front therefore identifies the shadow closure with the closed radial sweep. A nonendpoint visible point is off both apex edges; its open radial segment lies in the triangle interior and hence in B. Comparing the closed sweep with these strict radial segments gives frontier(B)=[M,D]∪[M,P]∪L. Every front point belongs to closure(βhalf). If such a point lies on the curve, the supplied frontier bound puts it on the original half-subarc unless it is one of the two already retained endpoints. The contact set is closed, and every noncontact front point belongs to the open half-sector.

C5. Let J be the base in Case I and K in Case II. The joined shadow is the open set int(Δ1)∪int(Δ2)∪(M,P), with the two compact sets J removed. Perpendicular coordinates identify the first set by three strict linear inequalities; the two closed triangles meet exactly on [M,P], and neither removed set meets the open seam. Each connected half-shadow approaches every seam point, so adjoining the seam and taking their union gives a connected joined shadow. Its closure is the union of the two half-closures. The half-frontier formulas and opposite-triangle disjointness give its exact frontier as the original chord together with both fronts. It lies in β. Same-direction front points on different halves must lie on the common seam and hence equal P; within a half, radial visibility already gives uniqueness. Normalization and positive norm therefore give the unique nonapex radial representation in the joined closure.

C6. In Case II failure of whole-triangle inclusion gives a point of K in the triangle interior; together with its base this makes int(K) nonempty. A visible noncontact point cannot lie on the base, because visible base points are endpoints. The supporting-functional lemma gives f≤f(Q)<f(M) on K. Its entire supporting face is visible, since a point before that face on an apex ray has larger f-value. The compact planar face is a segment with extreme endpoints. Extreme hull points lie in the original generator; a base endpoint of the face must again be an original endpoint by visibility. Thus both face endpoints are curve contacts. A noncontact point is strictly between them. Case I uses the whole base as its contact face. For any contact-free interval of the front parametrization, such a face brackets an interior parameter; its contact endpoints cannot lie inside that interval, so they bracket the whole interval. The contained-segment subarc theorem then makes the entire gap image exactly the straight open segment between its own endpoints.

C7. Apply chord separation to the ORIGINAL embedded circle and each such straight gap chord, whose interior lies in the original complementary component. The connected joined shadow avoids that chord and therefore lies in one of its two sectors. The opposite original base endpoint D_other lies in the shadow closure and outside the entire selected original half-subarc. The labeled sector-frontier bounds select the sector of the complementary arc through D_other. Consequently the closure of the joined shadow misses the open original subarc between the gap endpoints. Every retained front contact belongs to that closure, so this original interval contains no retained contact. On the closed front contact parameters, inverse original-subarc parametrization is continuous and injective and fixes 0 and 1. Its gap endpoint intervals are contact-free. Distinct such target gaps are disjoint: intersecting contact-free intervals with contact endpoints have the same endpoints, and injectivity would give the same source gap. The closed-contact affine-filling theorem therefore proves strict monotonicity, giving the asserted order agreement for all retained contacts.

C8. Transfer complementary gaps in both directions using that contact-order equivalence. A missing front contact parameter has neighboring contact endpoints by compact extrema of the closed contact set; the corresponding original parameter pair belongs to the stated set of gaps. This proves that the straight gap segments cover precisely L minus the curve. Distinct gap pairs have disjoint open original parameter intervals: overlap would force equal endpoints. These intervals are nonempty and open in a second-countable space, so their family is countable. In an interval with the contacts removed, the component of a gap point cannot cross either removed endpoint, because a preconnected subset of a linear order contains every intervening point; conversely the gap interval is preconnected. Transport through the embedded front identifies each straight gap with the asserted connected component. Its endpoints are distinct by original-subarc injectivity, and its open segment lies in βhalf by the noncontact-front inclusion. These conclusions, together with C1–C7, are exactly all clauses of the theorem.
-/
theorem halfSectorConvexFront
    (σ : Circle → ℂ) (hσ : Topology.IsEmbedding σ)
    (a : Set ℂ)
    (haComponent : ∃ z ∈ (Set.range σ)ᶜ,
      a = connectedComponentIn (Set.range σ)ᶜ z)
    (haBounded : Bornology.IsBounded a)
    (D1 D2 : ℂ) (hDistinct : D1 ≠ D2)
    (μ : Path D1 D2) (hμInjective : Function.Injective μ)
    (hμCurve : Set.range μ ⊆ Set.range σ)
    (hChord : openSegment ℝ D1 D2 ⊆ a)
    (β : Set ℂ)
    (hβComponent : ∃ z ∈ a \ openSegment ℝ D1 D2,
      β = connectedComponentIn (a \ openSegment ℝ D1 D2) z)
    (_hβFrontier : frontier β ⊆ segment ℝ D1 D2 ∪ Set.range μ)
    (τ : unitInterval) (hτ : τ ∈ Set.Ioo 0 1)
    (βhalf : Bool → Set ℂ) :
    let c : Set ℂ := Set.range σ
    let M : ℂ := (D1 + D2) / 2
    let P : ℂ := μ τ
    let D : Bool → ℂ := fun i ↦ if i then D2 else D1
    let m : Bool → unitInterval → ℂ := fun i ↦
      if i then (fun t ↦ μ.subpath 1 τ t) else (fun t ↦ μ.subpath 0 τ t)
    let Δ : Bool → Set ℂ := fun i ↦ convexHull ℝ {M, P, D i}
    ∀ (_hPerpendicular :
        (P - M).re * (D2 - D1).re + (P - M).im * (D2 - D1).im = 0)
      (_hFirstContact : ∀ t ∈ Set.Ioo (0 : ℝ) 1, M + t • (P - M) ∉ c)
      (_hRayEnters : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ t ∈ Set.Ioo (0 : ℝ) ε, M + t • (P - M) ∈ β)
      (_hHalfComponent : ∀ i, ∃ z ∈ β \ openSegment ℝ M P,
        βhalf i = connectedComponentIn (β \ openSegment ℝ M P) z)
      (_hHalfFrontier : ∀ i, frontier (βhalf i) ⊆
        Set.range (m i) ∪ segment ℝ M (D i) ∪ segment ℝ M P)
      (_hHalfNear : ∀ i, ∃ ε : ℝ, 0 < ε ∧
        Metric.ball M ε ∩ interior (Δ i) ⊆ βhalf i),
    let caseI : Bool → Prop := fun i ↦ interior (Δ i) ⊆ βhalf i
    let K : Bool → Set ℂ := fun i ↦
      convexHull ℝ ((Set.range (m i) ∩ Δ i) ∪ segment ℝ (D i) P)
    let L : Bool → Set ℂ := fun i ↦ if caseI i then segment ℝ (D i) P
      else {Q | Q ∈ K i ∧ IsVisible ℝ (K i) M Q}
    let B : Bool → Set ℂ := fun i ↦ if caseI i then interior (Δ i)
      else {x | x ∈ interior (Δ i) \ K i ∧
        M ∈ closure (connectedComponentIn (interior (Δ i) \ K i) x)}
    let angular : Bool → Set ℂ := fun i ↦
      (fun Q : ℂ ↦ (Q - M) / (‖Q - M‖ : ℂ)) '' segment ℝ (D i) P
    let gaps : Bool → Set (unitInterval × unitInterval) := fun i ↦
      {g | g.1 < g.2 ∧ m i g.1 ∈ L i ∩ c ∧ m i g.2 ∈ L i ∩ c ∧
        Disjoint ((m i) '' Set.Ioo g.1 g.2) (L i ∩ c)}
    let Bstar : Set ℂ := B false ∪ B true ∪ openSegment ℝ M P
    (∀ i, IsCompact (L i) ∧ (B i).Nonempty ∧ IsOpen (B i) ∧ B i ⊆ βhalf i) ∧
    (∀ i, ¬ caseI i → ∀ x ∈ B i,
      connectedComponentIn (interior (Δ i) \ K i) x = B i) ∧
    (∃ α : ∀ i : Bool, unitInterval ≃ₜ L i,
      (∀ i, ((α i) 0).1 = D i ∧ ((α i) 1).1 = P) ∧
      ∀ (i : Bool) (s t p q : unitInterval),
        ((α i) s).1 = m i p → ((α i) t).1 = m i q → (s ≤ t ↔ p ≤ q)) ∧
    (∃ radial : ∀ i : Bool, L i ≃ₜ angular i,
      ∀ (i : Bool) (Q : L i), (radial i Q).1 = (Q.1 - M) / (‖Q.1 - M‖ : ℂ)) ∧
    (∀ i, ContinuousOn (fun Q : ℂ ↦ ‖Q - M‖) (L i) ∧
      ∀ Q ∈ L i, 0 < ‖Q - M‖) ∧
    (∀ i Q, Q ∈ L i → Q ≠ D i → Q ≠ P → openSegment ℝ M Q ⊆ B i) ∧
    (∀ i, closure (B i) = ⋃ Q ∈ L i, segment ℝ M Q) ∧
    (∀ i, frontier (B i) = segment ℝ M (D i) ∪ segment ℝ M P ∪ L i) ∧
    (∀ i, L i ∩ c ⊆ Set.range (m i) ∧ IsClosed (L i ∩ c)) ∧
    (∀ i, (gaps i).Countable ∧
      (L i \ c = ⋃ g ∈ gaps i, openSegment ℝ (m i g.1) (m i g.2)) ∧
      (gaps i).Pairwise (fun g h ↦ Disjoint (Set.Ioo g.1 g.2) (Set.Ioo h.1 h.2)) ∧
      ∀ g ∈ gaps i,
        m i g.1 ≠ m i g.2 ∧
        openSegment ℝ (m i g.1) (m i g.2) ⊆ βhalf i ∧
        ∀ x ∈ openSegment ℝ (m i g.1) (m i g.2),
          connectedComponentIn (L i \ c) x =
            openSegment ℝ (m i g.1) (m i g.2)) ∧
    IsOpen Bstar ∧ IsConnected Bstar ∧ Bstar ⊆ β ∧
    frontier Bstar = segment ℝ D1 D2 ∪ (L false ∪ L true) ∧
    closure Bstar = ⋃ Q ∈ L false ∪ L true, segment ℝ M Q ∧
    (∀ x ∈ closure Bstar, x ≠ M →
      ∃! z : ↥(L false ∪ L true) × ℝ,
        0 < z.2 ∧ z.2 ≤ 1 ∧ x = (1 - z.2) • M + z.2 • z.1.1) := by
  intro c M P D m Δ hPerpendicular hFirstContact hRayEnters hHalfComponent hHalfFrontier hHalfNear
    caseI K L B angular gaps Bstar
  have hRayAvoids : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (D1 + D2) / 2 + t • (μ τ - (D1 + D2) / 2) ∉ Set.range σ := by
    intro t ht
    exact hFirstContact t ht
  rcases hRayEnters with ⟨ε, hεpos, hεle, hεray⟩
  have hRayTailSubset :
      {z : ℂ | ∃ t : ℝ, 0 < t ∧ t < ε ∧
        z = (D1 + D2) / 2 + t • (μ τ - (D1 + D2) / 2)} ⊆ β :=
    halfSectorConvexFront_ray_tail_subset D1 D2 (μ τ) β ε hεpos hεle hεray
  have hRayTailAvoids :
      Disjoint
        {z : ℂ | ∃ t : ℝ, 0 < t ∧ t < ε ∧
          z = (D1 + D2) / 2 + t • (μ τ - (D1 + D2) / 2)}
        (Set.range σ) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht0, htε, rfl⟩ hz
    exact hRayAvoids t ⟨ht0, lt_of_lt_of_le htε hεle⟩ hz
  have hRayTailNonempty :
      ({z : ℂ | ∃ t : ℝ, 0 < t ∧ t < ε ∧
        z = (D1 + D2) / 2 + t • (μ τ - (D1 + D2) / 2)}).Nonempty := by
    refine ⟨(D1 + D2) / 2 + (ε / 2) • (μ τ - (D1 + D2) / 2), ?_⟩
    refine ⟨ε / 2, half_pos hεpos, ?_, rfl⟩
    linarith
  have hβNonempty : β.Nonempty := by
    rcases hRayTailNonempty with ⟨z, hz⟩
    exact ⟨z, hRayTailSubset hz⟩
  have hPneD1 : μ τ ≠ D1 := by
    intro h
    have hτeq : τ = (0 : unitInterval) := hμInjective (by simpa using h)
    exact (ne_of_gt hτ.1) hτeq
  have hPneD2 : μ τ ≠ D2 := by
    intro h
    have hτeq : τ = (1 : unitInterval) := hμInjective (by simpa using h)
    exact (ne_of_lt hτ.2) hτeq
  have hMc : M ∉ Set.range σ := by
    have hMa : M ∈ a := hChord ⟨1/2, 1/2, by norm_num, by norm_num,
      by norm_num, by simp [M, Algebra.smul_def]; ring⟩
    rcases haComponent with ⟨z, hz, heq⟩
    rw [heq] at hMa
    exact connectedComponentIn_subset _ _ hMa
  have hPM : μ τ ≠ M := fun h ↦ hMc (h ▸ hμCurve ⟨τ, rfl⟩)
  have hDneM : ∀ i : Bool, (if i then D2 else D1) ≠ M := by
    intro i h
    apply hDistinct
    dsimp [M] at h
    cases i <;> simp only [Bool.false_eq_true, ite_false, ite_true] at h
    · linear_combination 2 * h
    · linear_combination -2 * h
  have hMbase : ∀ i : Bool, M ∉ segment ℝ (if i then D2 else D1) (μ τ) := by
    intro i
    apply halfSector_perpendicular_base_notMem M _ _ (hDneM i) hPM
    dsimp [M] at *
    cases i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · simp only [Complex.add_re, Complex.add_im,
        Complex.div_re, Complex.div_im] at *
      norm_num at *
      nlinarith [hPerpendicular]
    · simp only [Complex.add_re, Complex.add_im,
        Complex.div_re, Complex.div_im] at *
      norm_num at *
      nlinarith [hPerpendicular]
  have hmCurve : ∀ i : Bool,
      Set.range (if i then (fun t ↦ μ.subpath 1 τ t) else (fun t ↦ μ.subpath 0 τ t)) ⊆
        Set.range σ := by
    intro i
    cases i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals
      rw [Path.range_subpath]
      exact Set.Subset.trans (Set.image_subset_range _ _) hμCurve
  have hHullApex : ∀ i : Bool,
      M ∉ convexHull ℝ
        ((Set.range (if i then (fun t ↦ μ.subpath 1 τ t) else (fun t ↦ μ.subpath 0 τ t)) ∩
          convexHull ℝ {M, μ τ, if i then D2 else D1}) ∪
          segment ℝ (if i then D2 else D1) (μ τ)) := by
    intro i
    exact halfSector_hull_apex_notMem M (μ τ) _ _ (fun h ↦ hMc (hmCurve i h)) (hMbase i)
  have hVisibleRadial : ∀ i : Bool,
      Set.InjOn (fun Q : ℂ ↦ (Q-M) / (‖Q-M‖ : ℂ))
        {Q | Q ∈ convexHull ℝ
          ((Set.range (if i then (fun t ↦ μ.subpath 1 τ t) else (fun t ↦ μ.subpath 0 τ t)) ∩
            convexHull ℝ {M, μ τ, if i then D2 else D1}) ∪
            segment ℝ (if i then D2 else D1) (μ τ)) ∧
          IsVisible ℝ (convexHull ℝ
            ((Set.range (if i then (fun t ↦ μ.subpath 1 τ t) else (fun t ↦ μ.subpath 0 τ t)) ∩
              convexHull ℝ {M, μ τ, if i then D2 else D1}) ∪
              segment ℝ (if i then D2 else D1) (μ τ))) M Q} := by
    intro i
    exact halfSector_visible_radial_injOn M _ (hHullApex i)
  have hBaseHull : ∀ i : Bool, segment ℝ (if i then D2 else D1) (μ τ) ⊆ K i := by
    intro i
    exact Set.Subset.trans Set.subset_union_right (subset_convexHull ℝ _)
  have hHullTriangle : ∀ i : Bool, K i ⊆ convexHull ℝ {M, μ τ, if i then D2 else D1} := by
    intro i
    apply convexHull_min _ (convex_convexHull ℝ _)
    refine union_subset inter_subset_right ?_
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp [D])) (subset_convexHull ℝ _ (by simp [P]))
  have hHullCompact : ∀ i : Bool, IsCompact (K i) := by
    intro i
    apply isCompact_convexHull_finiteDimensional
    apply IsCompact.union _ (halfSector_segment_compact_connected _ _).1
    have htriangle : IsCompact (convexHull ℝ {M, μ τ, if i then D2 else D1}) :=
      (Set.toFinite _).isCompact_convexHull ℝ
    apply IsCompact.inter_right _ htriangle.isClosed
    apply isCompact_range
    dsimp [m]
    split_ifs <;> exact (μ.subpath _ _).continuous
  have hHalfPerp : ∀ i : Bool,
      ((if i then D2 else D1)-M).re*(μ τ-M).re +
        ((if i then D2 else D1)-M).im*(μ τ-M).im = 0 := by
    intro i
    dsimp [M] at *
    cases i <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals
      simp only [Complex.add_re, Complex.add_im,
        Complex.div_re, Complex.div_im] at *
      norm_num at *
      nlinarith [hPerpendicular]
  have haOutside : a ⊆ cᶜ := by
    obtain ⟨z,hz,rfl⟩ := haComponent
    exact connectedComponentIn_subset _ _
  have hMaffine : M = (1/2:ℝ) • D1 + (1/2:ℝ) • D2 := by
    simp only [M,Algebra.smul_def]
    push_cast
    ring
  have hCurveAxisD : ∀ i, Set.range (m i) ∩ segment ℝ M (D i) ⊆ {D i} := by
    intro i x hx
    change x = D i
    by_contra hxD
    obtain ⟨r,t,hr,ht,hrt,he⟩ := hx.2
    have hrpos : 0 < r := lt_of_le_of_ne hr (by
      intro hr0
      have ht1 : t=1 := by linarith
      exact hxD (by simpa [← hr0,ht1] using he.symm))
    have hxChord : x ∈ openSegment ℝ D1 D2 := by
      cases i
      · refine ⟨r/2+t,r/2,by linarith,by linarith,by linarith,?_⟩
        change r • M+t • D1=x at he
        rw [hMaffine] at he
        rw [← he]
        module
      · refine ⟨r/2,r/2+t,by linarith,by linarith,by linarith,?_⟩
        change r • M+t • D2=x at he
        rw [hMaffine] at he
        rw [← he]
        module
    exact haOutside (hChord hxChord) (hmCurve i hx.1)
  have hCurveAxisP : ∀ i, Set.range (m i) ∩ segment ℝ M P ⊆ {P} := by
    intro i x hx
    change x=P
    by_contra hxP
    have hxM : x ≠ M := fun he ↦ hMc (he ▸ hmCurve i hx.1)
    have hxopen : x ∈ openSegment ℝ M P := by
      have hseg := hx.2
      rw [← insert_endpoints_openSegment] at hseg
      rcases hseg with he | he | ho
      · exact (hxM he).elim
      · exact (hxP he).elim
      · exact ho
    rw [openSegment_eq_image_lineMap] at hxopen
    obtain ⟨t,ht,he⟩ := hxopen
    apply hFirstContact t ht
    have hform : M+t • (P-M)=x := by
      simpa only [AffineMap.lineMap_apply, vsub_eq_sub,vadd_eq_add,add_comm] using he
    rw [hform]
    exact hmCurve i hx.1
  have hEndpointVisible : ∀ i, IsVisible ℝ (K i) M (D i) ∧ IsVisible ℝ (K i) M P := by
    intro i
    exact triangle_hull_endpoints_visible_g2 M (D i) P (hDneM i) hPM (hHalfPerp i)
      (Set.range (m i)) (hCurveAxisD i) (hCurveAxisP i)
  have hVisibleCompact : ∀ i : Bool,
      IsCompact {Q ∈ K i | IsVisible ℝ (K i) M Q} := by
    intro i
    exact halfSector_visible_compact_g2 M _ _ (hDneM i) hPM (hHalfPerp i)
      (K i) (hHullCompact i) (convex_convexHull ℝ _) (hHullApex i)
      (hBaseHull i) (hHullTriangle i)
  have hVisibleImage : ∀ i : Bool,
      (fun Q : ℂ ↦ (Q-M) / (‖Q-M‖ : ℂ)) '' {Q | Q ∈ K i ∧ IsVisible ℝ (K i) M Q} =
        (fun Q : ℂ ↦ (Q-M) / (‖Q-M‖ : ℂ)) '' segment ℝ (if i then D2 else D1) (μ τ) := by
    intro i
    exact halfSector_visible_radial_image M _ _ (K i) (hHullCompact i).isClosed
      (hHullApex i) (hBaseHull i) (hHullTriangle i)
  have hVisibleFrontier : ∀ i : Bool, ∀ Q,
      Q ∈ K i → IsVisible ℝ (K i) M Q → Q ∈ frontier (K i) := by
    intro i Q hQ hQvis
    exact halfSector_visible_mem_frontier (hHullCompact i) (hHullApex i) hQ hQvis
  have hRadial :
      ContinuousOn
        (fun Q : ℂ ↦ (Q - (D1 + D2) / 2) / (‖Q - (D1 + D2) / 2‖ : ℂ))
        {Q : ℂ | Q ≠ (D1 + D2) / 2} := by
    apply Topology.continuousOn_radial_normalization
    intro Q hQ
    exact hQ
  have hTriangleFacts : ∀ i, (interior (Δ i)).Nonempty ∧
      M ∈ closure (interior (Δ i)) ∧
      Disjoint (interior (Δ i)) (segment ℝ M (D i) ∪ segment ℝ M P) := by
    intro i
    exact perpendicular_triangle_interior_g2 M (D i) P (hDneM i) hPM (hHalfPerp i)
  have hShadowApex : ∀ i x, x ∈ interior (Δ i) \ K i →
      M ∈ closure (connectedComponentIn (interior (Δ i) \ K i) x) := by
    intro i x hx
    apply convexHull_apex_mem_closure_component M ({P,D i} : Set ℂ) (K i)
      (insert_nonempty _ _) (convex_convexHull ℝ _)
    · intro z hz
      apply hBaseHull i
      rcases hz with rfl | hz
      · exact right_mem_segment ℝ _ _
      · exact (mem_singleton_iff.mp hz) ▸ left_mem_segment ℝ _ _
    · exact hx
  have hShadowNear : ∀ i ε, 0 < ε →
      ((interior (Δ i) \ K i) ∩ Metric.ball M ε).Nonempty := by
    intro i ε hε
    have hnhds : (K i)ᶜ ∩ Metric.ball M ε ∈ nhds M :=
      Filter.inter_mem ((hHullCompact i).isClosed.isOpen_compl.mem_nhds (hHullApex i))
        (Metric.ball_mem_nhds M hε)
    obtain ⟨x,hx,hxi⟩ := mem_closure_iff_nhds.mp (hTriangleFacts i).2.1 _ hnhds
    exact ⟨x,⟨hxi,hx.1⟩,hx.2⟩
  have hShadowConnected : ∀ i, IsConnected (interior (Δ i) \ K i) := by
    intro i
    apply convexCone_complement_connected_g2 M ({P,D i} : Set ℂ) (K i)
      (insert_nonempty _ _) (convex_convexHull ℝ _) (hHullCompact i).isClosed (hHullApex i)
    · intro z hz
      apply hBaseHull i
      rcases hz with rfl | hz
      · exact right_mem_segment ℝ _ _
      · exact (mem_singleton_iff.mp hz) ▸ left_mem_segment ℝ _ _
    · exact ((hShadowNear i 1 zero_lt_one).mono inter_subset_left)
  have hShadowSubset : ∀ i, interior (Δ i) \ K i ⊆ βhalf i := by
    intro i
    have hnofront : Disjoint (interior (Δ i) \ K i) (frontier (βhalf i)) := by
      apply disjoint_left.mpr
      intro x hx hxf
      rcases hHalfFrontier i hxf with (hxm | hxMD) | hxMP
      · exact hx.2 (subset_convexHull ℝ _ (Or.inl ⟨hxm,interior_subset hx.1⟩))
      · exact (hTriangleFacts i).2.2.le_bot ⟨hx.1,Or.inl hxMD⟩
      · exact (hTriangleFacts i).2.2.le_bot ⟨hx.1,Or.inr hxMP⟩
    have hcover : interior (Δ i) \ K i ⊆ interior (βhalf i) ∪ interior (βhalf i)ᶜ := by
      rw [← compl_frontier_eq_union_interior]
      exact hnofront.subset_compl_right
    obtain hsub | hsub := (hShadowConnected i).isPreconnected.subset_or_subset
      isOpen_interior isOpen_interior
      (disjoint_compl_right.mono interior_subset interior_subset) hcover
    · exact hsub.trans interior_subset
    · obtain ⟨ε,hε,hnear⟩ := hHalfNear i
      obtain ⟨x,hx,hxε⟩ := hShadowNear i ε hε
      exact False.elim (interior_subset (hsub hx) (hnear ⟨hxε,hx.1⟩))
  have hBcaseII : ∀ i, ¬ caseI i → B i = interior (Δ i) \ K i := by
    intro i hi
    dsimp [B]
    rw [ite_eq_right hi]
    exact Set.ext fun x ↦ ⟨fun hx ↦ hx.1,fun hx ↦ ⟨hx,hShadowApex i x hx⟩⟩
  have hBconnected : ∀ i, IsConnected (B i) := by
    intro i
    by_cases hi : caseI i
    · simpa only [B,ite_eq_left hi] using
        ((convex_convexHull ℝ _).interior.isConnected (hTriangleFacts i).1)
    · rw [hBcaseII i hi]
      exact hShadowConnected i
  have hBopen : ∀ i, IsOpen (B i) := by
    intro i
    by_cases hi : caseI i
    · simpa only [B,ite_eq_left hi] using (isOpen_interior : IsOpen (interior (Δ i)))
    · rw [hBcaseII i hi]
      exact isOpen_interior.sdiff (hHullCompact i).isClosed
  have hBsub : ∀ i, B i ⊆ βhalf i := by
    intro i
    by_cases hi : caseI i
    · simpa only [B,ite_eq_left hi] using hi
    · rw [hBcaseII i hi]
      exact hShadowSubset i
  have hLcompact : ∀ i, IsCompact (L i) := by
    intro i
    by_cases hi : caseI i
    · simpa only [L,ite_eq_left hi] using (halfSector_segment_compact_connected (D i) P).1
    · simpa only [L,ite_eq_right hi] using hVisibleCompact i
  have hLendpoints : ∀ i, D i ∈ L i ∧ P ∈ L i := by
    intro i
    by_cases hi : caseI i
    · simpa only [L,ite_eq_left hi] using
        (show D i ∈ segment ℝ (D i) P ∧ P ∈ segment ℝ (D i) P from
          ⟨left_mem_segment ℝ _ _,right_mem_segment ℝ _ _⟩)
    · simp only [L,ite_eq_right hi]
      exact ⟨⟨hBaseHull i (left_mem_segment ℝ _ _),(hEndpointVisible i).1⟩,
        ⟨hBaseHull i (right_mem_segment ℝ _ _),(hEndpointVisible i).2⟩⟩
  have hLavoid : ∀ i Q, Q ∈ L i → Q ≠ M := by
    intro i Q hQ he
    subst Q
    by_cases hi : caseI i
    · exact hMbase i (by simpa only [L,ite_eq_left hi] using hQ)
    · simp only [L,ite_eq_right hi,Set.mem_ofPred_eq] at hQ
      exact hHullApex i hQ.1
  have hBaseRadialInj : ∀ i, Set.InjOn (fun Q : ℂ ↦ (Q-M)/(‖Q-M‖:ℂ))
      (segment ℝ (D i) P) := by
    intro i x hx y hy hxy
    apply halfSector_visible_radial_injOn M (segment ℝ (D i) P) (hMbase i)
      (show x ∈ {Q ∈ segment ℝ (D i) P | IsVisible ℝ (segment ℝ (D i) P) M Q} from
        ⟨hx,triangle_base_visible_g2 M (D i) P (hDneM i) hPM (hHalfPerp i) x hx⟩)
      (show y ∈ {Q ∈ segment ℝ (D i) P | IsVisible ℝ (segment ℝ (D i) P) M Q} from
        ⟨hy,triangle_base_visible_g2 M (D i) P (hDneM i) hPM (hHalfPerp i) y hy⟩) hxy
  have hLradialInj : ∀ i, Set.InjOn (fun Q : ℂ ↦ (Q-M)/(‖Q-M‖:ℂ)) (L i) := by
    intro i
    by_cases hi : caseI i
    · simpa only [L,ite_eq_left hi] using hBaseRadialInj i
    · simpa only [L,ite_eq_right hi] using hVisibleRadial i
  have hLimage : ∀ i, (fun Q : ℂ ↦ (Q-M)/(‖Q-M‖:ℂ)) '' L i = angular i := by
    intro i
    by_cases hi : caseI i
    · simp only [L,ite_eq_left hi,angular]
    · simpa only [L,ite_eq_right hi] using hVisibleImage i
  have hRadialExists : ∃ radial : ∀ i, L i ≃ₜ angular i,
      ∀ i (Q : L i), (radial i Q).1=(Q.1-M)/(‖Q.1-M‖:ℂ) := by
    have hex : ∀ i, ∃ radial : L i ≃ₜ angular i,
        ∀ Q : L i, (radial Q).1=(Q.1-M)/(‖Q.1-M‖:ℂ) := by
      intro i
      obtain ⟨r,hr⟩ := halfSector_radial_homeomorph_of_injective M (L i)
        (hLcompact i) (hLavoid i) (hLradialInj i)
      exact ⟨r.trans (Homeomorph.setCongr (hLimage i)),hr⟩
    choose r hr using hex
    exact ⟨r,hr⟩
  have hAlphaBasic : ∃ α : ∀ i, unitInterval ≃ₜ L i,
      ∀ i, ((α i) 0).1=D i ∧ ((α i) 1).1=P := by
    obtain ⟨radial,hradial⟩ := hRadialExists
    have heach : ∀ i, ∃ α : unitInterval ≃ₜ L i, (α 0).1=D i ∧ (α 1).1=P := by
      intro i
      have hDP : D i ≠ P := by
        cases i
        · exact hPneD1.symm
        · exact hPneD2.symm
      obtain ⟨f,hf,hfr,hf0,hf1⟩ := segment_embedded_arc (D i) P hDP
      let b : unitInterval ≃ₜ segment ℝ (D i) P :=
        hf.toHomeomorph.trans (Homeomorph.setCongr hfr)
      have hb0 : (b 0).1=D i := hf0
      have hb1 : (b 1).1=P := hf1
      obtain ⟨rb,hrb⟩ := halfSector_radial_homeomorph_of_injective M (segment ℝ (D i) P)
        (halfSector_segment_compact_connected (D i) P).1
        (fun Q hQ ↦ ne_of_mem_of_not_mem hQ (hMbase i)) (hBaseRadialInj i)
      let α : unitInterval ≃ₜ L i := b.trans (rb.trans (radial i).symm)
      have hαdir (t : unitInterval) : ((α t).1-M)/(‖(α t).1-M‖:ℂ) =
          ((b t).1-M)/(‖(b t).1-M‖:ℂ) := by
        rw [← hradial i (α t)]
        have he : radial i (α t)=rb (b t) := (radial i).apply_symm_apply _
        rw [he,hrb]
      refine ⟨α,?_,?_⟩
      · apply hLradialInj i (α 0).2 (hLendpoints i).1
        simpa only [hb0] using hαdir 0
      · apply hLradialInj i (α 1).2 (hLendpoints i).2
        simpa only [hb1] using hαdir 1
    choose α hα using heach
    exact ⟨α,hα⟩
  have hLsubK : ∀ i, L i ⊆ K i := by
    intro i Q hQ
    by_cases hi : caseI i
    · exact hBaseHull i (by simpa only [L,ite_eq_left hi] using hQ)
    · simp only [L,ite_eq_right hi,Set.mem_ofPred_eq] at hQ
      exact hQ.1
  have hBint : ∀ i, B i ⊆ interior (Δ i) := by
    intro i x hx
    by_cases hi : caseI i
    · simpa only [B,ite_eq_left hi] using hx
    · rw [hBcaseII i hi] at hx
      exact hx.1
  have hLoffAxes : ∀ i Q, Q ∈ L i → Q ≠ D i → Q ≠ P →
      Q ∉ segment ℝ M (D i) ∪ segment ℝ M P := by
    intro i Q hQ hQD hQP haxis
    have hQM := hLavoid i Q hQ
    rcases haxis with haxis | haxis
    · have ho := mem_openSegment_of_ne_left_right hQM.symm hQD.symm haxis
      rw [openSegment_eq_image_lineMap] at ho
      obtain ⟨t,ht,he⟩ := ho
      exact (isVisible_iff_lineMap (hDneM i).symm).mp (hEndpointVisible i).1 t ht
        (he.symm ▸ hLsubK i hQ)
    · have ho := mem_openSegment_of_ne_left_right hQM.symm hQP.symm haxis
      rw [openSegment_eq_image_lineMap] at ho
      obtain ⟨t,ht,he⟩ := ho
      exact (isVisible_iff_lineMap hPM.symm).mp (hEndpointVisible i).2 t ht
        (he.symm ▸ hLsubK i hQ)
  have hShadowSegments : ∀ i Q, Q ∈ L i → Q ≠ D i → Q ≠ P →
      openSegment ℝ M Q ⊆ B i := by
    intro i Q hQ hQD hQP x hx
    have hxint : x ∈ interior (Δ i) :=
      perpendicular_triangle_radial_interior_g2 M (D i) P (hDneM i) hPM (hHalfPerp i)
        (hHullTriangle i (hLsubK i hQ)) (hLoffAxes i Q hQ hQD hQP) hx
    by_cases hi : caseI i
    · simpa only [B,ite_eq_left hi] using hxint
    · rw [hBcaseII i hi]
      refine ⟨hxint,?_⟩
      have hQvis : IsVisible ℝ (K i) M Q := by
        simp only [L,ite_eq_right hi,Set.mem_ofPred_eq] at hQ
        exact hQ.2
      rw [openSegment_eq_image_lineMap] at hx
      obtain ⟨t,ht,rfl⟩ := hx
      exact (isVisible_iff_lineMap (hLavoid i Q hQ).symm).mp hQvis t ht
  have hLdisjointB : ∀ i, Disjoint (L i) (B i) := by
    intro i
    apply disjoint_left.mpr
    intro Q hQ hQB
    by_cases hi : caseI i
    · have hbase : Q ∈ segment ℝ (D i) P := by simpa only [L,ite_eq_left hi] using hQ
      exact (perpendicular_triangle_base_disjoint_interior_g2 M (D i) P (hDneM i) hPM
        (hHalfPerp i)).le_bot ⟨hBint i hQB,hbase⟩
    · rw [hBcaseII i hi] at hQB
      exact hQB.2 (hLsubK i hQ)
  have hBclosure : ∀ i, closure (B i) = ⋃ Q ∈ L i, segment ℝ M Q := by
    intro i
    by_cases hi : caseI i
    · simp only [B,L,ite_eq_left hi]
      rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior
        (hTriangleFacts i).1]
      rw [((Set.toFinite _).isCompact_convexHull ℝ).isClosed.closure_eq]
      change convexHull ℝ {M,P,D i} = _
      rw [convexHull_insert (insert_nonempty P {D i}),convexHull_pair]
      ext x
      rw [mem_convexJoin,mem_iUnion₂]
      constructor
      · rintro ⟨z,hz,Q,hQ,hx⟩
        have hzM : z=M := mem_singleton_iff.mp hz
        subst z
        exact ⟨Q,by simpa only [segment_symm] using hQ,hx⟩
      · rintro ⟨Q,hQ,hx⟩
        exact ⟨M,rfl,Q,by simpa only [segment_symm] using hQ,hx⟩
    · rw [hBcaseII i hi]
      simp only [L,ite_eq_right hi]
      apply convexCone_visible_sweep_closure_g2 M ({P,D i}:Set ℂ) (K i)
        (insert_nonempty _ _) (convex_convexHull ℝ _) (hHullCompact i).isClosed
      · intro z hz
        apply hBaseHull i
        rcases hz with rfl | hz
        · exact right_mem_segment ℝ _ _
        · exact (mem_singleton_iff.mp hz) ▸ left_mem_segment ℝ _ _
      · exact hHullApex i
      · exact hHullTriangle i
      · exact (hTriangleFacts i).1
      · intro hM
        exact (hTriangleFacts i).2.2.le_bot ⟨hM,Or.inl (left_mem_segment ℝ _ _)⟩
      · exact hVisibleCompact i
  have hBfrontier : ∀ i, frontier (B i) = segment ℝ M (D i) ∪ segment ℝ M P ∪ L i := by
    intro i
    rw [(hBopen i).frontier_eq,hBclosure i]
    apply Subset.antisymm
    · intro x hx
      obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx.1
      by_cases hxM : x=M
      · subst x
        exact Or.inl (Or.inl (left_mem_segment ℝ _ _))
      by_cases hxQeq : x=Q
      · exact Or.inr (hxQeq ▸ hQ)
      by_cases hQD : Q=D i
      · subst Q
        exact Or.inl (Or.inl hxQ)
      by_cases hQP : Q=P
      · subst Q
        exact Or.inl (Or.inr hxQ)
      exact False.elim (hx.2 (hShadowSegments i Q hQ hQD hQP
        (mem_openSegment_of_ne_left_right (Ne.symm hxM) (Ne.symm hxQeq) hxQ)))
    · intro x hx
      refine ⟨?_,?_⟩
      · rcases hx with (hx | hx) | hx
        · exact mem_iUnion₂.mpr ⟨D i,(hLendpoints i).1,hx⟩
        · exact mem_iUnion₂.mpr ⟨P,(hLendpoints i).2,hx⟩
        · exact mem_iUnion₂.mpr ⟨x,hx,right_mem_segment ℝ _ _⟩
      · intro hxB
        rcases hx with hx | hx
        · exact (hTriangleFacts i).2.2.le_bot ⟨hBint i hxB,hx⟩
        · exact (hLdisjointB i).le_bot ⟨hx,hxB⟩
  have hHalfSubset : ∀ i, βhalf i ⊆ β := by
    intro i
    obtain ⟨z,hz,he⟩ := hHalfComponent i
    rw [he]
    exact (connectedComponentIn_subset _ _).trans inter_subset_left
  have hβSubset : β ⊆ a := by
    obtain ⟨z,hz,he⟩ := hβComponent
    rw [he]
    exact (connectedComponentIn_subset _ _).trans inter_subset_left
  have hmEnds : ∀ i, m i 0=D i ∧ m i 1=P := by
    intro i
    cases i <;> simp [m,D,P]
  have hEndsCurve : ∀ i, D i ∈ c ∧ P ∈ c := by
    intro i
    exact ⟨hmCurve i ⟨0,(hmEnds i).1⟩,hmCurve i ⟨1,(hmEnds i).2⟩⟩
  have hLclosureHalf : ∀ i, L i ⊆ closure (βhalf i) := by
    intro i Q hQ
    apply closure_mono (hBsub i)
    rw [hBclosure i]
    exact mem_iUnion₂.mpr ⟨Q,hQ,right_mem_segment ℝ _ _⟩
  have hContact : ∀ i, L i ∩ c ⊆ Set.range (m i) ∧ IsClosed (L i ∩ c) := by
    intro i
    refine ⟨?_,(hLcompact i).isClosed.inter (isCompact_range hσ.continuous).isClosed⟩
    intro Q hQ
    by_cases hQD : Q=D i
    · exact ⟨0,(hmEnds i).1.trans hQD.symm⟩
    by_cases hQP : Q=P
    · exact ⟨1,(hmEnds i).2.trans hQP.symm⟩
    have hQfront : Q ∈ frontier (βhalf i) := by
      refine ⟨hLclosureHalf i hQ.1,?_⟩
      intro hQi
      exact haOutside (hβSubset (hHalfSubset i (interior_subset hQi))) hQ.2
    rcases hHalfFrontier i hQfront with (hm | hMD) | hMP
    · exact hm
    · exact (hLoffAxes i Q hQ.1 hQD hQP (Or.inl hMD)).elim
    · exact (hLoffAxes i Q hQ.1 hQD hQP (Or.inr hMP)).elim
  have hNoncontactHalf : ∀ i, L i \ c ⊆ βhalf i := by
    intro i Q hQ
    by_contra hQnot
    have hQD : Q ≠ D i := fun he ↦ hQ.2 (he.symm ▸ (hEndsCurve i).1)
    have hQP : Q ≠ P := fun he ↦ hQ.2 (he.symm ▸ (hEndsCurve i).2)
    have hQfront : Q ∈ frontier (βhalf i) :=
      ⟨hLclosureHalf i hQ.1,fun hi ↦ hQnot (interior_subset hi)⟩
    rcases hHalfFrontier i hQfront with (hm | hMD) | hMP
    · exact hQ.2 (hmCurve i hm)
    · exact hLoffAxes i Q hQ.1 hQD hQP (Or.inl hMD)
    · exact hLoffAxes i Q hQ.1 hQD hQP (Or.inr hMP)
  have hSeamGeom : IsOpen (interior (Δ false) ∪ interior (Δ true) ∪ openSegment ℝ M P) ∧
      Δ false ∩ Δ true = segment ℝ M P ∧
      Disjoint (interior (Δ false)) (Δ true) ∧ Disjoint (Δ false) (interior (Δ true)) := by
    apply two_triangle_seam_geometry_g2 M D1 D2 P (hDneM true) hPM
    · dsimp [M]
      ring
    · exact hHalfPerp true
  let J : Bool → Set ℂ := fun i ↦ if caseI i then segment ℝ (D i) P else K i
  have hJcompact : ∀ i, IsCompact (J i) := by
    intro i
    by_cases hi : caseI i
    · simpa only [J,ite_eq_left hi] using (halfSector_segment_compact_connected (D i) P).1
    · simpa only [J,ite_eq_right hi] using hHullCompact i
  have hJtriangle : ∀ i, J i ⊆ Δ i := by
    intro i
    by_cases hi : caseI i
    · simp only [J,ite_eq_left hi]
      exact (hBaseHull i).trans (hHullTriangle i)
    · simpa only [J,ite_eq_right hi] using hHullTriangle i
  have hBJ : ∀ i, B i = interior (Δ i) \ J i := by
    intro i
    by_cases hi : caseI i
    · simp only [B,J,ite_eq_left hi]
      apply Subset.antisymm
      · intro x hx
        exact ⟨hx,fun hb ↦ (perpendicular_triangle_base_disjoint_interior_g2 M (D i) P
          (hDneM i) hPM (hHalfPerp i)).le_bot ⟨hx,hb⟩⟩
      · exact inter_subset_left
    · simpa only [J,ite_eq_right hi] using hBcaseII i hi
  have hJseam : ∀ i, Disjoint (J i) (openSegment ℝ M P) := by
    intro i
    have hPvisible : IsVisible ℝ (J i) M P := by
      by_cases hi : caseI i
      · simp only [J,ite_eq_left hi]
        exact triangle_base_visible_g2 M (D i) P (hDneM i) hPM (hHalfPerp i) P
          (right_mem_segment ℝ _ _)
      · simpa only [J,ite_eq_right hi] using (hEndpointVisible i).2
    apply disjoint_left.mpr
    intro x hx hxs
    rw [openSegment_eq_image_lineMap] at hxs
    obtain ⟨t,ht,rfl⟩ := hxs
    exact (isVisible_iff_lineMap hPM.symm).mp hPvisible t ht hx
  have hStarDifference : Bstar =
      (interior (Δ false) ∪ interior (Δ true) ∪ openSegment ℝ M P) \ (J false ∪ J true) := by
    apply Subset.antisymm
    · rintro x ((hx | hx) | hx)
      · have hxb := hx
        rw [hBJ false] at hx
        refine ⟨Or.inl (Or.inl hx.1),?_⟩
        rintro (hj | hj)
        · exact hx.2 hj
        · exact hSeamGeom.2.2.1.le_bot ⟨hx.1,hJtriangle true hj⟩
      · rw [hBJ true] at hx
        refine ⟨Or.inl (Or.inr hx.1),?_⟩
        rintro (hj | hj)
        · exact hSeamGeom.2.2.2.le_bot ⟨hJtriangle false hj,hx.1⟩
        · exact hx.2 hj
      · refine ⟨Or.inr hx,?_⟩
        rintro (hj | hj)
        · exact (hJseam false).le_bot ⟨hj,hx⟩
        · exact (hJseam true).le_bot ⟨hj,hx⟩
    · rintro x ⟨((hx | hx) | hx),hj⟩
      · left;left
        rw [hBJ false]
        exact ⟨hx,fun h ↦ hj (Or.inl h)⟩
      · left;right
        rw [hBJ true]
        exact ⟨hx,fun h ↦ hj (Or.inr h)⟩
      · exact Or.inr hx
  have hStarOpen : IsOpen Bstar := by
    rw [hStarDifference]
    exact hSeamGeom.1.sdiff ((hJcompact false).isClosed.union (hJcompact true).isClosed)
  have hSeamClosure : ∀ i, openSegment ℝ M P ⊆ closure (B i) := by
    intro i x hx
    rw [hBclosure i]
    exact mem_iUnion₂.mpr ⟨P,(hLendpoints i).2,openSegment_subset_segment ℝ _ _ hx⟩
  have hStarConnected : IsConnected Bstar := by
    have hc : ∀ i, IsConnected (B i ∪ openSegment ℝ M P) := by
      intro i
      exact (hBconnected i).subset_closure subset_union_left
        (union_subset subset_closure (hSeamClosure i))
    have hne : ((B false ∪ openSegment ℝ M P) ∩ (B true ∪ openSegment ℝ M P)).Nonempty := by
      refine ⟨(1/2:ℝ) • M+(1/2:ℝ) • P,Or.inr ?_,Or.inr ?_⟩
      all_goals exact ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
    have hu := IsConnected.union hne (hc false) (hc true)
    have he : (B false ∪ openSegment ℝ M P) ∪ (B true ∪ openSegment ℝ M P) = Bstar := by
      ext x
      constructor
      · rintro ((hx | hx) | (hx | hx))
        · exact Or.inl (Or.inl hx)
        · exact Or.inr hx
        · exact Or.inl (Or.inr hx)
        · exact Or.inr hx
      · rintro ((hx | hx) | hx)
        · exact Or.inl (Or.inl hx)
        · exact Or.inr (Or.inl hx)
        · exact Or.inl (Or.inr hx)
    exact he ▸ hu
  have hStarClosureUnion : closure Bstar = closure (B false) ∪ closure (B true) := by
    apply Subset.antisymm
    · apply closure_minimal _ (isClosed_closure.union isClosed_closure)
      rintro x ((hx | hx) | hx)
      · exact Or.inl (subset_closure hx)
      · exact Or.inr (subset_closure hx)
      · exact Or.inl (hSeamClosure false hx)
    · exact union_subset
        (closure_mono (fun _ hx ↦ Or.inl (Or.inl hx)))
        (closure_mono (fun _ hx ↦ Or.inl (Or.inr hx)))
  have hStarClosure : closure Bstar = ⋃ Q ∈ L false ∪ L true, segment ℝ M Q := by
    rw [hStarClosureUnion,hBclosure false,hBclosure true]
    apply Subset.antisymm
    · rintro x (hx | hx)
      · obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨Q,Or.inl hQ,hxQ⟩
      · obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
        exact mem_iUnion₂.mpr ⟨Q,Or.inr hQ,hxQ⟩
    · intro x hx
      obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
      rcases hQ with hQ | hQ
      · exact Or.inl (mem_iUnion₂.mpr ⟨Q,hQ,hxQ⟩)
      · exact Or.inr (mem_iUnion₂.mpr ⟨Q,hQ,hxQ⟩)
  have hChordDecompose : segment ℝ D1 D2 = segment ℝ M D1 ∪ segment ℝ M D2 := by
    have hMline : AffineMap.lineMap D1 D2 (1/2:ℝ)=M := by
      rw [AffineMap.lineMap_apply_module,hMaffine]
      module
    have hMseg : M ∈ segment ℝ D1 D2 := hMline ▸ lineMap_mem_segment (𝕜 := ℝ) D1 D2 (by norm_num)
    apply Subset.antisymm
    · intro x hx
      rw [segment_eq_image_lineMap] at hx
      obtain ⟨t,ht,rfl⟩ := hx
      by_cases htHalf : t ≤ (1/2:ℝ)
      · left
        have hh := (Wbtw.of_le_of_le ht.1 htHalf).map (AffineMap.lineMap D1 D2)
        have hh' : Wbtw ℝ D1 (AffineMap.lineMap D1 D2 t) M := by
          simpa only [AffineMap.lineMap_apply_zero,hMline] using hh
        exact hh'.symm.mem_segment
      · right
        have hh := (Wbtw.of_le_of_le (le_of_not_ge htHalf) ht.2).map (AffineMap.lineMap D1 D2)
        have hh' : Wbtw ℝ M (AffineMap.lineMap D1 D2 t) D2 := by
          simpa only [AffineMap.lineMap_apply_one,hMline] using hh
        exact hh'.mem_segment
    · exact union_subset
        ((convex_segment D1 D2).segment_subset hMseg (left_mem_segment ℝ _ _))
        ((convex_segment D1 D2).segment_subset hMseg (right_mem_segment ℝ _ _))
  have hSeamAvoidsAxes : ∀ i, Disjoint (openSegment ℝ M P) (segment ℝ M (D i)) := by
    intro i
    apply disjoint_left.mpr
    intro x hx hxa
    have he : x=M := (perpendicular_triangle_axes_intersection_g2 M (D i) P
      (hDneM i) hPM (hHalfPerp i)).subset ⟨hxa,openSegment_subset_segment ℝ _ _ hx⟩
    exact hPM.symm (left_mem_openSegment_iff.mp (he ▸ hx))
  have hSeamSubsetβ : openSegment ℝ M P ⊆ β := by
    let z : ℂ := M+(ε/2) • (P-M)
    have hzβ : z ∈ β := hεray (ε/2) ⟨by linarith,by linarith⟩
    have hzOpen : z ∈ openSegment ℝ M P := by
      have hz := lineMap_mem_openSegment ℝ M P (show ε/2 ∈ Ioo (0:ℝ) 1 from
        ⟨by linarith,by linarith⟩)
      simpa only [z,AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,add_comm] using hz
    have hAvoid : openSegment ℝ M P ⊆ cᶜ := by
      intro x hx
      rw [openSegment_eq_image_lineMap] at hx
      obtain ⟨t,ht,rfl⟩ := hx
      simpa only [AffineMap.lineMap_apply,vsub_eq_sub,vadd_eq_add,add_comm,Set.mem_compl_iff] using hFirstContact t ht
    have hca : connectedComponentIn cᶜ z=a := by
      have hza := hβSubset hzβ
      obtain ⟨w,hw,he⟩ := haComponent
      rw [he] at hza ⊢
      exact (connectedComponentIn_eq hza).symm
    have hsuba : openSegment ℝ M P ⊆ a := by
      rw [← hca]
      exact (convex_openSegment M P).isPreconnected.subset_connectedComponentIn hzOpen hAvoid
    have hsubcut : openSegment ℝ M P ⊆ a \ openSegment ℝ D1 D2 := by
      intro x hx
      refine ⟨hsuba hx,?_⟩
      intro hxc
      have hclosed := openSegment_subset_segment ℝ D1 D2 hxc
      rw [hChordDecompose] at hclosed
      rcases hclosed with hleft | hright
      · exact (hSeamAvoidsAxes false).le_bot ⟨hx,hleft⟩
      · exact (hSeamAvoidsAxes true).le_bot ⟨hx,hright⟩
    have hcb : connectedComponentIn (a \ openSegment ℝ D1 D2) z=β := by
      obtain ⟨w,hw,he⟩ := hβComponent
      rw [he] at hzβ ⊢
      exact (connectedComponentIn_eq hzβ).symm
    rw [← hcb]
    exact (convex_openSegment M P).isPreconnected.subset_connectedComponentIn hzOpen hsubcut
  have hStarSubsetβ : Bstar ⊆ β := by
    rintro x ((hx | hx) | hx)
    · exact hHalfSubset false (hBsub false hx)
    · exact hHalfSubset true (hBsub true hx)
    · exact hSeamSubsetβ hx
  have hChordAvoidβ : Disjoint (segment ℝ D1 D2) β := by
    apply disjoint_left.mpr
    intro x hx hxβ
    have hβcut : β ⊆ a \ openSegment ℝ D1 D2 := by
      obtain ⟨z,hz,he⟩ := hβComponent
      rw [he]
      exact connectedComponentIn_subset _ _
    rw [← insert_endpoints_openSegment] at hx
    rcases hx with he | he | ho
    · exact haOutside (hβSubset hxβ) (he.symm ▸ hμCurve ⟨0,μ.source⟩)
    · exact haOutside (hβSubset hxβ) (he.symm ▸ hμCurve ⟨1,μ.target⟩)
    · exact (hβcut hxβ).2 ho
  have hLseam : ∀ i, Disjoint (L i) (openSegment ℝ M P) := by
    intro i
    apply disjoint_left.mpr
    intro x hx hxs
    rw [openSegment_eq_image_lineMap] at hxs
    obtain ⟨t,ht,rfl⟩ := hxs
    exact (isVisible_iff_lineMap hPM.symm).mp (hEndpointVisible i).2 t ht (hLsubK i hx)
  have hOuterAvoid : Disjoint (segment ℝ D1 D2 ∪ (L false ∪ L true)) Bstar := by
    apply disjoint_left.mpr
    intro x hx hxStar
    rcases hx with hx | hx | hx
    · exact hChordAvoidβ.le_bot ⟨hx,hStarSubsetβ hxStar⟩
    · rcases hxStar with (hb | hb) | hs
      · exact (hLdisjointB false).le_bot ⟨hx,hb⟩
      · exact hSeamGeom.2.2.2.le_bot ⟨hHullTriangle false (hLsubK false hx),hBint true hb⟩
      · exact (hLseam false).le_bot ⟨hx,hs⟩
    · rcases hxStar with (hb | hb) | hs
      · exact hSeamGeom.2.2.1.le_bot ⟨hBint false hb,hHullTriangle true (hLsubK true hx)⟩
      · exact (hLdisjointB true).le_bot ⟨hx,hb⟩
      · exact (hLseam true).le_bot ⟨hx,hs⟩
  have hStarFrontier : frontier Bstar = segment ℝ D1 D2 ∪ (L false ∪ L true) := by
    rw [hStarOpen.frontier_eq]
    apply Subset.antisymm
    · intro x hx
      have hxcl := hx.1
      rw [hStarClosureUnion,closure_eq_self_union_frontier (B false),
        closure_eq_self_union_frontier (B true),hBfrontier false,hBfrontier true] at hxcl
      have hseam (hs : x ∈ segment ℝ M P) : x ∈ segment ℝ D1 D2 ∪ (L false ∪ L true) := by
        by_cases hxM : x=M
        · left
          rw [hChordDecompose]
          exact Or.inl (hxM.symm ▸ left_mem_segment ℝ M D1)
        by_cases hxP : x=P
        · exact Or.inr (Or.inl (hxP.symm ▸ (hLendpoints false).2))
        exact False.elim (hx.2 (Or.inr (mem_openSegment_of_ne_left_right
          (Ne.symm hxM) (Ne.symm hxP) hs)))
      rcases hxcl with (hb | ((ha | hs) | hl)) | (hb | ((ha | hs) | hl))
      · exact False.elim (hx.2 (Or.inl (Or.inl hb)))
      · left;rw [hChordDecompose];exact Or.inl ha
      · exact hseam hs
      · exact Or.inr (Or.inl hl)
      · exact False.elim (hx.2 (Or.inl (Or.inr hb)))
      · left;rw [hChordDecompose];exact Or.inr ha
      · exact hseam hs
      · exact Or.inr (Or.inr hl)
    · intro x hx
      refine ⟨?_,fun hb ↦ hOuterAvoid.le_bot ⟨hx,hb⟩⟩
      rw [hStarClosure]
      rcases hx with hc | hl
      · rw [hChordDecompose] at hc
        rcases hc with hc | hc
        · exact mem_iUnion₂.mpr ⟨D1,Or.inl (hLendpoints false).1,hc⟩
        · exact mem_iUnion₂.mpr ⟨D2,Or.inr (hLendpoints true).1,hc⟩
      · exact mem_iUnion₂.mpr ⟨x,hl,right_mem_segment ℝ _ _⟩
  have hSameDirectionSegment : ∀ x y : ℂ, x ≠ M → y ≠ M →
      (x-M)/(‖x-M‖:ℂ)=(y-M)/(‖y-M‖:ℂ) → ‖x-M‖ ≤ ‖y-M‖ → x ∈ segment ℝ M y := by
    intro x y hx hy he hle
    have hs : SameRay ℝ (x-M) (y-M) :=
      (sameRay_iff_inv_norm_smul_eq_of_ne (sub_ne_zero.mpr hx) (sub_ne_zero.mpr hy)).mpr (by
        simpa [Algebra.smul_def,div_eq_mul_inv,mul_comm] using he)
    obtain ⟨r,hr,hscale⟩ := hs.exists_nonneg_right (sub_ne_zero.mpr hy)
    have hnorm : ‖x-M‖=r*‖y-M‖ := by rw [hscale,norm_smul,Real.norm_of_nonneg hr]
    have hny : 0 < ‖y-M‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    have hr1 : r ≤ 1 := by nlinarith [hle,hnorm]
    refine ⟨1-r,r,sub_nonneg.mpr hr1,hr,by ring,?_⟩
    calc
      (1-r) • M+r • y = M+r • (y-M) := by module
      _ = x := by rw [← hscale]; abel
  have hFrontSeamEq : ∀ i Q, Q ∈ L i → Q ∈ segment ℝ M P → Q=P := by
    intro i Q hQ hQs
    by_contra hQP
    have ho := mem_openSegment_of_ne_left_right (hLavoid i Q hQ).symm (Ne.symm hQP) hQs
    exact (hLseam i).le_bot ⟨hQ,ho⟩
  have hCrossDirection : ∀ x ∈ L false, ∀ y ∈ L true,
      (x-M)/(‖x-M‖:ℂ)=(y-M)/(‖y-M‖:ℂ) → x=y := by
    intro x hx y hy he
    rcases le_total ‖x-M‖ ‖y-M‖ with hle | hle
    · have hxSeg := hSameDirectionSegment x y (hLavoid false x hx) (hLavoid true y hy) he hle
      have hxOther : x ∈ Δ true := (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (hHullTriangle true (hLsubK true hy)) hxSeg
      have hxBoth : x ∈ Δ false ∩ Δ true := ⟨hHullTriangle false (hLsubK false hx),hxOther⟩
      rw [hSeamGeom.2.1] at hxBoth
      have hxP := hFrontSeamEq false x hx hxBoth
      have hyP : y=P := hLradialInj true hy (hLendpoints true).2 (by simpa only [hxP] using he.symm)
      exact hxP.trans hyP.symm
    · have hySeg := hSameDirectionSegment y x (hLavoid true y hy) (hLavoid false x hx) he.symm hle
      have hyOther : y ∈ Δ false := (convex_convexHull ℝ _).segment_subset
        (subset_convexHull ℝ _ (by simp)) (hHullTriangle false (hLsubK false hx)) hySeg
      have hyBoth : y ∈ Δ false ∩ Δ true := ⟨hyOther,hHullTriangle true (hLsubK true hy)⟩
      rw [hSeamGeom.2.1] at hyBoth
      have hyP := hFrontSeamEq true y hy hyBoth
      have hxP : x=P := hLradialInj false hx (hLendpoints false).2 (by simpa only [hyP] using he)
      exact hxP.trans hyP.symm
  have hUnionRadial : Set.InjOn (fun Q : ℂ ↦ (Q-M)/(‖Q-M‖:ℂ)) (L false ∪ L true) := by
    intro x hx y hy he
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hLradialInj false hx hy he
    · exact hCrossDirection x hx y hy he
    · exact (hCrossDirection y hy x hx he.symm).symm
    · exact hLradialInj true hx hy he
  have hUnionAvoid : ∀ Q ∈ L false ∪ L true, Q ≠ M := by
    rintro Q (hQ | hQ)
    · exact hLavoid false Q hQ
    · exact hLavoid true Q hQ
  have hStarUnique : ∀ x ∈ closure Bstar, x ≠ M →
      ∃! z : ↥(L false ∪ L true) × ℝ,
        0 < z.2 ∧ z.2 ≤ 1 ∧ x=(1-z.2) • M+z.2 • z.1.1 := by
    intro x hx hxM
    rw [hStarClosure] at hx
    obtain ⟨Q,hQ,hxQ⟩ := mem_iUnion₂.mp hx
    rw [segment_eq_image] at hxQ
    obtain ⟨t,ht,he⟩ := hxQ
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (by
      intro ht0
      apply hxM
      simpa only [← ht0,sub_zero,one_smul,zero_smul,add_zero] using he.symm)
    refine ⟨(⟨Q,hQ⟩,t),⟨htpos,ht.2,he.symm⟩,?_⟩
    intro z hz
    have huniq := halfSector_radial_sweep_unique M (L false ∪ L true) hUnionAvoid hUnionRadial
      z.1.2 hQ hz.1 htpos (hz.2.2.symm.trans he.symm)
    exact Prod.ext (Subtype.ext huniq.1) huniq.2
  have hNorm : ∀ i, ContinuousOn (fun Q : ℂ ↦ ‖Q-M‖) (L i) ∧
      ∀ Q ∈ L i, 0 < ‖Q-M‖ := by
    intro i
    exact ⟨(continuous_id.sub continuous_const).norm.continuousOn,
      fun Q hQ ↦ norm_pos_iff.mpr (sub_ne_zero.mpr (hLavoid i Q hQ))⟩
  have hHullInterior : ∀ i, ¬caseI i → (interior (K i)).Nonempty := by
    intro i hi
    change ¬ interior (Δ i) ⊆ βhalf i at hi
    obtain ⟨x,hxi,hxβ⟩ := Set.not_subset.mp hi
    have hxK : x ∈ K i := by
      by_contra hn
      exact hxβ (hShadowSubset i ⟨hxi,hn⟩)
    apply convex_triangle_interior_nonempty_of_base (convex_convexHull ℝ _)
      (hBaseHull i (left_mem_segment ℝ _ _)) (hBaseHull i (right_mem_segment ℝ _ _)) hxK
    have he : ({M,D i,P} : Set ℂ)={M,P,D i} := by
      ext z; simp only [mem_insert_iff,mem_singleton_iff]; tauto
    rw [he]
    exact hxi
  have hContactFace : ∀ i Q, Q ∈ L i \ c →
      ∃ U V : ℂ, U ∈ L i ∩ c ∧ V ∈ L i ∩ c ∧
        Q ∈ openSegment ℝ U V ∧ segment ℝ U V ⊆ L i := by
    intro i Q hQ
    by_cases hi : caseI i
    · have hL : L i=segment ℝ (D i) P := ite_eq_left hi
      refine ⟨D i,P,⟨(hLendpoints i).1,(hEndsCurve i).1⟩,
        ⟨(hLendpoints i).2,(hEndsCurve i).2⟩,?_,?_⟩
      · apply mem_openSegment_of_ne_left_right
          (show D i ≠ Q from fun he ↦ hQ.2 (he ▸ (hEndsCurve i).1))
          (show P ≠ Q from fun he ↦ hQ.2 (he ▸ (hEndsCurve i).2))
        exact hL ▸ hQ.1
      · exact hL.symm ▸ Subset.rfl
    · have hL : L i={z | z ∈ K i ∧ IsVisible ℝ (K i) M z} := ite_eq_right hi
      have hqv := hL ▸ hQ.1
      have hA : D i ∈ Set.range (m i) ∩ Δ i :=
        ⟨⟨0,(hmEnds i).1⟩,subset_convexHull ℝ _ (by simp)⟩
      have hP : P ∈ Set.range (m i) ∩ Δ i :=
        ⟨⟨1,(hmEnds i).2⟩,subset_convexHull ℝ _ (by simp)⟩
      obtain ⟨U,V,hU,hV,hQseg,hseg⟩ := triangle_visible_contact_face_g2
        (Set.range (m i) ∩ Δ i) M (D i) P hA hP (hHullCompact i) (hHullInterior i hi)
        (by
          have he : ({M,D i,P} : Set ℂ)={M,P,D i} := by
            ext z; simp only [mem_insert_iff,mem_singleton_iff]; tauto
          rw [he]
          exact hHullTriangle i)
        (hHullApex i) (hEndpointVisible i).1 (hEndpointVisible i).2 hqv.1 hqv.2
        (fun hc ↦ hQ.2 (hmCurve i hc.1))
      have hs : segment ℝ U V ⊆ L i := by simpa only [hL] using hseg
      exact ⟨U,V,⟨hs (left_mem_segment ℝ U V),hmCurve i hU.1⟩,
        ⟨hs (right_mem_segment ℝ U V),hmCurve i hV.1⟩,hQseg,hs⟩
  have hmCont : ∀ i, Continuous (m i) := by
    intro i
    cases i
    · exact (μ.subpath 0 τ).continuous
    · exact (μ.subpath 1 τ).continuous
  have hmInj : ∀ i, Function.Injective (m i) := by
    intro i
    cases i
    · exact path_subpath_injective_g2 μ hμInjective hτ.1.ne
    · exact path_subpath_injective_g2 μ hμInjective hτ.2.ne'
  have hOpposite : ∀ i, D (!i) ∉ Set.range (m i) := by
    intro i
    cases i
    · change D2 ∉ Set.range (μ.subpath 0 τ)
      rw [Path.range_subpath_of_le μ 0 τ hτ.1.le]
      rintro ⟨t,ht,he⟩
      have ht1 : t=1 := hμInjective (he.trans μ.target.symm)
      exact (not_le_of_gt hτ.2) (ht1 ▸ ht.2)
    · change D1 ∉ Set.range (μ.subpath 1 τ)
      rw [Path.range_subpath_of_ge μ 1 τ hτ.2.le]
      rintro ⟨t,ht,he⟩
      have ht0 : t=0 := hμInjective (he.trans μ.source.symm)
      exact (not_le_of_gt hτ.1) (ht0 ▸ ht.1)
  have hLstarClosure : ∀ i, L i ⊆ closure Bstar := by
    intro i z hz
    apply frontier_subset_closure
    rw [hStarFrontier]
    exact Or.inr (by cases i; exact Or.inl hz; exact Or.inr hz)
  have hOriginalGapAvoid : ∀ i (p q : unitInterval), p<q →
      segment ℝ (m i p) (m i q) ⊆ L i →
      openSegment ℝ (m i p) (m i q) ⊆ βhalf i →
      Disjoint ((m i) '' Ioo p q) (L i ∩ c) := by
    intro i p q hpq hseg hopen
    let mp : Path (D i) P := ⟨⟨m i,hmCont i⟩,(hmEnds i).1,(hmEnds i).2⟩
    obtain ⟨mark,hmark⟩ := (hEndsCurve (!i)).1
    have hmarkS : σ mark ∈ closure Bstar := by
      rw [hmark]
      exact hLstarClosure (!i) (hLendpoints (!i)).1
    have hcomp : ∃ z ∈ a, connectedComponentIn (Set.range σ)ᶜ z=a := by
      obtain ⟨z,hz,he⟩ := haComponent
      exact ⟨z,he ▸ mem_connectedComponentIn hz,he.symm⟩
    have havoid := chord_shadow_opposite_subpath_g2 σ hσ mp (hmInj i) (hmCurve i)
      p q hpq a Bstar haBounded hcomp (hopen.trans ((hHalfSubset i).trans hβSubset))
      hStarConnected (fun z hz ↦ ⟨hβSubset (hStarSubsetβ hz),by
        intro hzs
        have hzL := hseg (openSegment_subset_segment ℝ _ _ hzs)
        exact hOuterAvoid.le_bot ⟨Or.inr (by cases i; exact Or.inl hzL; exact Or.inr hzL),hz⟩⟩)
      mark (by rw [hmark]; exact hOpposite i) hmarkS
    apply disjoint_left.mpr
    rintro z ⟨r,hr,rfl⟩ hz
    exact havoid r hr (hLstarClosure i hz.1)
  obtain ⟨α,hαEnds⟩ := hAlphaBasic
  have hFrontGap : ∀ i (l r : unitInterval), l<r →
      Disjoint ((fun t ↦ (α i t).1) '' Ioo l r) (L i ∩ c) →
      openSegment ℝ (α i l).1 (α i r).1 ⊆ L i \ c ∧
      segment ℝ (α i l).1 (α i r).1 ⊆ L i := by
    intro i l r hlr hd
    have hgap : ∀ t ∈ Ioo l r, (α i t).1 ∉ c := by
      intro t ht hc
      exact disjoint_left.mp hd (mem_image_of_mem _ ht) ⟨(α i t).2,hc⟩
    have he := arc_contact_face_gap_g2 (L i) c (α i) (hContactFace i) l r hlr hgap
    have hopen : openSegment ℝ (α i l).1 (α i r).1 ⊆ L i \ c := by
      rw [← he]
      rintro z ⟨t,ht,rfl⟩
      exact ⟨(α i t).2,hgap t ht⟩
    refine ⟨hopen,?_⟩
    exact segment_subset_closure_openSegment.trans
      (closure_minimal (hopen.trans sdiff_subset) (hLcompact i).isClosed)
  have hαOrder : ∀ i (s t p q : unitInterval),
      (α i s).1=m i p → (α i t).1=m i q → (s ≤ t ↔ p ≤ q) := by
    intro i
    let av : unitInterval → ℂ := fun t ↦ (α i t).1
    have hav : _root_.Topology.IsEmbedding av :=
      ((continuous_subtype_val.comp (α i).continuous).isClosedEmbedding
        (Subtype.val_injective.comp (α i).injective)).isEmbedding
    have hmemb : _root_.Topology.IsEmbedding (m i) := ((hmCont i).isClosedEmbedding (hmInj i)).isEmbedding
    have horder := arc_contact_order_g2 av (m i) hav hmemb (L i ∩ c)
      (hContact i).2 (hContact i).1
      ((hαEnds i).1.trans (hmEnds i).1.symm) ((hαEnds i).2.trans (hmEnds i).2.symm)
      ⟨(α i 0).2,by change (α i 0).1 ∈ c; rw [(hαEnds i).1]; exact (hEndsCurve i).1⟩
      ⟨(α i 1).2,by change (α i 1).1 ∈ c; rw [(hαEnds i).2]; exact (hEndsCurve i).2⟩ ?_
    · intro s t p q hsp htq
      exact horder s t p q ⟨(α i s).2,by change (α i s).1 ∈ c; rw [hsp]; exact hmCurve i ⟨p,rfl⟩⟩
        ⟨(α i t).2,by change (α i t).1 ∈ c; rw [htq]; exact hmCurve i ⟨q,rfl⟩⟩ hsp htq
    · intro l r hlr hl hr hd p q hpl hqr
      obtain ⟨hopen,hclosed⟩ := hFrontGap i l r hlr hd
      change m i p=(α i l).1 at hpl
      change m i q=(α i r).1 at hqr
      rw [← hpl,← hqr] at hopen hclosed
      have hpq : p ≠ q := by
        intro he
        have hh := hpl.symm.trans ((congrArg (m i) he).trans hqr)
        exact hlr.ne ((α i).injective (Subtype.ext hh))
      rcases lt_or_gt_of_ne hpq with hpq | hqp
      · rw [min_eq_left hpq.le,max_eq_right hpq.le]
        exact hOriginalGapAvoid i p q hpq hclosed (hopen.trans (hNoncontactHalf i))
      · rw [min_eq_right hqp.le,max_eq_left hqp.le]
        apply hOriginalGapAvoid i q p hqp
        · simpa only [segment_symm] using hclosed
        · simpa only [openSegment_symm] using hopen.trans (hNoncontactHalf i)
  have hGapFrontParams : ∀ i g, g ∈ gaps i → ∃ l r : unitInterval,
      l<r ∧ (α i l).1=m i g.1 ∧ (α i r).1=m i g.2 ∧
      Disjoint ((fun t ↦ (α i t).1) '' Ioo l r) (L i ∩ c) := by
    intro i g hg
    let l := (α i).symm ⟨m i g.1,hg.2.1.1⟩
    let r := (α i).symm ⟨m i g.2,hg.2.2.1.1⟩
    have hl : (α i l).1=m i g.1 := congrArg Subtype.val ((α i).apply_symm_apply _)
    have hr : (α i r).1=m i g.2 := congrArg Subtype.val ((α i).apply_symm_apply _)
    have hlr : l<r := by
      apply lt_of_not_ge
      intro hrl
      exact hg.1.not_ge ((hαOrder i r l g.2 g.1 hr hl).mp hrl)
    refine ⟨l,r,hlr,hl,hr,?_⟩
    apply disjoint_left.mpr
    rintro z ⟨t,ht,rfl⟩ hc
    obtain ⟨p,hp⟩ := (hContact i).1 hc
    have hgp : g.1<p := by
      apply lt_of_not_ge
      intro hp1
      exact ht.1.not_ge ((hαOrder i t l p g.1 hp.symm hl).mpr hp1)
    have hpg : p<g.2 := by
      apply lt_of_not_ge
      intro h2p
      exact ht.2.not_ge ((hαOrder i r t g.2 p hr hp.symm).mpr h2p)
    exact disjoint_left.mp hg.2.2.2 ⟨p,⟨hgp,hpg⟩,hp⟩ hc
  have hFrontGapOriginal : ∀ i (l r p q : unitInterval), l<r →
      (α i l).1=m i p → (α i r).1=m i q →
      (α i l).1 ∈ c → (α i r).1 ∈ c →
      Disjoint ((fun t ↦ (α i t).1) '' Ioo l r) (L i ∩ c) → (p,q) ∈ gaps i := by
    intro i l r p q hlr hl hr hlc hrc hd
    have hpq : p<q := by
      apply lt_of_not_ge
      intro hqp
      exact hlr.not_ge ((hαOrder i r l q p hr hl).mpr hqp)
    refine ⟨hpq,⟨hl ▸ (α i l).2,hl ▸ hlc⟩,⟨hr ▸ (α i r).2,hr ▸ hrc⟩,?_⟩
    apply disjoint_left.mpr
    rintro z ⟨u,hu,rfl⟩ huc
    let t := (α i).symm ⟨m i u,huc.1⟩
    have ht : (α i t).1=m i u := congrArg Subtype.val ((α i).apply_symm_apply _)
    have hlt : l<t := by
      apply lt_of_not_ge
      intro htl
      exact hu.1.not_ge ((hαOrder i t l u p ht hl).mp htl)
    have htr : t<r := by
      apply lt_of_not_ge
      intro hrt
      exact hu.2.not_ge ((hαOrder i r t q u hr ht).mp hrt)
    exact disjoint_left.mp hd ⟨t,⟨hlt,htr⟩,ht⟩ huc
  have hGapDetails : ∀ i g, g ∈ gaps i →
      m i g.1 ≠ m i g.2 ∧
      openSegment ℝ (m i g.1) (m i g.2) ⊆ L i \ c ∧
      ∀ x ∈ openSegment ℝ (m i g.1) (m i g.2),
        connectedComponentIn (L i \ c) x=openSegment ℝ (m i g.1) (m i g.2) := by
    intro i g hg
    obtain ⟨l,r,hlr,hl,hr,hd⟩ := hGapFrontParams i g hg
    have hopen := (hFrontGap i l r hlr hd).1
    rw [hl,hr] at hopen
    have hgap : ∀ t ∈ Ioo l r, (α i t).1 ∉ c := by
      intro t ht hc
      exact disjoint_left.mp hd (mem_image_of_mem _ ht) ⟨(α i t).2,hc⟩
    have himage := arc_contact_face_gap_g2 (L i) c (α i) (hContactFace i) l r hlr hgap
    rw [hl,hr] at himage
    refine ⟨(hmInj i).ne hg.1.ne,hopen,?_⟩
    intro x hx
    obtain ⟨t,ht,he⟩ := himage.symm ▸ hx
    let av : unitInterval → ℂ := fun u ↦ (α i u).1
    have hav : _root_.Topology.IsEmbedding av :=
      ((continuous_subtype_val.comp (α i).continuous).isClosedEmbedding
        (Subtype.val_injective.comp (α i).injective)).isEmbedding
    have hrange : Set.range av=L i := by
      apply Subset.antisymm
      · rintro z ⟨u,rfl⟩; exact (α i u).2
      · intro z hz
        exact ⟨(α i).symm ⟨z,hz⟩,congrArg Subtype.val ((α i).apply_symm_apply _)⟩
    have hc0 : av l ∈ c := by change (α i l).1 ∈ c; rw [hl]; exact hg.2.1.2
    have hc1 : av r ∈ c := by change (α i r).1 ∈ c; rw [hr]; exact hg.2.2.1.2
    have hd' : Disjoint (av '' Ioo l r) c := by
      apply disjoint_left.mpr
      rintro z ⟨u,hu,rfl⟩ hc
      exact hgap u hu hc
    have hcomp := embedded_arc_gap_component_g2 av hav c hc0 hc1 hd' ht
    change connectedComponentIn (Set.range av \ c) (α i t).1=
      (fun u ↦ (α i u).1) '' Ioo l r at hcomp
    change (α i t).1=x at he
    rw [hrange,he,himage] at hcomp
    exact hcomp
  have hGapUnion : ∀ i, L i \ c = ⋃ g ∈ gaps i, openSegment ℝ (m i g.1) (m i g.2) := by
    intro i
    apply Subset.antisymm
    · intro x hx
      let t := (α i).symm ⟨x,hx.1⟩
      have ht : (α i t).1=x := congrArg Subtype.val ((α i).apply_symm_apply _)
      let F : Set unitInterval := {u | (α i u).1 ∈ c}
      have hF : IsClosed F := (isCompact_range hσ.continuous).isClosed.preimage
        (continuous_subtype_val.comp (α i).continuous)
      have hF0 : (0:unitInterval) ∈ F := by
        change (α i 0).1 ∈ c
        rw [(hαEnds i).1]
        exact (hEndsCurve i).1
      have hF1 : (1:unitInterval) ∈ F := by
        change (α i 1).1 ∈ c
        rw [(hαEnds i).2]
        exact (hEndsCurve i).2
      obtain ⟨l,r,hl,hr,hlt,htr,hdis⟩ := exists_unitInterval_contact_gap_g2 F hF hF0 hF1
        (show t ∉ F from fun hc ↦ hx.2 (ht ▸ hc))
      have hd : Disjoint ((fun u ↦ (α i u).1) '' Ioo l r) (L i ∩ c) := by
        apply disjoint_left.mpr
        rintro z ⟨u,hu,rfl⟩ hc
        exact disjoint_left.mp hdis hu hc.2
      obtain ⟨p,hp⟩ := (hContact i).1 ⟨(α i l).2,hl⟩
      obtain ⟨q,hq⟩ := (hContact i).1 ⟨(α i r).2,hr⟩
      have hg := hFrontGapOriginal i l r p q (hlt.trans htr) hp.symm hq.symm hl hr hd
      apply mem_iUnion₂.mpr
      refine ⟨(p,q),hg,?_⟩
      have he := arc_contact_face_gap_g2 (L i) c (α i) (hContactFace i) l r (hlt.trans htr)
        (fun u hu hc ↦ disjoint_left.mp hdis hu hc)
      rw [← hp,← hq] at he
      exact he ▸ ⟨t,⟨hlt,htr⟩,ht⟩
    · intro x hx
      obtain ⟨g,hg,hxg⟩ := mem_iUnion₂.mp hx
      exact (hGapDetails i g hg).2.1 hxg
  have hGaps : ∀ i, (gaps i).Countable ∧
      (L i \ c = ⋃ g ∈ gaps i, openSegment ℝ (m i g.1) (m i g.2)) ∧
      (gaps i).Pairwise (fun g h ↦ Disjoint (Ioo g.1 g.2) (Ioo h.1 h.2)) ∧
      ∀ g ∈ gaps i, m i g.1 ≠ m i g.2 ∧
        openSegment ℝ (m i g.1) (m i g.2) ⊆ βhalf i ∧
        ∀ x ∈ openSegment ℝ (m i g.1) (m i g.2),
          connectedComponentIn (L i \ c) x=openSegment ℝ (m i g.1) (m i g.2) := by
    intro i
    have hp := contact_parameter_gaps_countable_g2 (m i) (L i ∩ c)
    exact ⟨hp.1,hGapUnion i,hp.2,fun g hg ↦ ⟨(hGapDetails i g hg).1,
      (hGapDetails i g hg).2.1.trans (hNoncontactHalf i),(hGapDetails i g hg).2.2⟩⟩
  refine ⟨fun i ↦ ⟨hLcompact i,(hBconnected i).nonempty,hBopen i,hBsub i⟩,?_,?_⟩
  · intro i hi x hx
    rw [hBcaseII i hi] at hx ⊢
    exact (hShadowConnected i).isPreconnected.connectedComponentIn hx
  exact ⟨⟨α,hαEnds,hαOrder⟩,hRadialExists,hNorm,hShadowSegments,hBclosure,hBfrontier,
    hContact,hGaps,hStarOpen,hStarConnected,hStarSubsetβ,hStarFrontier,hStarClosure,hStarUnique⟩

end HolomorphicAnosov

