import HolomorphicAnosov.Topology.HalfSectorConvexFront
import HolomorphicAnosov.Topology.ConvexTriangleBoundaryVisible
import HolomorphicAnosov.Topology.CompactConvexHullFiniteDimensional
import HolomorphicAnosov.Topology.ConvexHullApexComponentClosure
import HolomorphicAnosov.Topology.ConvexTriangleInteriorBase
import HolomorphicAnosov.Topology.ConvexTriangleBaseVisible

namespace HolomorphicAnosov
open Set
open scoped Classical

/-- A continuous injective map from a compact space into a Hausdorff space
induces a homeomorphism onto its subtype range.  This is the compact-to-
Hausdorff direction-map construction needed once the target affine front has
been shown to meet each normalized ray exactly once. -/
noncomputable def compact_continuous_injective_range_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) :
    X ≃ₜ Set.range f := by
  exact (hf.isClosedEmbedding hinj).toHomeomorph

/--
Normalized directions are injective along a chord whose supporting affine line
does not pass through its center.  Excluding only the segment is insufficient:
an apex outside the segment but on its supporting line gives a constant
normalization.  This is the elementary affine subcase needed in Cairns §4(A):
the target front is made from circle-arc pieces and straight replacement
chords, and a replacement chord can contribute at most one point to each ray
from the target midpoint.  The full target direction proof additionally has
to establish the corresponding assertion on the retained circle arc and the
compatibility at accumulated chord endpoints.

Source: Cairns (1951), §4(A), pp.863--864, where each straight replacement
chord is shown to lie in the selected half-sector and its radial coordinates
are unique.  The present declaration records only that local chord clause;
the affine line-intersection argument is intentionally retained as a named
provider until the target-front construction supplies the required incidence
hypotheses.
-/
theorem cairns_normalized_direction_injective_on_chord
    (N A B : ℂ) (hN : N ∉ affineSpan ℝ ({A, B} : Set ℂ)) :
    Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ))
      (segment ℝ A B) := by
  intro x hx y hy heq
  have hAspan : A ∈ affineSpan ℝ ({A,B} : Set ℂ) := subset_affineSpan ℝ _ (by simp)
  have hBspan : B ∈ affineSpan ℝ ({A,B} : Set ℂ) := subset_affineSpan ℝ _ (by simp)
  have hsegspan : segment ℝ A B ⊆ affineSpan ℝ ({A,B} : Set ℂ) :=
    (affineSpan ℝ ({A,B} : Set ℂ)).convex.segment_subset hAspan hBspan
  have hxspan : x ∈ affineSpan ℝ ({A,B} : Set ℂ) := hsegspan hx
  have hxN : x ≠ N := by intro h; exact hN (h ▸ hxspan)
  have hyspan : y ∈ affineSpan ℝ ({A,B} : Set ℂ) := hsegspan hy
  have hyN : y ≠ N := by intro h; exact hN (h ▸ hyspan)
  have hnx : (‖x-N‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxN))
  have hny : (‖y-N‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyN))
  have hmul : (x-N) * (‖y-N‖ : ℂ) = (y-N) * (‖x-N‖ : ℂ) := by
    apply (div_eq_div_iff hnx hny).mp
    exact heq
  by_cases hxy : x = y
  · exact hxy
  have hratio : (x-N) = ((‖x-N‖ / ‖y-N‖ : ℝ) : ℂ) * (y-N) := by
    calc
      x - N = ((x-N) * (‖y-N‖ : ℂ)) / (‖y-N‖ : ℂ) := by field_simp
      _ = ((y-N) * (‖x-N‖ : ℂ)) / (‖y-N‖ : ℂ) := by rw [hmul]
      _ = ((‖x-N‖ / ‖y-N‖ : ℝ) : ℂ) * (y-N) := by
        push_cast
        field_simp
  have hk : (‖x-N‖ / ‖y-N‖ : ℝ) ≠ 1 := by
    intro hk
    have hxy0 : x - N = y - N := by
      rw [hratio]
      norm_num [hk]
    exact hxy (sub_left_injective hxy0)
  let k : ℝ := ‖x-N‖ / ‖y-N‖
  have hratioK : x - N = (k : ℂ) * (y-N) := by simpa [k] using hratio
  have hkK : k ≠ 1 := by simpa [k] using hk
  have hkC : (1 - (k : ℂ)) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr (Ne.symm hkK)
  have hline : N ∈ affineSpan ℝ ({x, y} : Set ℂ) := by
    rw [← vsub_vadd N y]
    rw [vadd_right_mem_affineSpan_pair]
    refine ⟨(1-k)⁻¹, ?_⟩
    change (1-k)⁻¹ • (x-y) = N-y
    have hxyv : x-y = (k : ℂ) * (y-N) - (y-N) := by
      rw [← hratioK]
      ring
    rw [hxyv]
    rw [Algebra.smul_def]
    push_cast
    field_simp [hkC]
    ring_nf
    rfl
  have hxySub : ({x,y} : Set ℂ) ⊆ affineSpan ℝ ({A,B} : Set ℂ) := by
    intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hxspan
    · exact hyspan
  have hxline : affineSpan ℝ ({x,y} : Set ℂ) ≤ affineSpan ℝ ({A,B} : Set ℂ) :=
    affineSpan_le.2 hxySub
  exact (hN (hxline hline)).elim

private lemma cairns_circle_direction_ordered (N x y : ℂ) (hN : ‖N‖ < 1)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hle : ‖x-N‖ ≤ ‖y-N‖)
    (heq : (x-N)/(‖x-N‖ : ℂ) = (y-N)/(‖y-N‖ : ℂ)) : x = y := by
  have hxN : x ≠ N := by intro h; subst x; linarith
  have hyN : y ≠ N := by intro h; subst y; linarith
  have hnx : 0 < ‖x-N‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxN)
  have hny : 0 < ‖y-N‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyN)
  have hnxC : (‖x-N‖ : ℂ) ≠ 0 := by exact_mod_cast hnx.ne'
  have hnyC : (‖y-N‖ : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
  have hmul := (div_eq_div_iff hnxC hnyC).mp heq
  let k : ℝ := ‖x-N‖ / ‖y-N‖
  have hk0 : 0 ≤ k := (div_pos hnx hny).le
  have hk1 : k ≤ 1 := (div_le_one hny).mpr hle
  have hratio : x-N = (k : ℂ) * (y-N) := by
    dsimp [k]
    calc
      x - N = ((x - N) * (‖y - N‖ : ℂ)) / (‖y - N‖ : ℂ) := by
        exact (eq_div_iff hnyC).2 rfl
      _ = ((y - N) * (‖x - N‖ : ℂ)) / (‖y - N‖ : ℂ) := by rw [hmul]
      _ = ((‖x - N‖ / ‖y - N‖ : ℝ) : ℂ) * (y - N) := by
        simp only [Complex.ofReal_div]
        ring
  have hcomb : x = (1-k) • N + k • y := by
    simp only [Algebra.smul_def]
    push_cast
    linear_combination hratio
  have hbound : 1 ≤ (1-k)*‖N‖ + k := by
    calc
      1 = ‖x‖ := hx.symm
      _ = ‖(1-k) • N + k • y‖ := by rw [← hcomb]
      _ ≤ ‖(1-k) • N‖ + ‖k • y‖ := norm_add_le _ _
      _ = (1-k)*‖N‖ + k := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr hk1), abs_of_nonneg hk0, hy, mul_one]
  have hk : k = 1 := by nlinarith
  simpa [hk] using hcomb

/-- The normalized direction from a point strictly inside the unit disk meets the
unit circle at most once.  This is the retained-circle counterpart to the chord
injectivity provider above, and is the endpoint/ray uniqueness fact used in
Cairns's target-front construction.

Source: Cairns (1951), §4(A), pp.863--864.  Along a retained circular arc,
equal rays from the midpoint have ordered distances.  Writing the closer point
as `(1-k)N+k y`, the strict interior bound `‖N‖<1` and the unit-circle norms
force `k=1`, hence the two points coincide.  The proof below makes that
perspective-coordinate argument explicit over the complex normed plane.
-/
theorem cairns_normalized_direction_injective_on_circle (N : ℂ) (hN : ‖N‖ < 1) :
    Set.InjOn (fun Q : ℂ ↦ (Q-N)/(‖Q-N‖ : ℂ)) {Q : ℂ | ‖Q‖ = 1} := by
  intro x hx y hy heq
  rcases le_total ‖x-N‖ ‖y-N‖ with hle | hle
  · exact cairns_circle_direction_ordered N x y hN hx hy hle heq
  · exact (cairns_circle_direction_ordered N y x hN hy hx hle heq.symm).symm

/-- The midpoint of two distinct unit-circle points lies strictly inside the
unit disk.  Cairns uses this endpoint fact to ensure that the target midpoint
cannot lie on the retained target circle, so normalized directions have
nonzero denominators and the circle provider above applies.  We prove it from
the parallelogram identity for `Complex.normSq`: the positive squared distance
between distinct endpoints subtracts from the sum of their squared norms. -/
theorem cairns_midpoint_norm_lt_one_of_circle_distinct
    (E₁ E₂ : ℂ) (hE₁ : ‖E₁‖ = 1) (hE₂ : ‖E₂‖ = 1) (hE : E₁ ≠ E₂) :
    ‖(E₁ + E₂) / 2‖ < 1 := by
  have hs₁ : Complex.normSq E₁ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hE₁]
    norm_num
  have hs₂ : Complex.normSq E₂ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hE₂]
    norm_num
  have hd : 0 < Complex.normSq (E₁ - E₂) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr hE)
  have hid : Complex.normSq (E₁ + E₂) + Complex.normSq (E₁ - E₂) = 4 := by
    rw [Complex.normSq_add, Complex.normSq_sub]
    nlinarith [hs₁, hs₂]
  have hsum : Complex.normSq (E₁ + E₂) < 4 := by nlinarith [hid, hd]
  have hhalf : Complex.normSq ((E₁ + E₂) / 2) < 1 := by
    rw [Complex.normSq_div]
    norm_num
    nlinarith [hsum]
  rw [Complex.normSq_eq_norm_sq] at hhalf
  nlinarith [Complex.norm_nonneg ((E₁ + E₂) / 2)]

/-- The midpoint normalization has the expected two endpoint directions.  For
distinct endpoints, subtracting their midpoint gives one half of the chord
vector, and norm homogeneity cancels the positive factor one half.  These two
equalities are the endpoint compatibility used when the retained circular arc
is glued to straight chord pieces in the Cairns front.

Source: Cairns (1951), §4(A), pp.863--864, where the endpoint rays are the two
rays through the chord endpoints.  The proof is direct complex affine algebra.
-/
theorem cairns_midpoint_normalized_endpoint_directions (E₁ E₂ : ℂ) (hE : E₁ ≠ E₂) :
    ((E₁ - (E₁ + E₂) / 2) / (‖E₁ - (E₁ + E₂) / 2‖ : ℂ)) =
      ((E₁ - E₂) / (‖E₁ - E₂‖ : ℂ)) ∧
    ((E₂ - (E₁ + E₂) / 2) / (‖E₂ - (E₁ + E₂) / 2‖ : ℂ)) =
      ((E₂ - E₁) / (‖E₂ - E₁‖ : ℂ)) := by
  have h12 : E₁ - E₂ ≠ 0 := sub_ne_zero.mpr hE
  have hn12 : (‖E₁ - E₂‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr h12)
  have h21 : E₂ - E₁ ≠ 0 := sub_ne_zero.mpr hE.symm
  have hn21 : (‖E₂ - E₁‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr h21)
  constructor
  · have heq : E₁ - (E₁ + E₂) / 2 = (1 / 2 : ℝ) • (E₁ - E₂) := by
      simp only [Algebra.smul_def]
      push_cast
      ring
    rw [heq, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    push_cast
    field_simp
    simp [Algebra.smul_def]
    ring

  · have heq : E₂ - (E₁ + E₂) / 2 = (1 / 2 : ℝ) • (E₂ - E₁) := by
      simp only [Algebra.smul_def]
      push_cast
      ring
    rw [heq, norm_smul]
    simp only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    push_cast
    field_simp
    simp [Algebra.smul_def]
    ring

/-- A normalized chord endpoint is on the zero-cross-product boundary of the
selected direction semicircle.  Since `star D * D` is the real squared norm,
its imaginary part vanishes; the same holds for the opposite endpoint ray.
This is the sign compatibility needed when the retained arc and replacement
chords are glued at both endpoint directions.

Source: Cairns (1951), §4(A), pp.863--864. -/
theorem cairns_normalized_chord_direction_cross_im_zero (D : ℂ) (hD : D ≠ 0) :
    (star D * (D / (‖D‖ : ℂ))).im = 0 ∧
      (star D * ((-D) / (‖D‖ : ℂ))).im = 0 := by
  have hn : (‖D‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hD)
  have hstar : star D * D = (Complex.normSq D : ℂ) := by
    change (starRingEnd ℂ D) * D = _
    rw [← Complex.normSq_eq_conj_mul_self]
  have hs : (Complex.normSq D : ℂ) = (‖D‖ : ℂ)^2 := by
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hpos : (star D * (D / (‖D‖ : ℂ))).im = 0 := by
    rw [div_eq_mul_inv, ← mul_assoc, hstar, hs]
    have hscalar : (‖D‖ : ℂ)^2 * (‖D‖ : ℂ)⁻¹ = (‖D‖ : ℂ) := by
      field_simp
    rw [hscalar]
    exact Complex.ofReal_im _
  refine ⟨hpos, ?_⟩
  rw [neg_div, mul_neg, Complex.neg_im]
  exact neg_eq_zero.mpr hpos

/-- Injectivity of a normalized direction map survives gluing two front pieces
when each piece is individually ray-injective and no equal-direction pair
crosses between the pieces.  This is the elementary compatibility lemma used
when Cairns glues retained circular arcs to replacement chords at accumulated
endpoints; endpoint equalities are discharged by the explicit midpoint and
cross-coordinate providers above.

Source: Cairns (1951), §4(A), pp.863--864.  The source's retained front is a
union of arc and chord pieces, with the ray-intersection argument applied on
each piece and at their common endpoints. -/
theorem cairns_normalized_direction_injective_union
    (N : ℂ) (A B : Set ℂ)
    (hA : Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) A)
    (hB : Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) B)
    (hcross : ∀ x ∈ A, ∀ y ∈ B,
      (x - N) / (‖x - N‖ : ℂ) = (y - N) / (‖y - N‖ : ℂ) → x = y) :
    Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) (A ∪ B) := by
  intro x hx y hy heq
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · exact hA hxA hyA heq
  · exact hcross x hxA y hyB heq
  · exact (hcross y hyA x hxB heq.symm).symm
  · exact hB hxB hyB heq

/-- A convenient overlap form of the preceding gluing lemma.  If equal
normalized directions from two pieces are known to occur only at their
overlap, injectivity on one piece already supplies the cross-piece equality.
This is the exact interface needed for retained-arc/chord endpoint gluing.

Source: Cairns (1951), §4(A), pp.863--864: two neighboring front pieces can
share only their prescribed endpoint contacts. -/
theorem cairns_normalized_direction_injective_union_of_cross_mem_inter
    (N : ℂ) (A B : Set ℂ)
    (hA : Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) A)
    (hB : Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) B)
    (hoverlap : ∀ x ∈ A, ∀ y ∈ B,
      (x - N) / (‖x - N‖ : ℂ) = (y - N) / (‖y - N‖ : ℂ) →
      x ∈ A ∩ B ∧ y ∈ A ∩ B) :
    Set.InjOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) (A ∪ B) := by
  apply cairns_normalized_direction_injective_union N A B hA hB
  intro x hx y hy heq
  exact hA (hoverlap x hx y hy heq).1.1 (hoverlap x hx y hy heq).2.1 heq

/-- The normalized direction map is continuous on every set avoiding its
center.  This supplies the continuity half of the compact-front direction
homeomorphism; injectivity and surjectivity are handled by the front geometry.

Source: Cairns (1951), §4(A), pp.863--864, where the radial direction varies
continuously along each center-free front piece. -/
theorem cairns_normalized_direction_continuousOn
    (N : ℂ) (S : Set ℂ) (hN : ∀ Q ∈ S, Q ≠ N) :
    ContinuousOn (fun Q : ℂ ↦ (Q - N) / (‖Q - N‖ : ℂ)) S := by
  have hnum : Continuous (fun Q : ℂ ↦ Q - N) := continuous_id.sub continuous_const
  have hden : Continuous (fun Q : ℂ ↦ (‖Q - N‖ : ℂ)) := by fun_prop
  refine hnum.continuousOn.div hden.continuousOn ?_
  intro Q hQ
  exact_mod_cast (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hN Q hQ)))

/-- Equal normalized directions are equivalent to a positive real scaling of
the corresponding vectors from the center.  This converts the final
cross-piece endpoint argument into an affine ray parameter statement.

Source: Cairns (1951), §4(A), pp.863--864. -/
theorem cairns_normalized_direction_eq_iff_pos_smul
    (N x y : ℂ) (hx : x ≠ N) (hy : y ≠ N) :
    (x - N) / (‖x - N‖ : ℂ) = (y - N) / (‖y - N‖ : ℂ) ↔
      ∃ k : ℝ, 0 < k ∧ x - N = (k : ℂ) * (y - N) := by
  have hnx : 0 < ‖x-N‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hny : 0 < ‖y-N‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
  have hnxC : (‖x-N‖ : ℂ) ≠ 0 := by exact_mod_cast hnx.ne'
  have hnyC : (‖y-N‖ : ℂ) ≠ 0 := by exact_mod_cast hny.ne'
  constructor
  · intro heq
    refine ⟨‖x-N‖ / ‖y-N‖, div_pos hnx hny, ?_⟩
    have hmul := (div_eq_div_iff hnxC hnyC).mp heq
    calc
      x - N = ((x - N) * (‖y - N‖ : ℂ)) / (‖y - N‖ : ℂ) := (eq_div_iff hnyC).2 rfl
      _ = ((y - N) * (‖x - N‖ : ℂ)) / (‖y - N‖ : ℂ) := by rw [hmul]
      _ = ((‖x - N‖ / ‖y - N‖ : ℝ) : ℂ) * (y - N) := by
        simp only [Complex.ofReal_div]
        ring
  · rintro ⟨k, hk, hxy⟩
    rw [hxy, norm_mul]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    have hnormk : ‖(k : ℂ)‖ = k := by simp [abs_of_pos hk]
    rw [hnormk]
    field_simp
    push_cast
    rfl

/-- A replacement-chord point with the endpoint's normalized direction is that
endpoint, provided the chord's supporting affine line avoids the center.  This
is the endpoint-incidence specialization used when a retained arc is glued to
a straight replacement chord.

Source: Cairns (1951), §4(A), pp.863--864: each selected ray meets a straight
replacement chord at most once, including its endpoint rays. -/
theorem cairns_normalized_direction_endpoint_unique_on_chord
    (N A B Q : ℂ) (hN : N ∉ affineSpan ℝ ({A, B} : Set ℂ))
    (hQ : Q ∈ segment ℝ A B)
    (heq : (Q - N) / (‖Q - N‖ : ℂ) = (A - N) / (‖A - N‖ : ℂ)) :
    Q = A := by
  have hA : A ∈ segment ℝ A B := by
    rw [segment_eq_image]
    exact ⟨0, by simp, by simp⟩
  exact cairns_normalized_direction_injective_on_chord N A B hN hQ hA heq

/-- The analogous endpoint-incidence specialization for the second endpoint of
a replacement chord. -/
theorem cairns_normalized_direction_endpoint_unique_on_chord_right
    (N A B Q : ℂ) (hN : N ∉ affineSpan ℝ ({A, B} : Set ℂ))
    (hQ : Q ∈ segment ℝ A B)
    (heq : (Q - N) / (‖Q - N‖ : ℂ) = (B - N) / (‖B - N‖ : ℂ)) :
    Q = B := by
  have hB : B ∈ segment ℝ A B := by
    rw [segment_eq_image]
    exact ⟨1, by simp, by simp⟩
  exact cairns_normalized_direction_injective_on_chord N A B hN hQ hB heq

/--
For a connected radial shadow, the component selected by any of its points is
the whole shadow.  This is the abstract component step in the Case-II radial
converse: the affine perspective calculation only has to identify the shadow
as a connected set and show that it is the displayed difference.

The result is a direct specialization of the maximality characterization of
`connectedComponentIn` from `Mathlib.Topology.Connected.Basic`; it is kept as
a named lemma so the geometric provider can use it without repeating the
component argument at each half-sector.
-/
lemma connectedComponentIn_eq_of_isConnected
    {s : Set ℂ} (hs : IsConnected s) {x : ℂ} (hx : x ∈ s) :
    connectedComponentIn s x = s := by
  exact hs.isPreconnected.connectedComponentIn hx

/-- The closure of a component of a connected radial shadow is the closure of
the whole shadow.  This is the form used when the apex belongs only to the
closure of the strict radial locus. -/
lemma closure_connectedComponentIn_eq_of_isConnected
    {s : Set ℂ} (hs : IsConnected s) {x : ℂ} (hx : x ∈ s) :
    closure (connectedComponentIn s x) = closure s := by
  rw [connectedComponentIn_eq_of_isConnected hs hx]

/-- A preconnected set meeting both an open set and its complement meets the
frontier of that open set. This is the crossing principle used to force an
interior curve contact in the Case-II affine normalization. -/
lemma exists_inter_frontier_of_isPreconnected
    {s u : Set ℂ}
    (hs : IsPreconnected s) (_hu : IsOpen u)
    (hsu : (s ∩ u).Nonempty) (hsuc : (s ∩ uᶜ).Nonempty) :
    (s ∩ frontier u).Nonempty := by
  have hcover : s ⊆ closure u ∪ closure uᶜ := by
    intro z hz
    by_cases hzu : z ∈ u
    · exact Or.inl (subset_closure hzu)
    · exact Or.inr (subset_closure hzu)
  have hleft : (s ∩ closure u).Nonempty := by
    rcases hsu with ⟨z, hz, hzu⟩
    exact ⟨z, hz, subset_closure hzu⟩
  have hright : (s ∩ closure uᶜ).Nonempty := by
    rcases hsuc with ⟨z, hz, hzu⟩
    exact ⟨z, hz, subset_closure hzu⟩
  have hcross := isPreconnected_closed_iff.mp hs (closure u) (closure uᶜ)
    isClosed_closure isClosed_closure hcover hleft hright
  rw [frontier_eq_closure_inter_closure]
  exact hcross

/-- A point visible from an exterior point through a compact set lies on the
frontier of that set. This is the generic visible-front inclusion used in
Case II before the affine converse identifies every frontier point. -/
lemma cairns_visible_mem_frontier
    {K : Set ℂ} {M Q : ℂ}
    (hKcompact : IsCompact K)
    (hM : M ∉ K)
    (hQ : Q ∈ K)
    (hvis : IsVisible ℝ K M Q) : Q ∈ frontier K := by
  have hnotint : Q ∉ interior K := by
    intro hQi
    have hEq : M = Q := hvis.eq_of_mem_interior hQi
    exact hM (hEq ▸ hQ)
  rw [hKcompact.isClosed.frontier_eq]
  exact ⟨hQ, hnotint⟩

/-- If a preconnected half-triangle meets an open half-sector and also meets
its complement, the stated frontier containment forces an interior generator
contact on the original subarc. -/
lemma exists_frontier_generator_interior
    {Δ U D P : Set ℂ} {m : ℂ → ℂ}
    (hΔpre : IsPreconnected Δ)
    (hUopen : IsOpen U)
    (hWitness : (Δ ∩ U).Nonempty)
    (hCaseII : ¬ Δ ⊆ U)
    (hFront : frontier U ⊆ range m ∪ D ∪ P)
    (hEdges : Disjoint Δ (D ∪ P)) :
    (range m ∩ Δ).Nonempty := by
  obtain ⟨y, hyΔ, hyU⟩ := hWitness
  obtain ⟨x, hxΔ, hxU⟩ := not_subset.mp hCaseII
  obtain ⟨z, hzΔ, hzfront⟩ := exists_inter_frontier_of_isPreconnected
    hΔpre hUopen ⟨y, hyΔ, hyU⟩ ⟨x, hxΔ, hxU⟩
  rcases hFront hzfront with hzm | hzedges
  · rcases hzm with hzm | hzD
    · exact ⟨z, hzm, hzΔ⟩
    · exact (hEdges.le_bot ⟨hzΔ, Or.inl hzD⟩).elim
  · exact (hEdges.le_bot ⟨hzΔ, Or.inr hzedges⟩).elim

/-- In Cairns's genuine Case II half-sector, the complementary hull-boundary
arc is precisely its visible front, and the entire triangle-minus-hull is the
component adjacent to the chord midpoint.

Source: Cairns (1951), §3 Case II and (D,E), printed p.863,
`literature/cairns-jordan-schoenflies-1951.txt`. The original hull, curve subarc,
sector and near-midpoint selection are retained. This is an agent-written
expansion of the geometric identifications implicit in that construction, not
an assertion about arbitrary compact convex sets.

Proof. The existing half-sector theorem gives a compact visible front with
an interval parametrization whose endpoints are the two base vertices. The
hull is compact by compactness of the original subarc and triangle and the
finite-dimensional convex-hull theorem. It is contained in the triangle.
The apex lies outside the hull, since otherwise it would be visible from
itself, contradicting the positive distance on the visible front.

The apex-component lemma puts every point of the triangle interior outside
the hull in the selected radial component. The half-sector theorem puts
that component in the half-sector. Case II therefore supplies a point in
both the hull and the triangle interior. Since the hull contains the base,
`convex_triangle_interior_nonempty_of_base` gives nonempty hull interior:
extend that point past itself along the apex ray, express the extension
as an apex/base combination, and solve for the apex in the hull's affine
span. That span contains a nonempty open triangle interior and is the whole
plane, so the convex interior criterion applies.

The supporting-functional theorem `convex_triangle_boundary_visible` now
puts every hull boundary point off the base in the visible front. The front
is closed, giving the same inclusion for its closure. Conversely every
visible point belongs to the hull boundary. The separation argument in
`convex_triangle_visible_base_endpoint` shows that the front meets the base
only at its endpoints: a separator of the body interior and the visible ray
would be constant on the base and bounded below by that value on the apex,
contradicting its strict upper bound on the body interior. The interior
parameters of the front parametrization thus avoid the base, and their
density puts the entire front in the closure of the boundary minus the base.
Finally the already established apex-component assertion proves the second
equality pointwise. No radial property of the target homeomorphism is used.
-/
theorem cairns_half_sector_caseII_identifications
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
    (hβFrontier : frontier β ⊆ segment ℝ D1 D2 ∪ Set.range μ)
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
    ∀ i, ¬ caseI i →
      closure (frontier (K i) \ segment ℝ (D i) P) =
        {Q | Q ∈ K i ∧ IsVisible ℝ (K i) M Q} ∧
      interior (Δ i) \ K i =
        {x | x ∈ interior (Δ i) \ K i ∧
          M ∈ closure (connectedComponentIn (interior (Δ i) \ K i) x)} := by
  intro c M P D m Δ hPerpendicular hFirstContact hRayEnters hHalfComponent
    hHalfFrontier hHalfNear caseI K i hi
  have hgeometry := halfSectorConvexFront σ hσ a haComponent haBounded D1 D2 hDistinct
    μ hμInjective hμCurve hChord β hβComponent hβFrontier τ hτ βhalf
    hPerpendicular hFirstContact hRayEnters hHalfComponent hHalfFrontier hHalfNear
  have hi' : ¬ interior (convexHull ℝ
      {(D1 + D2) / 2, μ τ, if i then D2 else D1}) ⊆ βhalf i := hi
  let L : Set ℂ := {Q | Q ∈ K i ∧ IsVisible ℝ (K i) M Q}
  have hLcompact : IsCompact L := by
    simpa only [L, K, caseI, Δ, M, P, D, m, ite_eq_right hi'] using (hgeometry.1 i).1
  obtain ⟨α, hαend, hαorder⟩ := hgeometry.2.2.1
  have hDvis : D i ∈ L := by
    have hmem := ((α i) 0).property
    rw [(hαend i).1] at hmem
    simpa only [L, K, caseI, Δ, M, P, D, m, ite_eq_right hi'] using hmem
  have hPvis : P ∈ L := by
    have hmem := ((α i) 1).property
    rw [(hαend i).2] at hmem
    simpa only [L, K, caseI, Δ, M, P, D, m, ite_eq_right hi'] using hmem
  have hMnot : M ∉ K i := by
    intro hM
    have hML : M ∈ L := ⟨hM, IsVisible.rfl⟩
    have hpos := (hgeometry.2.2.2.2.1 i).2 M
      (by simpa only [L, K, caseI, Δ, M, P, D, m, ite_eq_right hi'] using hML)
    simp [M] at hpos
  have hKsub : K i ⊆ Δ i := by
    apply convexHull_min _ (convex_convexHull ℝ _)
    refine union_subset (inter_subset_right) ?_
    exact (convex_convexHull ℝ _).segment_subset
      (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp))
  have hKcompact : IsCompact (K i) := by
    apply isCompact_convexHull_finiteDimensional
    have hbase : IsCompact (segment ℝ (D i) P) := by
      rw [← convexHull_pair]
      exact (Set.toFinite _).isCompact_convexHull ℝ
    apply IsCompact.union _ hbase
    have htriangle : IsCompact (Δ i) := (Set.toFinite _).isCompact_convexHull ℝ
    apply IsCompact.inter_right _ htriangle.isClosed
    apply isCompact_range
    dsimp [m]
    split_ifs <;> exact (μ.subpath _ _).continuous
  have hcomponent (x : ℂ) (hx : x ∈ interior (Δ i) \ K i) :
      M ∈ closure (connectedComponentIn (interior (Δ i) \ K i) x) := by
    apply convexHull_apex_mem_closure_component M ({P, D i} : Set ℂ) (K i)
      (insert_nonempty _ _) (convex_convexHull ℝ _)
    · intro z hz
      apply subset_convexHull ℝ _
      right
      rcases hz with rfl | hz
      · exact right_mem_segment ℝ (D i) P
      · have hzD : z = D i := mem_singleton_iff.mp hz
        exact hzD ▸ left_mem_segment ℝ (D i) P
    · exact hx
  have hdiff : interior (Δ i) \ K i ⊆ βhalf i := by
    intro x hx
    apply (hgeometry.1 i).2.2.2
    simpa only [K, caseI, Δ, M, P, D, m, ite_eq_right hi'] using
      (show x ∈ {x | x ∈ interior (Δ i) \ K i ∧
        M ∈ closure (connectedComponentIn (interior (Δ i) \ K i) x)} from
        ⟨hx, hcomponent x hx⟩)
  have hKint : (interior (K i)).Nonempty := by
    obtain ⟨x, hx, hxβ⟩ := not_subset.mp hi
    have hxK : x ∈ K i := by
      by_contra hn
      exact hxβ (hdiff ⟨hx, hn⟩)
    apply convex_triangle_interior_nonempty_of_base (convex_convexHull ℝ _)
      hDvis.1 hPvis.1 hxK
    simpa only [Δ, Set.pair_comm (D i) P] using hx
  have hbase : ∀ q ∈ L ∩ segment ℝ (D i) P, q = D i ∨ q = P := by
    intro q hq
    apply convex_triangle_visible_base_endpoint (convex_convexHull ℝ _) hKint
      (by simpa only [Δ, Set.pair_comm (D i) P] using hKsub)
      hDvis.1 hPvis.1 hMnot hq.2 hq.1.2
  constructor
  · apply subset_antisymm
    · apply closure_minimal _ hLcompact.isClosed
      intro q hq
      have hqK : q ∈ K i := hKcompact.isClosed.closure_eq ▸ hq.1.1
      refine ⟨hqK, ?_⟩
      apply convex_triangle_boundary_visible (convex_convexHull ℝ _) hKint
        (by simpa only [Δ, Set.pair_comm (D i) P] using hKsub)
        hDvis.1 hPvis.1 hMnot hDvis.2 hPvis.2 hqK hq.1.2 hq.2
    · have hfront : L ⊆ frontier (K i) := by
        intro q hq
        exact cairns_visible_mem_frontier hKcompact hMnot hq.1 hq.2
      let f : unitInterval → ℂ := fun t ↦ ((α i) t).1
      have hf : Continuous f := continuous_subtype_val.comp (α i).continuous
      have hfmem (t : unitInterval) : f t ∈ L := by
        have hmem := ((α i) t).property
        simpa only [L, K, caseI, Δ, M, P, D, m, ite_eq_right hi'] using hmem
      have hf0 : f 0 = D i := (hαend i).1
      have hf1 : f 1 = P := (hαend i).2
      have hfinj : Function.Injective f :=
        Subtype.val_injective.comp (α i).injective
      have himage : f '' Ioo (0 : unitInterval) 1 ⊆
          frontier (K i) \ segment ℝ (D i) P := by
        rintro q ⟨t, ht, rfl⟩
        refine ⟨hfront (hfmem t), ?_⟩
        intro hq
        rcases hbase _ ⟨hfmem t, hq⟩ with he | he
        · have he0 := hfinj (he.trans hf0.symm)
          exact ht.1.ne' he0
        · have he1 := hfinj (he.trans hf1.symm)
          exact ht.2.ne he1
      intro q hq
      have hq' : q ∈ (if caseI i then segment ℝ (D i) P else L) := by
        simpa only [ite_eq_right hi] using hq
      obtain ⟨t, ht⟩ := (α i).surjective
        (⟨q, by simpa only [L, K, caseI, Δ, M, P, D, m] using hq'⟩)
      have hft : f t = q := congrArg Subtype.val ht
      have htclosure : t ∈ closure (Ioo (0 : unitInterval) 1) := by
        rw [closure_Ioo (by exact zero_ne_one)]
        exact ⟨bot_le, le_top⟩
      apply closure_mono himage
      rw [← hft]
      exact hf.continuousWithinAt.mem_closure_image htclosure
  · ext x
    constructor
    · intro hx
      refine ⟨hx, ?_⟩
      exact hcomponent x hx
    · exact fun hx ↦ hx.1

end HolomorphicAnosov
