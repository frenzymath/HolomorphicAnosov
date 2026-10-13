import HolomorphicAnosov.Geometry.IdealTriangleReflectionCenterConjugateG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionInvolutionG6
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
import HolomorphicAnosov.Geometry.IdealTriangleCarrierSideG6
import HolomorphicAnosov.Geometry.IdealTriangleKleinBarycenterG6
import Mathlib.Analysis.Convex.Topology
import HolomorphicAnosov.Geometry.IdealTriangleBoundary
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import HolomorphicAnosov.Geometry.IdealDiskSideReflectionEndpoints
import HolomorphicAnosov.Geometry.IdealTriangleReflectionSideG6
import HolomorphicAnosov.Geometry.IdealTriangleReflectionCarrierG6
import HolomorphicAnosov.Geometry.IdealTriangleNormalizedCarrierG6
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.RCLike.Real

open scoped ComplexConjugate
noncomputable section
namespace HolomorphicAnosov.IdealDiskTriangle

/-- An orthogonal geodesic's only unit-circle points are its two ideal endpoints (Lyubich, Conformal Geometry and Dynamics of Quadratic Polynomials, §2.4.4 p.66).-/
theorem eq_endpoint_of_sideEquation_eq_zero_unit {p q r : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1) (heq : sideEquation p q r = 0) :
    r = p ∨ r = q := by
  have hpu : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
  have hru : r * conj r = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hr]; norm_num
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  obtain ⟨ht, hst⟩ := ideal_reflection_coefficients_g6 hp hq
  have hprod : sideEquation p q r = 0 → (r - p) * (r - q) = 0 := by
    intro heq
    unfold sideEquation at heq
    split_ifs at heq with hs
    · have hq' : q = -p := by linear_combination hs
      have he := Complex.conj_eq_iff_im.mpr heq
      simp only [map_div₀] at he
      have hpc : conj p ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hpn
      have hcross := (div_eq_div_iff hpc hpn).mp he
      rw [hq']
      linear_combination -p*r*hcross - r^2*hpu + p^2*hru
    · let c := orthogonalCenter p q
      have hc : c * (p + q) = 2 * (p * q) := by
        dsimp [c, orthogonalCenter]
        field_simp
      have hsc : (p + q) * conj c = 2 := by
        dsimp [c, orthogonalCenter]
        simp only [map_div₀, map_mul, map_add, map_ofNat]
        have hs' : conj p + conj q ≠ 0 := by
          simpa only [map_add] using (map_ne_zero (starRingEnd ℂ)).mpr hs
        rw [← mul_div_assoc]
        apply (div_eq_iff hs').mpr
        have hstc := congrArg (starRingEnd ℂ) hst
        simp only [map_mul, map_add, Complex.conj_conj] at hstc
        linear_combination 2*hstc
      have hcircle : (r-c)*conj (r-c) - (c*conj c-1) = 0 := by
        rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq]
        exact_mod_cast heq
      simp only [map_sub] at hcircle
      linear_combination -(p+q)*r/2*hcircle - r^2/2*hsc -
        (r*conj r)/2*hc + ((p+q)*r/2-p*q)*hru
  exact (mul_eq_zero.mp (hprod heq)).imp sub_eq_zero.mp sub_eq_zero.mp

/-- A complete geodesic side has empty interior in the complex plane (Lyubich §2.4.4 p.66, explicit diameter and orthogonal-circle cases).-/
theorem interior_sideEquation_zero_eq_empty {p q : ℂ} (hp : ‖p‖ = 1) :
    interior {z | sideEquation p q z = 0} = ∅ := by
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  by_cases hs : p + q = 0
  · have hline : interior {z : ℂ | z.im = 0} = ∅ := by
      change interior (Complex.im ⁻¹' ({0} : Set ℝ)) = ∅
      rw [Complex.interior_preimage_im, interior_singleton, Set.preimage_empty]
    let H := (Homeomorph.mulRight₀ p hpn).symm
    have hpre := H.preimage_interior {z : ℂ | z.im = 0}
    rw [hline, Set.preimage_empty] at hpre
    simpa [H, sideEquation, hs, Homeomorph.mulRight₀_symm_apply, div_eq_mul_inv] using hpre.symm
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz₀ := interior_subset hz
    have hsub : {w | sideEquation p q w = 0} ⊆
        Metric.sphere (orthogonalCenter p q) ‖z - orthogonalCenter p q‖ := by
      intro w hw
      simp only [sideEquation, ite_eq_right hs, Set.mem_ofPred_eq] at hz₀ hw
      rw [Metric.mem_sphere, dist_eq_norm]
      nlinarith [norm_nonneg (w - orthogonalCenter p q), norm_nonneg (z - orthogonalCenter p q)]
    have h := interior_mono hsub hz
    rw [interior_sphere'] at h
    exact h

/-- No point on a side belongs to the interior of its triangle. -/
lemma openSide_not_mem_openTriangle (V : VertexTriple) {p q z : ℂ}
    (hp : p ∈ V.val) (hq : q ∈ V.val) (hpq : p ≠ q)
    (hz : z ∈ openSide p q) : z ∉ openTriangle V.val := by
  classical
  obtain ⟨r, hr, hrpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {p, q}) (t := V.val) (by rw [Finset.card_pair hpq, V.property.1]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrpq
  obtain ⟨hrp, hrq⟩ := hrpq
  have hpunit := V.property.2 p hp
  have hqunit := V.property.2 q hq
  have hrside : sideEquation p q r ≠ 0 := by
    intro heq
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hpunit hqunit
      (V.property.2 r hr) heq).elim hrp hrq
  have hc : ContinuousAt (idealDiskSideReflection p q) z := by
    unfold idealDiskSideReflection
    exact (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt)).div
      (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt))
      (idealDiskSideReflection_denominator_ne_zero_g6 hpunit hqunit hz.1)
  intro hin
  have hn : triangle V.val ∈ nhds z := mem_interior_iff_mem_nhds.mp hin
  have hnr : ∀ᶠ w in nhds z, idealDiskSideReflection p q w ∈ triangle V.val := by
    apply hc.preimage_mem_nhds
    simpa only [idealDiskSideReflection_fixed_openSide hpunit hqunit hpq hz] using hn
  have hnzero : {w | sideEquation p q w = 0} ∈ nhds z := by
    filter_upwards [hn, hnr] with w hw hwr
    have hpos := hw.2 p hp q hq r hr hpq (Ne.symm hrq) hrp
    have hneg := (idealDiskSideReflection_halfspace_sign_g6 hpunit hqunit hpq hw.1).mp
      (hwr.2 p hp q hq r hr hpq (Ne.symm hrq) hrp)
    exact (mul_eq_zero.mp (le_antisymm hneg hpos)).resolve_right hrside
  have hzempty := mem_interior_iff_mem_nhds.mpr hnzero
  rw [interior_sideEquation_zero_eq_empty hpunit] at hzempty
  exact hzempty

/-- Reflecting an ideal triangle across one of its sides changes its vertex triple (Epstein–Petronio reflection pairing, §3.2 p.126).-/
theorem reflectedVertices_ne_self (V : VertexTriple) {p q : ℂ}
    (hp : p ∈ V.val) (hq : q ∈ V.val) (hpq : p ≠ q) :
    reflectedVertices V.val p q ≠ V.val := by
  classical
  obtain ⟨r, hr, hrpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {p, q}) (t := V.val) (by rw [Finset.card_pair hpq, V.property.1]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrpq
  obtain ⟨hrp, hrq⟩ := hrpq
  have hpunit := V.property.2 p hp
  have hqunit := V.property.2 q hq
  have hrunit := V.property.2 r hr
  have hrside : sideEquation p q r ≠ 0 := by
    intro heq
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hpunit hqunit hrunit heq).elim hrp hrq
  intro heq
  have hsubset : triangle V.val ⊆ {z | sideEquation p q z = 0} := by
    intro z hz
    have hrefl := (idealDiskSideReflection_triangle_transport_vertex_g6 V
      hpunit hqunit hpq hp hq z).1 hz
    rw [heq] at hrefl
    have hpos := hz.2 p hp q hq r hr hpq (Ne.symm hrq) hrp
    have hneg := (idealDiskSideReflection_halfspace_sign_g6 hpunit hqunit hpq hz.1).mp
      (hrefl.2 p hp q hq r hr hpq (Ne.symm hrq) hrp)
    exact (mul_eq_zero.mp (le_antisymm hneg hpos)).resolve_right hrside
  obtain ⟨z, hz⟩ := normalized_triangle_carrier_nonempty_g6 V
  have hzempty := interior_mono hsubset hz
  rw [interior_sideEquation_zero_eq_empty hpunit] at hzempty
  exact hzempty

/-- A literal side reflection produces an adjacent distinct physical triangle. -/
lemma reflectionStep_adjacent {A B : VertexTriple}
    (h : reflectionStep A.val B.val) : adjacent A.val B.val := by
  classical
  obtain ⟨p, hp, q, hq, hpq, hB⟩ := h
  have hpunit := A.property.2 p hp
  have hqunit := A.property.2 q hq
  have hfix := idealDiskSideReflection_endpoints hpunit hqunit hpq
  refine ⟨?_, openSide p q, ⟨p, hp, q, hq, hpq, rfl⟩, p, ?_, q, ?_, hpq, rfl⟩
  · intro hAB
    exact reflectedVertices_ne_self A hp hq hpq (hB.symm.trans hAB.symm)
  · rw [hB]
    exact Finset.mem_image.mpr ⟨p, hp, hfix.1⟩
  · rw [hB]
    exact Finset.mem_image.mpr ⟨q, hq, hfix.2⟩

/-- Reachability by side reflections makes the geometric dual graph connected, once the raw orbit is known to preserve vertex triples. -/
lemma dualGraph_connected_of_orbit_preserved (V : VertexTriple)
    (hpreserve : ∀ W : Finset ℂ, reachable V.val W → W.card = 3 ∧ ∀ p ∈ W, ‖p‖ = 1) :
    (dualGraph V).Connected := by
  have hreach (W : Finset ℂ) (hW : reachable V.val W) :
      (dualGraph V).Reachable (initialTriangle V) ⟨⟨W, hpreserve W hW⟩, hW⟩ := by
    induction hW with
    | refl => exact .refl _
    | @tail W U hW hWU ih =>
      exact ih.trans ((show (dualGraph V).Adj
        ⟨⟨W, hpreserve W hW⟩, hW⟩
        ⟨⟨U, hpreserve U (hW.tail hWU)⟩, hW.tail hWU⟩ from
          reflectionStep_adjacent hWU).reachable)
  have : Nonempty (ReachedTriangle V) := ⟨initialTriangle V⟩
  exact SimpleGraph.Connected.mk fun A B ↦
    (hreach A.val.val A.property).symm.trans (hreach B.val.val B.property)

local notation "Kinv" => (fun w : ℂ ↦ w / ((1 + Real.sqrt (1 - ‖w‖ ^ 2) : ℝ) : ℂ))

lemma continuous_side_radial_inv : Continuous Kinv := by
  apply Continuous.div₀ continuous_id
  · fun_prop
  · intro z
    exact_mod_cast (ne_of_gt (by positivity : 0 < 1 + Real.sqrt (1 - ‖z‖ ^ 2)))

lemma kleinInv_radial_identity {w : ℂ} (hw : ‖w‖ < 1) :
    ‖Kinv w‖ < 1 ∧ ∃ t : ℝ, 0 < t ∧
      Kinv w = (t : ℂ) * w ∧ ‖Kinv w‖ ^ 2 + 1 = 2 * t := by
  let a : ℝ := Real.sqrt (1 - ‖w‖ ^ 2)
  have ha : 0 < a := Real.sqrt_pos.2 (by nlinarith [norm_nonneg w])
  have ha2 : a ^ 2 = 1 - ‖w‖ ^ 2 := Real.sq_sqrt (by nlinarith [norm_nonneg w])
  let t : ℝ := (1 + a)⁻¹
  have ht : 0 < t := inv_pos.mpr (by linarith)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    apply inv_le_one_of_one_le₀
    linarith
  have he : Kinv w = (t : ℂ) * w := by
    simp only [t, a, Complex.ofReal_inv, Complex.ofReal_add,
      Complex.ofReal_one, div_eq_mul_inv, mul_comm]
  have hn : ‖Kinv w‖ = t * ‖w‖ := by rw [he]; simp [abs_of_pos ht]
  refine ⟨?_, t, ht, he, ?_⟩
  · rw [hn]
    calc t * ‖w‖ ≤ ‖w‖ := mul_le_of_le_one_left (norm_nonneg w) ht1
         _ < 1 := hw
  · rw [hn]
    dsimp [t]
    field_simp
    nlinarith [ha2]

/-- Inverse Klein coordinates carry the open Euclidean chord between two unit points into their complete geodesic side. -/
lemma kleinInv_openSegment_subset_openSide {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) :
    Kinv '' openSegment ℝ p q ⊆ openSide p q := by
  rintro z ⟨w, hw, rfl⟩
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
  have hw := norm_combo_lt_of_ne hp.le hq.le hpq ha hb hab
  obtain ⟨hz, t, ht, he, hrad⟩ := kleinInv_radial_identity hw
  generalize hzdef : Kinv (a • p + b • q) = z at *
  refine ⟨hz, ?_⟩
  by_cases hs : p + q = 0
  · have hq' : q = -p := by linear_combination hs
    have hpn : p ≠ 0 := by intro h; simp [h] at hp
    simp only [sideEquation, ite_eq_left hs]
    rw [he, hq']
    simp only [Complex.real_smul, mul_neg]
    have hf : (t : ℂ) * ((a : ℂ) * p - (b : ℂ) * p) / p = (t * (a - b) : ℝ) := by
      push_cast
      field_simp
    convert congrArg Complex.im hf using 1
  · let c := orthogonalCenter p q
    have hc := idealTriangle_center_conjugate_g6 hp hq hs
    have hpc : (p * conj c).re = 1 := by
      have hpu : p * conj p = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
      have hqu : q * conj q = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; norm_num
      have hpqn : p + q ≠ 0 := hs
      have hcc : c * (p + q) = 2 * p * q := by
        dsimp [c, orthogonalCenter]; field_simp
      have hsum : p * conj c + conj p * c = 2 := by
        apply mul_right_cancel₀ hpqn
        linear_combination p * hc + conj p * hcc + 2*q*hpu
      have hre := congrArg Complex.re hsum
      norm_num [Complex.add_re, Complex.mul_re, Complex.conj_re,
        Complex.conj_im] at hre ⊢
      linarith
    have hqc : (q * conj c).re = 1 := by
      have hre := congrArg Complex.re hc
      norm_num [add_mul, Complex.add_re] at hre
      norm_num [c, Complex.mul_re] at hpc ⊢
      linarith
    have hre : ((a • p + b • q) * conj c).re = 1 := by
      simp only [add_mul, Complex.add_re, Complex.real_smul, mul_assoc,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      simp only [Complex.mul_re] at hpc hqc
      nlinarith
    have hzre : (z * conj c).re = t := by
      rw [he, mul_assoc]
      simpa using congrArg (t * ·) hre
    simp only [sideEquation, ite_eq_right hs, Complex.sq_norm, Complex.normSq_sub]
    rw [Complex.normSq_eq_norm_sq]
    change (z * conj (orthogonalCenter p q)).re = t at hzre
    rw [hzre]
    linarith


/-- Each ideal endpoint is a limit of points on the corresponding open side. -/
lemma left_mem_closure_openSide {p q : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) : p ∈ closure (openSide p q) := by
  apply closure_mono (kleinInv_openSegment_subset_openSide hp hq hpq)
  apply image_closure_subset_closure_image continuous_side_radial_inv
  refine ⟨p, segment_subset_closure_openSegment (left_mem_segment ℝ p q), ?_⟩
  simp [hp]

/-- The geometric triangle carrier determines its three ideal vertices. -/
theorem triangle_vertexTriple_injective :
    Function.Injective (fun V : VertexTriple ↦ triangle V.val) := by
  classical
  have hsub (A B : VertexTriple) (heq : triangle A.val = triangle B.val) : A.val ⊆ B.val := by
    intro p hp
    obtain ⟨q, hq, hqp⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := {p}) (t := A.val) (by rw [Finset.card_singleton, A.property.1]; norm_num)
    simp only [Finset.mem_singleton] at hqp
    let Z : Set ℂ := ⋃ u : B.val, ⋃ v : B.val, {z | sideEquation u.val v.val z = 0}
    have hclosed : IsClosed Z := by
      apply isClosed_iUnion_of_finite
      intro u
      apply isClosed_iUnion_of_finite
      intro v
      exact isClosed_eq (continuous_sideEquation u.val v.val) continuous_const
    have hside : openSide p q ⊆ Z := by
      intro z hz
      have hAz := openSide_mem_triangle_of_vertexTriple A hp hq (Ne.symm hqp) hz
      have hBz : z ∈ triangle B.val := heq ▸ hAz
      have hnon : z ∉ openTriangle B.val := by
        change z ∉ interior (triangle B.val)
        rw [← heq]
        exact openSide_not_mem_openTriangle A hp hq (Ne.symm hqp) hz
      obtain hz' | ⟨u, hu, v, hv, huv, hzs⟩ := triangle_subset_openTriangle_union_sides B.val hBz
      · exact (hnon hz').elim
      · exact Set.mem_iUnion.mpr ⟨⟨u, hu⟩, Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hzs.2⟩⟩
    have hpZ : p ∈ Z := closure_minimal hside hclosed
      (left_mem_closure_openSide (A.property.2 p hp) (A.property.2 q hq) (Ne.symm hqp))
    obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hpZ
    obtain ⟨v, huv⟩ := Set.mem_iUnion.mp hu
    rcases eq_endpoint_of_sideEquation_eq_zero_unit (B.property.2 u.val u.property)
      (B.property.2 v.val v.property) (A.property.2 p hp) huv with h | h
    · exact h ▸ u.property
    · exact h ▸ v.property
  intro A B heq
  apply Subtype.ext
  exact Finset.Subset.antisymm (hsub A B heq) (hsub B A heq.symm)

lemma openSide_comm (p q : ℂ) : openSide p q = openSide q p := by
  ext z
  simp only [openSide, Set.mem_ofPred_eq, sideEquation]
  by_cases hs : p + q = 0
  · have hs' : q + p = 0 := by simpa [add_comm] using hs
    have hq : q = -p := by linear_combination hs
    simp [hq, div_neg, Complex.neg_im]
  · have hs' : q + p ≠ 0 := by simpa [add_comm] using hs
    simp only [ite_eq_right hs, ite_eq_right hs']
    have hc : orthogonalCenter p q = orthogonalCenter q p := by
      unfold orthogonalCenter
      ring
    rw [hc]

lemma openSide_eq_of_pair_eq {p q r s : ℂ} (hpq : p ≠ q) (hrs : r ≠ s)
    (heq : ({p, q} : Finset ℂ) = {r, s}) : openSide p q = openSide r s := by
  have hp : p = r ∨ p = s := by
    have h : p ∈ ({r,s} : Finset ℂ) := heq ▸ (show p ∈ ({p,q} : Finset ℂ) by simp)
    simpa using h
  have hq : q = r ∨ q = s := by
    have h : q ∈ ({r,s} : Finset ℂ) := heq ▸ (show q ∈ ({p,q} : Finset ℂ) by simp)
    simpa using h
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact (hpq rfl).elim
  · rfl
  · exact openSide_comm _ _
  · exact (hpq rfl).elim

/-- Distinct actual vertex triples have at most one common complete side: the two endpoints of every common side exhaust the intersection of their vertex sets, whose cardinality is at most two. -/
lemma sharedSide_unique {A B : VertexTriple} (hne : A ≠ B) {S T : Set ℂ}
    (hAS : hasSide A.val S) (hBS : hasSide B.val S)
    (hAT : hasSide A.val T) (hBT : hasSide B.val T) : S = T := by
  classical
  have hpair {p q r s : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
      (hs : ‖s‖ = 1) (hpq : p ≠ q) (hrs : r ≠ s)
      (heq : openSide p q = openSide r s) : ({p,q} : Finset ℂ) = {r,s} := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      have hxe : x = p ∨ x = q := by simpa using hx
      have hxunit : ‖x‖ = 1 := hxe.elim (fun h ↦ h ▸ hp) (fun h ↦ h ▸ hq)
      have hxcl : x ∈ closure (openSide p q) := by
        rcases hxe with h | h
        · rw [h]
          exact left_mem_closure_openSide hp hq hpq
        · rw [h, openSide_comm p q]
          exact left_mem_closure_openSide hq hp hpq.symm
      rw [heq] at hxcl
      have hxzero : sideEquation r s x = 0 :=
        closure_minimal (fun _ h ↦ h.2)
          (isClosed_eq (continuous_sideEquation r s) continuous_const) hxcl
      simpa using eq_endpoint_of_sideEquation_eq_zero_unit hr hs hxunit hxzero
    · simp [hpq, hrs]
  obtain ⟨p, hpA, q, hqA, hpq, rfl⟩ := hAS
  obtain ⟨p', hpB, q', hqB, hpq', hS⟩ := hBS
  obtain ⟨r, hrA, s, hsA, hrs, rfl⟩ := hAT
  obtain ⟨r', hrB, s', hsB, hrs', hT⟩ := hBT
  have hPQ := hpair (A.property.2 p hpA) (A.property.2 q hqA)
    (B.property.2 p' hpB) (B.property.2 q' hqB) hpq hpq' hS
  have hRS := hpair (A.property.2 r hrA) (A.property.2 s hsA)
    (B.property.2 r' hrB) (B.property.2 s' hsB) hrs hrs' hT
  have hcard : (A.val ∩ B.val).card ≤ 2 := by
    have hlt : (A.val ∩ B.val).card < A.val.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro hsub
      apply hne
      apply Subtype.ext
      apply Finset.eq_of_subset_of_card_le
      · exact hsub.trans Finset.inter_subset_right
      · rw [A.property.1, B.property.1]
    rw [A.property.1] at hlt
    omega
  have hpqI : ({p,q} : Finset ℂ) = A.val ∩ B.val := by
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.subset_inter
      · simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hpA, hqA]
      · rw [hPQ]
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hpB, hqB]
    · simpa [hpq] using hcard
  have hrsI : ({r,s} : Finset ℂ) = A.val ∩ B.val := by
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.subset_inter
      · simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hrA, hsA]
      · rw [hRS]
        simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hrB, hsB]
    · simpa [hrs] using hcard
  exact openSide_eq_of_pair_eq hpq hrs (hpqI.trans hrsI.symm)

/-- Two complete disk geodesics with one common ideal endpoint and distinct other endpoints are disjoint inside the disk. -/
lemma openSide_disjoint_of_common_endpoint {p q r : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hr : ‖r‖ = 1)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    Disjoint (openSide p q) (openSide p r) := by
  apply Set.disjoint_left.mpr
  intro z hzq hzr
  have hqfix := idealDiskSideReflection_fixed_openSide hp hq hpq hzq
  have hrfix := idealDiskSideReflection_fixed_openSide hp hr hpr hzr
  unfold idealDiskSideReflection at hqfix hrfix
  have hqeq := (div_eq_iff (idealDiskSideReflection_denominator_ne_zero_g6 hp hq hzq.1)).mp hqfix
  have hreq := (div_eq_iff (idealDiskSideReflection_denominator_ne_zero_g6 hp hr hzq.1)).mp hrfix
  have hprod : (q-r) * (1 + z * conj z - 2*p*conj z) = 0 := by
    linear_combination hqeq - hreq
  have he : 1 + z * conj z = 2*p*conj z := sub_eq_zero.mp
    ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hqr))
  have he' : ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) = 2*p*conj z := by
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq] using he
  have hn := congrArg norm he'
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    norm_mul, norm_mul, hp, Complex.norm_conj] at hn
  norm_num at hn
  have hzlt := hzq.1
  change ‖z‖ < 1 at hzlt
  nlinarith [sq_nonneg (‖z‖ - 1)]

lemma reflectionStep_preserves_vertexTriple (A : Finset ℂ) (hA : A.card = 3 ∧ ∀ z ∈ A, ‖z‖ = 1)
    {B : Finset ℂ} (hB : reflectionStep A B) : B.card = 3 ∧ ∀ z ∈ B, ‖z‖ = 1 := by
  obtain ⟨p, hpA, q, hqA, hpq, rfl⟩ := hB
  have hp := hA.2 p hpA
  have hq := hA.2 q hqA
  have hsum : ‖p + q‖ < 2 := by
    have hg := ideal_reflection_gap_pos_g6 hp hq hpq
    rw [Complex.normSq_eq_norm_sq] at hg
    nlinarith [norm_nonneg (p + q)]
  have hden {z : ℂ} (hz : ‖z‖ = 1) : 2 - (p + q) * conj z ≠ 0 := by
    intro h
    have heq := congrArg norm (sub_eq_zero.mp h)
    simp only [norm_mul, Complex.norm_conj, hz, mul_one] at heq
    norm_num at heq
    linarith
  have hunit {z : ℂ} (hz : ‖z‖ = 1) : ‖idealDiskSideReflection p q z‖ = 1 := by
    obtain ⟨ht, hst⟩ := ideal_reflection_coefficients_g6 hp hq
    have hd := ideal_reflection_norm_difference_g6 ht hst z
    have hzsq : Complex.normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    rw [hzsq] at hd
    have heq : Complex.normSq ((p + q) - 2 * (p * q) * conj z) =
        Complex.normSq (2 - (p + q) * conj z) := by linarith
    have hrefl : Complex.normSq (idealDiskSideReflection p q z) = 1 := by
      unfold idealDiskSideReflection
      rw [Complex.normSq_div]
      have hdpos := Complex.normSq_pos.mpr (hden hz)
      rw [show p + q - 2 * p * q * conj z = (p + q) - 2 * (p * q) * conj z by ring,
        heq, div_self hdpos.ne']
    rw [Complex.normSq_eq_norm_sq] at hrefl
    nlinarith [norm_nonneg (idealDiskSideReflection p q z)]
  have hinj : Set.InjOn (idealDiskSideReflection p q) (A : Set ℂ) := by
    intro x hx y hy hxy
    have hd₁ := hden (hA.2 x hx)
    have hd₂ := hden (hA.2 y hy)
    unfold idealDiskSideReflection at hxy
    have heq := (div_eq_div_iff hd₁ hd₂).mp hxy
    have hprod : (p - q)^2 * (conj x - conj y) = 0 := by linear_combination heq
    have hc : conj x = conj y := sub_eq_zero.mp
      ((mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 (sub_ne_zero.mpr hpq)))
    simpa only [Complex.conj_conj] using congrArg conj hc
  constructor
  · exact (Finset.card_image_of_injOn hinj).trans hA.1
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    exact hunit (hA.2 w hw)

lemma reachable_preserves_vertexTriple (V : VertexTriple) (W : Finset ℂ)
    (hW : reachable V.val W) : W.card = 3 ∧ ∀ z ∈ W, ‖z‖ = 1 := by
  induction hW with
  | refl => exact V.property
  | @tail W U hW hWU ih => exact reflectionStep_preserves_vertexTriple W ih hWU

lemma sides_eq_or_disjoint (A : VertexTriple) {p q u v : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hu : u ∈ A.val) (hv : v ∈ A.val)
    (hpq : p ≠ q) (huv : u ≠ v) :
    openSide p q = openSide u v ∨ Disjoint (openSide p q) (openSide u v) := by
  classical
  have hshare : p = u ∨ p = v ∨ q = u ∨ q = v := by
    by_contra h
    push Not at h
    have hsub : ({p,q,u,v} : Finset ℂ) ⊆ A.val := by
      simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp,hq,hu,hv⟩
    have hc := Finset.card_le_card hsub
    rw [A.property.1] at hc
    simp [hpq, huv, h.1, h.2.1, h.2.2.1, h.2.2.2] at hc
  have hsame (x y w : ℂ) (hx : x ∈ A.val) (hy : y ∈ A.val) (hw : w ∈ A.val)
      (hxy : x ≠ y) (hxw : x ≠ w) :
      openSide x y = openSide x w ∨ Disjoint (openSide x y) (openSide x w) := by
    by_cases hyw : y = w
    · exact Or.inl (hyw ▸ rfl)
    · exact Or.inr (openSide_disjoint_of_common_endpoint (A.property.2 x hx)
        (A.property.2 y hy) (A.property.2 w hw) hxy hxw hyw)
  rcases hshare with h | h | h | h
  · subst u
    exact hsame p q v hp hq hv hpq huv
  · subst v
    rw [openSide_comm u p]
    exact hsame p q u hp hq hu hpq huv.symm
  · subst u
    rw [openSide_comm p q]
    exact hsame q p v hq hp hv hpq.symm huv
  · subst v
    rw [openSide_comm p q, openSide_comm u q]
    exact hsame q p u hq hp hu hpq.symm huv.symm

/-- A point on a side of a triangle lies on precisely that side among its three physical side sets. -/
lemma hasSide_point_unique (A : VertexTriple) {S T : Set ℂ}
    (hS : hasSide A.val S) (hT : hasSide A.val T) {z : ℂ}
    (hzS : z ∈ S) (hzT : z ∈ T) : S = T := by
  obtain ⟨p,hp,q,hq,hpq,rfl⟩ := hS
  obtain ⟨u,hu,v,hv,huv,rfl⟩ := hT
  rcases sides_eq_or_disjoint A hp hq hu hv hpq huv with h | h
  · exact h
  · exact (Set.disjoint_left.mp h hzS hzT).elim

lemma sideEquation_swap_product (p q z r : ℂ) :
    sideEquation p q z * sideEquation p q r = sideEquation q p z * sideEquation q p r := by
  by_cases hs : p+q = 0
  · have hq : q = -p := by linear_combination hs
    simp [sideEquation, hq, div_neg, Complex.neg_im]
  · have hs' : q+p ≠ 0 := by simpa [add_comm] using hs
    simp only [sideEquation, ite_eq_right hs, ite_eq_right hs']
    have hc : orthogonalCenter p q = orthogonalCenter q p := by
      unfold orthogonalCenter
      ring
    rw [hc]

lemma mem_triangle_three_iff {p q r z : ℂ} (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) :
    z ∈ triangle {p,q,r} ↔ z ∈ disk ∧
      0 ≤ sideEquation p q z * sideEquation p q r ∧
      0 ≤ sideEquation q r z * sideEquation q r p ∧
      0 ≤ sideEquation r p z * sideEquation r p q := by
  classical
  constructor
  · intro hz
    exact ⟨hz.1, hz.2 p (by simp) q (by simp) r (by simp) hpq hqr hrp,
      hz.2 q (by simp) r (by simp) p (by simp) hqr hrp hpq,
      hz.2 r (by simp) p (by simp) q (by simp) hrp hpq hqr⟩
  · rintro ⟨hz,h₁,h₂,h₃⟩
    refine ⟨hz, ?_⟩
    intro a ha b hb c hc hab hbc hca
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
    rcases ha with rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;>
      first | exact (hab rfl).elim | exact (hbc rfl).elim | exact (hca rfl).elim |
        exact h₁ | exact h₂ | exact h₃ |
        (rw [sideEquation_swap_product]; assumption)

/-- The original triangle and its reflection cover a neighborhood of each point on their shared side. -/
lemma triangle_union_reflection_mem_nhds (A : VertexTriple) {p q z : ℂ}
    (hp : p ∈ A.val) (hq : q ∈ A.val) (hpq : p ≠ q) (hz : z ∈ openSide p q) :
    triangle A.val ∪ triangle (reflectedVertices A.val p q) ∈ nhds z := by
  classical
  obtain ⟨r, hr, hrpq⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {p,q}) (t := A.val) (by rw [Finset.card_pair hpq, A.property.1]; norm_num)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hrpq
  obtain ⟨hrp,hrq⟩ := hrpq
  have hA : ({p,q,r} : Finset ℂ) = A.val := by
    apply Finset.eq_of_subset_of_card_le
    · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
      exact ⟨hp,hq,hr⟩
    · rw [A.property.1]
      simp [hpq, Ne.symm hrp, Ne.symm hrq]
  have hpunit := A.property.2 p hp
  have hqunit := A.property.2 q hq
  have hrunit := A.property.2 r hr
  have hzA := openSide_mem_triangle_of_vertexTriple A hp hq hpq hz
  have hzqr : sideEquation q r z ≠ 0 := by
    intro he
    have hd := openSide_disjoint_of_common_endpoint hqunit hpunit hrunit hpq.symm (Ne.symm hrq) (Ne.symm hrp)
    exact Set.disjoint_left.mp hd (openSide_comm p q ▸ hz) ⟨hz.1, he⟩
  have hzrp : sideEquation r p z ≠ 0 := by
    intro he
    have hd := openSide_disjoint_of_common_endpoint hpunit hqunit hrunit hpq (Ne.symm hrp) (Ne.symm hrq)
    exact Set.disjoint_left.mp hd hz (openSide_comm r p ▸ (show z ∈ openSide r p from ⟨hz.1,he⟩))
  have hpqr : sideEquation q r p ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hqunit hrunit hpunit he).elim hpq (Ne.symm hrp)
  have hqrp : sideEquation r p q ≠ 0 := by
    intro he
    exact (eq_endpoint_of_sideEquation_eq_zero_unit hrunit hpunit hqunit he).elim (Ne.symm hrq) hpq.symm
  let U : Set ℂ := {w | w ∈ disk ∧ 0 < sideEquation q r w * sideEquation q r p ∧
      0 < sideEquation r p w * sideEquation r p q}
  have hzU : z ∈ U := by
    refine ⟨hz.1, lt_of_le_of_ne (hzA.2 q hq r hr p hp (Ne.symm hrq) hrp hpq) ?_,
      lt_of_le_of_ne (hzA.2 r hr p hp q hq hrp hpq (Ne.symm hrq)) ?_⟩
    · exact Ne.symm (mul_ne_zero hzqr hpqr)
    · exact Ne.symm (mul_ne_zero hzrp hqrp)
  have hU : IsOpen U := by
    exact (isOpen_lt continuous_norm continuous_const).inter
      ((isOpen_lt continuous_const ((continuous_sideEquation q r).mul_const _)).inter
        (isOpen_lt continuous_const ((continuous_sideEquation r p).mul_const _)))
  have hcont : ContinuousAt (idealDiskSideReflection p q) z := by
    unfold idealDiskSideReflection
    exact (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt)).div
      (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt))
      (idealDiskSideReflection_denominator_ne_zero_g6 hpunit hqunit hz.1)
  have hUr : ∀ᶠ w in nhds z, idealDiskSideReflection p q w ∈ U := by
    apply hcont.preimage_mem_nhds
    rw [idealDiskSideReflection_fixed_openSide hpunit hqunit hpq hz]
    exact hU.mem_nhds hzU
  filter_upwards [hU.mem_nhds hzU, hUr] with w hw hwr
  by_cases hsign : 0 ≤ sideEquation p q w * sideEquation p q r
  · apply Or.inl
    rw [← hA]
    exact (mem_triangle_three_iff hpq (Ne.symm hrq) hrp).mpr ⟨hw.1, hsign, hw.2.1.le, hw.2.2.le⟩
  · apply Or.inr
    have hww := idealDiskSideReflection_involutive_disk_g6 hpunit hqunit hpq w hw.1
    rw [← hww]
    apply (idealDiskSideReflection_triangle_transport_vertex_g6 A hpunit hqunit hpq hp hq
      (idealDiskSideReflection p q w)).1
    rw [← hA]
    apply (mem_triangle_three_iff hpq (Ne.symm hrq) hrp).mpr
    refine ⟨hwr.1, ?_, hwr.2.1.le, hwr.2.2.le⟩
    exact (idealDiskSideReflection_halfspace_sign_g6 hpunit hqunit hpq hw.1).mpr (le_of_not_ge hsign)

/-- The affine chord equation corresponding to the circle or diameter side. -/
def linearSideEquation (p q w : ℂ) : ℝ :=
  if p+q = 0 then (w/p).im else 1-(w*conj (orthogonalCenter p q)).re

lemma sideEquation_inverse_radial {p q w : ℂ} (hw : ‖w‖ < 1) :
    ∃ t : ℝ, 0 < t ∧ sideEquation p q (Kinv w) = t * linearSideEquation p q w := by
  obtain ⟨hz,t,ht,he,hrad⟩ := kleinInv_radial_identity hw
  generalize hzdef : Kinv w = z at *
  by_cases hs : p+q = 0
  · refine ⟨t,ht,?_⟩
    simp only [sideEquation, linearSideEquation, ite_eq_left hs]
    rw [he, mul_div_assoc]
    simp
  · refine ⟨2*t, mul_pos (by norm_num) ht, ?_⟩
    simp only [sideEquation, linearSideEquation, ite_eq_right hs, Complex.sq_norm, Complex.normSq_sub]
    rw [Complex.normSq_eq_norm_sq]
    have hre : (z*conj (orthogonalCenter p q)).re = t*(w*conj (orthogonalCenter p q)).re := by
      rw [he, mul_assoc]
      simp
    rw [hre]
    nlinarith

lemma linearSideEquation_combo (p q x y : ℂ) (a b : ℝ) (hab : a+b=1) :
    linearSideEquation p q (a • x+b • y) =
      a*linearSideEquation p q x+b*linearSideEquation p q y := by
  unfold linearSideEquation
  split_ifs
  · simp only [Complex.real_smul, add_div, mul_div_assoc, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  · simp only [Complex.real_smul, add_mul, mul_assoc, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith

lemma convex_linear_side_cap (p q r : ℂ) :
    Convex ℝ {w : ℂ | ‖w‖ < 1 ∧ linearSideEquation p q w * sideEquation p q r < 0} := by
  intro x hx y hy a b ha hb hab
  constructor
  · have hball := (convex_ball (0:ℂ) 1) (by simpa using hx.1) (by simpa using hy.1) ha hb hab
    simpa using hball
  · rw [linearSideEquation_combo p q x y a b hab]
    have hax := mul_le_mul_of_nonneg_left hx.2.le ha
    have hby := mul_le_mul_of_nonneg_left hy.2.le hb
    rcases ha.eq_or_lt with he | he
    · have ha0 : a=0 := he.symm
      have hb1 : b=1 := by linarith
      simpa [ha0,hb1] using hy.2
    · have hax' := mul_lt_mul_of_pos_left hx.2 he
      nlinarith

end HolomorphicAnosov.IdealDiskTriangle


noncomputable section
open scoped ComplexConjugate
namespace HolomorphicAnosov.IdealDiskTriangle

/-- The explicit distance expression used to reflect points toward a fixed interior point. -/
def diskEnergy (c z : ℂ) : ℝ := ‖z-c‖ ^ 2 / (1-‖z‖ ^ 2)

lemma reflection_energy_numerator_complex {p q c z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) :
    ((p+q)-2*p*q*conj z-c*(2-(p+q)*conj z)) *
        conj ((p+q)-2*p*q*conj z-c*(2-(p+q)*conj z)) -
      (4-(p+q)*conj (p+q))*(z-c)*conj (z-c) =
    ((p+q)*(1+c*conj c)-2*c-2*p*q*conj c) *
      conj ((p+q)*(1+z*conj z)-2*z-2*p*q*conj z) := by
  have hpu : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
  have hqu : q * conj q = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hq]; norm_num
  simp only [map_sub, map_add, map_mul, map_ofNat, map_one, Complex.conj_conj]
  linear_combination
    (4*q*conj q*z*conj z-4*q*conj q*z*conj c-2*q*conj z+2*q*conj c-
      2*conj q*z*conj z*c+2*conj q*z*c*conj c)*hpu +
    (-2*p*conj z+2*p*conj c-2*conj p*z*conj z*c+2*conj p*z*c*conj c+
      4*z*conj z-4*z*conj c)*hqu

lemma scaled_sideEquation_complex {p q : ℂ} (hp : ‖p‖ = 1) (hq : ‖q‖ = 1)
    (hs : p+q ≠ 0) (z : ℂ) :
    (p+q)*(sideEquation p q z : ℂ) =
      (p+q)*(1+z*conj z)-2*z-2*p*q*conj z := by
  let c := orthogonalCenter p q
  have hc : c*(p+q) = 2*p*q := by dsimp [c, orthogonalCenter]; field_simp
  have hsc := idealTriangle_center_conjugate_g6 hp hq hs
  have he : (sideEquation p q z : ℂ) =
      (z-c)*conj (z-c)-(c*conj c-1) := by
    simp only [sideEquation, ite_eq_right hs, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [he]
  simp only [map_sub]
  linear_combination -z*hsc - conj z*hc

lemma reflection_energy_numerator_nonantipodal {p q c z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hs : p+q ≠ 0) :
    ‖((p+q)-2*p*q*conj z)-c*(2-(p+q)*conj z)‖ ^ 2 -
      (4-‖p+q‖ ^ 2)*‖z-c‖ ^ 2 =
        ‖p+q‖ ^ 2 * sideEquation p q c * sideEquation p q z := by
  have h := reflection_energy_numerator_complex (c := c) (z := z) hp hq
  rw [← scaled_sideEquation_complex hp hq hs c,
    ← scaled_sideEquation_complex hp hq hs z] at h
  simp only [map_mul, Complex.conj_ofReal] at h
  have hmul : (p+q)*(sideEquation p q c : ℂ) *
      (conj (p+q)*(sideEquation p q z : ℂ)) =
      ((‖p+q‖ ^ 2 * sideEquation p q c * sideEquation p q z : ℝ) : ℂ) := by
    rw [show (p+q)*(sideEquation p q c : ℂ) *
      (conj (p+q)*(sideEquation p q z : ℂ)) =
      ((p+q)*conj (p+q))*(sideEquation p q c : ℂ)*(sideEquation p q z : ℂ) by ring]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  rw [hmul, Complex.mul_conj, Complex.mul_conj] at h
  rw [mul_assoc (4 - (Complex.normSq (p+q) : ℂ)), Complex.mul_conj] at h
  simp only [Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

lemma reflection_energy_numerator_antipodal {p q c z : ℂ}
    (hp : ‖p‖ = 1) (hs : p+q = 0) :
    ‖((p+q)-2*p*q*conj z)-c*(2-(p+q)*conj z)‖ ^ 2 -
      (4-‖p+q‖ ^ 2)*‖z-c‖ ^ 2 =
        16 * sideEquation p q c * sideEquation p q z := by
  have hq : q = -p := by linear_combination hs
  have hpn : p ≠ 0 := by intro h; simp [h] at hp
  have hpu : p * conj p = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp]; norm_num
  let u := c/p
  let v := z/p
  have hc : c = p*u := by dsimp [u]; field_simp
  have hz : z = p*v := by dsimp [v]; field_simp
  have hnum : ((p+q)-2*p*q*conj z)-c*(2-(p+q)*conj z) =
      2*p*(conj v-u) := by
    rw [hq, hc, hz]
    simp only [map_mul]
    linear_combination 2*p*conj v*hpu
  rw [hnum, hs]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, norm_mul, hp]
  norm_num
  have hdist : ‖z-c‖ = ‖v-u‖ := by
    rw [hz, hc, ← mul_sub, norm_mul, hp, one_mul]
  rw [hdist]
  simp only [sideEquation, ite_eq_left hs]
  change (2 * ‖conj v-u‖) ^ 2 - 4 * ‖v-u‖ ^ 2 = 16*u.im*v.im
  rw [mul_pow, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Exact decrease identity for the hyperbolic distance expression. -/
lemma diskEnergy_reflection_difference {p q c z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ < 1) :
    (diskEnergy c (idealDiskSideReflection p q z) - diskEnergy c z) *
      ((4-‖p+q‖ ^ 2)*(1-‖z‖ ^ 2)) =
    (if p+q = 0 then 16 else ‖p+q‖ ^ 2) * sideEquation p q c * sideEquation p q z := by
  let d := 2-(p+q)*conj z
  let n := (p+q)-2*p*q*conj z
  have hd : d ≠ 0 := idealDiskSideReflection_denominator_ne_zero_g6 hp hq hz
  have hds : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hd)
  have hzpos : 0 < 1-‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hgap : 0 < 4-‖p+q‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq] using ideal_reflection_gap_pos_g6 hp hq hpq
  have hR := idealDiskSideReflection_mem_disk_g6 hp hq hpq hz
  have hRpos : 0 < 1-‖idealDiskSideReflection p q z‖ ^ 2 := by
    nlinarith [norm_nonneg (idealDiskSideReflection p q z)]
  obtain ⟨ht,hst⟩ := ideal_reflection_coefficients_g6 hp hq
  have hdiff := ideal_reflection_norm_difference_g6 ht hst z
  simp only [Complex.normSq_eq_norm_sq] at hdiff
  have hdiff' : ‖d‖ ^ 2 - ‖n‖ ^ 2 = (4-‖p+q‖ ^ 2)*(1-‖z‖ ^ 2) := by
    simpa only [d, n, mul_assoc] using hdiff
  have hquot : idealDiskSideReflection p q z = n/d := rfl
  have hden : (1-‖idealDiskSideReflection p q z‖ ^ 2)*‖d‖ ^ 2 =
      (4-‖p+q‖ ^ 2)*(1-‖z‖ ^ 2) := by
    rw [hquot, norm_div, div_pow]
    field_simp
    nlinarith [hdiff']
  have hdist : ‖idealDiskSideReflection p q z-c‖ ^ 2 * ‖d‖ ^ 2 = ‖n-c*d‖ ^ 2 := by
    rw [hquot, div_sub' hd, mul_comm d c, norm_div, div_pow]
    exact div_mul_cancel₀ _ hds
  have henergy : diskEnergy c (idealDiskSideReflection p q z) *
      ((4-‖p+q‖ ^ 2)*(1-‖z‖ ^ 2)) = ‖n-c*d‖ ^ 2 := by
    rw [← hden]
    unfold diskEnergy
    rw [← mul_assoc, div_mul_cancel₀ _ hRpos.ne']
    exact hdist
  have hbase : diskEnergy c z * ((4-‖p+q‖ ^ 2)*(1-‖z‖ ^ 2)) =
      (4-‖p+q‖ ^ 2)*‖z-c‖ ^ 2 := by
    unfold diskEnergy
    field_simp
  rw [sub_mul, henergy, hbase]
  by_cases hs : p+q = 0
  · simpa only [ite_eq_left hs, n, d] using reflection_energy_numerator_antipodal (c := c) (z := z) hp hs
  · simpa only [ite_eq_right hs, n, d] using reflection_energy_numerator_nonantipodal (c := c) (z := z) hp hq hs

/-- Reflecting across a side strictly decreases the distance expression when the point and center lie in opposite strict half-spaces. -/
lemma diskEnergy_reflection_lt {p q c z : ℂ}
    (hp : ‖p‖ = 1) (hq : ‖q‖ = 1) (hpq : p ≠ q) (hz : ‖z‖ < 1)
    (hopposite : sideEquation p q c * sideEquation p q z < 0) :
    diskEnergy c (idealDiskSideReflection p q z) < diskEnergy c z := by
  have h := diskEnergy_reflection_difference (c := c) hp hq hpq hz
  have hcoef : 0 < (if p+q = 0 then (16:ℝ) else ‖p+q‖ ^ 2) := by
    split_ifs with hs
    · norm_num
    · exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hs)
  have hgap : 0 < 4-‖p+q‖ ^ 2 := by
    simpa only [Complex.normSq_eq_norm_sq] using ideal_reflection_gap_pos_g6 hp hq hpq
  have hzpos : 0 < 1-‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  have hneg : (diskEnergy c (idealDiskSideReflection p q z) - diskEnergy c z) *
      ((4-‖p+q‖ ^ 2)*(1-‖z‖ ^ 2)) < 0 := by
    rw [h, mul_assoc]
    exact mul_neg_of_pos_of_neg hcoef hopposite
  have hdenpos := mul_pos hgap hzpos
  nlinarith

/-- A closed quadratic sublevel is compact and lies strictly inside the disk when its center does. -/
lemma isCompact_diskEnergy_sublevel {c : ℂ} (hc : ‖c‖ < 1) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact {z : ℂ | ‖z‖ ≤ 1 ∧ ‖z-c‖ ^ 2 ≤ R*(1-‖z‖ ^ 2)} ∧
      {z : ℂ | ‖z‖ ≤ 1 ∧ ‖z-c‖ ^ 2 ≤ R*(1-‖z‖ ^ 2)} ⊆ disk := by
  constructor
  · apply (isCompact_closedBall (0:ℂ) 1).of_isClosed_subset
    · exact (isClosed_le continuous_norm continuous_const).inter
        (isClosed_le (show Continuous (fun z : ℂ ↦ ‖z-c‖ ^ 2) by fun_prop)
          (show Continuous (fun z : ℂ ↦ R*(1-‖z‖ ^ 2)) by fun_prop))
    · intro z hz
      simpa using hz.1
  · intro z hz
    change ‖z‖ < 1
    rcases hz.1.lt_or_eq with h | h
    · exact h
    · have heq : z = c := by
        have hs : ‖z-c‖ ^ 2 ≤ 0 := by simpa [h] using hz.2
        have hn : ‖z-c‖ = 0 := by nlinarith [norm_nonneg (z-c)]
        exact sub_eq_zero.mp (norm_eq_zero.mp hn)
      rw [heq] at h
      exact (hc.ne h).elim

lemma continuousOn_diskEnergy (c : ℂ) : ContinuousOn (diskEnergy c) disk := by
  apply ContinuousOn.div₀ (by fun_prop) (by fun_prop)
  intro z hz
  change 1-‖z‖ ^ 2 ≠ 0
  change ‖z‖ < 1 at hz
  nlinarith [norm_nonneg z]

/-- Every nonempty subset of the disk has a minimum-energy point in its relative closure. -/
lemma diskEnergy_minimum_on_closure {c : ℂ} (hc : ‖c‖ < 1)
    {S : Set ℂ} (hS : S.Nonempty) (hSd : S ⊆ disk) :
    ∃ z ∈ closure S, z ∈ disk ∧ ∀ w ∈ closure S, w ∈ disk → diskEnergy c z ≤ diskEnergy c w := by
  obtain ⟨x, hx⟩ := hS
  have hxD := hSd hx
  have hxpos : 0 < 1-‖x‖ ^ 2 := by
    change ‖x‖ < 1 at hxD
    nlinarith [norm_nonneg x]
  let R := diskEnergy c x
  have hR : 0 ≤ R := div_nonneg (sq_nonneg _) hxpos.le
  let K : Set ℂ := {z | ‖z‖ ≤ 1 ∧ ‖z-c‖ ^ 2 ≤ R*(1-‖z‖ ^ 2)}
  obtain ⟨hK, hKd⟩ := isCompact_diskEnergy_sublevel hc hR
  change IsCompact K at hK
  change K ⊆ disk at hKd
  have hxK : x ∈ K := by
    refine ⟨hxD.le, ?_⟩
    dsimp [R, diskEnergy]
    rw [div_mul_cancel₀ _ hxpos.ne']
  have hcomp : IsCompact (K ∩ closure S) := hK.inter_right isClosed_closure
  obtain ⟨z, hz, hmin⟩ := hcomp.exists_isMinOn ⟨x, hxK, subset_closure hx⟩
    ((continuousOn_diskEnergy c).mono (fun _ h ↦ hKd h.1))
  refine ⟨z, hz.2, hKd hz.1, ?_⟩
  intro w hw hwD
  by_cases hwK : w ∈ K
  · exact hmin ⟨hwK, hw⟩
  · have hxbound := hmin ⟨hxK, subset_closure hx⟩
    apply hxbound.trans
    by_contra! hlt
    apply hwK
    refine ⟨hwD.le, ?_⟩
    have hwpos : 0 < 1-‖w‖ ^ 2 := by
      change ‖w‖ < 1 at hwD
      nlinarith [norm_nonneg w]
    exact (div_le_iff₀ hwpos).mp hlt.le

/-- The closure in the disk of any nonempty reflection-invariant set meets the initial triangle. -/
theorem invariant_set_closure_meets_triangle (V : VertexTriple) {c : ℂ}
    (hc : ‖c‖ < 1)
    (hcside : ∀ p ∈ V.val, ∀ q ∈ V.val, ∀ r ∈ V.val,
      p ≠ q → q ≠ r → r ≠ p → 0 < sideEquation p q c * sideEquation p q r)
    {S : Set ℂ} (hS : S.Nonempty) (hSd : S ⊆ disk)
    (hinv : ∀ p ∈ V.val, ∀ q ∈ V.val, p ≠ q →
      Set.MapsTo (idealDiskSideReflection p q) S S) :
    (closure S ∩ triangle V.val).Nonempty := by
  obtain ⟨z, hzS, hzD, hzmin⟩ := diskEnergy_minimum_on_closure hc hS hSd
  refine ⟨z, hzS, hzD, ?_⟩
  intro p hp q hq r hr hpq hqr hrp
  by_contra! hneg
  have hpos := hcside p hp q hq r hr hpq hqr hrp
  have hopposite : sideEquation p q c * sideEquation p q z < 0 := by
    have hrnon : sideEquation p q r ≠ 0 := by intro he; simp [he] at hpos
    rcases lt_or_gt_of_ne hrnon with hrneg | hrpos
    · have hcneg : sideEquation p q c < 0 := by nlinarith
      have hzpos : 0 < sideEquation p q z := by nlinarith
      exact mul_neg_of_neg_of_pos hcneg hzpos
    · have hcpos : 0 < sideEquation p q c := by nlinarith
      have hzneg : sideEquation p q z < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hcpos hzneg
  have hpunit := V.property.2 p hp
  have hqunit := V.property.2 q hq
  have hcont : ContinuousAt (idealDiskSideReflection p q) z := by
    unfold idealDiskSideReflection
    exact (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt)).div
      (continuousAt_const.sub (continuousAt_const.mul Complex.continuous_conj.continuousAt))
      (idealDiskSideReflection_denominator_ne_zero_g6 hpunit hqunit hzD)
  have hzrefl : idealDiskSideReflection p q z ∈ closure S := by
    apply closure_mono (Set.image_subset_iff.mpr (hinv p hp q hq hpq))
    exact mem_closure_image hcont hzS
  have hmin := hzmin _ hzrefl (idealDiskSideReflection_mem_disk_g6 hpunit hqunit hpq hzD)
  exact (not_lt_of_ge hmin) (diskEnergy_reflection_lt hpunit hqunit hpq hzD hopposite)

/-- Any nonempty disk subset invariant under all three initial side reflections meets the initial triangle itself. -/
theorem invariant_set_meets_triangle (V : VertexTriple)
    {S : Set ℂ} (hS : S.Nonempty) (hSd : S ⊆ disk)
    (hinv : ∀ p ∈ V.val, ∀ q ∈ V.val, p ≠ q →
      Set.MapsTo (idealDiskSideReflection p q) S S) :
    (S ∩ triangle V.val).Nonempty := by
  obtain ⟨c, hc⟩ := normalized_triangle_carrier_nonempty_g6 V
  have hcV := interior_subset hc
  have hcside : ∀ p ∈ V.val, ∀ q ∈ V.val, ∀ r ∈ V.val,
      p ≠ q → q ≠ r → r ≠ p → 0 < sideEquation p q c * sideEquation p q r := by
    intro p hp q hq r hr hpq hqr hrp
    have hcn : sideEquation p q c ≠ 0 := by
      intro he
      exact openSide_not_mem_openTriangle V hp hq hpq ⟨hcV.1,he⟩ hc
    have hrn : sideEquation p q r ≠ 0 := by
      intro he
      exact (eq_endpoint_of_sideEquation_eq_zero_unit (V.property.2 p hp)
        (V.property.2 q hq) (V.property.2 r hr) he).elim hrp hqr.symm
    exact lt_of_le_of_ne (hcV.2 p hp q hq r hr hpq hqr hrp) (Ne.symm (mul_ne_zero hcn hrn))
  obtain ⟨z,hzS,hzV⟩ := invariant_set_closure_meets_triangle V hcV.1 hcside hS hSd hinv
  rcases triangle_subset_openTriangle_union_sides V.val hzV with hzint | hzside
  · obtain ⟨w,hwV,hwS⟩ := mem_closure_iff_nhds.mp hzS _ (mem_interior_iff_mem_nhds.mp hzint)
    exact ⟨w,hwS,hwV⟩
  · obtain ⟨p,hp,q,hq,hpq,hz⟩ := hzside
    obtain ⟨w,hwU,hwS⟩ := mem_closure_iff_nhds.mp hzS _ (triangle_union_reflection_mem_nhds V hp hq hpq hz)
    rcases hwU with hwV | hwR
    · exact ⟨w,hwS,hwV⟩
    · exact ⟨idealDiskSideReflection p q w, hinv p hp q hq hpq hwS,
        (idealDiskSideReflection_triangle_transport_vertex_g6 V
          (V.property.2 p hp) (V.property.2 q hq) hpq hp hq w).2 hwR⟩

end HolomorphicAnosov.IdealDiskTriangle