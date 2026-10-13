import HolomorphicAnosov.Topology.GallierXuSurfacePresentation
import HolomorphicAnosov.Topology.DiskPrescribedBoundaryExtension
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Original triangle charts with prescribed side parameters

Source: Gallier–Xu, Proposition 3.2 and prescribed-boundary remark p.31,
Note F.4 p.167; Lee, Proposition 6.14 p.173.
DAG node: `topo.gallier_xu_original_triangle_disk_chart_g6`.
-/

noncomputable section
open Set Metric
namespace HolomorphicAnosov.Topology.GallierXu

/-- The positively oriented traversal of the triangle with vertices 0, 1 and I,
with unit time on each side. Source: Gallier–Xu Proposition 3.2, p.31. -/
def planarTriangleLoop (t : ℝ) : ℂ :=
  if t ≤ 1 then (t : ℂ) else if t ≤ 2 then (2-t : ℝ) + (t-1 : ℝ) * Complex.I
  else (3-t : ℝ) * Complex.I

/-- The affine pieces agree at times one and two; closed-half-line pasting gives continuity.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangleLoop_continuous : Continuous planarTriangleLoop := by
  unfold planarTriangleLoop
  refine Continuous.if_le (by fun_prop) ?_ continuous_id continuous_const ?_
  · apply Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
    intro x hx
    change x = 2 at hx
    subst x
    norm_num
  · intro x hx
    change x = 1 at hx
    subst x
    norm_num

/-- The times zero and three both map to the vertex zero.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangleLoop_end : planarTriangleLoop 0 = planarTriangleLoop 3 := by
  norm_num [planarTriangleLoop]

/-- On each side one coordinate determines time; equality across different sides forces the common endpoint, and the half-open domain omits the repeated final vertex.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangleLoop_injective : InjOn planarTriangleLoop (Ico 0 3) := by
  intro s hs t ht h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [planarTriangleLoop] at hr hi
  split_ifs at hr hi <;> simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
    mul_zero, sub_zero, mul_one, zero_add, add_zero] at hr hi <;>
    rcases hs with ⟨hs0, hs3⟩ <;> rcases ht with ⟨ht0, ht3⟩ <;> linarith

/-- The closed affine triangle with vertices 0, 1 and I. -/
def planarTriangle : Set ℂ := {z | 0 ≤ z.re ∧ 0 ≤ z.im ∧ z.re + z.im ≤ 1}

/-- The three defining weak affine inequalities are closed.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangle_closed : IsClosed planarTriangle := by
  exact (isClosed_le continuous_const Complex.continuous_re).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le (Complex.continuous_re.add Complex.continuous_im) continuous_const))

/-- A convex combination preserves each of the three affine inequalities.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangle_convex : Convex ℝ planarTriangle := by
  intro x hx y hy a b ha hb hab
  simp only [planarTriangle, mem_ofPred_eq, Complex.add_re, Complex.add_im,
    Complex.smul_re, Complex.smul_im, smul_eq_mul]
  refine ⟨add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1),
    add_nonneg (mul_nonneg ha hx.2.1) (mul_nonneg hb hy.2.1), ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hx.2.2 ha,
    mul_le_mul_of_nonneg_left hy.2.2 hb]

/-- Both coordinates are nonnegative with sum at most one, so the complex norm is bounded by their sum.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangle_bounded : Bornology.IsBounded planarTriangle := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mpr
  refine ⟨2, fun z hz ↦ ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
       _ ≤ 2 := by rw [abs_of_nonneg hz.1, abs_of_nonneg hz.2.1]; linarith [hz.2.2]

/-- The three nonzero real linear coordinate maps are open; taking interior of their closed half-space preimages gives exactly the strict inequalities.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangle_interior : interior planarTriangle =
    {z | 0 < z.re ∧ 0 < z.im ∧ z.re+z.im < 1} := by
  let sum : ℂ →L[ℝ] ℝ := Complex.reCLM + Complex.imCLM
  have hre : IsOpenMap Complex.re := Complex.reCLM.isOpenMap (fun r ↦ ⟨r, by simp⟩)
  have him : IsOpenMap Complex.im := Complex.imCLM.isOpenMap (fun r ↦ ⟨r * Complex.I, by simp⟩)
  have hsum : IsOpenMap sum := sum.isOpenMap (fun r ↦ ⟨r, by simp [sum]⟩)
  change interior ((Complex.re ⁻¹' Ici 0) ∩ ((Complex.im ⁻¹' Ici 0) ∩ (sum ⁻¹' Iic 1))) = _
  rw [interior_inter, interior_inter,
    ← hre.preimage_interior_eq_interior_preimage Complex.continuous_re,
    ← him.preimage_interior_eq_interior_preimage Complex.continuous_im,
    ← hsum.preimage_interior_eq_interior_preimage sum.continuous,
    interior_Ici, interior_Iic]
  rfl

/-- Subtract the strict-inequality interior from the closed triangle; a boundary point has at least one equality.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangle_frontier : frontier planarTriangle =
    {z | z ∈ planarTriangle ∧ (z.re = 0 ∨ z.im = 0 ∨ z.re+z.im = 1)} := by
  rw [frontier, planarTriangle_closed.closure_eq, planarTriangle_interior]
  ext z
  change (z ∈ planarTriangle ∧ ¬(0 < z.re ∧ 0 < z.im ∧ z.re+z.im < 1)) ↔ _
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, ?_⟩
    by_cases hre : z.re = 0
    · exact Or.inl hre
    by_cases him : z.im = 0
    · exact Or.inr (Or.inl him)
    right; right
    have hr : 0 < z.re := lt_of_le_of_ne hz.1 (Ne.symm hre)
    have hi : 0 < z.im := lt_of_le_of_ne hz.2.1 (Ne.symm him)
    have : ¬z.re+z.im < 1 := fun hlt ↦ h ⟨hr,hi,hlt⟩
    exact le_antisymm hz.2.2 (le_of_not_gt this)
  · rintro ⟨hz, h | h | h⟩ <;> refine ⟨hz, ?_⟩ <;> rintro ⟨hr, hi, hs⟩ <;> linarith

/-- The three affine pieces cover precisely the three equality sides; on each side its nonzero coordinate recovers a parameter in the closed traversal interval.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma planarTriangleLoop_image : planarTriangleLoop '' Icc 0 3 = frontier planarTriangle := by
  rw [planarTriangle_frontier]
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    unfold planarTriangleLoop
    split_ifs <;> simp only [planarTriangle, mem_ofPred_eq, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im,
      Complex.mul_im, mul_zero, sub_zero, mul_one, zero_add, add_zero]
    all_goals refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    all_goals solve | linarith [ht.1, ht.2] | simp | (right; right; ring)
  · rintro ⟨hz, h | h | h⟩
    · refine ⟨3-z.im, ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩, ?_⟩
      apply Complex.ext <;> simp only [planarTriangleLoop] <;> split_ifs <;>
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
          mul_zero, sub_zero, mul_one, zero_add, add_zero] <;>
        linarith [hz.1, hz.2.1, hz.2.2]
    · refine ⟨z.re, ⟨hz.1, by linarith [hz.2.2]⟩, ?_⟩
      have hr : z.re ≤ 1 := by linarith [hz.2.2]
      simp only [planarTriangleLoop, ite_eq_left hr]
      apply Complex.ext <;> simp [h]
    · refine ⟨z.im+1, ⟨by linarith [hz.2.1], by linarith [hz.1]⟩, ?_⟩
      apply Complex.ext <;> simp only [planarTriangleLoop] <;> split_ifs <;>
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im,
          mul_zero, sub_zero, mul_one, zero_add, add_zero] <;>
        linarith [hz.1, hz.2.1, hz.2.2]

/-- The explicit three-side traversal descends through the endpoint quotient,
retaining its original angle parameter. -/
theorem planarTriangle_boundary_parameter :
    ∃ j : Circle ≃ₜ frontier planarTriangle,
      ∀ t ∈ Icc (0 : ℝ) 3,
        (j (Circle.exp (2*Real.pi*t/3))).val = planarTriangleLoop t := by
  have : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  let g : AddCircle (3 : ℝ) → ℂ := AddCircle.liftIco 3 0 planarTriangleLoop
  have hg : Continuous g := AddCircle.liftIco_zero_continuous
    planarTriangleLoop_end planarTriangleLoop_continuous.continuousOn
  have hginj : Function.Injective g := by
    intro a b hab
    apply (AddCircle.equivIco (3 : ℝ) 0).injective
    apply Subtype.ext
    exact planarTriangleLoop_injective (by simpa using (AddCircle.equivIco (3 : ℝ) 0 a).property)
      (by simpa using (AddCircle.equivIco (3 : ℝ) 0 b).property) hab
  let e : AddCircle (3 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle (by norm_num)
  let j : Circle → ℂ := g ∘ e.symm
  have hj : _root_.Topology.IsEmbedding j :=
    ((hg.comp e.symm.continuous).isClosedEmbedding (hginj.comp e.symm.injective)).isEmbedding
  have hformula (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 3) :
      j (Circle.exp (2*Real.pi*t/3)) = planarTriangleLoop t := by
    have he : Circle.exp (2*Real.pi*t/3) = e (t : AddCircle (3 : ℝ)) := by
      rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
      congr 1
      ring
    rw [he]
    change g (e.symm (e (t : AddCircle (3 : ℝ)))) = _
    rw [e.symm_apply_apply]
    by_cases h : t = 3
    · subst t
      change AddCircle.liftIco 3 0 planarTriangleLoop (3 : ℝ) = _
      rw [AddCircle.coe_period]
      rw [← planarTriangleLoop_end]
      exact AddCircle.liftIco_zero_coe_apply (by norm_num : (0 : ℝ) ∈ Ico 0 3)
    · exact AddCircle.liftIco_zero_coe_apply ⟨ht.1, lt_of_le_of_ne ht.2 h⟩
  have hrange : range j = frontier planarTriangle := by
    rw [← planarTriangleLoop_image]
    apply Set.Subset.antisymm
    · rintro _ ⟨z, rfl⟩
      refine ⟨(AddCircle.equivIco (3 : ℝ) 0 (e.symm z)).val, ?_, rfl⟩
      simpa using Ico_subset_Icc_self (AddCircle.equivIco (3 : ℝ) 0 (e.symm z)).property
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨Circle.exp (2*Real.pi*t/3), hformula t ht⟩
  exact ⟨hj.toHomeomorph.trans (Homeomorph.setCongr hrange), hformula⟩

/-- A round disk chart on the affine triangle can prescribe the unit-speed
boundary traversal of its three sides. Source: Gallier–Xu Proposition 3.2 and
its prescribed-boundary remark, p.31; Note F.4 p.167. -/
theorem planarTriangle_disk_parameter :
    ∃ h : Metric.closedBall (0 : ℂ) 1 ≃ₜ planarTriangle,
      ∀ t ∈ Icc (0 : ℝ) 3,
        (h ⟨Circle.exp (2*Real.pi*t/3), by exact sphere_subset_closedBall (Circle.exp _).property⟩).val = planarTriangleLoop t := by
  have hne : (interior planarTriangle).Nonempty := by
    rw [planarTriangle_interior]
    exact ⟨(1/3 : ℝ) + (1/3 : ℝ)*Complex.I, by norm_num⟩
  obtain ⟨H, _, hcl, hfr⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    planarTriangle_convex hne planarTriangle_bounded
  rw [planarTriangle_closed.closure_eq] at hcl
  let H₀ : planarTriangle ≃ₜ Metric.closedBall (0 : ℂ) 1 :=
    (H.image planarTriangle).trans (Homeomorph.setCongr hcl)
  have hbd : ∀ z : planarTriangle, z.val ∈ frontier planarTriangle ↔ ‖(H₀ z : ℂ)‖ = 1 := by
    intro z
    change z.val ∈ frontier planarTriangle ↔ ‖H z.val‖ = 1
    have hm : H z.val ∈ sphere (0 : ℂ) 1 ↔ ‖H z.val‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right]
    rw [← hm, ← hfr]
    exact H.injective.mem_set_image.symm
  obtain ⟨j, hj⟩ := planarTriangle_boundary_parameter
  have hsubset : frontier planarTriangle ⊆ planarTriangle := by
    exact frontier_subset_closure.trans_eq planarTriangle_closed.closure_eq
  obtain ⟨F, hF⟩ := HolomorphicAnosov.disk_prescribed_boundary_extension
    (frontier planarTriangle) planarTriangle hsubset H₀ hbd j.symm
  refine ⟨F.symm, ?_⟩
  intro t ht
  let z : frontier planarTriangle := j (Circle.exp (2*Real.pi*t/3))
  have hz := hF z (hsubset z.property)
  have he : F ⟨z.val, hsubset z.property⟩ =
      ⟨Circle.exp (2*Real.pi*t/3), by exact sphere_subset_closedBall (Circle.exp _).property⟩ := by
    apply Subtype.ext
    exact hz.trans (congrArg Subtype.val (j.symm_apply_apply _))
  rw [← he, F.symm_apply_apply]
  exact hj t ht

/-- Affine coordinates of the original oriented triangle. -/
def triangleAffine {N : ℕ} (a b c : Fin N) (z : ℂ) : Fin N → ℝ :=
  (1-z.re-z.im) • Pi.single a 1 + z.re • Pi.single b 1 + z.im • Pi.single c 1

/-- The three barycentric coefficients are continuous affine functions of the planar coordinates.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma triangleAffine_continuous {N : ℕ} (a b c : Fin N) : Continuous (triangleAffine a b c) := by
  unfold triangleAffine
  fun_prop

/-- The coefficients are nonnegative and sum to one; every coordinate outside the original triangle vanishes.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma triangleAffine_mem {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) (z : planarTriangle) :
    triangleAffine (o 0).val (o 1).val (o 2).val z ∈ carrier K := by
  refine ⟨⟨?_, ?_⟩, s.val, s.property.1, ?_⟩
  · intro v
    simp only [triangleAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have ha : 0 ≤ 1-z.val.re-z.val.im := by linarith [z.property.2.2]
    have hb := z.property.1
    have hc := z.property.2.1
    simp only [Pi.single_apply]
    split_ifs <;> positivity
  · simp only [triangleAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Pi.single_apply]
    ; ring
  · intro v hv
    have ha : v ≠ (o 0).val := fun h ↦ hv (h ▸ (o 0).property)
    have hb : v ≠ (o 1).val := fun h ↦ hv (h ▸ (o 1).property)
    have hc : v ≠ (o 2).val := fun h ↦ hv (h ▸ (o 2).property)
    simp [triangleAffine, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hc]

/-- The coordinates at the second and third distinct vertices recover the real and imaginary parts.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma triangleAffine_injective {N : ℕ} (a b c : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Function.Injective (triangleAffine a b c) := by
  intro z w h
  apply Complex.ext
  · have hb := congrFun h b
    simpa [triangleAffine, hab.symm, hbc] using hb
  · have hc := congrFun h c
    simpa [triangleAffine, hac.symm, hbc.symm] using hc

/-- Surjectivity of the three-element vertex ordering lists every original vertex exactly once.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma triangle_vertices {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) :
    s.val = {(o 0).val, (o 1).val, (o 2).val} := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := o.surjective ⟨v, hv⟩
    have hi' := congrArg Subtype.val hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    fin_cases i
    · exact Or.inl hi'.symm
    · exact Or.inr (Or.inl hi'.symm)
    · exact Or.inr (Or.inr hi'.symm)
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl) <;> exact (o _).property

/-- The supported simplex has total coordinate sum one; its second and third vertex coordinates produce the inverse planar point, while the remaining coordinate is their complement.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma triangleAffine_range {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) :
    Set.range (fun z : planarTriangle ↦
      (⟨triangleAffine (o 0).val (o 1).val (o 2).val z,
        triangleAffine_mem s o z⟩ : carrier K)) =
      {x : carrier K | ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0} := by
  have ho : Function.Injective (fun i ↦ (o i).val) := Subtype.val_injective.comp o.injective
  have hab := ho.ne (show (0 : Fin 3) ≠ 1 by decide)
  have hac := ho.ne (show (0 : Fin 3) ≠ 2 by decide)
  have hbc := ho.ne (show (1 : Fin 3) ≠ 2 by decide)
  ext x
  constructor
  · rintro ⟨z, rfl⟩ v hv
    have h := (triangleAffine_mem s o z).2
    have ha : v ≠ (o 0).val := fun h ↦ hv (h ▸ (o 0).property)
    have hb : v ≠ (o 1).val := fun h ↦ hv (h ▸ (o 1).property)
    have hc : v ≠ (o 2).val := fun h ↦ hv (h ▸ (o 2).property)
    simp [triangleAffine, Pi.single_eq_of_ne ha, Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hc]
  · intro hx
    have hsum : x.val (o 0).val + x.val (o 1).val + x.val (o 2).val = 1 := by
      have hsub : ∑ v ∈ s.val, x.val v = ∑ v : Fin N, x.val v :=
        Finset.sum_subset (Finset.subset_univ _) (fun v _ hv ↦ hx v hv)
      rw [triangle_vertices s o] at hsub
      simpa [hab, hac, hbc, add_assoc] using hsub.trans x.property.1.2
    let z : planarTriangle := ⟨(x.val (o 1).val : ℂ) + x.val (o 2).val * Complex.I, by
      simp only [planarTriangle, mem_ofPred_eq, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
      refine ⟨x.property.1.1 _, x.property.1.1 _, ?_⟩
      linarith [x.property.1.1 (o 0).val]⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    funext v
    simp only [triangleAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases h0 : v = (o 0).val
    · subst v
      simp [z, hab, hac]
      linarith
    by_cases h1 : v = (o 1).val
    · subst v
      simp [z, hab.symm, hbc]
    by_cases h2 : v = (o 2).val
    · subst v
      simp [z, hac.symm, hbc.symm]
    have hv : v ∉ s.val := by rw [triangle_vertices s o]; simp [h0,h1,h2]
    simp [Pi.single_eq_of_ne h0, Pi.single_eq_of_ne h1, Pi.single_eq_of_ne h2, hx v hv]

/-- On each of the three unit traversal intervals the affine coordinates are exactly the linear interpolation of the corresponding ordered endpoints.
Source: Gallier–Xu Proposition 3.2, p.31, in the original affine triangle coordinates. -/
lemma triangleAffine_loop {N : ℕ} (v : Fin 3 → Fin N) (i : Fin 3)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    triangleAffine (v 0) (v 1) (v 2) (planarTriangleLoop (i.val+t)) =
      (1-t) • Pi.single (v i) 1 + t • Pi.single (v (finRotate 3 i)) 1 := by
  fin_cases i <;> norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add, finRotate_apply]
  all_goals unfold planarTriangleLoop
  all_goals split_ifs
  all_goals try { exfalso; linarith [ht.1,ht.2] }
  all_goals try have ht0 : t = 0 := by linarith [ht.1]
  all_goals try rw [ht0]
  all_goals funext k
  all_goals simp [triangleAffine, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  all_goals nlinarith [ht.1,ht.2]

/-- Each original triangle admits a disk chart with exactly its cyclic side parameters.
Source: Gallier–Xu Proposition 3.2 and prescribed-boundary remark p.31.

Parametrize the planar triangle boundary by the explicit three affine pieces, descend through
the endpoint-identified interval, and retain its angle formula. Its half-open injectivity and
closed-side coverage give a homeomorphism onto the frontier. A convex-body disk normalization
exists because the triangle is bounded, convex, and has nonempty interior. Correct its boundary
using the radial prescribed-boundary extension, then invert it. This gives a round disk chart
with the exact three unit-time boundary segments. Apply the affine coordinate map sending the
planar vertices to the supplied original vertices. Its second and third coordinates prove
injectivity, and all nonnegative supported barycentric vectors occur by taking these two
coordinates as the planar point. Thus the disk chart has exactly the required supported image
and every cyclic side is parametrized by its original affine parameter. -/
theorem original_triangle_disk_chart {N : ℕ} {K : AbstractSimplicialComplex (Fin N)}
    (s : Triangle K) (o : Fin 3 ≃ ↥s.val) :
    ∃ f : C(Disk, carrier K), Function.Injective f ∧
      Set.range f = {x : carrier K | ∀ v ∉ s.val, (x : Fin N → ℝ) v = 0} ∧
      ∀ (i : Fin 3) (t : ℝ), t ∈ Icc (0 : ℝ) 1 →
        (f ⟨Circle.exp (2*Real.pi*(i.val+t)/3),
          sphere_subset_closedBall (Circle.exp _).property⟩).val =
          (1-t) • Pi.single (o i).val 1 + t • Pi.single (o (finRotate 3 i)).val 1 := by
  obtain ⟨h, hh⟩ := planarTriangle_disk_parameter
  let a : C(planarTriangle, carrier K) :=
    ⟨fun z ↦ ⟨triangleAffine (o 0).val (o 1).val (o 2).val z, triangleAffine_mem s o z⟩,
      ((triangleAffine_continuous _ _ _).comp continuous_subtype_val).subtype_mk _⟩
  let f : C(Disk, carrier K) := a.comp ⟨h, h.continuous⟩
  have ho : Function.Injective (fun i ↦ (o i).val) := Subtype.val_injective.comp o.injective
  have ha : Function.Injective a := by
    intro z w he
    apply Subtype.ext
    exact triangleAffine_injective _ _ _ (ho.ne (by decide)) (ho.ne (by decide))
      (ho.ne (by decide)) (congrArg Subtype.val he)
  refine ⟨f, ha.comp h.injective, ?_, ?_⟩
  · change Set.range (a ∘ h) = _
    rw [Set.range_comp, h.surjective.range_eq, Set.image_univ]
    exact triangleAffine_range s o
  · intro i t ht
    have htime : i.val+t ∈ Icc (0 : ℝ) 3 := by
      have hi : i.val ≤ 2 := by omega
      have hi' : (i.val : ℝ) ≤ 2 := by exact_mod_cast hi
      constructor <;> linarith [ht.1,ht.2,Nat.cast_nonneg (α := ℝ) i.val]
    change triangleAffine (o 0).val (o 1).val (o 2).val
      ((h ⟨Circle.exp (2*Real.pi*(i.val+t)/3), _⟩).val) = _
    rw [hh _ htime]
    exact triangleAffine_loop (fun i ↦ (o i).val) i t ht


end HolomorphicAnosov.Topology.GallierXu
