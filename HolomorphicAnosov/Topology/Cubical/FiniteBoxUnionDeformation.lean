import HolomorphicAnosov.Topology.Cubical.ClosedCoordinateCell
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-! Arbitrarily small strong deformation neighborhoods for finite unions of
closed coordinate boxes, including degenerate boxes and the empty union.

The explicit rounding proof implements the finite polyhedral neighborhood
assertion of Hatcher, Algebraic Topology, Appendix A.5 p.523, in the original
ambient coordinate topology. DAG: `topo.finite_box_union_deformation_neighborhood_g12`.
-/

namespace HolomorphicAnosov.Cubical
noncomputable section
open Set Metric

private def endpointBump (ρ a x : ℝ) : ℝ := max 0 (min 1 (2 - |x-a| / ρ))
private def endpointCorrection (ρ d a x : ℝ) : ℝ :=
  endpointBump ρ a x * max (-d) (min d (a-x))
private def roundCoordinate (E : Finset ℝ) (ρ d x : ℝ) : ℝ :=
  x + ∑ a ∈ E, endpointCorrection ρ d a x

private theorem bump_bounds (ρ a x : ℝ) :
    0 ≤ endpointBump ρ a x ∧ endpointBump ρ a x ≤ 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem bump_zero {ρ a x : ℝ} (hρ : 0 < ρ) (h : 2*ρ ≤ |x-a|) :
    endpointBump ρ a x = 0 := by
  have hd : 2 ≤ |x-a| / ρ := (le_div_iff₀ hρ).mpr h
  unfold endpointBump
  rw [max_eq_left (le_trans (min_le_right _ _) (by linarith))]

private theorem bump_one {ρ a x : ℝ} (hρ : 0 < ρ) (h : |x-a| ≤ ρ) :
    endpointBump ρ a x = 1 := by
  have hd : |x-a| / ρ ≤ 1 := (div_le_one hρ).mpr h
  unfold endpointBump
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

private theorem correction_zero {ρ d a x : ℝ} (hρ : 0 < ρ) (h : 2*ρ ≤ |x-a|) :
    endpointCorrection ρ d a x = 0 := by
  simp [endpointCorrection, bump_zero hρ h]

private theorem correction_near {ρ d a x : ℝ} (hρ : 0 < ρ) (hdρ : d ≤ ρ)
    (hx : |x-a| ≤ d) : endpointCorrection ρ d a x = a-x := by
  have ha : -d ≤ a-x ∧ a-x ≤ d := by
    have := abs_le.mp hx
    constructor <;> linarith
  simp only [endpointCorrection, bump_one hρ (hx.trans hdρ), one_mul,
    min_eq_right ha.2, max_eq_right ha.1]

private theorem correction_between {ρ d a x : ℝ} (hd : 0 ≤ d) :
    min x a ≤ x + endpointCorrection ρ d a x ∧
      x + endpointCorrection ρ d a x ≤ max x a := by
  obtain ⟨hb0,hb1⟩ := bump_bounds ρ a x
  by_cases hxa : x ≤ a
  · have hcl0 : 0 ≤ max (-d) (min d (a-x)) :=
      le_trans (le_min hd (sub_nonneg.mpr hxa)) (le_max_right _ _)
    have hcla : max (-d) (min d (a-x)) ≤ a-x :=
      max_le (by linarith) (min_le_right _ _)
    rw [min_eq_left hxa,max_eq_right hxa]
    unfold endpointCorrection
    constructor <;> nlinarith
  · have hax : a ≤ x := le_of_not_ge hxa
    have hcl0 : max (-d) (min d (a-x)) ≤ 0 :=
      max_le (by linarith) ((min_le_right _ _).trans (sub_nonpos.mpr hax))
    have hcla : a-x ≤ max (-d) (min d (a-x)) := by
      rw [min_eq_right (by linarith)]
      exact le_max_right _ _
    rw [min_eq_right hax,max_eq_left hax]
    unfold endpointCorrection
    constructor <;> nlinarith

private theorem correction_other_zero {ρ d a b x : ℝ} (hρ : 0 < ρ)
    (hab : 4*ρ < |a-b|) (hxa : |x-a| < 2*ρ) :
    endpointCorrection ρ d b x = 0 := by
  apply correction_zero hρ
  have htri : |a-b| ≤ |x-a| + |x-b| := by
    calc
      |a-b| = |(a-x)+(x-b)| := by congr 1; ring
      _ ≤ |a-x| + |x-b| := abs_add_le _ _
      _ = |x-a| + |x-b| := by rw [abs_sub_comm a x]
  linarith

private theorem round_eq_single {E : Finset ℝ} {ρ d a x : ℝ}
    (hρ : 0 < ρ) (hsep : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → 4*ρ < |a-b|)
    (ha : a ∈ E) (hxa : |x-a| < 2*ρ) :
    roundCoordinate E ρ d x = x + endpointCorrection ρ d a x := by
  unfold roundCoordinate
  congr 1
  apply Finset.sum_eq_single a
  · intro b hb hba
    exact correction_other_zero hρ (hsep a ha b hb hba.symm) hxa
  · exact fun h ↦ (h ha).elim

private theorem round_near {E : Finset ℝ} {ρ d a x : ℝ}
    (hρ : 0 < ρ) (hsep : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → 4*ρ < |a-b|)
    (ha : a ∈ E) (hdρ : d < ρ) (hxa : |x-a| ≤ d) :
    roundCoordinate E ρ d x = a := by
  rw [round_eq_single hρ hsep ha (by linarith), correction_near hρ hdρ.le hxa]
  ring

private theorem round_interval {E : Finset ℝ} {ρ d a b x : ℝ}
    (hρ : 0 < ρ) (hsep : ∀ a ∈ E, ∀ b ∈ E, a ≠ b → 4*ρ < |a-b|)
    (ha : a ∈ E) (hb : b ∈ E) (hab : a ≤ b)
    (hd : 0 ≤ d) (hdρ : d < ρ) (hx : a-d ≤ x ∧ x ≤ b+d) :
    a ≤ roundCoordinate E ρ d x ∧ roundCoordinate E ρ d x ≤ b := by
  by_cases hxa : x < a
  · have hxnear : |x-a| ≤ d := by rw [abs_of_neg (sub_neg.mpr hxa)]; linarith
    rw [round_near hρ hsep ha hdρ hxnear]
    exact ⟨le_rfl,hab⟩
  by_cases hbx : b < x
  · have hxnear : |x-b| ≤ d := by rw [abs_of_pos (sub_pos.mpr hbx)]; linarith
    rw [round_near hρ hsep hb hdρ hxnear]
    exact ⟨hab,le_rfl⟩
  have hax : a ≤ x := le_of_not_gt hxa
  have hxb : x ≤ b := le_of_not_gt hbx
  by_cases hactive : ∃ c ∈ E, |x-c| < 2*ρ
  · obtain ⟨c,hc,hxc⟩ := hactive
    have hac : a ≤ c := by
      by_contra h
      have hca : c < a := lt_of_not_ge h
      have hs := hsep c hc a ha (ne_of_lt hca)
      rw [abs_of_neg (sub_neg.mpr hca)] at hs
      have ht := neg_abs_le (x-c)
      have ht' := le_abs_self (x-c)
      linarith
    have hcb : c ≤ b := by
      by_contra h
      have hbc : b < c := lt_of_not_ge h
      have hs := hsep c hc b hb (ne_of_gt hbc)
      rw [abs_of_pos (sub_pos.mpr hbc)] at hs
      have ht := neg_abs_le (x-c)
      linarith
    rw [round_eq_single hρ hsep hc hxc]
    obtain ⟨hlo,hhi⟩ := correction_between (ρ := ρ) (a := c) (x := x) hd
    exact ⟨(le_min hax hac).trans hlo, hhi.trans (max_le hxb hcb)⟩
  · have hall : ∀ c ∈ E, endpointCorrection ρ d c x = 0 := by
      intro c hc
      apply correction_zero hρ
      exact le_of_not_gt (fun h ↦ hactive ⟨c,hc,h⟩)
    simp only [roundCoordinate,Finset.sum_eq_zero hall,add_zero]
    exact ⟨hax,hxb⟩

private theorem finite_endpoint_separation (E : Finset ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ E, ∀ b ∈ E, a ≠ b → 4*ρ < |a-b| := by
  classical
  let G : Finset ℝ := insert 1 (((E.product E).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ |p.1-p.2|))
  have hG : G.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  have hpos : 0 < G.min' hG := by
    apply (Finset.lt_min'_iff _ _).mpr
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · norm_num
    · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact abs_pos.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)
  refine ⟨G.min' hG / 8, by positivity, ?_⟩
  intro a ha b hb hab
  have hmem : |a-b| ∈ G := Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(a,b),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha,hb⟩,hab⟩,rfl⟩)
  have hmin := Finset.min'_le G |a-b| hmem
  linarith

private theorem continuous_roundCoordinate (E : Finset ℝ) (ρ : ℝ) :
    Continuous (fun p : ℝ × ℝ ↦ roundCoordinate E ρ p.1 p.2) := by
  unfold roundCoordinate endpointCorrection endpointBump
  fun_prop

private theorem round_zero (E : Finset ℝ) (ρ x : ℝ) : roundCoordinate E ρ 0 x = x := by
  simp [roundCoordinate,endpointCorrection]

private def boxEndpoints {N : ℕ} (B : Finset (ClosedCoordinateCell N)) : Finset ℝ :=
  B.biUnion (fun c ↦ Finset.univ.image c.lower ∪ Finset.univ.image c.upper)

private theorem lower_mem_endpoints {N : ℕ} {B : Finset (ClosedCoordinateCell N)}
    {c : ClosedCoordinateCell N} (hc : c ∈ B) (i : Fin N) : c.lower i ∈ boxEndpoints B := by
  classical
  exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

private theorem upper_mem_endpoints {N : ℕ} {B : Finset (ClosedCoordinateCell N)}
    {c : ClosedCoordinateCell N} (hc : c ∈ B) (i : Fin N) : c.upper i ∈ boxEndpoints B := by
  classical
  exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)⟩

/-- A finite union of coordinate boxes has arbitrarily small open strong
 deformation neighborhoods. The proof rounds coordinates near their finitely many
 endpoints, with rounding distance equal to distance from the union. The resulting
 point lies in a nearest box. Straight segments stay in the same metric thickening
 by comparison with the corresponding segment in that convex box. On the union
 the rounding distance is zero, so the entire homotopy fixes it.
 Source: explicit coordinate proof of Hatcher, Appendix A.5, p.523. -/
theorem finiteBoxUnion_deformationNeighborhood {N : ℕ}
    (B : Finset (ClosedCoordinateCell N)) (V : Set (Fin N → ℝ)) (hV : IsOpen V)
    (hAV : (⋃ c ∈ B, c.carrier) ⊆ V) :
    let A := ⋃ c ∈ B, c.carrier
    ∃ U : Set (Fin N → ℝ), IsOpen U ∧ U ⊆ V ∧
      ∃ hAU : A ⊆ U, ∃ r : C(U,A),
        (∀ a : A, r ⟨a.val,hAU a.property⟩ = a) ∧
        Nonempty ((ContinuousMap.id U).HomotopyRel
          ((ContinuousMap.inclusion hAU).comp r) {x : U | x.val ∈ A}) ∧
        (A = ∅ → U = ∅) := by
  classical
  intro A
  by_cases hA : A = ∅
  · refine ⟨A,by rw [hA]; exact isOpen_empty,hAV,Set.Subset.rfl,ContinuousMap.id _,?_,?_,fun _ ↦ hA⟩
    · exact fun _ ↦ rfl
    · exact ⟨ContinuousMap.HomotopyRel.refl (ContinuousMap.id _) _⟩
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
  have hAc : IsCompact A := by
    apply B.finite_toSet.isCompact_biUnion
    intro c hc
    change IsCompact (Icc c.lower c.upper)
    rw [← pi_univ_Icc]
    exact isCompact_univ_pi fun i ↦
      ConditionallyCompleteLinearOrder.isCompact_Icc (c.lower i) (c.upper i)
  obtain ⟨ρ,hρ,hsep⟩ := finite_endpoint_separation (boxEndpoints B)
  obtain ⟨ε,hε,hεV⟩ := hAc.exists_thickening_subset_open hV hAV
  let δ := min ρ ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδρ : δ < ρ := by dsimp [δ]; have := min_le_left ρ ε; linarith
  have hδε : δ ≤ ε := by dsimp [δ]; have := min_le_right ρ ε; linarith
  let U := Metric.thickening δ A
  have hAU : A ⊆ U := Metric.self_subset_thickening hδ _
  let R : (Fin N → ℝ) → (Fin N → ℝ) := fun x i ↦
    roundCoordinate (boxEndpoints B) ρ (Metric.infDist x A) (x i)
  have hR : Continuous R := by
    apply continuous_pi
    intro i
    exact (continuous_roundCoordinate _ _).comp ((Metric.continuous_infDist_pt A).prodMk (continuous_apply i))
  have hfix : ∀ x ∈ A, R x = x := by
    intro x hx
    funext i
    simp [R,Metric.infDist_zero_of_mem hx,round_zero]
  have hnearest : ∀ x ∈ U, ∃ c ∈ B, ∃ y ∈ c.carrier,
      dist x y < δ ∧ R x ∈ c.carrier := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hAc.exists_infDist_eq_dist hAne x
    obtain ⟨c,hc,hyc⟩ := (by simpa only [A,mem_iUnion] using hy)
    have hdist : Metric.infDist x A < δ := (Metric.mem_thickening_iff_infDist_lt hAne).mp hx
    have hint (i : Fin N) : c.lower i ≤ R x i ∧ R x i ≤ c.upper i := by
      have hcoord : |x i-y i| ≤ Metric.infDist x A := by
        rw [hxy]
        exact dist_le_pi_dist x y i
      have habs := abs_le.mp hcoord
      exact round_interval hρ hsep (lower_mem_endpoints hc i)
        (upper_mem_endpoints hc i) (c.lower_le_upper i) Metric.infDist_nonneg
        (hdist.trans hδρ) (show c.lower i - Metric.infDist x A ≤ x i ∧ x i ≤ c.upper i + Metric.infDist x A by
          have hyl := hyc.1 i
          have hyu := hyc.2 i
          constructor <;> linarith)
    exact ⟨c,hc,y,hyc,by rwa [← hxy],fun i ↦ (hint i).1,fun i ↦ (hint i).2⟩
  have hRmem : ∀ x ∈ U, R x ∈ A := by
    intro x hx
    obtain ⟨c,hc,y,hy,hd,hr⟩ := hnearest x hx
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,hr⟩⟩
  let r : C(U,A) := ⟨fun x ↦ ⟨R x.val,hRmem x.val x.property⟩,
    (hR.comp continuous_subtype_val).subtype_mk _⟩
  have hstay : ∀ t : unitInterval, ∀ x ∈ U, (1-(t:ℝ)) • x + (t:ℝ) • R x ∈ U := by
    intro t x hx
    obtain ⟨c,hc,y,hy,hd,hr⟩ := hnearest x hx
    let z := (1-(t:ℝ)) • y + (t:ℝ) • R x
    have hz : z ∈ A := mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hc,
      (convex_Icc c.lower c.upper) hy hr (by linarith [t.property.2]) t.property.1 (by ring)⟩⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨z,hz,?_⟩
    have hdcalc : dist ((1-(t:ℝ)) • x + (t:ℝ) • R x) z = (1-(t:ℝ))*dist x y := by
      dsimp [z]
      rw [dist_add_right,dist_eq_norm,← smul_sub,norm_smul,Real.norm_eq_abs,
        abs_of_nonneg (by linarith [t.property.2]),dist_eq_norm]
    rw [hdcalc]
    have := dist_nonneg (x := x) (y := y)
    have := t.property.1
    nlinarith
  refine ⟨U,Metric.isOpen_thickening,(Metric.thickening_mono hδε A).trans hεV,hAU,r,?_,⟨?_⟩,fun he ↦ (hA he).elim⟩
  · intro a
    exact Subtype.ext (hfix a.val a.property)
  refine {
    toFun := fun p ↦ ⟨(1-(p.1:ℝ)) • p.2.val + (p.1:ℝ) • R p.2.val,hstay p.1 p.2.val p.2.property⟩
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (hR.comp (continuous_subtype_val.comp continuous_snd)))).subtype_mk _
  · intro x; apply Subtype.ext; simp
  · intro x; apply Subtype.ext; simp [r]
  · intro t x hx
    apply Subtype.ext
    change (1-(t:ℝ)) • x.val + (t:ℝ) • R x.val = x.val
    rw [hfix x.val hx,← add_smul,sub_add_cancel,one_smul]

end
end HolomorphicAnosov.Cubical
