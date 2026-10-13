import HolomorphicAnosov.Topology.CairnsBoundedComponentDiskExtension
import HolomorphicAnosov.Topology.JordanComplementTwoRegions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto

/-!
# Ambient extension of a bounded Jordan component

Source: Cairns, *An Elementary Proof of the Jordan-Schoenflies Theorem* (1951),
main theorem p.860, Theorem 4.1 pp.864–865 and final construction pp.866–867.
The inversion and boundary-fixed recentering below explicitly fill the elementary
ambient-extension step left implicit by the source's familiar extension argument.
-/

open Set Metric Topology _root_.Topology
namespace HolomorphicAnosov

/-- For an interior point `w`, the map `x ↦ x + (1 - ‖x‖) • w` is a self-homeomorphism
of the closed unit disk, fixes the circle pointwise, and preserves the open disk.

Agent-written proof of the elementary recentering step omitted in Cairns's final ambient
extension. For each target `y`, the inverse equation is the fixed-point equation for
`x ↦ y - (1 - ‖x‖) • w`. The reverse triangle inequality makes this a contraction of the
complete plane with constant `‖w‖ < 1`. The Banach fixed-point theorem supplies existence and
uniqueness, hence global bijectivity. The triangle inequality proves that the closed disk
maps into itself. Applied to the inverse equation, the same inequality rules out an inverse
point of norm greater than one for a target of norm at most one. Thus the restriction is a
continuous bijection of the compact disk and is a homeomorphism. Its formula fixes all norm-one
points. A strict triangle bound preserves norm less than one; boundary fixing gives the converse.
-/
private theorem diskRecenter_exists (w : ℂ) (hw : ‖w‖ < 1) :
    ∃ T : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1,
      (∀ x, (T x : ℂ) = (x : ℂ) + (1 - ‖(x : ℂ)‖) • w) ∧
      (∀ x : closedBall (0 : ℂ) 1, ‖(x : ℂ)‖ = 1 → T x = x) ∧
      (∀ x, ‖(T x : ℂ)‖ < 1 ↔ ‖(x : ℂ)‖ < 1) := by
  let t : ℂ → ℂ := fun x ↦ x + (1 - ‖x‖) • w
  have hc (y : ℂ) : ContractingWith ‖w‖₊ (fun x : ℂ ↦ y - (1 - ‖x‖) • w) := by
    refine ⟨hw, LipschitzWith.of_dist_le_mul fun x z ↦ ?_⟩
    rw [dist_eq_norm]
    have he : (y - (1 - ‖x‖) • w) - (y - (1 - ‖z‖) • w) =
        (‖x‖ - ‖z‖) • w := by module
    rw [he, norm_smul, Real.norm_eq_abs]
    simpa [mul_comm, dist_eq_norm] using
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le x z) (norm_nonneg w)
  have hinj : Function.Injective t := by
    intro x z h
    apply (hc (t x)).fixedPoint_unique'
    · change t x - (1 - ‖x‖) • w = x
      simp [t]
    · change t x - (1 - ‖z‖) • w = z
      rw [h]
      simp [t]
  have hsurj : Function.Surjective t := by
    intro y
    let x := ContractingWith.fixedPoint _ (hc y)
    have hx := (hc y).fixedPoint_isFixedPt
    refine ⟨x, ?_⟩
    change y - (1 - ‖x‖) • w = x at hx
    dsimp [t]
    exact (sub_eq_iff_eq_add.mp hx).symm
  have hmap (x : ℂ) (hx : ‖x‖ ≤ 1) : ‖t x‖ ≤ 1 := by
    have hn := norm_add_le x ((1 - ‖x‖) • w)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hx)] at hn
    change ‖x + (1 - ‖x‖) • w‖ ≤ 1
    nlinarith [norm_nonneg x]
  have hpre (x : ℂ) (hx : ‖t x‖ ≤ 1) : ‖x‖ ≤ 1 := by
    by_contra hn
    have hxn : 1 < ‖x‖ := lt_of_not_ge hn
    have he : x = t x - (1 - ‖x‖) • w := by simp [t]
    have hnorm := norm_sub_le (t x) ((1 - ‖x‖) • w)
    rw [← he, norm_smul, Real.norm_eq_abs, abs_of_neg (sub_neg.mpr hxn)] at hnorm
    nlinarith
  let f : closedBall (0 : ℂ) 1 → closedBall (0 : ℂ) 1 := fun x ↦
    ⟨t x, by
      simpa only [mem_closedBall, dist_zero_right] using
        hmap x (by simpa only [mem_closedBall, dist_zero_right] using x.property)⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro x z h
      exact Subtype.ext (hinj (congrArg Subtype.val h))
    · intro y
      obtain ⟨x, hx⟩ := hsurj y
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      simpa only [mem_closedBall, dist_zero_right] using
        hpre x (by simpa only [hx, mem_closedBall, dist_zero_right] using y.property)
  let e := Equiv.ofBijective f hbij
  have hcont : Continuous e := by
    change Continuous f
    dsimp [f, t]
    fun_prop
  let T : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1 :=
    hcont.homeoOfEquivCompactToT2
  have hformula (x) : (T x : ℂ) = (x : ℂ) + (1 - ‖(x : ℂ)‖) • w := rfl
  have hfix (x : closedBall (0 : ℂ) 1) (hx : ‖(x : ℂ)‖ = 1) : T x = x := by
    apply Subtype.ext
    simp [hformula, hx]
  refine ⟨T, hformula, hfix, ?_⟩
  intro x
  constructor
  · intro hx
    have hle : ‖(x : ℂ)‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using x.property
    rcases hle.eq_or_lt with he | he
    · rw [hfix x he] at hx
      exact (lt_irrefl 1 (he ▸ hx)).elim
    · exact he
  · intro hx
    have hn := norm_add_le (x : ℂ) ((1 - ‖(x : ℂ)‖) • w)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hx)] at hn
    rw [hformula]
    nlinarith

/-- Move a prescribed interior point to zero without changing any point of the boundary.

This is the inverse of `diskRecenter_exists`: the formula sends zero to `w`, so its inverse
sends `w` to zero. Boundary fixing and preservation of the interior pass to the inverse by
bijectivity. This form is the one used to normalize the inverted exterior chart.
-/
private theorem diskRecenter_to_zero (w : closedBall (0 : ℂ) 1) (hw : ‖(w : ℂ)‖ < 1) :
    ∃ R : closedBall (0 : ℂ) 1 ≃ₜ closedBall (0 : ℂ) 1,
      R w = ⟨0, by simp⟩ ∧
      (∀ x : closedBall (0 : ℂ) 1, ‖(x : ℂ)‖ = 1 → R x = x) ∧
      (∀ x, ‖(R x : ℂ)‖ < 1 ↔ ‖(x : ℂ)‖ < 1) := by
  obtain ⟨T, hT, hfix, hint⟩ := diskRecenter_exists w hw
  refine ⟨T.symm, ?_, ?_, ?_⟩
  · apply T.injective
    rw [T.apply_symm_apply]
    apply Subtype.ext
    simp [hT]
  · intro x hx
    apply T.injective
    rw [T.apply_symm_apply, hfix x hx]
  · intro x
    simpa only [T.apply_symm_apply] using (hint (T.symm x)).symm

/-- A given bounded component has Cairns's bounded-region data, and the complement of its
closure has the exterior-region data.

Source: Cairns (1951), final §5, pp.866–867, two complementary regions. The actual supplier lists
exactly two component sets `U,V`, of which only `U` is bounded. A witness defining `Q` as a
component must belong to the curve complement, because `Q` is nonempty. Hence `Q` is one of
`U,V`; boundedness excludes `V`. The supplier's disjoint partition and formula
`closure Q = Q ∪ curve` identify `V` with `(closure Q)ᶜ`. All openness, connectivity and frontier
claims then transfer directly. Finally `closure V = V ∪ frontier V = V ∪ curve = Qᶜ` by the
same disjoint partition. No assertion that an arbitrary open set is regular open is used.
-/
private theorem cairns_bounded_component_region_data
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (Q : Set ℂ) (hQne : Q.Nonempty)
    (hQcomponent : ∃ z : ℂ, Q = connectedComponentIn (range γ)ᶜ z)
    (hQbounded : Bornology.IsBounded Q) :
    IsConnected Q ∧ IsOpen Q ∧ frontier Q = range γ ∧ closure Q = Q ∪ range γ ∧
      IsConnected (closure Q)ᶜ ∧ IsOpen (closure Q)ᶜ ∧
      ¬Bornology.IsBounded (closure Q)ᶜ ∧ frontier (closure Q)ᶜ = range γ ∧
      closure (closure Q)ᶜ = Qᶜ := by
  obtain ⟨U, V, hUne, hVne, hUV, hunion, hdisj, hcomponents,
    hUc, hVc, hUo, hVo, hUb, hVb, hUf, hVf, hUcl⟩ :=
    cairns_jordan_complement_two_regions γ hγ
  obtain ⟨z, hzQ⟩ := hQcomponent
  have hz : z ∈ (range γ)ᶜ := by
    by_contra hz
    rw [hzQ, connectedComponentIn_eq_empty hz] at hQne
    exact Set.not_nonempty_empty hQne
  have hmem : Q ∈ ({U, V} : Set (Set ℂ)) := by
    rw [← hcomponents]
    exact ⟨z, hz, hzQ.symm⟩
  have hQU : Q = U := by
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exact h
    · have hQV : Q = V := Set.mem_singleton_iff.mp h
      exact False.elim (hVb (hQV ▸ hQbounded))
  subst U
  have hV : V = (closure Q)ᶜ := by
    rw [hUcl]
    ext x
    have hu := Set.ext_iff.mp hunion x
    have hd := Set.disjoint_left.mp hdisj
    simp only [mem_union, mem_compl_iff] at hu ⊢
    constructor
    · intro hx
      exact fun hh ↦ hh.elim (fun hqx ↦ hd hqx hx) (fun hcx ↦ (hu.mp (Or.inr hx)) hcx)
    · intro hx
      have hc : x ∉ range γ := fun hc ↦ hx (Or.inr hc)
      exact (hu.mpr hc).resolve_left (fun hq ↦ hx (Or.inl hq))
  subst V
  refine ⟨hUc, hUo, hUf, hUcl, hVc, hVo, hVb, hVf, ?_⟩
  rw [closure_eq_self_union_frontier, hVf]
  ext x
  have hu := Set.ext_iff.mp hunion x
  have hd : x ∈ Q → x ∈ (closure Q)ᶜ → False := (Set.disjoint_left.mp hdisj) (a := x)
  simp only [mem_union, mem_compl_iff] at hu ⊢
  tauto



/-- Elementary inversion geometry for the exterior of a bounded open set. Agent-written
expansion of the omitted exterior step in Cairns (1951), final §5.

Write `I(z)=(z-a)⁻¹`, `E=(closure Q)ᶜ`, and `B={0}∪I(E)`. At a nonzero point `z`, membership
in `B` is equivalent to `a+z⁻¹∈E`, by the inverse equations. Choose `R>0` with
`closure Q⊆ball a R`; then `ball 0 R⁻¹⊆B`, because a nonzero point in this ball has inverse
at distance greater than `R` from `a`. This proves openness at zero. At other points the
membership criterion and continuity of inversion prove openness. The continuous image `I(E)`
is connected. Every neighborhood of zero meets that image: choose a positive real number
smaller than both its radius and `R⁻¹`. Thus adjoining zero preserves connectivity. Finally,
choose `δ>0` with `ball a δ⊆Q`. Points of `E` have distance at least `δ` from `a`, so their
inverses have norm at most `δ⁻¹`, proving boundedness. -/
private theorem invertedExterior_geometry
    (Q : Set ℂ) (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (a : ℂ) (ha : a ∈ Q) (hEc : IsConnected (closure Q)ᶜ) :
    let I : ℂ → ℂ := fun z ↦ (z - a)⁻¹
    let B := insert 0 (I '' (closure Q)ᶜ)
    IsOpen B ∧ IsConnected B ∧ Bornology.IsBounded B ∧
      (∀ z : ℂ, z ≠ 0 → (z ∈ B ↔ a + z⁻¹ ∈ (closure Q)ᶜ)) := by
  let I : ℂ → ℂ := fun z ↦ (z - a)⁻¹
  let B := insert 0 (I '' (closure Q)ᶜ)
  change IsOpen B ∧ IsConnected B ∧ Bornology.IsBounded B ∧ _
  have haE : a ∉ (closure Q)ᶜ := fun h ↦ h (subset_closure ha)
  have hmem (z : ℂ) (hz : z ≠ 0) : z ∈ B ↔ a + z⁻¹ ∈ (closure Q)ᶜ := by
    constructor
    · intro hzB
      rcases hzB with hzB | ⟨x, hx, hix⟩
      · exact (hz hzB).elim
      · rw [← hix]
        simpa [I] using hx
    · intro hx
      apply Set.mem_insert_of_mem
      exact ⟨a + z⁻¹, hx, by simp [I]⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_ball a).mp hQb.closure
  have hRpos : 0 < R := by simpa using hR (subset_closure ha)
  have hball : ball (0 : ℂ) R⁻¹ ⊆ B := by
    intro z hz
    by_cases hz0 : z = 0
    · exact hz0 ▸ Set.mem_insert 0 _
    apply (hmem z hz0).mpr
    intro hzc
    have hnorm : ‖z‖ < R⁻¹ := by simpa only [mem_ball, dist_zero_right] using hz
    have hlarge : R < ‖z‖⁻¹ := by
      have hh := (inv_lt_inv₀ (inv_pos.mpr hRpos) (norm_pos_iff.mpr hz0)).mpr hnorm
      simpa only [inv_inv] using hh
    have hsmall := hR hzc
    simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_inv] at hsmall
    exact (not_lt_of_ge hlarge.le) hsmall
  have hBo : IsOpen B := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    by_cases hz0 : z = 0
    · subst z
      exact Metric.mem_nhds_iff.mpr ⟨R⁻¹, inv_pos.mpr hRpos, hball⟩
    · have hcont : ContinuousAt (fun z : ℂ ↦ a + z⁻¹) z :=
        continuousAt_const.add (continuousAt_inv₀ hz0)
      have he := hcont.preimage_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds
        ((hmem z hz0).mp hz))
      have hn : {z : ℂ | z ≠ 0} ∈ 𝓝 z :=
        isClosed_singleton.isOpen_compl.mem_nhds hz0
      filter_upwards [he, hn] with w hw hw0 using (hmem w hw0).mpr hw
  have hIc : IsConnected (I '' (closure Q)ᶜ) := by
    apply hEc.image I
    intro z hz
    have hz_ne : z - a ≠ 0 := sub_ne_zero.mpr (fun h ↦ haE (h ▸ hz))
    exact ((continuousAt_id.sub (continuousAt_const (y := a))).inv₀ hz_ne).continuousWithinAt
  have hzero : (0 : ℂ) ∈ closure (I '' (closure Q)ᶜ) := by
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    let r : ℝ := min ε R⁻¹ / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrε : r < ε := by dsimp [r]; linarith [min_le_left ε R⁻¹]
    have hrR : r < R⁻¹ := by dsimp [r]; linarith [min_le_right ε R⁻¹, inv_pos.mpr hRpos]
    have hb : (r : ℂ) ∈ B := hball (by simpa [mem_ball, abs_of_pos hr] using hrR)
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have himg : (r : ℂ) ∈ I '' (closure Q)ᶜ := (Set.mem_insert_iff.mp hb).resolve_left hr0
    exact ⟨r, himg, by simpa [dist_zero_left, abs_of_pos hr] using hrε⟩
  have hBc : IsConnected B := hIc.subset_closure (Set.subset_insert _ _)
    (Set.insert_subset_iff.mpr ⟨hzero, subset_closure⟩)
  obtain ⟨δ, hδ, hδQ⟩ := Metric.isOpen_iff.mp hQo a ha
  have hBb : Bornology.IsBounded B := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨δ⁻¹, ?_⟩
    intro z hz
    rcases hz with rfl | ⟨x, hx, rfl⟩
    · simpa using (inv_pos.mpr hδ).le
    · have hδx : δ ≤ ‖x - a‖ := by
        by_contra h
        exact hx (subset_closure (hδQ (by simpa [mem_ball, dist_eq_norm] using lt_of_not_ge h)))
      dsimp [I]
      rw [norm_inv]
      exact (inv_le_inv₀ (hδ.trans_le hδx) hδ).mpr hδx
  exact ⟨hBo, hBc, hBb, hmem⟩

/-- The inverted exterior with zero adjoined is precisely the component containing zero of
the transformed curve's complement. Agent-written elementary expansion of Cairns's exterior
construction; it does not invoke the Jordan theorem on the transformed curve.

Inversion is continuous and injective on the original compact curve, since `a∈Q` is off that
curve. Thus the transformed curve is embedded. A nonzero point lies on it exactly when its
inverse under `z↦a+z⁻¹` lies on the original curve. The two disjoint open sets
`B={0}∪I(E)` and `A={z≠0 | a+z⁻¹∈Q}` therefore partition its complement, using
`closure Q=Q∪curve`. The preceding lemma makes `B` connected and it contains zero. Hence it
is contained in the component at zero. Conversely a connected component cannot meet both
members of a disjoint open partition; its intersection with `B` contains zero, so it lies in
`B`. Both inclusions give the exact component equality. -/
private theorem invertedExterior_component
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (Q : Set ℂ) (hQo : IsOpen Q) (hQb : Bornology.IsBounded Q)
    (hQc : Q ⊆ (range γ)ᶜ) (hQcl : closure Q = Q ∪ range γ)
    (a : ℂ) (ha : a ∈ Q) (hEc : IsConnected (closure Q)ᶜ) :
    let I : ℂ → ℂ := fun z ↦ (z - a)⁻¹
    let B := insert 0 (I '' (closure Q)ᶜ)
    Topology.IsEmbedding (I ∘ γ) ∧
      B = connectedComponentIn (range (I ∘ γ))ᶜ 0 := by
  let I : ℂ → ℂ := fun z ↦ (z - a)⁻¹
  let B := insert 0 (I '' (closure Q)ᶜ)
  let A := {z : ℂ | z ≠ 0 ∧ a + z⁻¹ ∈ Q}
  have haC : a ∉ range γ := hQc ha
  obtain ⟨hBo, hBc, hBb, hmem⟩ := invertedExterior_geometry Q hQo hQb a ha hEc
  have hγa (t : Circle) : γ t - a ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    exact haC ⟨t, h⟩
  have hcont : Continuous (I ∘ γ) := by
    exact (hγ.continuous.sub continuous_const).inv₀ hγa
  have hinj : Function.Injective (I ∘ γ) := by
    intro s t h
    apply hγ.injective
    have hh : γ s - a = γ t - a := inv_injective h
    exact sub_left_inj.mp hh
  have hemb : Topology.IsEmbedding (I ∘ γ) := (hcont.isClosedEmbedding hinj).isEmbedding
  have hzero : (0 : ℂ) ∉ range (I ∘ γ) := by
    rintro ⟨t, ht⟩
    exact hγa t (inv_eq_zero.mp ht)
  have hcurve (z : ℂ) (hz : z ≠ 0) :
      z ∈ range (I ∘ γ) ↔ a + z⁻¹ ∈ range γ := by
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, by simp [I]⟩
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      simp [I, ht]
  have hAo : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hcont : ContinuousAt (fun z : ℂ ↦ a + z⁻¹) z :=
      continuousAt_const.add (continuousAt_inv₀ hz.1)
    have he := hcont.preimage_mem_nhds (hQo.mem_nhds hz.2)
    have hn : {z : ℂ | z ≠ 0} ∈ 𝓝 z := isClosed_singleton.isOpen_compl.mem_nhds hz.1
    filter_upwards [hn, he] with w hw0 hw using ⟨hw0, hw⟩
  have hpartition : B ∪ A = (range (I ∘ γ))ᶜ := by
    ext z
    by_cases hz : z = 0
    · subst z
      simp [B, hzero]
    have hc := hcurve z hz
    have hd : a + z⁻¹ ∈ Q → a + z⁻¹ ∉ range γ := fun h ↦ hQc h
    simp only [mem_union, mem_compl_iff]
    rw [hmem z hz]
    change (a + z⁻¹ ∉ closure Q ∨ (z ≠ 0 ∧ a + z⁻¹ ∈ Q)) ↔ _
    rw [hQcl]
    simp only [mem_union]
    tauto
  have hdisj : Disjoint B A := by
    apply Set.disjoint_left.mpr
    intro z hzB hzA
    exact ((hmem z hzA.1).mp hzB) (subset_closure hzA.2)
  have hzeroB : (0 : ℂ) ∈ B := Set.mem_insert 0 _
  refine ⟨hemb, Set.Subset.antisymm ?_ ?_⟩
  · exact hBc.isPreconnected.subset_connectedComponentIn hzeroB
      (hpartition ▸ Set.subset_union_left)
  · apply IsPreconnected.subset_left_of_subset_union hBo hAo hdisj
    · rw [hpartition]
      exact connectedComponentIn_subset _ _
    · exact ⟨0, mem_connectedComponentIn hzero, hzeroB⟩
    · exact isPreconnected_connectedComponentIn

/-- Turn a centered chart on the inverted closed region into a closed exterior chart.
Agent-written expansion of the exterior formula in the Cairns ambient argument.

On `S`, define `G(z)=F((z-a)⁻¹)⁻¹`. The inner point is nonzero, and injectivity of `F` and
`F(0)=0` keep its image nonzero. Its norm is at most one, so the outer inverse has norm at
least one. For `y` in the closed exterior use the inverse formula
`a+(F.symm(y⁻¹))⁻¹`. Its intermediate point is nonzero by `F(0)=0`, and the supplied inverse
membership criterion puts it in `S`. Inversion identities and the inverse equations for `F`
give both composite identities. Each formula is continuous because all denominators on the
corresponding domains are nonzero. These maps form the claimed homeomorphism. -/
private theorem exteriorChart_of_centered_diskChart
    (S C : Set ℂ) (a : ℂ) (haS : a ∉ S) (h0C : (0 : ℂ) ∈ C)
    (hmem : ∀ z : ℂ, z ≠ a → ((z - a)⁻¹ ∈ C ↔ z ∈ S))
    (F : C ≃ₜ closedBall (0 : ℂ) 1) (hF0 : (F ⟨0, h0C⟩ : ℂ) = 0) :
    ∃ G : S ≃ₜ {z : ℂ | 1 ≤ ‖z‖}, ∀ z : S,
      (G z : ℂ) = (F ⟨((z : ℂ) - a)⁻¹,
        (hmem z (fun h ↦ haS (h ▸ z.property))).mpr z.property⟩ : ℂ)⁻¹ := by
  have hz_ne (z : S) : (z : ℂ) - a ≠ 0 :=
    sub_ne_zero.mpr (fun h ↦ haS (h ▸ z.property))
  let j : S → C := fun z ↦ ⟨((z : ℂ) - a)⁻¹,
    (hmem z (sub_ne_zero.mp (hz_ne z))).mpr z.property⟩
  have hjc : Continuous j := by
    exact ((continuous_subtype_val.sub continuous_const).inv₀ hz_ne).subtype_mk _
  have hj0 (z : S) : (j z : ℂ) ≠ 0 := inv_ne_zero (hz_ne z)
  have hFzero (z : C) : (F z : ℂ) = 0 ↔ (z : ℂ) = 0 := by
    constructor
    · intro hz
      have hh : F z = F ⟨0, h0C⟩ := Subtype.ext (hz.trans hF0.symm)
      exact congrArg Subtype.val (F.injective hh)
    · intro hz
      have hh : z = ⟨0, h0C⟩ := Subtype.ext hz
      simpa only [hh] using hF0
  have hfj0 (z : S) : (F (j z) : ℂ) ≠ 0 := fun h ↦ hj0 z ((hFzero _).mp h)
  let f : S → {z : ℂ | 1 ≤ ‖z‖} := fun z ↦ ⟨(F (j z) : ℂ)⁻¹, by
    change 1 ≤ ‖(F (j z) : ℂ)⁻¹‖
    rw [norm_inv]
    have hle : ‖(F (j z) : ℂ)‖ ≤ 1 := by
      simpa only [mem_closedBall, dist_zero_right] using (F (j z)).property
    simpa only [inv_one] using
      (inv_le_inv₀ zero_lt_one (norm_pos_iff.mpr (hfj0 z))).mpr hle⟩
  have hfc : Continuous f := by
    exact ((continuous_subtype_val.comp (F.continuous.comp hjc)).inv₀ hfj0).subtype_mk _
  have hy0 (y : {z : ℂ | 1 ≤ ‖z‖}) : (y : ℂ) ≠ 0 := by
    intro h
    have hy := y.property
    norm_num [h] at hy
  let b : {z : ℂ | 1 ≤ ‖z‖} → closedBall (0 : ℂ) 1 := fun y ↦ ⟨(y : ℂ)⁻¹, by
    simp only [mem_closedBall, dist_zero_right, norm_inv]
    simpa only [inv_one] using
      (inv_le_inv₀ (norm_pos_iff.mpr (hy0 y)) zero_lt_one).mpr y.property⟩
  have hbc : Continuous b := (continuous_subtype_val.inv₀ hy0).subtype_mk _
  let k : {z : ℂ | 1 ≤ ‖z‖} → C := fun y ↦ F.symm (b y)
  have hkc : Continuous k := F.symm.continuous.comp hbc
  have hk0 (y : {z : ℂ | 1 ≤ ‖z‖}) : (k y : ℂ) ≠ 0 := by
    intro h
    have hf := (hFzero (k y)).mpr h
    change (F (F.symm (b y)) : ℂ) = 0 at hf
    rw [F.apply_symm_apply] at hf
    exact inv_ne_zero (hy0 y) hf
  have hka (y : {z : ℂ | 1 ≤ ‖z‖}) : a + (k y : ℂ)⁻¹ ≠ a := by
    intro h
    exact inv_ne_zero (hk0 y) (add_eq_left.mp h)
  let g : {z : ℂ | 1 ≤ ‖z‖} → S := fun y ↦ ⟨a + (k y : ℂ)⁻¹,
    (hmem _ (hka y)).mp (by simp)⟩
  have hgc : Continuous g := by
    exact (continuous_const.add ((continuous_subtype_val.comp hkc).inv₀ hk0)).subtype_mk _
  have hleft (z : S) : g (f z) = z := by
    have hb : b (f z) = F (j z) := by
      apply Subtype.ext
      exact inv_inv _
    have hk : k (f z) = j z := by
      change F.symm (b (f z)) = j z
      rw [hb, F.symm_apply_apply]
    apply Subtype.ext
    change a + (k (f z) : ℂ)⁻¹ = z
    rw [hk]
    simp [j]
  have hright (y : {z : ℂ | 1 ≤ ‖z‖}) : f (g y) = y := by
    have hj : j (g y) = k y := by
      apply Subtype.ext
      simp [j, g]
    apply Subtype.ext
    change (F (j (g y)) : ℂ)⁻¹ = y
    rw [hj]
    change (F (F.symm (b y)) : ℂ)⁻¹ = y
    rw [F.apply_symm_apply]
    exact inv_inv _
  exact ⟨⟨⟨f, g, hleft, hright⟩, hfc, hgc⟩, fun _ ↦ rfl⟩

/-- Glue compatible inside and outside charts on a closed two-set cover of the plane.
Agent-written elementary pasting step in the Cairns ambient construction.

Define the map by the inside chart on `P` and the outside chart on its complement. Agreement
on `P∩S` makes its restriction to `S` the outside chart. Closed-cover pasting proves continuity.
Both charts are injective, and a point in `S\P` maps to norm strictly greater than one while
points of `P` map to norm at most one; these facts prove global injectivity. Every point is in
the closed disk or the closed exterior, so chart surjectivity proves global surjectivity.
For a closed set `K`, its image is the union of the two chart images of its closed restrictions
to `P` and `S`. Each image is closed in its target region by the homeomorphism, and those target
regions are closed in the plane. The pasted map is therefore closed. A continuous, closed
bijection is a homeomorphism and has the asserted restrictions. -/
theorem glue_disk_exterior_charts
    (P S : Set ℂ) (hPc : IsClosed P) (hSc : IsClosed S) (hcover : P ∪ S = univ)
    (F : P ≃ₜ closedBall (0 : ℂ) 1) (G : S ≃ₜ {z : ℂ | 1 ≤ ‖z‖})
    (hagree : ∀ (x : ℂ) (hxP : x ∈ P) (hxS : x ∈ S),
      (F ⟨x, hxP⟩ : ℂ) = (G ⟨x, hxS⟩ : ℂ))
    (hstrict : ∀ x : S, (x : ℂ) ∉ P → 1 < ‖(G x : ℂ)‖) :
    ∃ H : ℂ ≃ₜ ℂ,
      (∀ x : P, H x = F x) ∧ (∀ x : S, H x = G x) := by
  classical
  have hother (x : ℂ) (hx : x ∉ P) : x ∈ S :=
    ((Set.ext_iff.mp hcover x).mpr (Set.mem_univ x)).resolve_left hx
  let h : ℂ → ℂ := fun x ↦ if hx : x ∈ P then F ⟨x, hx⟩ else G ⟨x, hother x hx⟩
  have hF (x : P) : h x = (F x : ℂ) := by simp [h, x.property]
  have hG (x : S) : h x = (G x : ℂ) := by
    by_cases hx : (x : ℂ) ∈ P
    · simpa only [h, dite_eq_left hx] using hagree x hx x.property
    · simp [h, hx]
  have hcontP : ContinuousOn h P := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp F.continuous using 1
    exact funext hF
  have hcontS : ContinuousOn h S := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert continuous_subtype_val.comp G.continuous using 1
    exact funext hG
  have hcont : Continuous h := by
    rw [← continuousOn_univ, ← hcover]
    exact hcontP.union_of_isClosed hcontS hPc hSc
  have hnorm (x : P) : ‖h x‖ ≤ 1 := by
    rw [hF]
    simpa only [mem_closedBall, dist_zero_right] using (F x).property
  have hinj : Function.Injective h := by
    intro x y heq
    by_cases hx : x ∈ P <;> by_cases hy : y ∈ P
    · have hf : F ⟨x, hx⟩ = F ⟨y, hy⟩ := by
        apply Subtype.ext
        simpa only [← hF] using heq
      exact congrArg Subtype.val (F.injective hf)
    · have hgt := hstrict ⟨y, hother y hy⟩ hy
      have hle := hnorm ⟨x, hx⟩
      rw [heq, hG ⟨y, hother y hy⟩] at hle
      exact False.elim (not_lt_of_ge hle hgt)
    · have hgt := hstrict ⟨x, hother x hx⟩ hx
      have hle := hnorm ⟨y, hy⟩
      rw [← heq, hG ⟨x, hother x hx⟩] at hle
      exact False.elim (not_lt_of_ge hle hgt)
    · have hg : G ⟨x, hother x hx⟩ = G ⟨y, hother y hy⟩ := by
        apply Subtype.ext
        simpa only [← hG] using heq
      exact congrArg Subtype.val (G.injective hg)
  have hsurj : Function.Surjective h := by
    intro y
    by_cases hy : ‖y‖ ≤ 1
    · let y' : closedBall (0 : ℂ) 1 := ⟨y, by simpa using hy⟩
      refine ⟨F.symm y', ?_⟩
      rw [hF, F.apply_symm_apply]
    · let y' : {z : ℂ | 1 ≤ ‖z‖} := ⟨y, (lt_of_not_ge hy).le⟩
      refine ⟨G.symm y', ?_⟩
      rw [hG, G.apply_symm_apply]
  have hclosed : IsClosedMap h := by
    intro K hK
    let KP : Set P := Subtype.val ⁻¹' K
    let KS : Set S := Subtype.val ⁻¹' K
    have hKP : IsClosed KP := hK.preimage continuous_subtype_val
    have hKS : IsClosed KS := hK.preimage continuous_subtype_val
    have hFP : IsClosed ((fun x : P ↦ (F x : ℂ)) '' KP) :=
      (isClosed_closedBall.isClosedMap_subtype_val.comp F.isClosedMap) KP hKP
    have hext : IsClosed {z : ℂ | 1 ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
    have hGS : IsClosed ((fun x : S ↦ (G x : ℂ)) '' KS) :=
      (hext.isClosedMap_subtype_val.comp G.isClosedMap) KS hKS
    have himage : h '' K = ((fun x : P ↦ (F x : ℂ)) '' KP) ∪
        ((fun x : S ↦ (G x : ℂ)) '' KS) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        by_cases hxP : x ∈ P
        · exact Or.inl ⟨⟨x, hxP⟩, hx, (hF ⟨x, hxP⟩).symm⟩
        · exact Or.inr ⟨⟨x, hother x hxP⟩, hx, (hG ⟨x, hother x hxP⟩).symm⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ⟨x, hx, hF x⟩
        · exact ⟨x, hx, hG x⟩
    rw [himage]
    exact hFP.union hGS
  have hh : IsHomeomorph h := isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨hcont, hclosed, hinj, hsurj⟩
  exact ⟨hh.homeomorph h, hF, hG⟩

/-- Assemble the ambient extension from the exact bounded-component disk-extension contract.

Agent-written expansion of the omitted exterior construction in Cairns (1951), final §5.
Choose `a∈Q`. Invert the exterior about `a`, add zero, and use the private inversion lemmas to
identify this bounded connected open set as the component at zero of the transformed embedded
curve. Apply the supplied disk-extension theorem to the original bounded component and to
this transformed component. Use the inverse original curve parametrization for the inside
boundary values, and its circle inverse on the transformed curve for the second boundary map.
Normalize the second chart at zero with the boundary-fixed disk recentering homeomorphism.
Its closed-region inversion membership criterion follows from the two closure formulas and
the partition into the original interior, curve and exterior. The exterior-chart construction
therefore applies. On a curve point both charts evaluate to its original circle parameter:
the two circle inversions cancel and recentering fixes the boundary. Points strictly outside
the original closure map to norm greater than one because the normalized chart preserves the
open disk. The closed-chart gluing lemma gives the global homeomorphism. Its two restrictions,
the original disk-image identity, and the exterior chart's surjectivity give exactly the three
asserted image equalities. The disk-extension contract here is an ordinary argument, instantiated
with `cairns_bounded_component_disk_extension` in the public theorem below. -/
private theorem ambient_of_disk_extension_contract
    (hex : ∀ (γ : Circle → ℂ), Topology.IsEmbedding γ →
      ∀ (Q : Set ℂ), Q.Nonempty →
      (∃ z : ℂ, Q = connectedComponentIn (range γ)ᶜ z) → Bornology.IsBounded Q →
      ∀ h : range γ ≃ₜ Circle,
      frontier Q = range γ ∧ closure Q = Q ∪ range γ ∧
      ∃ F : closure Q ≃ₜ closedBall (0 : ℂ) 1,
        (∀ (z : closure Q) (hz : (z : ℂ) ∈ range γ),
          (F z : ℂ) = (h ⟨z, hz⟩ : ℂ)) ∧
        (fun z : closure Q ↦ (F z : ℂ)) '' {z | (z : ℂ) ∈ Q} = ball (0 : ℂ) 1)
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (Q : Set ℂ) (hQne : Q.Nonempty)
    (hQcomponent : ∃ z : ℂ, Q = connectedComponentIn (range γ)ᶜ z)
    (hQbounded : Bornology.IsBounded Q) (hQo : IsOpen Q)
    (hQc : Q ⊆ (range γ)ᶜ) (hQcl : closure Q = Q ∪ range γ)
    (hEc : IsConnected (closure Q)ᶜ) :
    ∃ H : ℂ ≃ₜ ℂ, H '' range γ = sphere (0 : ℂ) 1 ∧
      H '' Q = ball (0 : ℂ) 1 ∧ H '' (closure Q)ᶜ = {z : ℂ | 1 < ‖z‖} := by
  classical
  obtain ⟨a, ha⟩ := hQne
  let I : ℂ → ℂ := fun z ↦ (z - a)⁻¹
  let B := insert 0 (I '' (closure Q)ᶜ)
  let γ' := I ∘ γ
  obtain ⟨hBo, hBc, hBb, hBm⟩ := invertedExterior_geometry Q hQo hQbounded a ha hEc
  obtain ⟨hγ', hBcomp⟩ :=
    invertedExterior_component γ hγ Q hQo hQbounded hQc hQcl a ha hEc
  have h0B : (0 : ℂ) ∈ B := Set.mem_insert 0 _
  let h : range γ ≃ₜ Circle := hγ.toHomeomorph.symm
  let k : range γ' ≃ₜ Circle := hγ'.toHomeomorph.symm.trans (Homeomorph.inv Circle)
  obtain ⟨_, _, F, hFbd, hFint⟩ := hex γ hγ Q ⟨a, ha⟩ hQcomponent hQbounded h
  obtain ⟨_, hBcl, g, hgbd, hgint⟩ := hex γ' hγ' B ⟨0, h0B⟩ ⟨0, hBcomp⟩ hBb k
  let z0 : closure B := ⟨0, subset_closure h0B⟩
  have hw : ‖(g z0 : ℂ)‖ < 1 := by
    have hh : (g z0 : ℂ) ∈ ball (0 : ℂ) 1 := by
      rw [← hgint]
      exact ⟨z0, h0B, rfl⟩
    simpa only [mem_ball, dist_zero_right] using hh
  obtain ⟨R, hR0, hRbd, hRint⟩ := diskRecenter_to_zero (g z0) hw
  let g0 := g.trans R
  have hg00 : (g0 z0 : ℂ) = 0 := congrArg Subtype.val hR0
  have hg0int (z : closure B) : ‖(g0 z : ℂ)‖ < 1 ↔ (z : ℂ) ∈ B := by
    change ‖(R (g z) : ℂ)‖ < 1 ↔ _
    rw [hRint]
    constructor
    · intro hz
      have hh : (g z : ℂ) ∈ ball (0 : ℂ) 1 := by simpa using hz
      rw [← hgint] at hh
      obtain ⟨w, hwB, hwz⟩ := hh
      have he : w = z := g.injective (Subtype.ext hwz)
      simpa only [he, mem_ofPred_eq] using hwB
    · intro hz
      have hh : (g z : ℂ) ∈ ball (0 : ℂ) 1 := by
        rw [← hgint]
        exact ⟨z, hz, rfl⟩
      simpa only [mem_ball, dist_zero_right] using hh
  have hgamma_mem (z : ℂ) (hz : z ≠ a) : I z ∈ range γ' ↔ z ∈ range γ := by
    constructor
    · rintro ⟨t, ht⟩
      refine ⟨t, ?_⟩
      exact sub_left_inj.mp (inv_injective ht)
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
  have hclosuremem (z : ℂ) (hz : z ≠ a) : I z ∈ closure B ↔ z ∈ Qᶜ := by
    rw [hBcl, mem_union, hBm _ (inv_ne_zero (sub_ne_zero.mpr hz)), hgamma_mem z hz]
    have hi : a + (I z)⁻¹ = z := by simp [I]
    rw [hi, hQcl]
    have hd : z ∈ Q → z ∉ range γ := fun hq ↦ hQc hq
    simp only [mem_compl_iff, mem_union]
    tauto
  obtain ⟨G, hG⟩ := exteriorChart_of_centered_diskChart Qᶜ (closure B) a
    (not_not.mpr ha) (subset_closure h0B) hclosuremem g0 hg00
  have hCmem (t : Circle) : γ t ∈ closure Q := by
    rw [hQcl]
    exact Or.inr ⟨t, rfl⟩
  have hCnotQ (t : Circle) : γ t ∉ Q := fun ht ↦ hQc ht ⟨t, rfl⟩
  have hFcircle (t : Circle) : (F ⟨γ t, hCmem t⟩ : ℂ) = t := by
    rw [hFbd _ ⟨t, rfl⟩]
    exact congrArg (fun c : Circle ↦ (c : ℂ)) (hγ.toHomeomorph_symm_apply t)
  have hGcircle (t : Circle) : (G ⟨γ t, hCnotQ t⟩ : ℂ) = t := by
    rw [hG]
    have hgval : (g ⟨I (γ t), (hclosuremem (γ t) (fun he ↦ hCnotQ t (he.symm ▸ ha))).mpr
        (hCnotQ t)⟩ : ℂ) = (t : ℂ)⁻¹ := by
      rw [hgbd _ ⟨t, rfl⟩]
      change ((hγ'.toHomeomorph.symm ⟨γ' t, _⟩ : Circle) : ℂ)⁻¹ = (t : ℂ)⁻¹
      rw [hγ'.toHomeomorph_symm_apply]
    have hgnorm : ‖(g ⟨I (γ t), (hclosuremem (γ t) (fun he ↦ hCnotQ t (he.symm ▸ ha))).mpr
        (hCnotQ t)⟩ : ℂ)‖ = 1 := by rw [hgval]; simp
    change (R (g _) : ℂ)⁻¹ = t
    rw [hRbd _ hgnorm, hgval, inv_inv]
  have hagree (x : ℂ) (hxP : x ∈ closure Q) (hxS : x ∈ Qᶜ) :
      (F ⟨x, hxP⟩ : ℂ) = (G ⟨x, hxS⟩ : ℂ) := by
    rw [hQcl] at hxP
    obtain ⟨t, rfl⟩ := hxP.resolve_left hxS
    exact (hFcircle t).trans (hGcircle t).symm
  have hstrict (x : ↥(Qᶜ)) (hx : (x : ℂ) ∉ closure Q) : 1 < ‖(G x : ℂ)‖ := by
    rw [hG, norm_inv]
    let u : closure B := ⟨I x, (hclosuremem (x : ℂ) (fun he ↦ x.property (he.symm ▸ ha))).mpr x.property⟩
    have huB : (u : ℂ) ∈ B := Set.mem_insert_of_mem _ ⟨x, hx, rfl⟩
    have hlt := (hg0int u).mpr huB
    have hunz : (u : ℂ) ≠ 0 := inv_ne_zero (sub_ne_zero.mpr (fun he ↦ x.property (he.symm ▸ ha)))
    have hgunz : (g0 u : ℂ) ≠ 0 := by
      intro hzero
      have he : g0 u = g0 z0 := Subtype.ext (hzero.trans hg00.symm)
      exact hunz (congrArg Subtype.val (g0.injective he))
    simpa only [inv_one] using
      (inv_lt_inv₀ zero_lt_one (norm_pos_iff.mpr hgunz)).mpr hlt
  have hcover : closure Q ∪ Qᶜ = univ := by
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ Q
    · exact Or.inl (subset_closure hx)
    · exact Or.inr hx
  obtain ⟨H, hHF, hHG⟩ := glue_disk_exterior_charts (closure Q) Qᶜ isClosed_closure
    hQo.isClosed_compl hcover F G hagree hstrict
  refine ⟨H, ?_, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, ⟨t, rfl⟩, rfl⟩
      rw [hHF ⟨γ t, hCmem t⟩, hFcircle]
      exact t.property
    · intro hy
      let t : Circle := ⟨y, hy⟩
      exact ⟨γ t, ⟨t, rfl⟩, (hHF ⟨γ t, hCmem t⟩).trans (hFcircle t)⟩
  · rw [← hFint]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, subset_closure hx⟩, hx, (hHF ⟨x, subset_closure hx⟩).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, hHF x⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxQ : x ∈ Qᶜ := fun hq ↦ hx (subset_closure hq)
      rw [hHG ⟨x, hxQ⟩]
      exact hstrict ⟨x, hxQ⟩ hx
    · intro hy
      change 1 < ‖y‖ at hy
      let y' : {z : ℂ | 1 ≤ ‖z‖} := ⟨y, hy.le⟩
      let x := G.symm y'
      have hx : (x : ℂ) ∉ closure Q := by
        intro hxP
        have he := hagree x hxP x.property
        have hle : ‖(F ⟨x, hxP⟩ : ℂ)‖ ≤ 1 := by
          simpa only [mem_closedBall, dist_zero_right] using (F ⟨x, hxP⟩).property
        rw [he] at hle
        change ‖(G (G.symm y') : ℂ)‖ ≤ 1 at hle
        rw [G.apply_symm_apply] at hle
        exact not_lt_of_ge hle hy
      refine ⟨x, hx, ?_⟩
      rw [hHG x]
      exact congrArg Subtype.val (G.apply_symm_apply y')


/-- A nonempty bounded complementary component of an embedded circle admits an
ambient plane homeomorphism taking it to the disk and the curve to the circle.

Source: Cairns (1951), Theorem 4.1 and final §5 construction; agent-written expansion
of the omitted exterior extension in the parent Jordan–Schoenflies proof.

Natural-language proof:

1. Use the two-regions theorem to identify the given nonempty bounded component Q with its bounded
region: its only alternative is the unbounded region. Put c=range γ and E=(closure Q) complement.
The region and closure identities identify E with the other component. The inverse of the circle
embedding supplies a boundary homeomorphism c→Circle.

2. Let h:c→S1 be any prescribed homeomorphism. Apply the bounded-component extension child to Q to
get f:closure(Q)→closedD, f|c=h and f(Q)=D. This proves the full boundary-extension clause
immediately from the genuine component theorem. In particular choosing h as the inverse of gamma
supplies one disk chart, but arbitrary h is preserved. To obtain an ambient map rather than only
this inside chart, the remaining steps construct an outside map agreeing with that chosen h.

3. Choose a∈Q and define I(z)=(z−a) inverse, with inverse z=a+w inverse away from zero. The set
B={0}∪I(E), E=(closure Q) complement, is open, bounded and connected: choose R>0 with closure Q
contained in ball(a,R), so ball(0,1/R) is contained in B; away from zero use the inverse membership
formula B(w) iff E(a+1/w). The continuous image I(E) is connected and zero lies in its closure since
every small positive real point in that ball is in I(E). Choose δ>0 with ball(a,δ) contained in Q;
then points of I(E) have norm at most1/δ. The transformed curve is embedded by continuity and
injectivity on its compact circle domain. The sets B and A={w≠0 | a+1/w∈Q} are disjoint ambient-open
sets partitioning the transformed curve complement, using closure Q=Q∪c. Connectedness of B and 0∈B
give B contained in the component at0; preconnectedness of that component and the open disjoint
partition give the reverse containment. Thus B is exactly its nonempty bounded component, without
applying Jordan separation a second time. Apply the existing bounded-component extension child to B
to obtain its frontier and closure formulas and the prescribed disk chart.

4. On the transformed curve prescribe k(I(z))=1/h(z). Circle inversion and the two embedded-curve
parametrizations make k a homeomorphism. The component-extension child gives g:closure B→closedD
with boundary k and g(B)=D. Let w=g(0)∈D. Define T_w(x)=x+(1−||x||)w. For every target y, the
inverse equation x=y−(1−||x||)w is a contraction on the complete plane with constant ||w||<1, by the
reverse triangle inequality. Mathlib's Banach fixed-point theorem supplies a unique solution,
proving global bijectivity. The triangle inequality maps closedD into itself. If ||x||>1 while
||T_w(x)||≤1, the inverse equation gives ||x||≤1+(||x||−1)||w||, a contradiction. Thus inverse
images of closedD lie there too. The restriction is a continuous bijection of compact closedD and
hence a homeomorphism. Its formula fixes the circle and maps0 to w. The strict triangle estimate
maps the interior into itself; boundary fixing gives the converse. Therefore R=T_w inverse fixes the
circle, preserves the interior and sends w to0. Set g0=R composed with g, obtaining g0(0)=0 and the
original boundary k. This fully proved contraction argument is agent-written expansion of the
source's omitted familiar extension, not a second agent-origin child.

5. Use closure B=B∪I(c) and the inversion membership formula to identify inverse points of E∪c with
the nonzero points of closure B. For z in E∪c define fout(z)=g0(I(z)) inverse. Injectivity of g0 and
g0(0)=0 make the denominator nonzero. Its norm is at most1, so fout(z) is in the closed exterior.
For a target y with ||y||≥1, define the inverse a+(g0 inverse(y inverse)) inverse. The intermediate
point is nonzero and the membership formula puts the result in E∪c. The two formulas are inverse by
field inversion and chart inverse identities; each is continuous because the denominators stay
nonzero. Thus fout is a homeomorphism of the closed exterior regions. Its boundary restriction
is1/k(I(z))=h(z), agreeing with f. On E, interior preservation gives the strict norm inequality
||fout(z)||>1, and the inverse chart gives surjectivity onto that open exterior.

6. The two-regions identities give closure E=Q complement, so closure Q and closure E form a closed
cover and meet in c. Define H using f on closure Q and fout elsewhere; agreement on c makes its
restriction to closure E exactly fout. Closed-pair pasting proves continuity. The two charts are
injective, and images of points outside closure Q have norm strictly greater than1 while inside-
chart images have norm at most1; this proves global injectivity. The closed disk and closed exterior
cover the target plane, giving surjectivity. For any closed K, H(K) is the union of the chart images
of the closed restrictions of K to the two source regions. Each is closed in its closed target
region because the charts are homeomorphisms, hence closed in the plane. Thus H is a continuous
closed bijection and therefore a homeomorphism. Its chart restrictions give exactly H(c)=S1, H(Q)=D
and H(E)={||z||>1}. All auxiliary constructions remain private proof steps of this same agent-origin
node.
-/
theorem cairns_bounded_component_ambient_extension
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ)
    (Q : Set ℂ) (hQne : Q.Nonempty)
    (hQcomponent : ∃ z : ℂ, Q = connectedComponentIn (range γ)ᶜ z)
    (hQbounded : Bornology.IsBounded Q) :
    ∃ H : ℂ ≃ₜ ℂ,
      H '' range γ = sphere (0 : ℂ) 1 ∧
      H '' Q = ball (0 : ℂ) 1 ∧
      H '' (closure Q)ᶜ = {z : ℂ | 1 < ‖z‖} := by
  obtain ⟨hQconn, hQo, hQfront, hQcl, hEconn, hEopen, hEunbounded, hEfront, hEcl⟩ :=
    cairns_bounded_component_region_data γ hγ Q hQne hQcomponent hQbounded
  have hQc : Q ⊆ (range γ)ᶜ := by
    obtain ⟨z, rfl⟩ := hQcomponent
    exact connectedComponentIn_subset _ _
  exact ambient_of_disk_extension_contract cairns_bounded_component_disk_extension
    γ hγ Q hQne hQcomponent hQbounded hQo hQc hQcl hEconn

end HolomorphicAnosov
