import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp

noncomputable section
open Bundle Set
namespace HolomorphicAnosov

/-- Two continuous positive, complex-homogeneous fibre lengths on a complex line bundle
are uniformly comparable over a compact base.

Source: Ghys, Holomorphic Anosov systems (1995), Lemma 3.3, printed p.592;
Hatcher, Vector Bundles and K-Theory (2017), Lemma 1.1, p.8. In a nonzero local
frame every vector is a complex scalar multiple of that frame. Thus the ratio of
the two lengths is independent of the nonzero vector. Frame evaluation proves
continuity of this positive ratio on the base, and compactness gives its positive
minimum and finite maximum. At the zero vector homogeneity gives both lengths
zero. On the empty base choose both constants equal to one. -/
theorem compact_complex_line_norm_comparison
    {B : Type*} [TopologicalSpace B] [CompactSpace B] {E : B → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace ℂ E)]
    {J : Type*} (e : J → Trivialization ℂ (π ℂ E))
    [∀ j, (e j).IsLinear ℂ]
    (hcover : ∀ x : B, ∃ j, x ∈ (e j).baseSet)
    (p q : ∀ x, E x → ℝ)
    (hp : Continuous (fun v : TotalSpace ℂ E ↦ p v.proj v.snd))
    (hq : Continuous (fun v : TotalSpace ℂ E ↦ q v.proj v.snd))
    (hp0 : ∀ x v, v ≠ 0 → 0 < p x v)
    (hq0 : ∀ x v, v ≠ 0 → 0 < q x v)
    (hp_smul : ∀ x (a : ℂ) v, p x (a • v) = ‖a‖ * p x v)
    (hq_smul : ∀ x (a : ℂ) v, q x (a • v) = ‖a‖ * q x v) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ x v, c * q x v ≤ p x v ∧ p x v ≤ C * q x v := by
  classical
  have hscale (x : B) (A : E x ≃ₗ[ℂ] ℂ) (v : E x) :
      p x v = (p x (A.symm 1) / q x (A.symm 1)) * q x v := by
    have hu : A.symm 1 ≠ 0 := A.symm.map_ne_zero_iff.mpr one_ne_zero
    have hqne := ne_of_gt (hq0 x _ hu)
    have hv : v = A v • A.symm 1 := by
      apply A.injective
      simp only [map_smul, A.apply_symm_apply, smul_eq_mul, mul_one]
    conv_lhs => rw [hv, hp_smul]
    conv_rhs => rw [hv, hq_smul]
    field_simp
  choose j hj using hcover
  let A (x : B) : E x ≃ₗ[ℂ] ℂ := (e (j x)).linearEquivAt ℂ x (hj x)
  let r (x : B) : ℝ := p x ((A x).symm 1) / q x ((A x).symm 1)
  have hrpos (x : B) : 0 < r x :=
    div_pos (hp0 x _ ((A x).symm.map_ne_zero_iff.mpr one_ne_zero))
      (hq0 x _ ((A x).symm.map_ne_zero_iff.mpr one_ne_zero))
  have hr (x : B) (v : E x) : p x v = r x * q x v := hscale x (A x) v
  have hrframe (x : B) (A' : E x ≃ₗ[ℂ] ℂ) :
      r x = p x (A'.symm 1) / q x (A'.symm 1) := by
    rw [hr]
    exact (mul_div_cancel_right₀ _ (ne_of_gt
      (hq0 x _ (A'.symm.map_ne_zero_iff.mpr one_ne_zero)))).symm
  have hc : Continuous r := by
    have hlocal (i : J) : ContinuousOn r (e i).baseSet := by
      let frame (x : (e i).baseSet) : TotalSpace ℂ E :=
        ⟨x.val, ((e i).linearEquivAt ℂ x.val x.prop).symm 1⟩
      have hf : Continuous frame := by
        have h := (e i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          (continuous_subtype_val.prodMk (continuous_const (y := (1 : ℂ))))
          (fun z : (e i).baseSet ↦ (e i).mem_target.mpr z.prop)
        convert h using 1
        funext z
        exact (e i).toPretrivialization.mk_symm z.prop 1
      have hratio : Continuous (fun x : (e i).baseSet ↦
          p x.val (frame x).snd / q x.val (frame x).snd) :=
        (hp.comp hf).div (hq.comp hf) (fun x ↦ ne_of_gt
          (hq0 x.val _ (((e i).linearEquivAt ℂ x.val x.prop).symm.map_ne_zero_iff.mpr
            one_ne_zero)))
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert hratio using 1
      funext x
      exact hrframe x.val ((e i).linearEquivAt ℂ x.val x.prop)
    rw [continuous_iff_continuousAt]
    intro x
    exact (hlocal (j x)).continuousAt ((e (j x)).open_baseSet.mem_nhds (hj x))
  rcases isEmpty_or_nonempty B with hB | hB
  · exact ⟨1, 1, zero_lt_one, le_rfl, fun x ↦ isEmptyElim x⟩
  obtain ⟨lo, _, hlo⟩ := isCompact_univ.exists_isMinOn (univ_nonempty (α := B)) hc.continuousOn
  obtain ⟨hi, _, hhi⟩ := isCompact_univ.exists_isMaxOn (univ_nonempty (α := B)) hc.continuousOn
  refine ⟨r lo, r hi, hrpos lo, hhi (mem_univ lo), ?_⟩
  intro x v
  have hqnonneg : 0 ≤ q x v := by
    by_cases hv : v = 0
    · have hz := hq_smul x 0 v
      simpa only [zero_smul, norm_zero, zero_mul, hv] using hz.symm.le
    · exact (hq0 x v hv).le
  rw [hr]
  exact ⟨mul_le_mul_of_nonneg_right (hlo (mem_univ x)) hqnonneg,
    mul_le_mul_of_nonneg_right (hhi (mem_univ x)) hqnonneg⟩

end HolomorphicAnosov

