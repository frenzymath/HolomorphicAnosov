import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp

noncomputable section
open Bundle Set
namespace HolomorphicAnosov

/-- On a complex line bundle with continuous fibre norm, every covector field
with continuous evaluation has continuous operator norm.

Source: Ghys, Holomorphic Anosov systems (1995), pp.591–592, the compact-base
norm argument; Hatcher, Vector Bundles and K-Theory (2017), Lemma 1.1 p.8,
continuous frame evaluation; Rudin, Real and Complex Analysis (1987),
Definition 5.3 p.96, operator norm. This is the existing frame calculation from
homogeneous_jet_section_metric, made reusable for its native-carrier consumer.

Proof: in a local nonzero frame u, every v is a scalar multiple of u, so
||beta||=||beta(u)||/||u||. The numerator and denominator are continuous and
the denominator is positive. The covering frame neighborhoods give continuity
at every base point. Empty bases require no frame choice. -/
theorem continuous_line_covector_norm
    {B : Type*} [TopologicalSpace B] {E : B → Type*}
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [TopologicalSpace (TotalSpace ℂ E)]
    (hnorm : Continuous (fun v : TotalSpace ℂ E ↦ ‖v.snd‖))
    {I : Type*} (e : I → Trivialization ℂ (π ℂ E))
    [∀ i, (e i).IsLinear ℂ]
    (hcover : ∀ x : B, ∃ i, x ∈ (e i).baseSet)
    (β : ∀ x, E x →L[ℂ] ℂ)
    (hβ : Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd)) :
    Continuous (fun x ↦ ‖β x‖) := by
  have hframe_continuous (i : I) :
      Continuous (fun z : (e i).baseSet × ℂ ↦
        (⟨z.1.val, ((e i).linearEquivAt ℂ z.1.val z.1.prop).symm z.2⟩ :
          TotalSpace ℂ E)) := by
    have h := (e i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
      (fun z : (e i).baseSet × ℂ ↦ (e i).mem_target.mpr z.1.prop)
    convert h using 1
    funext z
    exact (e i).toPretrivialization.mk_symm z.1.prop z.2
  have hnorm_frame (x : B) (A : E x ≃ₗ[ℂ] ℂ) (L : E x →L[ℂ] ℂ) :
      ‖L‖ = ‖L (A.symm 1)‖ / ‖A.symm 1‖ := by
    have hu : A.symm 1 ≠ 0 := A.symm.map_ne_zero_iff.mpr one_ne_zero
    have hn : 0 < ‖A.symm 1‖ := norm_pos_iff.mpr hu
    apply le_antisymm
    · apply L.opNorm_le_bound (div_nonneg (norm_nonneg _) hn.le)
      intro v
      have hv : v = (A v) • A.symm 1 := by
        apply A.injective
        simp only [map_smul, A.apply_symm_apply, smul_eq_mul, mul_one]
      rw [hv, map_smul, norm_smul, norm_smul]
      exact le_of_eq (by field_simp)
    · exact (div_le_iff₀ hn).mpr (L.le_opNorm (A.symm 1))
  have hnorm_continuous (β : ∀ x, E x →L[ℂ] ℂ)
      (hβ : Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd)) :
      Continuous (fun x ↦ ‖β x‖) := by
    have hlocal (i : I) : ContinuousOn (fun x ↦ ‖β x‖) (e i).baseSet := by
      let frame (x : (e i).baseSet) : TotalSpace ℂ E :=
        ⟨x.val, ((e i).linearEquivAt ℂ x.val x.prop).symm 1⟩
      have hf : Continuous frame :=
        (hframe_continuous i).comp (continuous_id.prodMk continuous_const)
      have hc : Continuous (fun x : (e i).baseSet ↦
          ‖β x.val (frame x).snd‖ / ‖(frame x).snd‖) :=
        (hβ.comp hf).norm.div (hnorm.comp hf) (fun x ↦ norm_ne_zero_iff.mpr
          (((e i).linearEquivAt ℂ x.val x.prop).symm.map_ne_zero_iff.mpr one_ne_zero))
      apply continuousOn_iff_continuous_domRestrict.mpr
      convert hc using 1
      funext x
      exact hnorm_frame x.val ((e i).linearEquivAt ℂ x.val x.prop) (β x.val)
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨i, hi⟩ := hcover x
    exact (hlocal i).continuousAt ((e i).open_baseSet.mem_nhds hi)
  exact hnorm_continuous β hβ

end HolomorphicAnosov

