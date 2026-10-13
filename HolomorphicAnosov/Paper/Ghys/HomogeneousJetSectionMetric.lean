import HolomorphicAnosov.Analysis.ContinuousLineCovectorNorm
import HolomorphicAnosov.Analysis.ContinuousDualEvaluationClosed
import HolomorphicAnosov.Paper.Ghys.SectionTransport
import HolomorphicAnosov.Paper.Ghys.ComplexCovectorExt
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! This file constructs covector differences and a complete weighted supremum metric on continuous
homogeneous affine second-jet sections over a compact base. (Ghys, pp. 591–592; Kriegl–Michor,
§§37.12, 37.16; Rudin, Def. 5.3; Hatcher, Lemma 1.1; Hirsch–Pugh–Shub, Sublemma 5.2) -/

noncomputable section

open Bundle Set Filter
open scoped ENNReal

namespace HolomorphicAnosov.Ghys.HomogeneousJetSectionMetric

universe u v w k

variable {B : Type u} [TopologicalSpace B] {E : B → Type v}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace ℂ E)]

/-- The nonzero first jets, with the topology induced by the complex line bundle. (Ghys, pp.
591–592) -/
abbrev Punctured (E : B → Type v) [∀ x, Zero (E x)] :=
  {v : TotalSpace ℂ E // v.snd ≠ 0}

/-- Scaling of the first derivative by a nonzero complex scalar. (Ghys, p. 591) -/
def scaleFirst (ω : ℂˣ) (v : Punctured E) : Punctured E :=
  ⟨⟨v.val.proj, (ω : ℂ) • v.val.snd⟩, smul_ne_zero ω.ne_zero v.property⟩

/-- The real supremum of a nonempty set of values, with value zero for the empty set. -/
def supOrZero (values : Set ℝ) : ℝ := by
  classical
  exact if values.Nonempty then sSup values else 0

/-- Continuous homogeneous second-jet sections over a compact base have unique continuous
complex-linear covector differences and a complete metric given by their weighted supremum norm,
equivalently the supremum of the fibrewise operator norms. Over an empty base the section space is a
singleton with zero distance. (Ghys, pp. 591–592; Kriegl–Michor, §§37.12, 37.16; Rudin, Def. 5.3;
Hatcher, Lemma 1.1; Hirsch–Pugh–Shub, Sublemma 5.2) -/
theorem homogeneous_jet_section_metric
    [CompactSpace B] [FiberBundle ℂ E] [VectorBundle ℂ ℂ E]
    (hnorm : Continuous (fun v : TotalSpace ℂ E ↦ ‖v.snd‖))
    {J₂ : Type w} [TopologicalSpace J₂]
    (p : C(J₂, Punctured E)) (scale₂ : ℂˣ → J₂ → J₂) (shift : ℂ → J₂ → J₂)
    {I : Type k} (e : I → Trivialization ℂ (π ℂ E))
    [∀ i, (e i).IsLinear ℂ]
    (q : I → Trivialization ℂ (fun z : J₂ ↦ p z))
    (hcover : ∀ x : B, ∃ i, x ∈ (e i).baseSet)
    (hchart : ∀ i, (q i).baseSet = {v | v.val.proj ∈ (e i).baseSet})
    (hscale_proj : ∀ ω z, p (scale₂ ω z) = scaleFirst ω (p z))
    (hshift_proj : ∀ μ z, p (shift μ z) = p z)
    (hscale : ∀ i ω z, (p z).val.proj ∈ (e i).baseSet →
      (q i (scale₂ ω z)).2 = (ω : ℂ) ^ 2 * (q i z).2)
    (hshift : ∀ i μ z, (p z).val.proj ∈ (e i).baseSet →
      (q i (shift μ z)).2 = (q i z).2 - μ * (e i (p z).val).2)
    (c d : I → I → B → ℂ)
    (_hc : ∀ i j, ContinuousOn (c i j) ((e i).baseSet ∩ (e j).baseSet))
    (_hd : ∀ i j, ContinuousOn (d i j) ((e i).baseSet ∩ (e j).baseSet))
    (_hc_ne : ∀ i j x, x ∈ (e i).baseSet ∩ (e j).baseSet → c i j x ≠ 0)
    (_hfirst_overlap : ∀ i j (v : TotalSpace ℂ E),
      v.proj ∈ (e i).baseSet ∩ (e j).baseSet →
      (e j v).2 = c i j v.proj * (e i v).2)
    (_hsecond_overlap : ∀ i j z,
      (p z).val.proj ∈ (e i).baseSet ∩ (e j).baseSet →
      (q j z).2 = c i j (p z).val.proj * (q i z).2 +
        d i j (p z).val.proj * (e i (p z).val).2 ^ 2)
    (hne : Nonempty (SectionTransport.Section p scaleFirst scale₂)) :
    let S := SectionTransport.Section p scaleFirst scale₂
    ∃ (Δ : S → S → Punctured E → ℂ)
      (α : S → S → ∀ x : B, E x →L[ℂ] ℂ) (m : MetricSpace S),
      (∀ s t, Continuous (Δ s t) ∧ ∀ v : Punctured E,
        shift (Δ s t v) (s.val v) = t.val v ∧
        ∀ μ, shift μ (s.val v) = t.val v → μ = Δ s t v) ∧
      (∀ s t, Continuous (fun v : TotalSpace ℂ E ↦ α s t v.proj v.snd) ∧
        (∀ v : Punctured E, α s t v.val.proj v.val.snd = Δ s t v) ∧
        ∀ β : ∀ x : B, E x →ₗ[ℂ] ℂ,
          (∀ v : Punctured E, β v.val.proj v.val.snd = Δ s t v) →
          β = fun x ↦ (α s t x).toLinearMap) ∧
      (∀ s t,
        BddAbove (range (fun v : Punctured E ↦ ‖Δ s t v‖ / ‖v.val.snd‖)) ∧
        BddAbove (range (fun x : B ↦ ‖α s t x‖)) ∧
        @dist S m.toDist s t =
          supOrZero (range (fun v : Punctured E ↦ ‖Δ s t v‖ / ‖v.val.snd‖)) ∧
        @dist S m.toDist s t = supOrZero (range (fun x : B ↦ ‖α s t x‖))) ∧
      @CompleteSpace S m.toUniformSpace ∧
      (IsEmpty B → ∃ s₀ : S, ∀ s : S, s = s₀) := by
  classical
  by_cases hB : IsEmpty B
  · have : IsEmpty B := hB
    let S := SectionTransport.Section p scaleFirst scale₂
    have hP : IsEmpty (Punctured E) := ⟨fun v ↦ isEmptyElim v.val.proj⟩
    have hT : IsEmpty (TotalSpace ℂ E) := ⟨fun v ↦ isEmptyElim v.proj⟩
    have hS : Subsingleton S := ⟨fun s t ↦ Subtype.ext (ContinuousMap.ext
      (fun v ↦ isEmptyElim v))⟩
    let m : MetricSpace S := MetricSpace.induced (fun _ : S ↦ (0 : ℝ))
      (fun _ _ _ ↦ Subsingleton.elim _ _) inferInstance
    let Δ : S → S → Punctured E → ℂ := fun _ _ v ↦ isEmptyElim v
    let α : S → S → ∀ x : B, E x →L[ℂ] ℂ := fun _ _ x ↦ isEmptyElim x
    refine ⟨Δ, α, m, ?_, ?_, ?_, ?_, ?_⟩
    · intro s t
      exact ⟨continuous_of_discreteTopology, fun v ↦ isEmptyElim v⟩
    · intro s t
      refine ⟨continuous_of_discreteTopology, fun v ↦ isEmptyElim v, ?_⟩
      intro β hβ
      exact funext (fun x ↦ isEmptyElim x)
    · intro s t
      have hΔ : range (fun v : Punctured E ↦ ‖Δ s t v‖ / ‖v.val.snd‖) = ∅ := by
        ext y
        simp only [mem_range, mem_empty_iff_false, iff_false]
        rintro ⟨v, hv⟩
        exact isEmptyElim v
      have hα : range (fun x : B ↦ ‖α s t x‖) = ∅ := by
        ext y
        simp only [mem_range, mem_empty_iff_false, iff_false]
        rintro ⟨x, hx⟩
        exact isEmptyElim x
      rw [hΔ, hα]
      refine ⟨bddAbove_empty, bddAbove_empty, ?_, ?_⟩ <;>
        simpa [supOrZero] using (Subsingleton.elim s t)
    · exact inferInstance
    · intro _
      obtain ⟨s₀⟩ := hne
      exact ⟨s₀, fun s ↦ Subsingleton.elim _ _⟩
  · have : Nonempty B := not_isEmpty_iff.mp hB
    have hP : Nonempty (Punctured E) := by
      obtain ⟨x⟩ := ‹Nonempty B›
      obtain ⟨i, hi⟩ := hcover x
      let a := (e i).linearEquivAt ℂ x hi
      refine ⟨⟨⟨x, a.symm 1⟩, ?_⟩⟩
      exact (a.symm.map_eq_zero_iff.not.mpr one_ne_zero)
    let V := {b : lp (fun x : B ↦ E x →L[ℂ] ℂ) ∞ |
      Continuous (fun v : TotalSpace ℂ E ↦ b v.proj v.snd)}
    have hclosed := continuous_dual_evaluation_closed (E := E) hnorm
    have hcompleteV : CompleteSpace V := hclosed.completeSpace_coe
    
    have hnorm_sup (b : lp (fun x : B ↦ E x →L[ℂ] ℂ) ∞) :
        BddAbove (range (fun v : Punctured E ↦ ‖b v.val.proj v.val.snd‖ / ‖v.val.snd‖)) ∧
        ‖b‖ = supOrZero (range (fun v : Punctured E ↦
          ‖b v.val.proj v.val.snd‖ / ‖v.val.snd‖)) ∧
        ‖b‖ = supOrZero (range (fun x : B ↦ ‖b x‖)) := by
      let R := range (fun v : Punctured E ↦ ‖b v.val.proj v.val.snd‖ / ‖v.val.snd‖)
      have hbound (v : Punctured E) :
          ‖b v.val.proj v.val.snd‖ / ‖v.val.snd‖ ≤ ‖b‖ := by
        apply (div_le_iff₀ (norm_pos_iff.mpr v.property)).mpr
        exact ((b v.val.proj).le_opNorm v.val.snd).trans
          (mul_le_mul_of_nonneg_right
            (lp.norm_apply_le_norm ENNReal.top_ne_zero b v.val.proj) (norm_nonneg _))
      have hbdd : BddAbove R := ⟨‖b‖, by rintro _ ⟨v, rfl⟩; exact hbound v⟩
      have hnon : R.Nonempty := range_nonempty _
      have hpos : 0 ≤ sSup R := by
        obtain ⟨v⟩ := hP
        exact (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans
          (le_csSup hbdd (mem_range_self v))
      have hle : ‖b‖ ≤ sSup R := by
        apply lp.norm_le_of_forall_le hpos
        intro x
        apply (b x).opNorm_le_bound hpos
        intro v
        by_cases hv : v = 0
        · simp [hv]
        · have hh := le_csSup hbdd (mem_range_self (⟨⟨x, v⟩, hv⟩ : Punctured E))
          exact (div_le_iff₀ (norm_pos_iff.mpr hv)).mp hh
      refine ⟨hbdd, ?_, ?_⟩
      · rw [supOrZero, ite_eq_left hnon]
        exact le_antisymm hle (csSup_le hnon (by rintro _ ⟨v, rfl⟩; exact hbound v))
      · rw [supOrZero, ite_eq_left (range_nonempty _)]
        exact lp.norm_eq_ciSup b
    let S := SectionTransport.Section p scaleFirst scale₂
    
    have hmetric_assembly
        (A : S ≃ V)
        (Δ : S → S → Punctured E → ℂ)
        (α : S → S → ∀ x : B, E x →L[ℂ] ℂ)
        (hα : ∀ s t x, α s t x = (A t).val x - (A s).val x)
        (hΔ : ∀ s t (v : Punctured E), Δ s t v = α s t v.val.proj v.val.snd) :
        ∃ m : MetricSpace S,
          (∀ s t,
            BddAbove (range (fun v : Punctured E ↦ ‖Δ s t v‖ / ‖v.val.snd‖)) ∧
            BddAbove (range (fun x : B ↦ ‖α s t x‖)) ∧
            @dist S m.toDist s t =
              supOrZero (range (fun v : Punctured E ↦ ‖Δ s t v‖ / ‖v.val.snd‖)) ∧
            @dist S m.toDist s t = supOrZero (range (fun x : B ↦ ‖α s t x‖))) ∧
          @CompleteSpace S m.toUniformSpace := by
      let m : MetricSpace S := MetricSpace.induced A A.injective inferInstance
      let : MetricSpace S := m
      let iso : S ≃ᵢ V := { A with isometry_toFun := fun _ _ ↦ rfl }
      refine ⟨m, ?_, iso.completeSpace⟩
      intro s t
      let b : lp (fun x : B ↦ E x →L[ℂ] ℂ) ∞ := (A t).val - (A s).val
      have hbx (x : B) : b x = α s t x := (hα s t x).symm
      have hdist : dist s t = ‖b‖ := by
        change dist (A s).val (A t).val = ‖b‖
        rw [dist_comm, dist_eq_norm]
      obtain ⟨hbdd, hratio, hop⟩ := hnorm_sup b
      have hnorms : BddAbove (range (fun x : B ↦ ‖b x‖)) :=
        (memℓp_infty_iff.mp b.property)
      simp_rw [hbx] at hbdd hratio hop hnorms
      simp_rw [hΔ]
      exact ⟨hbdd, hnorms, hdist.trans hratio, hdist.trans hop⟩
    have hreconstruct (s : S) (β : lp (fun x : B ↦ E x →L[ℂ] ℂ) ∞)
        (hβ : Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd)) :
        ∃ t : S,
          (∀ v : Punctured E, t.val v = shift (β v.val.proj v.val.snd) (s.val v)) ∧
          (∀ (v : Punctured E) μ, shift μ (s.val v) = t.val v →
            μ = β v.val.proj v.val.snd) ∧
          ∀ i (v : Punctured E), v.val.proj ∈ (e i).baseSet →
            (q i (t.val v)).2 = (q i (s.val v)).2 -
              β v.val.proj v.val.snd * (e i v.val).2 := by
      let F : Punctured E → ℂ := fun v ↦ β v.val.proj v.val.snd
      have hF : Continuous F := hβ.comp continuous_subtype_val
      let t : Punctured E → J₂ := fun v ↦ shift (F v) (s.val v)
      have hproj (v : Punctured E) : p (t v) = v := by
        exact (hshift_proj _ _).trans (s.property.1 v)
      have hcoef (i : I) (v : Punctured E) (hv : v.val.proj ∈ (e i).baseSet) :
          (q i (t v)).2 = (q i (s.val v)).2 - F v * (e i v.val).2 := by
        dsimp [t]
        rw [hshift i _ _ (by simpa only [s.property.1 v] using hv), s.property.1 v]
      have ht : Continuous t := by
        rw [continuous_iff_continuousAt]
        intro v
        obtain ⟨i, hi⟩ := hcover v.val.proj
        have hq : v ∈ (q i).baseSet := by simpa only [hchart, Set.mem_ofPred_eq] using hi
        apply (q i).continuousAt_of_comp_left
        · have heq : (fun z : J₂ ↦ p z) ∘ t = (id : Punctured E → Punctured E) := funext hproj
          rw [heq]
          exact continuousAt_id
        · simpa only [hproj] using hq
        · have hs : ContinuousAt (fun w : Punctured E ↦ q i (s.val w)) v :=
            ((q i).continuousAt (by rw [(q i).mem_source, s.property.1 v]; exact hq)).comp
              s.val.continuous.continuousAt
          have ha : ContinuousAt (fun w : Punctured E ↦ (e i w.val).2) v :=
            (((e i).continuousAt ((e i).mem_source.mpr hi)).comp
              continuous_subtype_val.continuousAt).snd
          have hc : ContinuousAt (fun w : Punctured E ↦
              (w, (q i (s.val w)).2 - F w * (e i w.val).2)) v :=
            continuousAt_id.prodMk (hs.snd.sub (hF.continuousAt.mul ha))
          apply hc.congr_of_eventuallyEq
          have hn := (q i).open_baseSet.mem_nhds hq
          filter_upwards [hn] with w hw
          have he : w.val.proj ∈ (e i).baseSet := by simpa only [hchart, Set.mem_ofPred_eq] using hw
          apply Prod.ext
          · exact ((q i).coe_fst' (by rw [hproj]; exact hw)).trans (hproj w)
          · exact hcoef i w he
      have hhom (ω : ℂˣ) (v : Punctured E) : t (scaleFirst ω v) = scale₂ ω (t v) := by
        obtain ⟨i, hi⟩ := hcover v.val.proj
        have hq : scaleFirst ω v ∈ (q i).baseSet := by
          simpa only [hchart, Set.mem_ofPred_eq, scaleFirst] using hi
        have hl : t (scaleFirst ω v) ∈ (q i).source := by
          rw [(q i).mem_source, hproj]; exact hq
        have hr : scale₂ ω (t v) ∈ (q i).source := by
          rw [(q i).mem_source, hscale_proj, hproj]; exact hq
        apply (q i).toOpenPartialHomeomorph.injOn hl hr
        change q i (t (scaleFirst ω v)) = q i (scale₂ ω (t v))
        apply Prod.ext
        · rw [(q i).coe_fst hl, (q i).coe_fst hr, hproj, hscale_proj, hproj]
        · rw [hcoef i (scaleFirst ω v) hi, s.property.2 ω v,
            hscale i ω _ (by simpa only [s.property.1 v] using hi),
            hscale i ω _ (by simpa only [hproj] using hi), hcoef i v hi]
          have hFscale : F (scaleFirst ω v) = (ω : ℂ) * F v := by
            exact (β v.val.proj).map_smul (ω : ℂ) v.val.snd
          have hascale : (e i (scaleFirst ω v).val).2 = (ω : ℂ) * (e i v.val).2 := by
            exact ((e i).linear ℂ hi).map_smul (ω : ℂ) v.val.snd
          rw [hFscale, hascale]
          ring
      have huniq (v : Punctured E) (μ : ℂ) (hμ : shift μ (s.val v) = t v) : μ = F v := by
        obtain ⟨i, hi⟩ := hcover v.val.proj
        have ha : (e i v.val).2 ≠ 0 := by
          intro ha
          apply v.property
          apply ((e i).linearEquivAt ℂ v.val.proj hi).injective
          simpa only [Trivialization.linearEquivAt_apply, map_zero] using ha
        have hh := congrArg (fun z ↦ (q i z).2) hμ
        rw [hshift i μ _ (by simpa only [s.property.1 v] using hi),
          s.property.1 v, hcoef i v hi] at hh
        exact mul_right_cancel₀ ha (sub_right_inj.mp hh)
      exact ⟨⟨⟨t, ht⟩, hproj, hhom⟩, fun _ ↦ rfl, huniq, hcoef⟩
    obtain ⟨s₀⟩ := hne
    let decode : V → S := fun β ↦ Classical.choose (hreconstruct s₀ β β.property)
    have hdecode (β : V) (v : Punctured E) :
        (decode β).val v = shift (β.val v.val.proj v.val.snd) (s₀.val v) := by
      exact (Classical.choose_spec (hreconstruct s₀ β β.property)).1 v
    have hdecode_injective : Function.Injective decode := by
      intro β γ hβγ
      apply Subtype.ext
      apply lp.ext
      apply funext
      intro x
      apply ContinuousLinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · obtain ⟨i, hi⟩ := hcover x
        let vp : Punctured E := ⟨⟨x, v⟩, hv⟩
        have hsame : shift (β.val x v) (s₀.val vp) = shift (γ.val x v) (s₀.val vp) := by
          rw [← hdecode β vp, ← hdecode γ vp, hβγ]
        have hdb : (decode γ).val vp = (decode β).val vp := congrArg (fun z : S ↦ z.val vp) hβγ.symm
        have hμβ : shift (β.val x v) (s₀.val vp) = (decode β).val vp :=
          (hsame.trans (hdecode γ vp).symm).trans hdb
        have hμγβ : shift (γ.val x v) (s₀.val vp) = (decode β).val vp :=
          (hdecode γ vp).symm.trans hdb
        have huγβ := (Classical.choose_spec (hreconstruct s₀ β β.property)).2.1 vp
          (γ.val x v) hμγβ
        simpa only [vp] using huγβ.symm
    have hfibre_extension
        (F : Punctured E → ℂ)
        (hF : ∀ (ω : ℂˣ) (v : Punctured E), F (scaleFirst ω v) = (ω : ℂ) * F v)
        (i : I) (x : B) (hx : x ∈ (e i).baseSet) :
        ∃! L : E x →L[ℂ] ℂ, ∀ (v : E x) (hv : v ≠ 0),
          L v = F ⟨⟨x,v⟩,hv⟩ := by
      let A := (e i).linearEquivAt ℂ x hx
      let : FiniteDimensional ℂ (E x) :=
        FiniteDimensional.of_injective A.toLinearMap A.injective
      let Ac : E x ≃L[ℂ] ℂ := A.toContinuousLinearEquiv
      let V (a : ℂˣ) : Punctured E :=
        ⟨⟨x, A.symm (a : ℂ)⟩, A.symm.map_ne_zero_iff.mpr a.ne_zero⟩
      have hV (a b : ℂˣ) : V (a * b) = scaleFirst a (V b) := by
        apply Subtype.ext
        change (⟨x, A.symm ((a : ℂ) * (b : ℂ))⟩ : TotalSpace ℂ E) =
          ⟨x, (a : ℂ) • A.symm (b : ℂ)⟩
        congr 1
        exact A.symm.map_smul (a : ℂ) (b : ℂ)
      obtain ⟨L₀, hL₀, _⟩ := homogeneous_complex_covector_extension
        (fun a ↦ F (V a)) (fun a b ↦ by rw [hV]; exact hF a (V b))
      let L := L₀.comp Ac.toContinuousLinearMap
      have hL (v : E x) (hv : v ≠ 0) : L v = F ⟨⟨x,v⟩,hv⟩ := by
        let a : ℂˣ := Units.mk0 (A v) (A.map_ne_zero_iff.mpr hv)
        have ha : (a : ℂ) = A v := rfl
        have hVa : V a = (⟨⟨x,v⟩,hv⟩ : Punctured E) := by
          apply Subtype.ext
          change (⟨x,A.symm (A v)⟩ : TotalSpace ℂ E) = ⟨x,v⟩
          rw [A.symm_apply_apply]
        change L₀ (A v) = _
        rw [← ha, hL₀ a, hVa]
      refine ⟨L, hL, ?_⟩
      intro K hK
      apply ContinuousLinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · exact (hK v hv).trans (hL v hv).symm
    have hevaluation_continuous
        (F : Punctured E → ℂ) (hF : Continuous F)
        (β : ∀ x, E x →L[ℂ] ℂ)
        (hβ : ∀ v : Punctured E, β v.val.proj v.val.snd = F v) :
        Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd) := by
      have hlocal (i : I) :
          ContinuousOn (fun v : TotalSpace ℂ E ↦ β v.proj v.snd) (e i).source := by
        let frame (x : (e i).baseSet) : Punctured E :=
          ⟨⟨x.val, ((e i).linearEquivAt ℂ x.val x.prop).symm 1⟩,
            ((e i).linearEquivAt ℂ x.val x.prop).symm.map_ne_zero_iff.mpr one_ne_zero⟩
        have hf : Continuous frame := by
          apply Continuous.subtype_mk
          have hh := (e i).toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
            (continuous_subtype_val.prodMk (continuous_const (y := (1 : ℂ))))
            (fun x : (e i).baseSet ↦ (e i).mem_target.mpr x.prop)
          convert hh using 1
          funext x
          exact (e i).toPretrivialization.mk_symm x.prop 1
        let base (v : (e i).source) : (e i).baseSet :=
          ⟨v.val.proj, (e i).mem_source.mp v.prop⟩
        have hb : Continuous base := by
          apply Continuous.subtype_mk
          have hh := ((e i).continuousOn.comp_continuous continuous_subtype_val
            (fun v : (e i).source ↦ v.prop)).fst
          convert hh using 1
          funext v
          exact ((e i).coe_fst v.prop).symm
        have ha : Continuous (fun v : (e i).source ↦ (e i v.val).2) :=
          ((e i).continuousOn.comp_continuous continuous_subtype_val (fun v ↦ v.prop)).snd
        have hc : Continuous (fun v : (e i).source ↦ (e i v.val).2 * F (frame (base v))) :=
          ha.mul (hF.comp (hf.comp hb))
        apply continuousOn_iff_continuous_domRestrict.mpr
        convert hc using 1
        funext v
        let A := (e i).linearEquivAt ℂ v.val.proj ((e i).mem_source.mp v.prop)
        have hvec : v.val.snd = (A v.val.snd) • A.symm 1 := by
          apply A.injective
          simp only [map_smul, A.apply_symm_apply, smul_eq_mul, mul_one]
        have hval := hβ (frame (base v))
        change β v.val.proj (A.symm 1) = _ at hval
        change β v.val.proj v.val.snd = _
        rw [hvec, map_smul, smul_eq_mul, hval]
        rfl
      rw [continuous_iff_continuousAt]
      intro v
      obtain ⟨i, hi⟩ := hcover v.proj
      exact (hlocal i).continuousAt ((e i).open_source.mem_nhds ((e i).mem_source.mpr hi))
    have hcovector_extension (F : Punctured E → ℂ) (hF : Continuous F)
        (hhom : ∀ (ω : ℂˣ) (v : Punctured E), F (scaleFirst ω v) = (ω : ℂ) * F v) :
        ∃ β : ∀ x, E x →L[ℂ] ℂ,
          Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd) ∧
          ∀ v : Punctured E, β v.val.proj v.val.snd = F v := by
      have hx (x : B) : ∃ L : E x →L[ℂ] ℂ,
          ∀ (v : E x) (hv : v ≠ 0), L v = F ⟨⟨x,v⟩,hv⟩ := by
        obtain ⟨i, hi⟩ := hcover x
        exact (hfibre_extension F hhom i x hi).exists
      choose β hβ using hx
      have heval (v : Punctured E) : β v.val.proj v.val.snd = F v :=
        hβ v.val.proj v.val.snd v.prop
      exact ⟨β, hevaluation_continuous F hF β heval, heval⟩
    have hquotient_continuousAt (s t : S) (i : I) (v : Punctured E)
        (hv : v.val.proj ∈ (e i).baseSet) :
        ContinuousAt (fun w : Punctured E ↦
          ((q i (s.val w)).2 - (q i (t.val w)).2) / (e i w.val).2) v := by
      have hsec (v : Punctured E) := And.intro (s.property.1 v) (t.property.1 v)
      have hq : v ∈ (q i).baseSet := by
        simpa only [hchart i, Set.mem_ofPred_eq] using hv
      have hs : ContinuousAt (fun w : Punctured E ↦ q i (s.val w)) v :=
        ((q i).continuousAt (show s.val v ∈ (q i).source from by rw [(q i).mem_source, (hsec v).1]; exact hq)).comp
          s.val.continuous.continuousAt
      have ht : ContinuousAt (fun w : Punctured E ↦ q i (t.val w)) v :=
        ((q i).continuousAt (show t.val v ∈ (q i).source from by rw [(q i).mem_source, (hsec v).2]; exact hq)).comp
          t.val.continuous.continuousAt
      have he : ContinuousAt (fun w : Punctured E ↦ (e i w.val).2) v :=
        (((e i).continuousAt ((e i).mem_source.mpr hv)).comp
          continuous_subtype_val.continuousAt).snd
      have hene : (e i v.val).2 ≠ 0 := by
        intro hz
        apply v.property
        apply ((e i).linearEquivAt ℂ v.val.proj hv).injective
        simpa only [Trivialization.linearEquivAt_apply, map_zero] using hz
      exact (hs.snd.sub ht.snd).div he hene
    have hprincipal (s t : S) :
        ∃ F : Punctured E → ℂ,
          Continuous F ∧
          (∀ v, shift (F v) (s.val v) = t.val v ∧
            ∀ μ, shift μ (s.val v) = t.val v → μ = F v) ∧
          ∀ i (v : Punctured E), v.val.proj ∈ (e i).baseSet →
            F v = ((q i (s.val v)).2 - (q i (t.val v)).2) / (e i v.val).2 := by
      have hsec (v : Punctured E) := And.intro (s.property.1 v) (t.property.1 v)
      classical
      let Q (i : I) (v : Punctured E) :=
        ((q i (s.val v)).2 - (q i (t.val v)).2) / (e i v.val).2
      have hQ (i : I) (v : Punctured E) (hv : v.val.proj ∈ (e i).baseSet) :
          shift (Q i v) (s.val v) = t.val v ∧ ∀ μ, shift μ (s.val v) = t.val v → μ = Q i v := by
        have hq : v ∈ (q i).baseSet := by
          simpa only [hchart i, Set.mem_ofPred_eq] using hv
        have ha : (e i v.val).2 ≠ 0 := by
          intro hz
          apply v.property
          apply ((e i).linearEquivAt ℂ v.val.proj hv).injective
          simpa only [Trivialization.linearEquivAt_apply, map_zero] using hz
        have hs : (p (s.val v)).val.proj ∈ (e i).baseSet := by rw [(hsec v).1]; exact hv
        constructor
        · have hleft : shift (Q i v) (s.val v) ∈ (q i).source := by
            rw [(q i).mem_source, hshift_proj, (hsec v).1]; exact hq
          have hright : t.val v ∈ (q i).source := by
            rw [(q i).mem_source, (hsec v).2]; exact hq
          apply (q i).toOpenPartialHomeomorph.injOn hleft hright
          change q i (shift (Q i v) (s.val v)) = q i (t.val v)
          apply Prod.ext
          · rw [(q i).coe_fst hleft, (q i).coe_fst hright,
              hshift_proj, (hsec v).1, (hsec v).2]
          · rw [hshift i _ _ hs, (hsec v).1]
            dsimp [Q]
            rw [div_mul_cancel₀ _ ha]
            ring
        · intro μ hμ
          have hh := congrArg (fun z ↦ (q i z).2) hμ
          rw [hshift i μ _ hs, (hsec v).1] at hh
          apply (eq_div_iff ha).mpr
          linear_combination -hh
      let index (v : Punctured E) := (hcover v.val.proj).choose
      have hindex (v : Punctured E) : v.val.proj ∈ (e (index v)).baseSet :=
        (hcover v.val.proj).choose_spec
      let F (v : Punctured E) := Q (index v) v
      have hF (v : Punctured E) :
          shift (F v) (s.val v) = t.val v ∧ ∀ μ, shift μ (s.val v) = t.val v → μ = F v :=
        hQ (index v) v (hindex v)
      have hlocal (i : I) (v : Punctured E) (hv : v.val.proj ∈ (e i).baseSet) :
          F v = Q i v := (hQ i v hv).2 (F v) (hF v).1
      refine ⟨F, ?_, hF, hlocal⟩
      rw [continuous_iff_continuousAt]
      intro v
      let i := index v
      have hi : v.val.proj ∈ (e i).baseSet := hindex v
      have hc := hquotient_continuousAt s t i v hi
      apply hc.congr_of_eventuallyEq
      have hq : v ∈ (q i).baseSet := by simpa only [hchart i, Set.mem_ofPred_eq] using hi
      filter_upwards [(q i).open_baseSet.mem_nhds hq] with w hw
      exact hlocal i w (by simpa only [hchart i, Set.mem_ofPred_eq] using hw)
    have hsection_covector (s t : S) :
        ∃ β : ∀ x, E x →L[ℂ] ℂ,
          Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd) ∧
          (∀ v : Punctured E,
            shift (β v.val.proj v.val.snd) (s.val v) = t.val v ∧
            ∀ μ, shift μ (s.val v) = t.val v → μ = β v.val.proj v.val.snd) := by
      obtain ⟨F, hF, huniq, hlocal⟩ := hprincipal s t
      have hhom (ω : ℂˣ) (v : Punctured E) :
          F (scaleFirst ω v) = (ω : ℂ) * F v := by
        obtain ⟨i, hi⟩ := hcover v.val.proj
        have hi' : (scaleFirst ω v).val.proj ∈ (e i).baseSet := hi
        have he : (e i (scaleFirst ω v).val).2 = (ω : ℂ) * (e i v.val).2 :=
          ((e i).linear ℂ hi).map_smul (ω : ℂ) v.val.snd
        rw [hlocal i (scaleFirst ω v) hi', hlocal i v hi,
          s.property.2 ω v, t.property.2 ω v,
          hscale i ω (s.val v) (by simpa only [s.property.1 v] using hi),
          hscale i ω (t.val v) (by simpa only [t.property.1 v] using hi), he]
        field_simp [Units.ne_zero ω]
      obtain ⟨β, hβ, heval⟩ := hcovector_extension F hF hhom
      refine ⟨β, hβ, ?_⟩
      intro v
      rw [heval v]
      exact huniq v
    have hnorm_continuous (β : ∀ x, E x →L[ℂ] ℂ)
        (hβ : Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd)) :
        Continuous (fun x ↦ ‖β x‖) :=
      continuous_line_covector_norm hnorm e hcover β hβ
    have hbounded (β : ∀ x, E x →L[ℂ] ℂ)
        (hβ : Continuous (fun v : TotalSpace ℂ E ↦ β v.proj v.snd)) :
        BddAbove (range (fun x ↦ ‖β x‖)) :=
      (isCompact_range (hnorm_continuous β hβ)).bddAbove
    have hdecode_surjective : Function.Surjective decode := by
      intro t
      obtain ⟨β, hβ, hshiftβ⟩ := hsection_covector s₀ t
      let b : lp (fun x ↦ E x →L[ℂ] ℂ) ∞ :=
        ⟨β, memℓp_infty_iff.mpr (hbounded β hβ)⟩
      let bV : V := ⟨b, hβ⟩
      refine ⟨bV, ?_⟩
      apply Subtype.ext
      apply ContinuousMap.ext
      intro v
      exact (hdecode bV v).trans (hshiftβ v).1
    let A : S ≃ V := (Equiv.ofBijective decode ⟨hdecode_injective, hdecode_surjective⟩).symm
    have hdecodeA (s : S) : decode (A s) = s :=
      (Equiv.ofBijective decode ⟨hdecode_injective, hdecode_surjective⟩).apply_symm_apply s
    have hAcoef (s : S) (i : I) (v : Punctured E)
        (hi : v.val.proj ∈ (e i).baseSet) :
        (q i (s.val v)).2 = (q i (s₀.val v)).2 -
          (A s).val v.val.proj v.val.snd * (e i v.val).2 := by
      have hh := (Classical.choose_spec
        (hreconstruct s₀ (A s).val (A s).prop)).2.2 i v hi
      change (q i ((decode (A s)).val v)).2 = _ at hh
      rw [hdecodeA] at hh
      exact hh
    let α : S → S → ∀ x, E x →L[ℂ] ℂ := fun s t x ↦
      (A t).val x - (A s).val x
    let Δ : S → S → Punctured E → ℂ := fun s t v ↦ α s t v.val.proj v.val.snd
    have hαcont (s t : S) :
        Continuous (fun v : TotalSpace ℂ E ↦ α s t v.proj v.snd) :=
      (A t).prop.sub (A s).prop
    have hprincipalα (s t : S) : ∀ v : Punctured E,
        shift (Δ s t v) (s.val v) = t.val v ∧
        ∀ μ, shift μ (s.val v) = t.val v → μ = Δ s t v := by
      obtain ⟨F, hF, huniq, hlocal⟩ := hprincipal s t
      intro v
      obtain ⟨i, hi⟩ := hcover v.val.proj
      have ha : (e i v.val).2 ≠ 0 := by
        intro hz
        apply v.prop
        apply ((e i).linearEquivAt ℂ v.val.proj hi).injective
        simpa only [Trivialization.linearEquivAt_apply, map_zero] using hz
      have heq : F v = Δ s t v := by
        rw [hlocal i v hi, hAcoef s i v hi, hAcoef t i v hi]
        change (_ - _) / _ =
          (A t).val v.val.proj v.val.snd - (A s).val v.val.proj v.val.snd
        field_simp
        ring
      rw [← heq]
      exact huniq v
    obtain ⟨m, hm, hcomplete⟩ := hmetric_assembly A Δ α (fun _ _ _ ↦ rfl)
      (fun _ _ _ ↦ rfl)
    refine ⟨Δ, α, m, ?_, ?_, hm, hcomplete, ?_⟩
    · intro s t
      exact ⟨(hαcont s t).comp continuous_subtype_val, hprincipalα s t⟩
    · intro s t
      refine ⟨hαcont s t, fun _ ↦ rfl, ?_⟩
      intro β hβ
      funext x
      apply LinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · exact hβ ⟨⟨x,v⟩,hv⟩
    · intro hEmpty
      exact False.elim (hB hEmpty)



end HolomorphicAnosov.Ghys.HomogeneousJetSectionMetric
