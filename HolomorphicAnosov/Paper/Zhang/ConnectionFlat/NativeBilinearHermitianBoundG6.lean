import HolomorphicAnosov.Paper.Zhang.CompactAnosovHermitianOperatorBounds

/-! Uniform Hermitian bounds for bilinear tensors with continuous coordinate coefficients on a
compact manifold. (Zhang, eq. (8), p. 6; Demailly, VI §4, pp. 296–297) -/

open Set Bundle
open scoped ContDiff Manifold _root_.Topology
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace HolomorphicAnosov

/-- A bilinear tensor with continuous local coefficients on a compact manifold is uniformly bounded
by the product of the Hermitian norms of its arguments. -/
theorem uniform_native_bilinear_hermitian_bound
    {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]
    (R : (x : X) → TangentSpace (realModel d) x →L[ℝ]
      TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hR : ∀ x : X,
      let t := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
      ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ O ⊆ t.baseSet ∧
        ∃ A : X → ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℂ,
          ContinuousOn A O ∧ ∀ y ∈ O, ∀ v w,
            R y (t.symm y v) (t.symm y w) = A y v w)
    (h : HermitianTangentMetricCore d X) (hh : IsSmoothHermitianTangentMetric h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x v w,
      ‖R x (complexTangentToReal d x v) (complexTangentToReal d x w)‖ ≤
        C * hermitianBoundsNorm h x v * hermitianBoundsNorm h x w := by
  classical
  let : NormedSpace ℝ (ComplexModel d) := inferInstance
  let : NormedAddCommGroup (ComplexModel d →L[ℝ] ℂ) := inferInstance
  let : NormedSpace ℝ (ComplexModel d →L[ℝ] ℂ) := inferInstance
  let : NormedAddCommGroup (ComplexModel d →L[ℝ] ComplexModel d →L[ℝ] ℂ) := inferInstance
  let p := HermitianFibreAlgebra.hermitianBoundsRealSeminorm h
  have hp := Preparation.continuous_hermitian_tangent_norm h hh
  have hlocal (x : X) : ∃ O : Set X, IsOpen O ∧ x ∈ O ∧ ∃ C : ℝ, 1 ≤ C ∧
      ∀ y ∈ O, ∀ v w,
        ‖R y (complexTangentToReal d y v) (complexTangentToReal d y w)‖ ≤
          C * p y v * p y w := by
    let t := trivializationAt (ComplexModel d) (TangentSpace (realModel d)) x
    obtain ⟨O, hO, hxO, hOt, A, hA, hRA⟩ := hR x
    obtain ⟨K, hKnhds, hKO, hKcompact⟩ := local_compact_nhds (hO.mem_nhds hxO)
    let : CompactSpace K := isCompact_iff_compactSpace.mp hKcompact
    let frame (y : K) : ComplexModel d →ₗ[ℝ] TangentSpace (complexModel d) y.val :=
      (complexTangentToReal d y.val).symm.toLinearEquiv.toLinearMap.comp
        (t.linearEquivAt ℝ y.val (hOt (hKO y.property))).symm.toLinearMap
    have hf : Continuous (fun z : K × ComplexModel d ↦
        (⟨z.1.val, frame z.1 z.2⟩ : TangentBundle (complexModel d) X)) := by
      have hr : Continuous (fun z : K × ComplexModel d ↦
          (⟨z.1.val, t.symm z.1.val z.2⟩ : TangentBundle (realModel d) X)) :=
        t.continuousOn_symm.comp_continuous
          ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
          (fun z ↦ ⟨hOt (hKO z.1.property), mem_univ _⟩)
      exact (continuous_complexTangentToReal_symm (d := d) (X := X)).comp hr
    let q : K → Seminorm ℝ (ComplexModel d) := fun y ↦ (p y.val).comp (frame y)
    have hq : Continuous (fun z : K × ComplexModel d ↦ q z.1 z.2) := hp.comp hf
    have hqpos (y : K) (v : ComplexModel d) (hv : v ≠ 0) : 0 < q y v := by
      apply HermitianFibreAlgebra.coreLength_pos (h y.val)
      intro hz
      apply hv
      have hinj : Function.Injective (frame y) :=
        (complexTangentToReal d y.val).symm.injective.comp
          (t.linearEquivAt ℝ y.val (hOt (hKO y.property))).symm.injective
      exact hinj (hz.trans (map_zero (frame y)).symm)
    obtain ⟨T, hT, hTbound⟩ := Preparation.uniform_seminorm_upper_bound
      (fun _ : K ↦ normSeminorm ℝ (ComplexModel d)) q
      continuous_snd.norm hq hqpos
    have hAK : Continuous (fun y : K ↦ A y.val) :=
      hA.comp_continuous continuous_subtype_val (fun y ↦ hKO y.property)
    have hAKnorm : Continuous (fun y : K ↦ ‖A y.val‖) := hAK.norm
    obtain ⟨M, hM⟩ := isCompact_univ.bddAbove_image hAKnorm.continuousOn
    let C := max 1 M * T ^ 2
    have hC : 1 ≤ C := by
      dsimp [C]
      exact one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hT)
    refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hKnhds, C, hC, ?_⟩
    intro y hy v w
    let yk : K := ⟨y, interior_subset hy⟩
    let E := t.linearEquivAt ℝ y (hOt (hKO yk.property))
    let vc := E (complexTangentToReal d y v)
    let wc := E (complexTangentToReal d y w)
    have hback (a : TangentSpace (complexModel d) y) :
        frame yk (E (complexTangentToReal d y a)) = a := by
      change (complexTangentToReal d y).symm (E.symm (E (complexTangentToReal d y a))) = a
      rw [E.symm_apply_apply, ContinuousLinearEquiv.symm_apply_apply]
    have htv : ‖vc‖ ≤ T * p y v := by
      have hb := hTbound yk vc
      change ‖vc‖ ≤ T * p y (frame yk vc) at hb
      rw [show frame yk vc = v from hback v] at hb
      exact hb
    have htw : ‖wc‖ ≤ T * p y w := by
      have hb := hTbound yk wc
      change ‖wc‖ ≤ T * p y (frame yk wc) at hb
      rw [show frame yk wc = w from hback w] at hb
      exact hb
    have hAval : ‖A y‖ ≤ max 1 M :=
      (hM (mem_image_of_mem _ (mem_univ yk))).trans (le_max_right _ _)
    have hReval : R y (complexTangentToReal d y v) (complexTangentToReal d y w) = A y vc wc := by
      have hv := E.symm_apply_apply (complexTangentToReal d y v)
      have hw := E.symm_apply_apply (complexTangentToReal d y w)
      exact (congrArg₂ (fun s t ↦ R y s t) hv hw).symm.trans (hRA y (hKO yk.property) vc wc)
    rw [hReval]
    calc
      ‖A y vc wc‖ ≤ ‖A y‖ * ‖vc‖ * ‖wc‖ := (A y).le_opNorm₂ vc wc
      _ ≤ max 1 M * (T * p y v) * (T * p y w) := by gcongr
      _ = C * p y v * p y w := by dsimp [C]; ring
  choose O hO hx C hC hbound using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO
    (fun x _ ↦ mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨max 1 (∑ x ∈ s, C x), le_max_left _ _, ?_⟩
  intro y v w
  obtain ⟨x, hxs, hy⟩ := mem_iUnion₂.mp (hs (mem_univ y))
  have hle : C x ≤ max 1 (∑ x ∈ s, C x) :=
    (Finset.single_le_sum (fun z _ ↦ zero_le_one.trans (hC z)) hxs).trans (le_max_right _ _)
  exact (hbound x y hy v w).trans (by
    change C x * p y v * p y w ≤ max 1 (∑ x ∈ s, C x) * p y v * p y w
    gcongr)

end HolomorphicAnosov

