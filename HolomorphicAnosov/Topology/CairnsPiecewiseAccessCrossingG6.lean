import HolomorphicAnosov.Topology.CairnsTwoRegionCrossingG6

open Set
namespace HolomorphicAnosov

/-- The piecewise affine access path in Cairns's diagonal construction crosses
any two-region labeling once. Normalize its parameter interval to the unit
interval. On its crossed affine piece, signed distance from the crossed edge is
a nonzero constant times the parameter displacement. It therefore changes sign
at the unique boundary meeting, and the continuous crossing lemma applies. -/
theorem cairns_piecewise_access_crossing_g6 {n : ℕ} (p : Polygon ℂ (n+1))
    (hne : p.HasNondegenerateEdges)
    (hsimple : ∀ i j : Fin (n+1), i ≠ j →
      p.edgeSet ℝ i ∩ p.edgeSet ℝ j ⊆
        p.vertices '' ({i,finRotate (n+1) i} ∩ {j,finRotate (n+1) j}))
    (Q E : Set ℂ) (hoQ : IsOpen Q) (hoE : IsOpen E)
    (hd : Disjoint Q E) (hc : Q ∪ E = (p.boundary ℝ)ᶜ)
    (hclQ : p.boundary ℝ ⊆ closure Q) (hclE : p.boundary ℝ ⊆ closure E)
    (m : ℕ) (hm : 0 < m) (w : Fin (m+1) → ℂ) (γ : ℝ → ℂ)
    (hγ : ContinuousOn γ (Icc (0:ℝ) m)) (hinj : InjOn γ (Icc (0:ℝ) m))
    (haff : ∀ (r : Fin m) (s : ℝ), s ∈ Icc (0:ℝ) 1 →
      γ ((r.val:ℝ)+s) = AffineMap.lineMap (w r.castSucc) (w r.succ) s)
    (r : Fin m) (s : ℝ) (k : Fin (n+1)) (hs : s ∈ Ioo (0:ℝ) 1)
    (hedge : γ ((r.val:ℝ)+s) ∈ openSegment ℝ (p k) (p (finRotate (n+1) k)))
    (htrans : (star (p (finRotate (n+1) k)-p k) * (w r.succ-w r.castSucc)).im ≠ 0)
    (hunique : ∀ τ ∈ Icc (0:ℝ) m, γ τ ∈ p.boundary ℝ ↔ τ = (r.val:ℝ)+s) :
    (γ 0 ∈ Q ∧ γ m ∈ E) ∨ (γ 0 ∈ E ∧ γ m ∈ Q) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hr0 : (0:ℝ) ≤ r.val := Nat.cast_nonneg _
  have hrm : (r.val:ℝ)+1 ≤ m := by exact_mod_cast r.isLt
  let t : ℝ := ((r.val:ℝ)+s)/m
  have ht0 : 0 < t := div_pos (by linarith [hs.1]) hmR
  have ht1 : t < 1 := (div_lt_one hmR).mpr (by linarith [hs.2])
  have hmt : (m:ℝ)*t = (r.val:ℝ)+s := mul_div_cancel₀ _ hmR.ne'
  let f : ℝ → ℂ := fun u ↦ γ ((m:ℝ)*u)
  have hmaps : MapsTo (fun u : ℝ ↦ (m:ℝ)*u) (Icc 0 1) (Icc 0 m) := by
    intro u hu
    exact ⟨mul_nonneg hmR.le hu.1, by nlinarith [hu.2]⟩
  have hf : ContinuousOn f (Icc 0 1) :=
    hγ.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have hfi : InjOn f (Icc 0 1) := by
    intro u hu v hv huv
    exact (mul_left_cancel₀ hmR.ne') (hinj (hmaps hu) (hmaps hv) huv)
  have hft : f t = γ ((r.val:ℝ)+s) := congrArg γ hmt
  have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht0.le,ht1.le⟩
  have hcross : f '' Icc 0 1 ∩ p.boundary ℝ = {f t} := by
    ext z
    constructor
    · rintro ⟨⟨u,hu,rfl⟩,huc⟩
      have heq : (m:ℝ)*u = (r.val:ℝ)+s := (hunique _ (hmaps hu)).mp huc
      have : u=t := (mul_left_cancel₀ hmR.ne') (heq.trans hmt.symm)
      simp [this]
    · rintro rfl
      refine ⟨⟨t,htI,rfl⟩,?_⟩
      exact (hunique _ (hmaps htI)).mpr hmt
  let L : ℂ →ₗ[ℝ] ℝ := Complex.imLm.comp
    (LinearMap.mulLeft ℝ (star (p (finRotate (n+1) k)-p k)))
  have hL (z : ℂ) :
      (star (p (finRotate (n+1) k)-p k)*(z-p k)).im = L z-L (p k) := by
    simp only [L, LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_sub, Complex.sub_im]
    rfl
  have hzero : L (γ ((r.val:ℝ)+s)) = L (p k) := by
    obtain ⟨ε,hε,hline⟩ := segment_local_line (hne k) hedge
    have hz := (hline _ (Metric.mem_ball_self hε)).mp (openSegment_subset_segment ℝ _ _ hedge)
    rw [hL] at hz
    exact sub_eq_zero.mp hz
  have hLv : L (w r.succ-w r.castSucc) ≠ 0 := htrans
  have hformula (u : ℝ) (hu : (m:ℝ)*u-(r.val:ℝ) ∈ Icc (0:ℝ) 1) :
      L (f u)-L (p k) = ((m:ℝ)*u-((r.val:ℝ)+s))*L (w r.succ-w r.castSucc) := by
    have h1 := haff r ((m:ℝ)*u-(r.val:ℝ)) hu
    have h2 := haff r s ⟨hs.1.le,hs.2.le⟩
    rw [show (r.val:ℝ)+((m:ℝ)*u-(r.val:ℝ)) = (m:ℝ)*u by ring] at h1
    have h1L := congrArg L h1
    have h2L := congrArg L h2
    simp only [AffineMap.lineMap_apply_module, map_add, map_smul, smul_eq_mul] at h1L h2L
    rw [hzero] at h2L
    dsimp only [f]
    rw [h1L,h2L,map_sub]
    ring
  obtain ⟨δ,hδ,hδbound⟩ := exists_between (show (0:ℝ) <
      min t (min (1-t) (min (s/m) ((1-s)/m))) by
    exact lt_min ht0 (lt_min (by linarith) (lt_min (div_pos hs.1 hmR) (div_pos (by linarith [hs.2]) hmR))))
  have hδt : δ < t := hδbound.trans_le (min_le_left _ _)
  have hδ1 : δ < 1-t := hδbound.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδs : (m:ℝ)*δ < s := by
    have := hδbound.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    nlinarith [(lt_div_iff₀ hmR).mp this]
  have hδs1 : (m:ℝ)*δ < 1-s := by
    have := hδbound.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    nlinarith [(lt_div_iff₀ hmR).mp this]
  have hsign : ∀ u ∈ Ioo (t-δ) t, ∀ v ∈ Ioo t (t+δ),
      (star (p (finRotate (n+1) k)-p k)*(f u-p k)).im *
        (star (p (finRotate (n+1) k)-p k)*(f v-p k)).im < 0 := by
    intro u hu v hv
    have hum : (m:ℝ)*u < (r.val:ℝ)+s := by nlinarith [hu.2]
    have hvm : (r.val:ℝ)+s < (m:ℝ)*v := by nlinarith [hv.1]
    have hui : (m:ℝ)*u-(r.val:ℝ) ∈ Icc (0:ℝ) 1 := by
      constructor <;> nlinarith [hu.1,hu.2]
    have hvi : (m:ℝ)*v-(r.val:ℝ) ∈ Icc (0:ℝ) 1 := by
      constructor <;> nlinarith [hv.1,hv.2]
    rw [hL,hL,hformula u hui,hformula v hvi]
    have hprod := mul_neg_of_neg_of_pos (sub_neg.mpr hum) (sub_pos.mpr hvm)
    have hsq := sq_pos_of_ne_zero hLv
    nlinarith [mul_neg_of_neg_of_pos hprod hsq]
  have hh := cairns_two_region_crossing_g6 p hne hsimple Q E hoQ hoE hd hc
    hclQ hclE f hf hfi ⟨k,t,⟨ht0,ht1⟩,hcross,hft.symm ▸ hedge,
      δ,hδ,hδt,hδ1,hsign⟩
  simpa only [f,mul_zero,mul_one] using hh

end HolomorphicAnosov
