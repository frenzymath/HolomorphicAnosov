import HolomorphicAnosov.Geometry.ComplexModel
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Lemmas
import HolomorphicAnosov.Topology.DiskDegreeLocalHomeomorphismCount
import Mathlib.Topology.Homotopy.Affine
import Mathlib.Tactic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open Set Metric
open scoped ContDiff _root_.Topology
namespace HolomorphicAnosov.Ghys

/-- The straight homotopy from `g z` to `F z` avoids `F a` when `g z` and `g a` are separated by `m`
and both perturbation errors are less than `m / 4`. -/
theorem fixed_comparison_boundary_avoidance_g18
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g F : E → E} {a z : E} {m : ℝ}
    (hm : 0 < m) (hsep : m ≤ ‖g z - g a‖)
    (hz : ‖F z - g z‖ < m / 4) (ha : ‖F a - g a‖ < m / 4)
    (t : unitInterval) :
    (1 - (t : ℝ)) • g z + (t : ℝ) • F z ≠ F a := by
  intro heq
  have ht : ‖(t : ℝ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg t.property.1] using t.property.2
  have herr : ‖(t : ℝ) • (F z - g z) - (F a - g a)‖ < m / 2 := by
    calc
      _ ≤ ‖(t : ℝ) • (F z - g z)‖ + ‖F a - g a‖ := norm_sub_le _ _
      _ ≤ ‖F z - g z‖ + ‖F a - g a‖ := by
        rw [norm_smul]
        exact add_le_add (mul_le_of_le_one_left (norm_nonneg (F z - g z)) ht) le_rfl
      _ < _ := by linarith
  have hc : g z - g a + ((t : ℝ) • (F z - g z) - (F a - g a)) = 0 := by
    calc
      _ = ((1 - (t : ℝ)) • g z + (t : ℝ) • F z) - F a := by module
      _ = 0 := sub_eq_zero.mpr heq
  have hn : ‖g z - g a‖ = ‖(t : ℝ) • (F z - g z) - (F a - g a)‖ :=
    (congrArg norm (eq_neg_of_add_eq_zero_left hc)).trans (norm_neg _)
  rw [← hn] at herr
  linarith

open HolomorphicAnosov.Topology

/-- A C¹ map with positive derivative determinant that is uniformly close to a homeomorphism is
injective on a buffered subset of a disk, provided its images there lie in the homeomorphic
image of the open disk. -/
theorem buffered_disk_comparison_injective_g18
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (F g : DiskDegreePlane → DiskDegreePlane)
    (hF : ContDiffOn ℝ 1 F O)
    (_hg : ContinuousOn g (closedBall c r))
    (hdet : ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ F z).toLinearMap)
    (V W : Set DiskDegreePlane) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hmatch : ∀ z : closedBall c r, g z = (h ⟨z.val, hBV z.property⟩).val)
    (K : Set DiskDegreePlane) (hK : K ⊆ ball c r)
    (m : ℝ) (hm : 0 < m)
    (hsep : ∀ a ∈ K, ∀ z ∈ sphere c r, m ≤ ‖g z - g a‖)
    (herr : ∀ z ∈ closedBall c r, ‖F z - g z‖ < m / 4)
    (hpre : ∀ a ∈ K, ∃ z : V, z.val ∈ ball c r ∧ (h z).val = F a) :
    InjOn F K := by
  intro a ha b hb hab
  have haB : a ∈ closedBall c r := ball_subset_closedBall (hK ha)
  have hboundary : ∀ z ∈ sphere c r, F z ≠ F a := by
    intro z hz
    simpa using fixed_comparison_boundary_avoidance_g18 hm (hsep a ha z hz)
      (herr z (sphere_subset_closedBall hz)) (herr a haB) (1 : unitInterval)
  let FB := diskDegreeRestriction c r F (hF.continuousOn.mono hBO)
  let gB := diskDegreeHomeomorphRestriction c r V W h hBV
  let H : ContinuousMap.Homotopy gB FB :=
    { toFun := fun p ↦ (1 - (p.1 : ℝ)) • gB p.2 + (p.1 : ℝ) • FB p.2
      continuous_toFun := by fun_prop
      map_zero_left := by intro z; simp
      map_one_left := by intro z; simp }
  have hH : BoundaryAvoidingDiskHomotopy c r FB gB (F a) := by
    refine ⟨H.symm, ?_⟩
    intro t z hz
    change (1 - ((unitInterval.symm t) : ℝ)) • gB z +
      ((unitInterval.symm t) : ℝ) • FB z ≠ F a
    change (1 - ((unitInterval.symm t) : ℝ)) •
      (h ⟨z.val, hBV z.property⟩).val + ((unitInterval.symm t) : ℝ) • F z ≠ F a
    rw [← hmatch z]
    exact fixed_comparison_boundary_avoidance_g18 hm (hsep a ha z hz)
      (herr z z.property) (herr a haB) (unitInterval.symm t)
  obtain ⟨_, _, d, _, _, _, _, hunique⟩ :=
    disk_degree_local_homeomorphism_count c r hr O hO hBO F hF hdet (F a) hboundary
  obtain ⟨z, hz, hu⟩ := hunique V W hV hW h hBV (hpre a ha) hH
  exact (hu a ⟨hK ha, rfl⟩).trans (hu b ⟨hK hb, hab.symm⟩).symm

/-- Maps converging uniformly on a closed disk to a homeomorphism are eventually injective on every
compact subset of its interior, provided they are eventually C¹ with positive derivative
determinant on a neighborhood of the disk. -/
theorem eventually_buffered_disk_comparison_injective_g18
    (c : DiskDegreePlane) (r : ℝ) (hr : 0 < r)
    (O : Set DiskDegreePlane) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (F : ℕ → DiskDegreePlane → DiskDegreePlane) (g : DiskDegreePlane → DiskDegreePlane)
    (hg : ContinuousOn g (closedBall c r))
    (V W : Set DiskDegreePlane) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hmatch : ∀ z : closedBall c r, g z = (h ⟨z.val, hBV z.property⟩).val)
    (K : Set DiskDegreePlane) (hKc : IsCompact K) (hK : K ⊆ ball c r)
    (hconv : TendstoUniformlyOn F g Filter.atTop (closedBall c r))
    (hregular : ∀ᶠ k in Filter.atTop,
      ContDiffOn ℝ 1 (F k) O ∧
        ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ (F k) z).toLinearMap) :
    ∀ᶠ k in Filter.atTop, InjOn (F k) K := by
  have hKB : K ⊆ closedBall c r := hK.trans ball_subset_closedBall
  have hinj : InjOn g (closedBall c r) := by
    intro x hx y hy he
    apply congrArg Subtype.val (h.injective
      (a₁ := (⟨x, hBV hx⟩ : V)) (a₂ := (⟨y, hBV hy⟩ : V)) ?_)
    apply Subtype.ext
    exact (hmatch ⟨x, hx⟩).symm.trans (he.trans (hmatch ⟨y, hy⟩))
  have himage : IsOpen (g '' ball c r) := by
    have he : g '' ball c r = Subtype.val ''
        (h '' ((Subtype.val : V → DiskDegreePlane) ⁻¹' ball c r)) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨h ⟨x, hBV (ball_subset_closedBall hx)⟩, ?_, ?_⟩
        · exact ⟨⟨x, hBV (ball_subset_closedBall hx)⟩, hx, rfl⟩
        · exact (hmatch ⟨x, ball_subset_closedBall hx⟩).symm
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x.val, hx, hmatch ⟨x.val, ball_subset_closedBall hx⟩⟩
    rw [he]
    exact hW.isOpenMap_subtype_val _
      (h.isOpenMap _ (isOpen_ball.preimage continuous_subtype_val))
  obtain ⟨m, hm, hsep⟩ : ∃ m > 0,
      ∀ a ∈ K, ∀ z ∈ sphere c r, m ≤ ‖g z - g a‖ := by
    let T := K ×ˢ sphere c r
    have hTc : IsCompact T := hKc.prod (isCompact_sphere c r)
    by_cases hne : T.Nonempty
    · have hcont : ContinuousOn (fun z : DiskDegreePlane × DiskDegreePlane ↦
          ‖g z.2 - g z.1‖) T :=
        ((hg.comp continuous_snd.continuousOn
          (fun _ hz ↦ sphere_subset_closedBall hz.2)).sub
          (hg.comp continuous_fst.continuousOn (fun _ hz ↦ hKB hz.1))).norm
      obtain ⟨z, hz, hmin⟩ := hTc.exists_isMinOn hne hcont
      have hp : 0 < ‖g z.2 - g z.1‖ := by
        apply norm_pos_iff.mpr
        intro he
        have hez := hinj (sphere_subset_closedBall hz.2) (hKB hz.1) (sub_eq_zero.mp he)
        have hlt : dist z.2 c < r := hez ▸ hK hz.1
        exact (ne_of_lt hlt) hz.2
      refine ⟨‖g z.2 - g z.1‖, hp, ?_⟩
      intro a ha w hw
      exact hmin (a := (a,w)) (show (a,w) ∈ T from ⟨ha, hw⟩)
    · exact ⟨1, zero_lt_one, fun a ha z hz ↦ (hne ⟨(a,z),ha,hz⟩).elim⟩
  have hcompact : IsCompact (g '' K) := hKc.image_of_continuousOn (hg.mono hKB)
  obtain ⟨δ, hδ, hδimage⟩ := hcompact.exists_thickening_subset_open himage (image_mono hK)
  have htol : 0 < min (m / 4) δ := lt_min (by positivity) hδ
  filter_upwards [hregular, (Metric.tendstoUniformlyOn_iff.mp hconv) _ htol] with k hk herr
  apply buffered_disk_comparison_injective_g18 c r hr O hO hBO (F k) g hk.1 hg
    hk.2 V W hV hW h hBV hmatch K hK m hm hsep
  · intro z hz
    have hzerr := (herr z hz).trans_le (min_le_left (m / 4) δ)
    simpa only [dist_eq_norm, norm_sub_rev] using hzerr
  · intro a ha
    have haerr : dist (F k a) (g a) < δ := by
      simpa only [dist_comm] using (herr a (hKB ha)).trans_le (min_le_right (m / 4) δ)
    have hmem : F k a ∈ g '' ball c r :=
      hδimage (mem_thickening_iff.mpr ⟨g a, mem_image_of_mem g ha, haerr⟩)
    obtain ⟨z, hz, he⟩ := hmem
    refine ⟨⟨z, hBV (ball_subset_closedBall hz)⟩, hz, ?_⟩
    exact (hmatch ⟨z, ball_subset_closedBall hz⟩).symm.trans he

end HolomorphicAnosov.Ghys


noncomputable section
open Set Metric Filter
open scoped ContDiff _root_.Topology
namespace HolomorphicAnosov.Ghys
open HolomorphicAnosov.Topology

/-- The real linear isometry from `ComplexModel 1` to the degree plane given by evaluation at the
unique coordinate. -/
def complexLineDiskIsometry_g18 : ComplexModel 1 ≃ₗᵢ[ℝ] DiskDegreePlane :=
  ({ toLinearEquiv := LinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℂ)
     norm_map' := by
       intro v
       change ‖v default‖ = ‖v‖
       apply le_antisymm (norm_le_pi_norm v default)
       apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
       intro i
       exact le_of_eq (congrArg (fun j ↦ ‖v j‖) (Subsingleton.elim i default)) } :
    ComplexModel 1 ≃ₗᵢ[ℝ] ℂ).trans Complex.orthonormalBasisOneI.repr

/-- Conjugation by the real linear isometry from `ComplexModel 1` to the degree plane preserves the
derivative determinant. -/
theorem complex_line_disk_derivative_det_g18
    (F : ComplexModel 1 → ComplexModel 1) (x : ComplexModel 1)
    (hF : DifferentiableAt ℝ F x) :
    let e := complexLineDiskIsometry_g18
    LinearMap.det (fderiv ℝ (e ∘ F ∘ e.symm) (e x)).toLinearMap =
      LinearMap.det (fderiv ℝ F x).toLinearMap := by
  dsimp only
  let e := complexLineDiskIsometry_g18
  have hf : HasFDerivAt F (fderiv ℝ F x) (e.symm (e x)) := by simpa using hF.hasFDerivAt
  have hd := e.toContinuousLinearEquiv.hasFDerivAt.comp (e x)
    (hf.comp (e x) e.symm.toContinuousLinearEquiv.hasFDerivAt)
  change LinearMap.det (fderiv ℝ (e.toContinuousLinearEquiv ∘ F ∘ e.symm) (e x)).toLinearMap = _
  rw [hd.fderiv]
  exact LinearMap.det_conj (fderiv ℝ F x).toLinearMap e.toLinearEquiv


/-- Maps on `ComplexModel 1` converging uniformly on a closed disk to a homeomorphism are eventually
injective on every compact subset of its interior, provided they are eventually C¹ with positive
derivative determinant on a neighborhood of the disk. -/
theorem eventually_complex_buffered_disk_comparison_injective_g18
    (c : ComplexModel 1) (r : ℝ) (hr : 0 < r)
    (O : Set (ComplexModel 1)) (hO : IsOpen O) (hBO : closedBall c r ⊆ O)
    (F : ℕ → ComplexModel 1 → ComplexModel 1) (g : ComplexModel 1 → ComplexModel 1)
    (hg : ContinuousOn g (closedBall c r))
    (V W : Set (ComplexModel 1)) (hV : IsOpen V) (hW : IsOpen W)
    (h : V ≃ₜ W) (hBV : closedBall c r ⊆ V)
    (hmatch : ∀ z : closedBall c r, g z = (h ⟨z.val, hBV z.property⟩).val)
    (K : Set (ComplexModel 1)) (hKc : IsCompact K) (hK : K ⊆ ball c r)
    (hconv : TendstoUniformlyOn F g atTop (closedBall c r))
    (hregular : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (F k) O ∧
      ∀ z ∈ O, 0 < LinearMap.det (fderiv ℝ (F k) z).toLinearMap) :
    ∀ᶠ k in atTop, InjOn (F k) K := by
  let e := complexLineDiskIsometry_g18
  let O' := e '' O
  let V' := e '' V
  let W' := e '' W
  let K' := e '' K
  let F' := fun k ↦ e ∘ F k ∘ e.symm
  let g' := e ∘ g ∘ e.symm
  have hcb : ∀ z ∈ closedBall (e c) r, e.symm z ∈ closedBall c r := by
    intro z hz
    rw [← e.image_closedBall] at hz
    obtain ⟨x,hx,rfl⟩ := hz
    simpa using hx
  have hO' : IsOpen O' := e.toHomeomorph.isOpenMap O hO
  have hV' : IsOpen V' := e.toHomeomorph.isOpenMap V hV
  have hW' : IsOpen W' := e.toHomeomorph.isOpenMap W hW
  have hBO' : closedBall (e c) r ⊆ O' := by
    rw [← e.image_closedBall]
    exact image_mono hBO
  have hBV' : closedBall (e c) r ⊆ V' := by
    rw [← e.image_closedBall]
    exact image_mono hBV
  let ev : V ≃ₜ V' := e.toHomeomorph.image V
  let ew : W ≃ₜ W' := e.toHomeomorph.image W
  let h' : V' ≃ₜ W' := ev.symm.trans (h.trans ew)
  have hmatch' : ∀ z : closedBall (e c) r,
      g' z = (h' ⟨z.val,hBV' z.property⟩).val := by
    intro z
    have hz := hcb z.val z.property
    have hv : ev.symm ⟨z.val,hBV' z.property⟩ = ⟨e.symm z.val,hBV hz⟩ := by
      apply ev.injective
      apply Subtype.ext
      rw [ev.apply_symm_apply]
      change z.val = e (e.symm z.val)
      exact (e.apply_symm_apply _).symm
    change e (g (e.symm z.val)) = e (h (ev.symm ⟨z.val,hBV' z.property⟩)).val
    rw [hv,hmatch ⟨e.symm z.val,hz⟩]
  have hg' : ContinuousOn g' (closedBall (e c) r) :=
    e.continuous.comp_continuousOn (hg.comp e.symm.continuous.continuousOn hcb)
  have hK' : K' ⊆ ball (e c) r := by rw [← e.image_ball]; exact image_mono hK
  have hconv' : TendstoUniformlyOn F' g' atTop (closedBall (e c) r) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hconv) ε hε] with k hk
    intro z hz
    change dist (e (g (e.symm z))) (e (F k (e.symm z))) < ε
    rw [e.dist_map]
    exact hk _ (hcb z hz)
  have hregular' : ∀ᶠ k in atTop, ContDiffOn ℝ 1 (F' k) O' ∧
      ∀ z ∈ O', 0 < LinearMap.det (fderiv ℝ (F' k) z).toLinearMap := by
    filter_upwards [hregular] with k hk
    have hmaps : MapsTo e.symm O' O := by
      rintro z ⟨x,hx,rfl⟩
      simpa using hx
    refine ⟨e.toContinuousLinearEquiv.contDiff.comp_contDiffOn
      (hk.1.comp e.symm.toContinuousLinearEquiv.contDiff.contDiffOn hmaps),?_⟩
    rintro z ⟨x,hx,rfl⟩
    rw [complex_line_disk_derivative_det_g18 (F k) x
      ((hk.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp))]
    exact hk.2 x hx
  have hfinal := eventually_buffered_disk_comparison_injective_g18 (e c) r hr O' hO' hBO'
    F' g' hg' V' W' hV' hW' h' hBV' hmatch' K'
    (hKc.image e.continuous) hK' hconv' hregular'
  filter_upwards [hfinal] with k hk
  intro x hx y hy hxy
  apply e.injective
  apply hk (mem_image_of_mem e hx) (mem_image_of_mem e hy)
  change e (F k (e.symm (e x))) = e (F k (e.symm (e y)))
  simpa only [e.symm_apply_apply] using congrArg e hxy

end HolomorphicAnosov.Ghys
