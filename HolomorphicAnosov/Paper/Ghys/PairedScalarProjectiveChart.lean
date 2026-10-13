import HolomorphicAnosov.Ghys.AffineProjectiveStructure
import HolomorphicAnosov.Geometry.ComplexTangent
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Paired holomorphic scalar coordinates with complementary derivative kernels give local
biholomorphic projective product charts. Projective coordinate inverses preserve their real
derivative kernels. (Ghys, §5 p.598; Demailly, V §15.A p.277) -/

noncomputable section
open Set Filter _root_.Topology
open scoped ContDiff Manifold
namespace HolomorphicAnosov.Ghys
universe u

/-- A holomorphic map with invertible derivative has a local biholomorphic chart in the original
complex surface coordinates. -/
theorem surface_local_biholomorph_of_bijective_derivative
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (G : S → ℂ × ℂ) (O : Set S) (hO : IsOpen O) (x : S) (hx : x ∈ O)
    (hG : ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ G O)
    (hD : ∀ y ∈ O, Function.Bijective
      (mfderiv (complexModel 2) 𝓘(ℂ, ℂ × ℂ) G y)) :
    ∃ e : OpenPartialHomeomorph S (ℂ × ℂ),
      x ∈ e.source ∧ e.source ⊆ O ∧ (∀ y ∈ e.source, e y = G y) ∧
      ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e.symm e.target := by
  let k := chartAt (ComplexModel 2) x
  let F : ComplexModel 2 → ℂ × ℂ := G ∘ k.symm
  let V := k.target ∩ k.symm ⁻¹' O
  have hV : IsOpen V :=
    k.continuousOn_symm.isOpen_inter_preimage k.open_target hO
  have hk : ContMDiffOn (complexModel 2) (complexModel 2) ∞ k k.source :=
    contMDiffOn_chart
  have hki : ContMDiffOn (complexModel 2) (complexModel 2) ∞ k.symm k.target :=
    contMDiffOn_chart_symm
  have hkm : k.MDifferentiable (complexModel 2) (complexModel 2) :=
    ⟨hk.mdifferentiableOn (by simp), hki.mdifferentiableOn (by simp)⟩
  have hF (z : ComplexModel 2) (hz : z ∈ V) : ContDiffAt ℂ ∞ F z := by
    exact (((hG (k.symm z) hz.2).contMDiffAt (hO.mem_nhds hz.2)).comp z
      ((hki z hz.1).contMDiffAt (k.open_target.mem_nhds hz.1))).contDiffAt
  have hFD (z : ComplexModel 2) (hz : z ∈ V) :
      Function.Bijective (fderiv ℂ F z) := by
    have hgmd := ((hG (k.symm z) hz.2).contMDiffAt
      (hO.mem_nhds hz.2)).mdifferentiableAt (by simp)
    rw [← mfderiv_eq_fderiv,
      mfderiv_comp z hgmd (hkm.mdifferentiableAt_symm hz.1)]
    exact (hD (k.symm z) hz.2).comp (hkm.symm.mfderiv_bijective hz.1)
  have hxk : x ∈ k.source := mem_chart_source _ x
  have hkx : k x ∈ V := ⟨k.map_source hxk, by simpa [k.left_inv hxk] using hx⟩
  let L : ComplexModel 2 ≃L[ℂ] ℂ × ℂ :=
    ContinuousLinearEquiv.ofBijective (fderiv ℂ F (k x))
      (LinearMap.ker_eq_bot.mpr (hFD (k x) hkx).1)
      (LinearMap.range_eq_top.mpr (hFD (k x) hkx).2)
  have hFL : HasFDerivAt F (L : ComplexModel 2 →L[ℂ] ℂ × ℂ) (k x) := by
    rw [ContinuousLinearEquiv.coe_ofBijective]
    exact ((hF (k x) hkx).differentiableAt (by simp)).hasFDerivAt
  let p₀ := (hF (k x) hkx).toOpenPartialHomeomorph F hFL (by simp)
  let p := p₀.restrOpen V hV
  have hxp : k x ∈ p.source :=
    ⟨(hF (k x) hkx).mem_toOpenPartialHomeomorph_source hFL (by simp), hkx⟩
  have hpV : p.source ⊆ V := fun _ hz ↦ hz.2
  have hpF : (p : ComplexModel 2 → ℂ × ℂ) = F := rfl
  have hpi : ContDiffOn ℂ ∞ p.symm p.target := by
    intro y hy
    have hz := hpV (p.map_target hy)
    let A : ComplexModel 2 ≃L[ℂ] ℂ × ℂ :=
      ContinuousLinearEquiv.ofBijective (fderiv ℂ F (p.symm y))
        (LinearMap.ker_eq_bot.mpr (hFD _ hz).1)
        (LinearMap.range_eq_top.mpr (hFD _ hz).2)
    apply ContDiffAt.contDiffWithinAt
    apply p.contDiffAt_symm (f₀' := A) hy
    · rw [hpF, ContinuousLinearEquiv.coe_ofBijective]
      exact ((hF _ hz).differentiableAt (by simp)).hasFDerivAt
    · rw [hpF]
      exact hF _ hz
  let e := k.trans p
  have heO : e.source ⊆ O := by
    intro y hy
    have h := (hpV hy.2).2
    change k.symm (k y) ∈ O at h
    rwa [k.left_inv hy.1] at h
  have heG : ∀ y ∈ e.source, e y = G y := by
    intro y hy
    change F (k y) = G y
    simp only [F, Function.comp_apply, k.left_inv hy.1]
  refine ⟨e, ⟨hxk, hxp⟩, heO, heG, (hG.mono heO).congr heG, ?_⟩
  exact hki.comp (hpi.contMDiffOn.mono (fun _ hy ↦ hy.1)) (fun _ hy ↦ hy.2)

/-- Two holomorphic scalar coordinates with complementary derivative kernels form local
biholomorphic product coordinates. -/
theorem surface_scalar_pair_biholomorphic_chart
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (q₁ q₂ : S → ℂ) (O : Set S) (hO : IsOpen O) (x : S) (hx : x ∈ O)
    (h₁ : ContMDiffOn (complexModel 2) 𝓘(ℂ) ∞ q₁ O)
    (h₂ : ContMDiffOn (complexModel 2) 𝓘(ℂ) ∞ q₂ O)
    (hker : ∀ y ∈ O, IsCompl
      (mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).ker
      (mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).ker) :
    ∃ e : OpenPartialHomeomorph S (ℂ × ℂ),
      x ∈ e.source ∧ e.source ⊆ O ∧
      (∀ y ∈ e.source, e y = (q₁ y, q₂ y)) ∧
      ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e e.source ∧
      ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e.symm e.target := by
  let : NormedSpace ℂ (ℂ × ℂ) := Prod.normedSpace
  apply surface_local_biholomorph_of_bijective_derivative
    (fun y ↦ (q₁ y, q₂ y)) O hO x hx
  · rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h₁.prodMk h₂
  intro y hy
  have h₁d := ((h₁ y hy).contMDiffAt (hO.mem_nhds hy)).mdifferentiableAt (by simp)
  have h₂d := ((h₂ y hy).contMDiffAt (hO.mem_nhds hy)).mdifferentiableAt (by simp)
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod, mfderiv_prodMk h₁d h₂d]
  let L := (mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).toLinearMap.prod
    (mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).toLinearMap
  have hLi : Function.Injective L := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_prod]
    exact (hker y hy).disjoint.eq_bot
  have hdim : Module.finrank ℂ (TangentSpace (complexModel 2) y) =
      Module.finrank ℂ (ℂ × ℂ) := by
    exact (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).toLinearEquiv.finrank_eq
  exact ⟨hLi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hLi⟩

/-- A scalar product chart postcomposed with two projective chart inverses is a projective product
chart on the restricted domain. (Demailly, V §15.A p.277) -/
theorem surface_projective_pair_postcompose
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    (e : OpenPartialHomeomorph S (ℂ × ℂ))
    (he : ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e.symm e.target)
    (k₁ k₂ : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (hk₁ : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k₁ k₁.source)
    (hk₁i : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k₁.symm k₁.target)
    (hk₂ : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k₂ k₂.source)
    (hk₂i : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k₂.symm k₂.target)
    (x : S) (hx : x ∈ e.source)
    (hx₁ : (e x).1 ∈ k₁.target) (hx₂ : (e x).2 ∈ k₂.target) :
    ∃ c : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine),
      x ∈ c.source ∧ c.source ⊆ e.source ∧
      (∀ y, c y = (k₁.symm (e y).1, k₂.symm (e y).2)) ∧
      ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞
        c c.source ∧
      ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞
        c.symm c.target := by
  let J := k₁.symm.prod k₂.symm
  have hJ : ContMDiffOn 𝓘(ℂ, ℂ × ℂ)
      ((complexModel 1).prod (complexModel 1)) ∞ J J.source := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hk₁i.prodMap hk₂i
  have hJi : ContMDiffOn ((complexModel 1).prod (complexModel 1))
      𝓘(ℂ, ℂ × ℂ) ∞ J.symm J.target := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hk₁.prodMap hk₂
  refine ⟨e.trans J, ⟨hx, hx₁, hx₂⟩, inter_subset_left, fun _ ↦ rfl, ?_, ?_⟩
  · exact hJ.comp (he.mono inter_subset_left) (fun _ hz ↦ hz.2)
  · exact hei.comp (hJi.mono inter_subset_left) (fun _ hz ↦ hz.2)

/-- Paired holomorphic scalar coordinates with complementary derivative kernels yield a local
biholomorphic projective product chart in any two specified projective coordinate patches.
(Ghys, §5 p.598; Demailly, V §15.A p.277) -/
theorem surface_scalar_pair_projective_chart_in_coordinates
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (q₁ q₂ : S → ℂ) (O : Set S) (hO : IsOpen O) (x : S) (hx : x ∈ O)
    (h₁ : ContMDiffOn (complexModel 2) 𝓘(ℂ) ∞ q₁ O)
    (h₂ : ContMDiffOn (complexModel 2) 𝓘(ℂ) ∞ q₂ O)
    (hker : ∀ y ∈ O, IsCompl
      (mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).ker
      (mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).ker)
    (k₁ k₂ : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (hk₁ : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k₁ k₁.source)
    (hk₁i : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k₁.symm k₁.target)
    (hk₂ : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k₂ k₂.source)
    (hk₂i : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k₂.symm k₂.target)
    (hx₁ : q₁ x ∈ k₁.target) (hx₂ : q₂ x ∈ k₂.target) :
    ∃ c : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine),
      x ∈ c.source ∧ c.source ⊆ O ∧
      (∀ y ∈ c.source, c y = (k₁.symm (q₁ y), k₂.symm (q₂ y))) ∧
      ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞
        c c.source ∧
      ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞
        c.symm c.target := by
  obtain ⟨e, hxe, heO, heq, he, hei⟩ :=
    surface_scalar_pair_biholomorphic_chart q₁ q₂ O hO x hx h₁ h₂ hker
  obtain ⟨c, hxc, hce, hcv, hc, hci⟩ :=
    surface_projective_pair_postcompose e he hei k₁ k₂ hk₁ hk₁i hk₂ hk₂i x hxe
      (by simpa only [heq x hxe] using hx₁) (by simpa only [heq x hxe] using hx₂)
  refine ⟨c, hxc, hce.trans heO, ?_, hc, hci⟩
  intro y hy
  rw [hcv, heq y (hce hy)]

/-- The real derivative kernel of a holomorphic scalar function is the transported restriction of
scalars of its complex derivative kernel. (Demailly, I §3.C p.23) -/
theorem scalar_real_kernel_eq_complex_kernel
    {d : ℕ} {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel d) S]
    (q : S → ℂ) (x : S)
    (hq : MDifferentiableAt (complexModel d) 𝓘(ℂ) q x) :
    (mfderiv (realModel d) 𝓘(ℝ, ℂ) q x).ker =
      ((mfderiv (complexModel d) 𝓘(ℂ) q x).toLinearMap.ker.restrictScalars ℝ).map
        (complexTangentToReal d x).toLinearEquiv.toLinearMap := by
  have hreal : HasMFDerivAt (realModel d) 𝓘(ℝ, ℂ) q x
      ((mfderiv (complexModel d) 𝓘(ℂ) q x).restrictScalars ℝ) :=
    ⟨hq.continuousAt, hq.hasMFDerivAt.2.restrictScalars ℝ⟩
  rw [hreal.mfderiv]
  ext v
  constructor
  · intro hv
    exact ⟨v, hv, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact hw

/-- Postcomposition with a projective coordinate inverse preserves the real derivative kernel of a
scalar first integral. -/
theorem projective_coordinate_inverse_real_kernel
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    (q : S → ℂ) (x : S)
    (hq : MDifferentiableAt (realModel 2) 𝓘(ℝ, ℂ) q x)
    (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (hk : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source)
    (hki : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target)
    (hx : q x ∈ k.target) :
    (mfderiv (realModel 2) (realModel 1) (k.symm ∘ q) x).ker =
      (mfderiv (realModel 2) 𝓘(ℝ, ℂ) q x).ker := by
  have hkR : k.MDifferentiable (realModel 1) 𝓘(ℝ, ℂ) := by
    constructor
    · intro z hz
      obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp
        ((hk z hz).contMDiffAt (k.open_source.mem_nhds hz))
      exact ((contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩ :
        ContMDiffAt (realModel 1) 𝓘(ℝ, ℂ) ∞ k z).mdifferentiableAt
          (by simp)).mdifferentiableWithinAt
    · intro z hz
      obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp
        ((hki z hz).contMDiffAt (k.open_target.mem_nhds hz))
      exact ((contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩ :
        ContMDiffAt 𝓘(ℝ, ℂ) (realModel 1) ∞ k.symm z).mdifferentiableAt
          (by simp)).mdifferentiableWithinAt
  rw [mfderiv_comp x (hkR.mdifferentiableAt_symm hx) hq]
  ext v
  change (mfderiv 𝓘(ℝ, ℂ) (realModel 1) k.symm (q x))
    ((mfderiv (realModel 2) 𝓘(ℝ, ℂ) q x) v) = 0 ↔
      (mfderiv (realModel 2) 𝓘(ℝ, ℂ) q x) v = 0
  exact (hkR.symm.mfderiv_bijective hx).1.eq_iff' (map_zero _)

/-- Agreement as ambient germs with a scalar first integral postcomposed with a projective
coordinate inverse implies equality of their real derivative kernels. -/
theorem projective_coordinate_inverse_real_kernel_of_eventuallyEq
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    (q : S → ℂ) (φ : S → ComplexProjectiveLine) (x : S)
    (hq : MDifferentiableAt (realModel 2) 𝓘(ℝ, ℂ) q x)
    (k : OpenPartialHomeomorph ComplexProjectiveLine ℂ)
    (hk : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ k k.source)
    (hki : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ k.symm k.target)
    (hx : q x ∈ k.target) (heq : φ =ᶠ[𝓝 x] k.symm ∘ q) :
    (mfderiv (realModel 2) (realModel 1) φ x).ker =
      (mfderiv (realModel 2) 𝓘(ℝ, ℂ) q x).ker := by
  have hd := heq.mfderiv_eq (I := realModel 2) (I' := realModel 1)
  have hd' : mfderiv (realModel 2) (realModel 1) φ x =
      mfderiv (realModel 2) (realModel 1) (k.symm ∘ q) x := by
    ext v
    exact congrArg (fun L ↦ L v) hd
  rw [hd']
  exact projective_coordinate_inverse_real_kernel q x hq k hk hki hx

/-- Finite projectivization of a scalar product chart preserves its source and both holomorphic
directions. (Demailly, V §15.A p.277) -/
theorem surface_projectivize_scalar_pair_chart
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    (e : OpenPartialHomeomorph S (ℂ × ℂ))
    (he : ContMDiffOn (complexModel 2) 𝓘(ℂ, ℂ × ℂ) ∞ e e.source)
    (hei : ContMDiffOn 𝓘(ℂ, ℂ × ℂ) (complexModel 2) ∞ e.symm e.target) :
    ∃ c : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine),
      c.source = e.source ∧
      (∀ y, c y = (complexProjectiveLineFinite (e y).1,
        complexProjectiveLineFinite (e y).2)) ∧
      ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞
        c c.source ∧
      ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞
        c.symm c.target := by
  let j := canonicalPlaneCoordinate.symm.trans (complexProjectiveLineChart 1).symm
  have hjs : j.source = univ := by
    simp [j, canonicalPlaneCoordinate, complexProjectiveLineChart]
  have hjv (z : ℂ) : j z = complexProjectiveLineFinite z := rfl
  have hchart : complexProjectiveLineChart 1 ∈
      IsManifold.maximalAtlas (complexModel 1) ∞ ComplexProjectiveLine :=
    IsManifold.subset_maximalAtlas ⟨1, rfl⟩
  have hj : ContMDiffOn 𝓘(ℂ) (complexModel 1) ∞ j j.source :=
    (contMDiffOn_symm_of_mem_maximalAtlas hchart).comp
      (canonicalPlaneCoordinate_properties.2.1.2.mono inter_subset_left)
      (fun _ hz ↦ hz.2)
  have hji : ContMDiffOn (complexModel 1) 𝓘(ℂ) ∞ j.symm j.target :=
    canonicalPlaneCoordinate_properties.2.1.1.comp
      ((contMDiffOn_of_mem_maximalAtlas hchart).mono inter_subset_left)
      (fun _ hz ↦ hz.2)
  let J := j.prod j
  have hJs : J.source = univ := by simp [J, hjs]
  have hJ : ContMDiffOn 𝓘(ℂ, ℂ × ℂ)
      ((complexModel 1).prod (complexModel 1)) ∞ J J.source := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hj.prodMap hj
  have hJi : ContMDiffOn ((complexModel 1).prod (complexModel 1))
      𝓘(ℂ, ℂ × ℂ) ∞ J.symm J.target := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hji.prodMap hji
  let c := e.trans J
  have hcs : c.source = e.source := by simp [c, hJs]
  refine ⟨c, hcs, fun y ↦ ?_, ?_, ?_⟩
  · exact Prod.ext (hjv _) (hjv _)
  · exact hJ.comp (he.mono inter_subset_left) (fun _ hz ↦ hz.2)
  · exact hei.comp (hJi.mono inter_subset_left) (fun _ hz ↦ hz.2)

/-- Paired scalar first integrals with complementary complex derivative kernels give a local
biholomorphic chart in the ordered product of projective lines. (Ghys, §5 p.598; Demailly, V
§15.A p.277) -/
theorem surface_scalar_pair_projective_chart
    {S : Type u} [TopologicalSpace S] [ChartedSpace (ComplexModel 2) S]
    [IsManifold (complexModel 2) ∞ S]
    (q₁ q₂ : S → ℂ) (O : Set S) (hO : IsOpen O) (x : S) (hx : x ∈ O)
    (h₁ : ContMDiffOn (complexModel 2) 𝓘(ℂ) ∞ q₁ O)
    (h₂ : ContMDiffOn (complexModel 2) 𝓘(ℂ) ∞ q₂ O)
    (hker : ∀ y ∈ O, IsCompl
      (mfderiv (complexModel 2) 𝓘(ℂ) q₁ y).ker
      (mfderiv (complexModel 2) 𝓘(ℂ) q₂ y).ker) :
    ∃ c : OpenPartialHomeomorph S (ComplexProjectiveLine × ComplexProjectiveLine),
      x ∈ c.source ∧ c.source ⊆ O ∧
      (∀ y ∈ c.source, c y =
        (complexProjectiveLineFinite (q₁ y), complexProjectiveLineFinite (q₂ y))) ∧
      ContMDiffOn (complexModel 2) ((complexModel 1).prod (complexModel 1)) ∞
        c c.source ∧
      ContMDiffOn ((complexModel 1).prod (complexModel 1)) (complexModel 2) ∞
        c.symm c.target := by
  obtain ⟨e, hxe, heO, heq, he, hei⟩ :=
    surface_scalar_pair_biholomorphic_chart q₁ q₂ O hO x hx h₁ h₂ hker
  obtain ⟨c, hcs, hcv, hc, hci⟩ := surface_projectivize_scalar_pair_chart e he hei
  refine ⟨c, hcs.symm ▸ hxe, hcs.symm ▸ heO, ?_, hc, hci⟩
  intro y hy
  rw [hcv, heq y (hcs ▸ hy)]

end HolomorphicAnosov.Ghys
