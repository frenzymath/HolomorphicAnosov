import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

noncomputable section
open Filter
open scoped Topology ENNReal
namespace HolomorphicAnosov

/-- A unique admissible choice at one positive tolerance agrees with every sufficiently
small admissible choice. Thus eventual uniform existence at every tolerance produces
one selection satisfying all those eventual estimates. Source: elementary uniqueness
and filter intersection; used to make normal projections independent of error bounds.
Choose at a fixed positive tolerance, using the supplied fallback when absent. For a
new tolerance take its minimum with the fixed one. Monotonicity makes that witness
admissible at the fixed tolerance; uniqueness identifies it with the original choice. -/
theorem unique_small_selection_g18 {I : Type*} (l : Filter I)
    {X : I → Type*} {Y : I → Type*}
    (fallback : ∀ i, X i → Y i) (P : ∀ i, X i → Y i → ℝ → Prop)
    (hmono : ∀ i x y ε ε', P i x y ε → ε ≤ ε' → P i x y ε')
    (R : ℝ) (hR : 0 < R)
    (hunique : ∀ i x y y', P i x y R → P i x y' R → y = y')
    (hexists : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x, ∃ y, P i x y ε) :
    ∃ f : ∀ i, X i → Y i, ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x, P i x (f i x) ε := by
  classical
  let f : ∀ i, X i → Y i := fun i x ↦
    if h : ∃ y, P i x y R then h.choose else fallback i x
  have hf : ∀ᶠ i in l, ∀ x, P i x (f i x) R := by
    filter_upwards [hexists R hR] with i hi
    intro x
    simpa only [f,dite_eq_left (hi x)] using (hi x).choose_spec
  refine ⟨f,?_⟩
  intro ε hε
  filter_upwards [hf,hexists (min ε R) (lt_min hε hR)] with i hi he
  intro x
  obtain ⟨y,hy⟩ := he x
  have hfy := hunique i x (f i x) y (hi x)
    (hmono i x y _ _ hy (min_le_right _ _))
  exact hfy.symm ▸ hmono i x y _ _ hy (min_le_left _ _)

/-- A uniform eventual extended-real error bound has a nonnegative real null majorant.
Take the real value of the pointwise supremum. The supremum is eventually finite,
and the uniform bounds imply convergence of its real value to zero. -/
theorem uniform_ennreal_null_majorant_g18 {I : Type*} (l : Filter I)
    {X : I → Type*} (e : ∀ i, X i → ℝ≥0∞)
    (he : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x, e i x ≤ ENNReal.ofReal ε) :
    ∃ δ : I → ℝ, (∀ i, 0 ≤ δ i) ∧ Tendsto δ l (𝓝 0) ∧
      ∀ᶠ i in l, ∀ x, e i x ≤ ENNReal.ofReal (δ i) := by
  let s : I → ℝ≥0∞ := fun i ↦ ⨆ x, e i x
  have hs (ε : ℝ) (hε : 0 < ε) : ∀ᶠ i in l, s i ≤ ENNReal.ofReal ε :=
    (he ε hε).mono (fun _ hi ↦ iSup_le hi)
  refine ⟨fun i ↦ (s i).toReal,fun _ ↦ ENNReal.toReal_nonneg,?_,?_⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hs (ε / 2) (half_pos hε)] with i hi
    rw [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg]
    calc
      (s i).toReal ≤ (ENNReal.ofReal (ε / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hi
      _ = ε / 2 := ENNReal.toReal_ofReal (half_pos hε).le
      _ < ε := half_lt_self hε
  · filter_upwards [hs 1 (by norm_num)] with i hi
    intro x
    rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hi)]
    exact le_iSup (fun x ↦ e i x) x

/-- Uniform multiplicative estimates at every positive tolerance admit one real null
sequence of tolerances. Normalize by the source size and apply the extended-real
uniform-error majorant to the absolute relative distortion. At zero source size,
the estimate at tolerance one already forces the target size to vanish on the
eventual tail; no separate global zero-fiber hypothesis is required. -/
theorem uniform_multiplicative_null_error_g18 {I : Type*} (l : Filter I)
    {X : I → Type*} (a b : ∀ i, X i → ℝ)
    (ha : ∀ i x, 0 ≤ a i x)
    (he : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x,
      (1-ε)*a i x ≤ b i x ∧ b i x ≤ (1+ε)*a i x) :
    ∃ δ : I → ℝ, (∀ i, 0 ≤ δ i) ∧ Tendsto δ l (𝓝 0) ∧
      ∀ᶠ i in l, ∀ x, (1-δ i)*a i x ≤ b i x ∧ b i x ≤ (1+δ i)*a i x := by
  let error : ∀ i, X i → ℝ≥0∞ := fun i x ↦
    if a i x = 0 then 0 else ENNReal.ofReal |b i x / a i x - 1|
  have herror : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ x, error i x ≤ ENNReal.ofReal ε := by
    intro ε hε
    filter_upwards [he ε hε] with i hi
    intro x
    by_cases hx : a i x = 0
    · simp only [error,hx,ite_eq_left,zero_le]
    · have hp : 0 < a i x := lt_of_le_of_ne (ha i x) (Ne.symm hx)
      have hlo : 1-ε ≤ b i x / a i x := (le_div_iff₀ hp).mpr (hi x).1
      have hhi : b i x / a i x ≤ 1+ε := (div_le_iff₀ hp).mpr (hi x).2
      have habs : |b i x / a i x - 1| ≤ ε := abs_le.mpr ⟨by linarith only [hlo],by linarith only [hhi]⟩
      simpa only [error,hx,ite_false] using ENNReal.ofReal_le_ofReal habs
  obtain ⟨δ,hδ,ht,hbound⟩ := uniform_ennreal_null_majorant_g18 l error herror
  refine ⟨δ,hδ,ht,?_⟩
  filter_upwards [hbound,he 1 zero_lt_one] with i hi hunit
  intro x
  by_cases hx : a i x = 0
  · have hb : b i x = 0 := le_antisymm
      (by simpa only [hx,mul_zero] using (hunit x).2)
      (by simpa only [hx,mul_zero] using (hunit x).1)
    simp only [hx,hb,mul_zero,le_refl,and_self]
  · have hp : 0 < a i x := lt_of_le_of_ne (ha i x) (Ne.symm hx)
    have h := hi x
    simp only [error,hx,ite_false] at h
    have habs : |b i x / a i x - 1| ≤ δ i := (ENNReal.ofReal_le_ofReal_iff (hδ i)).mp h
    obtain ⟨hlo,hhi⟩ := abs_le.mp habs
    exact ⟨(le_div_iff₀ hp).mp (by linarith only [hlo]),
      (div_le_iff₀ hp).mp (by linarith only [hhi])⟩

end HolomorphicAnosov


end

noncomputable section
open Set Filter
open scoped Topology Manifold ContDiff
namespace HolomorphicAnosov

variable {E E' H H' X Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H] [TopologicalSpace H']
  (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace Y] [ChartedSpace H' Y]

omit [TopologicalSpace Y] in
/-- Uniqueness and strict continuous error bounds identify a selected map with its
local candidate on a neighborhood, retaining the formula needed for differentiation. -/
theorem unique_local_selection_eq_g18
    (W : Set X) (selected : X → Y) (P : X → Y → Prop)
    (hselected : ∀ z ∈ W, P z (selected z))
    (hunique : ∀ z ∈ W, ∀ y y', P z y → P z y' → y = y')
    (O : TopologicalSpace.Opens X) (z₀ : O) (hz₀ : z₀.val ∈ interior W)
    (ψ : O → Y)
    (distance : O → ENNReal) (size : O → ℝ) (R : ℝ)
    (hdistance : ContinuousAt distance z₀) (hsize : ContinuousAt size z₀)
    (hdistance₀ : distance z₀ < ENNReal.ofReal R) (hsize₀ : size z₀ < R)
    (hcertificate : ∀ z : O, z.val ∈ W → distance z < ENNReal.ofReal R →
      size z < R → P z.val (ψ z)) :
    (fun z : O ↦ selected z.val) =ᶠ[𝓝 z₀] ψ := by
  have hnear : ∀ᶠ z : O in 𝓝 z₀,
      z.val ∈ W ∧ distance z < ENNReal.ofReal R ∧ size z < R := by
    filter_upwards [continuous_subtype_val.continuousAt (isOpen_interior.mem_nhds hz₀),
      hdistance.eventually_lt continuousAt_const hdistance₀,
      hsize.eventually_lt continuousAt_const hsize₀] with z hz hd hs
    exact ⟨interior_subset hz,hd,hs⟩
  show (fun z : O ↦ selected z.val) =ᶠ[𝓝 z₀] ψ
  filter_upwards [hnear] with z hz
  exact hunique z.val hz.1 (selected z.val) (ψ z) (hselected z.val hz.1)
    (hcertificate z hz.1 hz.2.1 hz.2.2)


/-- A selected admissible point agrees near a marked point with a smooth local
candidate whenever two continuous errors remain strictly below the admissibility
threshold. This is the local uniqueness gluing step for physical normal projections. -/
theorem unique_local_smooth_gluing_g18
    (W : Set X) (selected : X → Y) (P : X → Y → Prop)
    (hselected : ∀ z ∈ W, P z (selected z))
    (hunique : ∀ z ∈ W, ∀ y y', P z y → P z y' → y = y')
    (O : TopologicalSpace.Opens X) (z₀ : O) (hz₀ : z₀.val ∈ interior W)
    (ψ : O → Y) (hψ : ContMDiff I I' 1 ψ)
    (distance : O → ENNReal) (size : O → ℝ) (R : ℝ)
    (hdistance : ContinuousAt distance z₀) (hsize : ContinuousAt size z₀)
    (hdistance₀ : distance z₀ < ENNReal.ofReal R) (hsize₀ : size z₀ < R)
    (hcertificate : ∀ z : O, z.val ∈ W → distance z < ENNReal.ofReal R →
      size z < R → P z.val (ψ z)) :
    ContMDiffAt I I' 1 selected z₀.val := by
  have heq := unique_local_selection_eq_g18 W selected P hselected hunique O z₀ hz₀
    ψ distance size R hdistance hsize hdistance₀ hsize₀ hcertificate
  exact contMDiffAt_subtype_iff.mp (hψ.contMDiffAt.congr_of_eventuallyEq heq)

/-- The local uniqueness gluing preserves every displayed coordinate formula for the
candidate. This supplies a germ equality as well as smoothness, so its derivative can
be identified in the same original charts. -/
theorem unique_local_smooth_formula_g18
    (W : Set X) (selected : X → Y) (P : X → Y → Prop)
    (hselected : ∀ z ∈ W, P z (selected z))
    (hunique : ∀ z ∈ W, ∀ y y', P z y → P z y' → y = y')
    (O : TopologicalSpace.Opens X) (z₀ : O) (hz₀ : z₀.val ∈ interior W)
    (ψ : O → Y) (hψ : ContMDiff I I' 1 ψ)
    (distance : O → ENNReal) (size : O → ℝ) (R : ℝ)
    (hdistance : ContinuousAt distance z₀) (hsize : ContinuousAt size z₀)
    (hdistance₀ : distance z₀ < ENNReal.ofReal R) (hsize₀ : size z₀ < R)
    (hcertificate : ∀ z : O, z.val ∈ W → distance z < ENNReal.ofReal R →
      size z < R → P z.val (ψ z))
    {Z : Type*} (coordinate : Y → Z) (raw : X → Z)
    (hformula : ∀ z : O, coordinate (ψ z) = raw z.val) :
    ContMDiffAt I I' 1 selected z₀.val ∧
      (coordinate ∘ selected) =ᶠ[𝓝 z₀.val] raw := by
  have heq := unique_local_selection_eq_g18 W selected P hselected hunique O z₀ hz₀
    ψ distance size R hdistance hsize hdistance₀ hsize₀ hcertificate
  refine ⟨contMDiffAt_subtype_iff.mp (hψ.contMDiffAt.congr_of_eventuallyEq heq),?_⟩
  rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z₀]
  exact heq.mono (fun z hz ↦ (congrArg coordinate hz).trans (hformula z))

end HolomorphicAnosov

end



noncomputable section
open Filter
open scoped Topology ContDiff Manifold
namespace HolomorphicAnosov
variable {E E' E₁ H H' H₁ X X' Y Z : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H₁]
  (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
  (I₁ : ModelWithCorners ℝ E₁ H₁)
  [TopologicalSpace X] [ChartedSpace H X]
  [TopologicalSpace X'] [ChartedSpace H₁ X']
  [TopologicalSpace Y] [ChartedSpace H' Y]

/-- Transport both local regularity and its exact coordinate germ by an original
leaf diffeomorphism. -/
theorem diffeomorph_transport_smooth_germ_g18
    (F : Diffeomorph I I₁ X X' ∞) (p : X → Y) (x : X)
    (hp : ContMDiffAt I I' 1 p x) (c : Y → Z) (raw : X' → Z)
    (heq : (c ∘ p) =ᶠ[𝓝 x] (raw ∘ F)) :
    ContMDiffAt I₁ I' 1 (p ∘ F.symm) (F x) ∧
      (c ∘ p ∘ F.symm) =ᶠ[𝓝 (F x)] raw := by
  refine ⟨?_,?_⟩
  · have hp' : ContMDiffAt I I' 1 p (F.symm (F x)) :=
      by simpa only [F.symm_apply_apply] using hp
    exact hp'.comp (F x) (F.symm.contMDiff.contMDiffAt.of_le (by simp))
  · have hcont : Tendsto F.symm (𝓝 (F x)) (𝓝 x) := by
      simpa only [F.symm_apply_apply] using (F.symm.continuous.continuousAt (x := F x)).tendsto
    have h := heq.comp_tendsto hcont
    filter_upwards [h] with z hz
    exact hz.trans (congrArg raw (F.apply_symm_apply z))
end HolomorphicAnosov
end
