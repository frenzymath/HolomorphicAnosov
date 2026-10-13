import HolomorphicAnosov.Analysis.Complex.QCRengelFiniteEnergyAffine
import HolomorphicAnosov.Analysis.Complex.HolomorphicImageArea
import HolomorphicAnosov.Analysis.Complex.QCRengelRectangleEnergy
import HolomorphicAnosov.Analysis.Complex.QCPartitionOppositeDiagonals
import HolomorphicAnosov.Analysis.Complex.QCRectangleOppositeCornerCrossing

/-! # Two-piece equality rigidity in a normalized rectangle

Source: Lehto--Virtanen, *Quasiconformal Mappings in the Plane* (1973),
Chapter I, Lemma 4.2, p.25, with the equality case of Rengel's inequality
from I.§4.3, pp.22--23. -/

namespace HolomorphicAnosov

open Set Filter MeasureTheory _root_.Topology Analysis.MarkedRectangle
open scoped ENNReal
open scoped Pointwise

/-- A source-faithful marked model for a partition piece.  The complete two a-sides of
its model rectangle are required to map into the two corresponding a-sides of the
ambient rectangle.  `flip` records the harmless reversal of the two side labels.
This packages the whole-side condition in Lehto--Virtanen I.Lemma 4.2 rather than
replacing it by pointwise interior height bounds. -/
def HasMarkedConformalModulusWithCompleteASides
    (Q : Set ℂ) (p : Fin 4 → ℂ) (m M : ℝ) (flip : Bool) : Prop :=
  ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ m = a / b ∧
    ∃ F F_inv : ℂ → ℂ,
      DifferentiableOn ℂ F (OpenRectangle a b) ∧
      DifferentiableOn ℂ F_inv Q ∧
      BijOn F (OpenRectangle a b) Q ∧
      MapsTo F_inv Q (OpenRectangle a b) ∧
      (∀ z ∈ OpenRectangle a b, F_inv (F z) = z) ∧
      (∀ w ∈ Q, F (F_inv w) = w) ∧
      ∃ boundaryExtension : ClosedRectangle a b ≃ₜ closure Q,
        (∀ z : ClosedRectangle a b,
          (z : ℂ) ∈ OpenRectangle a b → (boundaryExtension z : ℂ) = F z) ∧
        (∀ (i : Fin 4) (z : ClosedRectangle a b),
          (z : ℂ) = RectangleCorner a b i → (boundaryExtension z : ℂ) = p i) ∧
        (∀ z : ClosedRectangle a b,
          (z : ℂ) ∈ ClosedRectangleSide a b 0 →
            (boundaryExtension z : ℂ) ∈
              ClosedRectangleSide M 1 (if flip then 2 else 0)) ∧
        (∀ z : ClosedRectangle a b,
          (z : ℂ) ∈ ClosedRectangleSide a b 2 →
            (boundaryExtension z : ℂ) ∈
              ClosedRectangleSide M 1 (if flip then 0 else 2))

/-- The side-aware witness contains the ordinary marked conformal-modulus witness.
This is a projection, so all existing modulus inequalities remain applicable. -/
lemma HasMarkedConformalModulusWithCompleteASides.hasModulus
    {Q : Set ℂ} {p : Fin 4 → ℂ} {m M : ℝ} {flip : Bool}
    (h : HasMarkedConformalModulusWithCompleteASides Q p m M flip) :
    HasMarkedConformalModulus Q p m := by
  obtain ⟨a, b, ha, hb, hm, F, F_inv, hF, hF_inv, hFbij, hFmaps,
    hFleft, hFright, boundaryExtension, hExt, hCorners, _, _⟩ := h
  exact ⟨a, b, ha, hb, hm, F, F_inv, hF, hF_inv, hFbij, hFmaps,
    hFleft, hFright, boundaryExtension, hExt, hCorners⟩

/-- The marked moduli carried by the two pieces are nondegenerate.  This
elementary consequence is kept separate because the equality-rigidity step
uses positivity when turning the saturated sum into the two Rengel equalities.
The side lengths in each witness are strictly positive by definition. -/
lemma qc_partition_moduli_pos
    {P₁ P₂ : Set ℂ} {p₁ p₂ : Fin 4 → ℂ} {hm₁ hm₂ : ℝ}
    (hmod₁ : HasMarkedConformalModulus P₁ p₁ hm₁)
    (hmod₂ : HasMarkedConformalModulus P₂ p₂ hm₂) :
    0 < hm₁ ∧ 0 < hm₂ := by
  constructor
  · obtain ⟨a, b, ha, hb, hab, _⟩ := hmod₁
    rw [hab]
    exact div_pos ha hb
  · obtain ⟨a, b, ha, hb, hab, _⟩ := hmod₂
    rw [hab]
    exact div_pos ha hb

/-- Each marked corner is a point of the corresponding closed piece.  The
closure extension in a modulus witness is onto `closure P`, so evaluating it
at the source corner produces the prescribed mark as an actual closure point.
This records the boundary transport needed before applying the partition
equality argument. -/
lemma qc_partition_marked_corners_mem_closure
    {P : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus P p m) :
    ∀ i : Fin 4, p i ∈ closure P := by
  obtain ⟨a, b, ha, hb, hm, F, F_inv, hF, hF_inv, hFbij, hFmaps,
    hFleft, hFright, boundaryExtension, hExt, hCorners⟩ := hmod
  intro i
  let z : ClosedRectangle a b :=
    ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩
  have hz : (boundaryExtension z : ℂ) = p i := by
    exact hCorners i z rfl
  have hzmem : (boundaryExtension z : ℂ) ∈ closure P :=
    (boundaryExtension z).property
  rw [hz] at hzmem
  exact hzmem

/-- A marked rectangle witness cannot represent an empty piece: the open source
rectangle has a concrete midpoint, and the witness bijection maps that point
into the target region. -/
lemma qc_partition_piece_nonempty
    {P : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus P p m) : P.Nonempty := by
  obtain ⟨a, b, ha, hb, hm, F, F_inv, hF, hF_inv, hFbij, hFmaps,
    hFleft, hFright, boundaryExtension, hExt, hCorners⟩ := hmod
  let z : ℂ := (a / 2 : ℂ) + (b / 2 : ℂ) * Complex.I
  have hz : z ∈ OpenRectangle a b := by
    simp [z, OpenRectangle, Complex.reProdIm]
    constructor <;> linarith
  exact ⟨F z, hFbij.mapsTo hz⟩

/-- The interior of a marked rectangle model is connected, and the witness
map therefore transfers connectedness to its target piece. -/
lemma qc_partition_piece_connected
    {P : Set ℂ} {p : Fin 4 → ℂ} {m : ℝ}
    (hmod : HasMarkedConformalModulus P p m) : IsConnected P := by
  obtain ⟨a, b, ha, hb, hm, F, F_inv, hF, hF_inv, hFbij, hFmaps,
    hFleft, hFright, boundaryExtension, hExt, hCorners⟩ := hmod
  have hconv : Convex ℝ (OpenRectangle a b) := by
    change Convex ℝ (Complex.equivRealProdLm.toLinearMap ⁻¹'
      (Ioo 0 a ×ˢ Ioo 0 b))
    exact ((convex_Ioo (0 : ℝ) a).prod (convex_Ioo (0 : ℝ) b)).linear_preimage
      Complex.equivRealProdLm.toLinearMap
  have hne : (OpenRectangle a b).Nonempty := by
    refine ⟨((a / 2 : ℝ) : ℂ) + ((b / 2 : ℝ) : ℂ) * Complex.I, ?_⟩
    simp [OpenRectangle, Complex.reProdIm]
    constructor <;> linarith
  have hconn : IsConnected (OpenRectangle a b) := hconv.isConnected hne
  rw [← hFbij.image_eq]
  exact hconn.image F hF.continuousOn

/-- Under the saturated sum, positivity of both piece moduli makes each one
strictly smaller than the ambient width. -/
lemma qc_partition_moduli_lt_ambient
    {M hm₁ hm₂ : ℝ} (hM : 0 < M) (hmod₁ : 0 < hm₁) (hmod₂ : 0 < hm₂)
    (hsum : hm₁ + hm₂ = M) : hm₁ < M ∧ hm₂ < M := by
  have hM' : 0 ≤ M := hM.le
  constructor <;> nlinarith [hM']

/-- Two nonempty zero-origin open rectangles always intersect. -/
lemma qc_partition_origin_rectangles_not_disjoint {a b c d : ℝ}
    (ha : (OpenRectangle a b).Nonempty) (hc : (OpenRectangle c d).Nonempty) :
    ¬ Disjoint (OpenRectangle a b) (OpenRectangle c d) := by
  obtain ⟨z, hz⟩ := ha
  obtain ⟨w, hw⟩ := hc
  change (0 < z.re ∧ z.re < a) ∧ (0 < z.im ∧ z.im < b) at hz
  change (0 < w.re ∧ w.re < c) ∧ (0 < w.im ∧ w.im < d) at hw
  let v : ℂ := ⟨min z.re w.re, min z.im w.im⟩
  have hv : v ∈ OpenRectangle a b := by
    exact ⟨⟨lt_min hz.1.1 hw.1.1, (min_le_left _ _).trans_lt hz.1.2⟩,
      ⟨lt_min hz.2.1 hw.2.1, (min_le_left _ _).trans_lt hz.2.2⟩⟩
  have hv' : v ∈ OpenRectangle c d := by
    exact ⟨⟨lt_min hz.1.1 hw.1.1, (min_le_right _ _).trans_lt hw.1.2⟩,
      ⟨lt_min hz.2.1 hw.2.1, (min_le_right _ _).trans_lt hw.2.2⟩⟩
  intro hdisj
  exact Set.disjoint_left.mp hdisj hv hv'

/-- Historical audit helper: the former zero-origin rigidity conclusion was incompatible
with two nonempty disjoint pieces. The main theorem now uses translated rectangles. -/
lemma qc_partition_conclusion_incompatible {P₁ P₂ : Set ℂ}
    (h₁ : P₁.Nonempty) (h₂ : P₂.Nonempty) (hd : Disjoint P₁ P₂) (M : ℝ) :
    ¬ ∃ x₁ x₂ : ℝ, 0 ≤ x₁ ∧ x₁ ≤ x₂ ∧ x₂ ≤ M ∧
      P₁ = OpenRectangle x₁ (x₂ - x₁) ∧
      P₂ = OpenRectangle x₂ (M - x₂) := by
  rintro ⟨x₁, x₂, _, _, _, rfl, rfl⟩
  exact qc_partition_origin_rectangles_not_disjoint h₁ h₂ hd

/-- Historical semantic audit: the old common-corner models force opposite
corner arcs to cross inside two supposedly disjoint pieces. The corrected
rigidity theorem below uses independent corner maps and complete horizontal
sides; this contradiction is not used in its proof. -/
theorem qc_partition_hypotheses_inconsistent
    (M : ℝ) (hM : 0 < M)
    (P₁ P₂ : Set ℂ)
    (hopen₁ : IsOpen P₁) (hopen₂ : IsOpen P₂)
    (hdisj : Disjoint P₁ P₂)
    (hinside₁ : closure P₁ ⊆ closure (OpenRectangle M 1))
    (hinside₂ : closure P₂ ⊆ closure (OpenRectangle M 1))
    (hm₁ hm₂ : ℝ)
    (hmod₁ : HasMarkedConformalModulus P₁ (fun i : Fin 4 ↦ RectangleCorner M 1 i) hm₁)
    (hmod₂ : HasMarkedConformalModulus P₂ (fun i : Fin 4 ↦ RectangleCorner M 1 i) hm₂) : False := by
  obtain ⟨α, β, hα, hβ, hα0, hα1, hβ0, hβ1, hclosed, hopen, hne⟩ :=
    qc_partition_opposite_diagonals hM hopen₁ hopen₂ hdisj hinside₁ hinside₂ hmod₁ hmod₂
  obtain ⟨s, t, hs0, hs1, ht0, ht1, heq⟩ :=
    qc_rectangle_opposite_corner_crossing hM α β hα hβ hα0 hα1 hβ0 hβ1
      hclosed hopen
  exact hne s t hs0 hs1 ht0 ht1 heq

/-- Rescale the marked source and extend its boundary parametrization. -/
private lemma partition_normalized_model {Q : Set ℂ} {p : Fin 4 → ℂ}
    {m M : ℝ} {flip : Bool}
    (h : HasMarkedConformalModulusWithCompleteASides Q p m M flip) :
    0 < m ∧ ∃ f : ℂ → ℂ,
      ContinuousOn f (ClosedRectangle m 1) ∧
      DifferentiableOn ℂ f (OpenRectangle m 1) ∧
      BijOn f (OpenRectangle m 1) Q ∧
      ∀ x ∈ Icc 0 m, (f (x : ℂ)).im = (if flip then 1 else 0) ∧
        (f ((x : ℂ) + Complex.I)).im = (if flip then 0 else 1) := by
  classical
  obtain ⟨a, b, ha, hb, rfl, F, Fi, hF, hFi, hbij, hmaps, hleft, hright,
    e, he, hcorners, hbottom, htop⟩ := h
  let g : ℂ → ℂ := Function.extend Subtype.val
    (fun z : ClosedRectangle a b ↦ (e z : ℂ)) (fun _ ↦ 0)
  have hge (z : ClosedRectangle a b) : g z = (e z : ℂ) :=
    Subtype.val_injective.extend_apply _ _ z
  have hgc : ContinuousOn g (ClosedRectangle a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.continuous).congr (fun z ↦ (hge z).symm)
  have hsub : OpenRectangle a b ⊆ ClosedRectangle a b := fun _ hz ↦
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hgF : EqOn g F (OpenRectangle a b) := fun z hz ↦
    (hge ⟨z, hsub hz⟩).trans (he ⟨z, hsub hz⟩ hz)
  let S : ℂ → ℂ := fun z ↦ (b : ℂ) * z
  have hS (z : ℂ) : S z ∈ OpenRectangle a b ↔ z ∈ OpenRectangle (a / b) 1 := by
    simp only [S, OpenRectangle, Complex.mem_reProdIm, mem_Ioo,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, add_zero]
    rw [mul_pos_iff_of_pos_left hb, ← lt_div_iff₀' hb,
      mul_pos_iff_of_pos_left hb, ← lt_div_iff₀' hb, div_self hb.ne']
  have hSc : MapsTo S (ClosedRectangle (a / b) 1) (ClosedRectangle a b) := by
    intro z hz
    simp only [S, ClosedRectangle, Complex.mem_reProdIm, mem_Icc, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    change (0 ≤ b * z.re ∧ b * z.re ≤ a) ∧ (0 ≤ b * z.im ∧ b * z.im ≤ b)
    exact ⟨⟨mul_nonneg hb.le hz.1.1, (le_div_iff₀' hb).mp hz.1.2⟩,
      ⟨mul_nonneg hb.le hz.2.1, by nlinarith [hz.2.2]⟩⟩
  have hSb : BijOn S (OpenRectangle (a / b) 1) (OpenRectangle a b) := by
    refine ⟨fun z hz ↦ (hS z).mpr hz, ?_, ?_⟩
    · intro z hz w hw hzw
      exact mul_left_cancel₀ (by exact_mod_cast hb.ne' : (b : ℂ) ≠ 0) hzw
    · intro w hw
      refine ⟨w / b, (hS _).mp ?_, ?_⟩
      all_goals simp_all [S, mul_div_cancel₀, mul_comm, hb.ne']
  refine ⟨div_pos ha hb, g ∘ S, hgc.comp (by fun_prop) hSc,
    (hF.congr hgF).comp (by fun_prop) (fun z hz ↦ (hS z).mpr hz),
    (hbij.congr hgF.symm).comp hSb, ?_⟩
  intro x hx
  have hx' : 0 ≤ b * x ∧ b * x ≤ a :=
    ⟨mul_nonneg hb.le hx.1, (le_div_iff₀' hb).mp hx.2⟩
  have hz0 : S (x : ℂ) ∈ ClosedRectangle a b := by
    simpa [S, ClosedRectangle, Complex.mem_reProdIm] using And.intro hx' (And.intro (le_refl (0 : ℝ)) hb.le)
  have hz1 : S ((x : ℂ) + Complex.I) ∈ ClosedRectangle a b := by
    simpa [S, ClosedRectangle, Complex.mem_reProdIm] using And.intro hx' (And.intro hb.le (le_refl b))
  have h0 := hbottom ⟨S (x : ℂ), hz0⟩ (by simpa [S, ClosedRectangleSide, Complex.mem_reProdIm] using hx')
  have h1 := htop ⟨S ((x : ℂ) + Complex.I), hz1⟩ (by simpa [S, ClosedRectangleSide, Complex.mem_reProdIm] using hx')
  change (g (S (x : ℂ))).im = _ ∧ (g (S ((x : ℂ) + Complex.I))).im = _
  rw [hge ⟨_, hz0⟩, hge ⟨_, hz1⟩]
  cases flip <;> simpa [ClosedRectangleSide, Complex.mem_reProdIm] using And.intro h0.2 h1.2

/-- Membership in a horizontally translated normalized rectangle. -/
private lemma partition_mem_translate (l w : ℝ) (z : ℂ) :
    z ∈ (l : ℂ) +ᵥ OpenRectangle w 1 ↔
      (l < z.re ∧ z.re < l + w) ∧ (0 < z.im ∧ z.im < 1) := by
  rw [Set.mem_vadd_set]
  constructor
  · rintro ⟨u, hu, rfl⟩
    change (l < l + u.re ∧ l + u.re < l + w) ∧ (0 < 0 + u.im ∧ 0 + u.im < 1)
    exact ⟨⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩, by simpa using hu.2⟩
  · intro hz
    refine ⟨z - (l : ℂ), ?_, by simp [vadd_eq_add]⟩
    change (0 < z.re - l ∧ z.re - l < w) ∧ (0 < z.im - 0 ∧ z.im - 0 < 1)
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, by simpa using hz.2⟩

/-- The two complete horizontal sides determine the affine image rectangle. -/
private lemma partition_affine_image {Q : Set ℂ} {m : ℝ} {flip : Bool} {f : ℂ → ℂ}
    (hm : 0 < m) (hc : ContinuousOn f (ClosedRectangle m 1))
    (hb : BijOn f (OpenRectangle m 1) Q)
    (hs : ∀ x ∈ Icc 0 m, (f (x : ℂ)).im = (if flip then 1 else 0) ∧
      (f ((x : ℂ) + Complex.I)).im = (if flip then 0 else 1))
    {c d : ℂ} (he : ∀ z ∈ OpenRectangle m 1, f z = c * z + d) :
    ∃ l : ℝ, Q = (l : ℂ) +ᵥ OpenRectangle m 1 := by
  have hsub : OpenRectangle m 1 ⊆ ClosedRectangle m 1 := fun _ hz ↦
    ⟨⟨hz.1.1.le, hz.1.2.le⟩, ⟨hz.2.1.le, hz.2.2.le⟩⟩
  have hclosed : IsClosed (ClosedRectangle m 1) := isClosed_Icc.reProdIm isClosed_Icc
  have hclosure : closure (OpenRectangle m 1) ⊆
      {z ∈ ClosedRectangle m 1 | f z = c * z + d} :=
    closure_minimal (fun z hz ↦ ⟨hsub hz, he z hz⟩)
      (hclosed.isClosed_eq hc (by fun_prop))
  rw [RectangleModelPreparation.closure_openRectangle hm zero_lt_one] at hclosure
  have hec (z : ℂ) (hz : z ∈ ClosedRectangle m 1) := (hclosure hz).2
  have he0 := hec 0 (by simp [ClosedRectangle, Complex.mem_reProdIm, hm.le])
  have hem := hec (m : ℂ) (by simp [ClosedRectangle, Complex.mem_reProdIm, hm.le])
  have heI := hec Complex.I (by simp [ClosedRectangle, Complex.mem_reProdIm, hm.le])
  have hs0 := hs 0 ⟨le_rfl, hm.le⟩
  have hsm := hs m ⟨hm.le, le_rfl⟩
  simp only [Complex.ofReal_zero, zero_add] at hs0
  rw [he0, heI] at hs0
  rw [hem] at hsm
  simp only [mul_zero, zero_add, Complex.add_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add] at hs0 hsm
  have hci : c.im = 0 := by nlinarith [hs0.1, hsm.1]
  cases flip
  · have hdi : d.im = 0 := hs0.1
    have hcr : c.re = 1 := by simpa [hdi] using hs0.2
    have hc1 : c = 1 := Complex.ext (by simpa using hcr) (by simpa using hci)
    refine ⟨d.re, ?_⟩
    rw [← hb.image_eq]
    ext z
    rw [partition_mem_translate]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [he u hu, hc1, one_mul]
      simp only [Complex.add_re, Complex.add_im, hdi, add_zero]
      exact ⟨⟨by linarith [hu.1.1], by linarith [hu.1.2]⟩, hu.2⟩
    · intro hz
      have hu : z - d ∈ OpenRectangle m 1 := by
        change (0 < z.re - d.re ∧ z.re - d.re < m) ∧ (0 < z.im - d.im ∧ z.im - d.im < 1)
        rw [hdi, sub_zero]
        exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
      exact ⟨z - d, hu, by rw [he _ hu, hc1]; ring⟩
  · have hdi : d.im = 1 := hs0.1
    have hcr : c.re = -1 := by have h := hs0.2; simp at h; linarith
    have hc1 : c = -1 := Complex.ext (by simpa using hcr) (by simpa using hci)
    refine ⟨d.re - m, ?_⟩
    rw [← hb.image_eq]
    ext z
    rw [partition_mem_translate]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [he u hu, hc1, neg_one_mul]
      simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im, hdi]
      exact ⟨⟨by linarith [hu.1.2], by linarith [hu.1.1]⟩,
        ⟨by linarith [hu.2.2], by linarith [hu.2.1]⟩⟩
    · intro hz
      have hu : d - z ∈ OpenRectangle m 1 := by
        change (0 < d.re - z.re ∧ d.re - z.re < m) ∧ (0 < d.im - z.im ∧ d.im - z.im < 1)
        rw [hdi]
        exact ⟨⟨by linarith [hz.1.2], by linarith [hz.1.1]⟩,
          ⟨by linarith [hz.2.2], by linarith [hz.2.1]⟩⟩
      exact ⟨d - z, hu, by rw [he _ hu, hc1]; ring⟩

/-- The two-piece equality case, Lehto–Virtanen I.Lemma 4.2 p.25.
Normalize each source to height one. Rengel gives modulus at most image area;
disjointness and the saturated modulus sum force equality for each piece.
Finite-energy rigidity makes each map affine. Continuity extends that identity
to the closed source; the two complete horizontal sides force slope +1 or −1,
so each image is a translated full-height rectangle. Disjoint horizontal
intervals inside [0,M] whose lengths sum to M are complementary. The spatial
order in the conclusion is independent of the Boolean boundary orientation. -/
theorem qc_partition_translated_full_height_residual
    (M : ℝ) (hM : 0 < M)
    (P₁ P₂ : Set ℂ)
    (_hopen₁ : IsOpen P₁) (hopen₂ : IsOpen P₂)
    (hdisj : Disjoint P₁ P₂)
    (hinside₁ : closure P₁ ⊆ closure (OpenRectangle M 1))
    (hinside₂ : closure P₂ ⊆ closure (OpenRectangle M 1))
    (p₁ p₂ : Fin 4 → ℂ)
    (hm₁ hm₂ : ℝ)
    (hmod : ∃ swap : Bool,
      HasMarkedConformalModulusWithCompleteASides P₁ p₁ hm₁ M swap ∧
      HasMarkedConformalModulusWithCompleteASides P₂ p₂ hm₂ M (Bool.not swap))
    (hsum : hm₁ + hm₂ = M) :
    ∃ x₁ x₂ : ℝ, 0 ≤ x₁ ∧ x₁ ≤ x₂ ∧ x₂ ≤ M ∧
      ((P₁ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1 ∧
          P₂ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1) ∨
       (P₁ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1 ∧
          P₂ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1)) := by
  obtain ⟨flip, hm1, hm2⟩ := hmod
  obtain ⟨hw1, f1, hc1, hf1, hb1, hs1⟩ := partition_normalized_model hm1
  obtain ⟨hw2, f2, hc2, hf2, hb2, hs2⟩ := partition_normalized_model hm2
  have hsep {w : ℝ} {f : ℂ → ℂ} {flip : Bool}
      (hs : ∀ x ∈ Icc 0 w, (f (x : ℂ)).im = (if flip then 1 else 0) ∧
        (f ((x : ℂ) + Complex.I)).im = (if flip then 0 else 1)) :
      ∀ x ∈ Ioo 0 w, 1 ≤ dist (f (x : ℂ)) (f ((x : ℂ) + Complex.I)) := by
    intro x hx
    have hi := Complex.abs_im_le_norm (f (x : ℂ) - f ((x : ℂ) + Complex.I))
    rw [Complex.sub_im, (hs x ⟨hx.1.le, hx.2.le⟩).1,
      (hs x ⟨hx.1.le, hx.2.le⟩).2] at hi
    cases flip <;> simpa [dist_eq_norm] using hi
  have hsep1 := hsep hs1
  have hsep2 := hsep hs2
  let E1 := ∫⁻ z in OpenRectangle hm₁ 1, ‖deriv f1 z‖ₑ ^ 2
  let E2 := ∫⁻ z in OpenRectangle hm₂ 1, ‖deriv f2 z‖ₑ ^ 2
  have hl1 : ENNReal.ofReal hm₁ ≤ E1 := by
    simpa [E1] using qc_rengel_rectangle_energy hw1 zero_lt_one (by norm_num : (0 : ℝ) ≤ 1)
      hc1 hf1 (by simpa using hsep1)
  have hl2 : ENNReal.ofReal hm₂ ≤ E2 := by
    simpa [E2] using qc_rengel_rectangle_energy hw2 zero_lt_one (by norm_num : (0 : ℝ) ≤ 1)
      hc2 hf2 (by simpa using hsep2)
  have harea {w : ℝ} {f : ℂ → ℂ} {Q : Set ℂ}
      (hf : DifferentiableOn ℂ f (OpenRectangle w 1))
      (hb : BijOn f (OpenRectangle w 1) Q) :
      (∫⁻ z in OpenRectangle w 1, ‖deriv f z‖ₑ ^ 2) = volume Q := by
    have h := Analysis.Complex.lintegral_norm_deriv_sq_eq_volume_image
      (isOpen_Ioo.reProdIm isOpen_Ioo) hf hb.injOn
    simp only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm] at h
    change (∫⁻ z in OpenRectangle w 1, ‖deriv f z‖ₑ ^ 2) = volume (f '' OpenRectangle w 1) at h
    rwa [hb.image_eq] at h
  have hE1 : E1 = volume P₁ := harea hf1 hb1
  have hE2 : E2 = volume P₂ := harea hf2 hb2
  have hcl := RectangleModelPreparation.closure_openRectangle hM zero_lt_one
  have hsumE : E1 + E2 ≤ ENNReal.ofReal M := by
    rw [hE1, hE2, ← measure_union hdisj hopen₂.measurableSet]
    calc
      volume (P₁ ∪ P₂) ≤ volume (ClosedRectangle M 1) := measure_mono (by
        rw [← hcl]
        exact union_subset (subset_closure.trans hinside₁) (subset_closure.trans hinside₂))
      _ = ENNReal.ofReal M := by
        have ht := Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv
          (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) 1)
        change volume (ClosedRectangle M 1) = volume (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) 1) at ht
        rw [ht]
        change volume.prod volume (Icc (0 : ℝ) M ×ˢ Icc (0 : ℝ) 1) = _
        rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
        simp
  have hfin1 : E1 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((le_add_right le_rfl).trans hsumE)
  have hfin2 : E2 ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    ((le_add_left le_rfl).trans hsumE)
  have hr1 := ENNReal.toReal_mono hfin1 hl1
  have hr2 := ENNReal.toReal_mono hfin2 hl2
  have hrs := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsumE
  rw [ENNReal.toReal_add hfin1 hfin2, ENNReal.toReal_ofReal hM.le] at hrs
  rw [ENNReal.toReal_ofReal hw1.le] at hr1
  rw [ENNReal.toReal_ofReal hw2.le] at hr2
  have he1 : E1 = ENNReal.ofReal hm₁ := (ENNReal.toReal_eq_toReal_iff' hfin1 ENNReal.ofReal_ne_top).mp (by
    rw [ENNReal.toReal_ofReal hw1.le]; linarith)
  have he2 : E2 = ENNReal.ofReal hm₂ := (ENNReal.toReal_eq_toReal_iff' hfin2 ENNReal.ofReal_ne_top).mp (by
    rw [ENNReal.toReal_ofReal hw2.le]; linarith)
  obtain ⟨c1, d1, hn1, ha1⟩ := qc_rengel_finite_energy_affine hw1 hc1 hf1 hsep1 he1
  obtain ⟨c2, d2, hn2, ha2⟩ := qc_rengel_finite_energy_affine hw2 hc2 hf2 hsep2 he2
  obtain ⟨l1, hp1⟩ := partition_affine_image hw1 hc1 hb1 hs1 ha1
  obtain ⟨l2, hp2⟩ := partition_affine_image hw2 hc2 hb2 hs2 ha2
  have hbounds {Q : Set ℂ} {l w : ℝ} (hw : 0 < w)
      (hp : Q = (l : ℂ) +ᵥ OpenRectangle w 1)
      (hi : closure Q ⊆ closure (OpenRectangle M 1)) : 0 ≤ l ∧ l + w ≤ M := by
    rw [hp, closure_vadd, RectangleModelPreparation.closure_openRectangle hw zero_lt_one,
      hcl] at hi
    have h0 : (0 : ℂ) ∈ ClosedRectangle w 1 := by
      simp [ClosedRectangle, Complex.mem_reProdIm, hw.le]
    have hw' : (w : ℂ) ∈ ClosedRectangle w 1 := by
      simp [ClosedRectangle, Complex.mem_reProdIm, hw.le]
    have hleft := hi (vadd_mem_vadd_set (a := (l : ℂ)) h0)
    have hright := hi (vadd_mem_vadd_set (a := (l : ℂ)) hw')
    exact ⟨by simpa [vadd_eq_add] using hleft.1.1,
      by simpa [vadd_eq_add] using hright.1.2⟩
  have hlb1 := hbounds hw1 hp1 hinside₁
  have hlb2 := hbounds hw2 hp2 hinside₂
  have horder : l1 + hm₁ ≤ l2 ∨ l2 + hm₂ ≤ l1 := by
    by_contra h
    push Not at h
    have hgap : max l1 l2 < min (l1 + hm₁) (l2 + hm₂) :=
      lt_min (max_lt_iff.mpr ⟨by linarith, h.1⟩)
        (max_lt_iff.mpr ⟨h.2, by linarith⟩)
    let x := (max l1 l2 + min (l1 + hm₁) (l2 + hm₂)) / 2
    have hx1 : l1 < x := by dsimp [x]; linarith [le_max_left l1 l2]
    have hx2 : l2 < x := by dsimp [x]; linarith [le_max_right l1 l2]
    have hx3 : x < l1 + hm₁ := by dsimp [x]; linarith [min_le_left (l1 + hm₁) (l2 + hm₂)]
    have hx4 : x < l2 + hm₂ := by dsimp [x]; linarith [min_le_right (l1 + hm₁) (l2 + hm₂)]
    have hz1 : (⟨x, 1 / 2⟩ : ℂ) ∈ P₁ := by
      rw [hp1, partition_mem_translate]
      exact ⟨⟨hx1, hx3⟩, by norm_num⟩
    have hz2 : (⟨x, 1 / 2⟩ : ℂ) ∈ P₂ := by
      rw [hp2, partition_mem_translate]
      exact ⟨⟨hx2, hx4⟩, by norm_num⟩
    exact Set.disjoint_left.mp hdisj hz1 hz2
  rcases horder with horder | horder
  · have hl1 : l1 = 0 := by linarith [hlb1.1, hlb2.2]
    have hl2 : l2 = hm₁ := by linarith [hlb2.2]
    refine ⟨0, hm₁, le_rfl, hw1.le, by linarith, Or.inl ?_⟩
    constructor
    · simpa only [hl1, sub_zero] using hp1
    · simpa only [hl2, show M - hm₁ = hm₂ by linarith] using hp2
  · have hl2 : l2 = 0 := by linarith [hlb2.1, hlb1.2]
    have hl1 : l1 = hm₂ := by linarith [hlb1.2]
    refine ⟨0, hm₂, le_rfl, hw2.le, by linarith, Or.inr ?_⟩
    constructor
    · simpa only [hl1, show M - hm₂ = hm₁ by linarith] using hp1
    · simpa only [hl2, sub_zero] using hp2

/-- The finite two-piece partition lemma used by the final geometric proof.
The source says that two disjoint Jordan subregions of a normalized rectangle,
with their a-sides on the two horizontal sides and with saturated modulus sum,
must be translated axis-parallel full-height rectangles. The translation is
explicit in the conclusion so the two pieces can be disjoint.  The extremal-length data are
kept explicit in this reusable proposition; no differentiability of the
original homeomorphism is assumed here. -/
theorem qc_partition_two_piece_rigidity
    (M : ℝ) (hM : 0 < M)
    (P₁ P₂ : Set ℂ)
    (hopen₁ : IsOpen P₁) (hopen₂ : IsOpen P₂)
    (hdisj : Disjoint P₁ P₂)
    (hinside₁ : closure P₁ ⊆ closure (OpenRectangle M 1))
    (hinside₂ : closure P₂ ⊆ closure (OpenRectangle M 1))
    (p₁ p₂ : Fin 4 → ℂ)
    (hm₁ hm₂ : ℝ)
    (hmod : ∃ swap : Bool,
      HasMarkedConformalModulusWithCompleteASides P₁ p₁ hm₁ M swap ∧
      HasMarkedConformalModulusWithCompleteASides P₂ p₂ hm₂ M (Bool.not swap))
    (hsum : hm₁ + hm₂ = M) :
    ∃ x₁ x₂ : ℝ, 0 ≤ x₁ ∧ x₁ ≤ x₂ ∧ x₂ ≤ M ∧
      ((P₁ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1 ∧
          P₂ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1) ∨
       (P₁ = (x₂ : ℂ) +ᵥ OpenRectangle (M - x₂) 1 ∧
          P₂ = (x₁ : ℂ) +ᵥ OpenRectangle (x₂ - x₁) 1)) := by
  exact qc_partition_translated_full_height_residual M hM P₁ P₂ hopen₁ hopen₂ hdisj
    hinside₁ hinside₂ p₁ p₂ hm₁ hm₂ hmod hsum

end HolomorphicAnosov

