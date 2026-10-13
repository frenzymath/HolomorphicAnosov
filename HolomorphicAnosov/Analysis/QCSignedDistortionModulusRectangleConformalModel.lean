import HolomorphicAnosov.Analysis.MarkedRectangleCircleShortArc
import HolomorphicAnosov.Analysis.Complex.BoundedRiemannMap
import HolomorphicAnosov.Analysis.Complex.HolomorphicEmbeddingInverse
import HolomorphicAnosov.Analysis.MarkedRectangleG3JordanRegionSimplyConnected
import HolomorphicAnosov.Analysis.MarkedRectangleG3RectangleRigidity
import HolomorphicAnosov.Analysis.MarkedRectangleG3DiskSchwarzChristoffel
import HolomorphicAnosov.Analysis.MarkedRectangleG3CaratheodorySameMap
import HolomorphicAnosov.Analysis.MarkedRectangleG3PositiveCircle

/-!
# The marked Jordan-quadrilateral rectangle model

Source: Ahlfors, *Lectures on Quasiconformal Mappings* (1966), Chapter II A, p.21;
Tao, 246C Notes 2 (12 April 2018), §2, Theorem 20 and Exercise 21(i)–(iii).
The Ahlfors modulus is width/height, with the right and left sides distinguished.
Tao's numerical convention with these labels is its reciprocal.

The region below is the actual bounded connected component of a Jordan-curve complement.
Its boundary arcs are specified using the existing positive boundary parametrization and
positive circle arcs, with no boundary differentiability. All interior functions are total
complex functions, used only on their indicated open domains. The extension is a homeomorphism
of the actual closed-rectangle and region-closure subtypes, and extends the same forward map.
No conformal model, quasiconformality, or boundary smoothness is an input.
-/

noncomputable section

namespace HolomorphicAnosov.Analysis.MarkedRectangle

open Set


-- Circle arc transport proof by G5 W01, instantiated below with the actual Carathéodory
-- transition. The native Circle.path identities avoid any boundary smoothness assumption.
/-- Mathlib's native circle exponential is the literal unit circle map. -/
private lemma coe_exp_circleMap (a : ℝ) :
    (Circle.exp a : ℂ) = circleMap 0 1 a := by
  simp [circleMap, Circle.coe_exp]

/-- The period-one boundary parameter is the same exponential with angular scale `2π`. -/
private lemma phase_coe (t : ℝ) :
    (circlePhase t : ℂ) = circleMap 0 1 (2 * Real.pi * t) := by
  exact coe_exp_circleMap _

/-- The source's existential angular arc is the native positively directed path range. -/
lemma positiveClosedCircleArc_eq_range_path (u v : Circle) (huv : u ≠ v) :
    {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc u v} = range (Circle.path u v) := by
  rw [Circle.range_path]
  ext z
  constructor
  · rintro ⟨a, b, hab, hba, hau, hbv, t, ht, htz⟩
    have ha : Circle.exp a = Circle.exp u.val.arg := by
      apply Subtype.ext
      simpa only [coe_exp_circleMap, Circle.exp_arg] using hau
    have hb : Circle.exp b = Circle.exp (Circle.angleDiff u v + u.val.arg) := by
      have hend : Circle.exp (Circle.angleDiff u v + u.val.arg) = v := by
        rw [Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]
      rw [hend]
      exact Subtype.ext (by simpa only [coe_exp_circleMap] using hbv)
    have hi := exp_short_image_eq hab hba
      (by linarith [Circle.angleDiff_pos huv])
      (by linarith [Circle.angleDiff_lt_two_pi u v]) ha hb
    rw [← hi]
    exact ⟨t, ht, Subtype.ext (by simpa only [coe_exp_circleMap] using htz)⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨u.val.arg, Circle.angleDiff u v + u.val.arg,
      by linarith [Circle.angleDiff_pos huv],
      by linarith [Circle.angleDiff_lt_two_pi u v], ?_, ?_, t, ht, ?_⟩
    · simp only [← coe_exp_circleMap, Circle.exp_arg]
    · rw [← coe_exp_circleMap, Circle.exp_add, Circle.exp_arg, Circle.exp_angleDiff_mul]
    · exact (coe_exp_circleMap t).symm


/-- Preserving all positive fourtuples sends every directed closed arc into its counterpart. -/
lemma positiveClosedCircleArc_mapsTo
    (e : Circle ≃ₜ Circle)
    (he : ∀ q : Fin 4 → Circle, PositiveCircleFour q → PositiveCircleFour (e ∘ q))
    (u v : Circle) (huv : u ≠ v) :
    MapsTo e {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc u v}
      {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc (e u) (e v)} := by
  intro z hz
  have heuv : e u ≠ e v := fun h ↦ huv (e.injective h)
  by_cases hzu : z = u
  · subst z
    rw [positiveClosedCircleArc_eq_range_path (e u) (e v) heuv]
    exact (Circle.path (e u) (e v)).source_mem_range
  by_cases hzv : z = v
  · subst z
    rw [positiveClosedCircleArc_eq_range_path (e u) (e v) heuv]
    exact (Circle.path (e u) (e v)).target_mem_range
  obtain ⟨a, b, hab, hba, hau, hbv, t, ht, htz⟩ := hz
  have ha : Circle.exp a = u := Subtype.ext (by simpa only [coe_exp_circleMap] using hau)
  have hb : Circle.exp b = v := Subtype.ext (by simpa only [coe_exp_circleMap] using hbv)
  have hz : Circle.exp t = z := Subtype.ext (by simpa only [coe_exp_circleMap] using htz)
  have hat : a < t := lt_of_le_of_ne ht.1 (fun h ↦ hzu (by rw [← hz, ← ha, h]))
  have htb : t < b := lt_of_le_of_ne ht.2 (fun h ↦ hzv (by rw [← hz, ← hb, h]))
  let q : Fin 4 → ℝ := ![a, t, b, (b + a + 2 * Real.pi) / 2]
  have hq : StrictMono q := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals simp_all [q] <;> linarith
  have hqspan : q 3 < q 0 + 2 * Real.pi := by dsimp [q]; linarith
  let pts : Fin 4 → Circle := fun i ↦ Circle.exp (q i)
  have hp : PositiveCircleFour pts := by
    refine ⟨fun i ↦ q i / (2 * Real.pi), ?_, ?_, ?_⟩
    · intro i j hij
      exact div_lt_div_of_pos_right (hq hij) (by positivity)
    · dsimp only
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
      have hc : (q 0 / (2 * Real.pi) + 1) * (2 * Real.pi) = q 0 + 2 * Real.pi := by
        field_simp
      rw [hc]
      exact hqspan
    · intro i
      unfold circlePhase pts
      congr 1
      field_simp
  obtain ⟨s, hsmono, hsspan, hs⟩ := he pts hp
  have hp0 : pts 0 = u := ha
  have hp1 : pts 1 = z := hz
  have hp2 : pts 2 = v := hb
  have hs0 : circleMap 0 1 (2 * Real.pi * s 0) = (e u : ℂ) := by
    rw [← phase_coe, ← hs 0]
    simp [hp0]
  have hs1 : circleMap 0 1 (2 * Real.pi * s 1) = (e z : ℂ) := by
    rw [← phase_coe, ← hs 1]
    simp [hp1]
  have hs2 : circleMap 0 1 (2 * Real.pi * s 2) = (e v : ℂ) := by
    rw [← phase_coe, ← hs 2]
    simp [hp2]
  refine ⟨2 * Real.pi * s 0, 2 * Real.pi * s 2, ?_, ?_, hs0, hs2,
    2 * Real.pi * s 1, ⟨?_, ?_⟩, hs1⟩
  · exact mul_lt_mul_of_pos_left (hsmono (by decide : (0 : Fin 4) < 2)) (by positivity)
  · nlinarith [hsmono (by decide : (2 : Fin 4) < 3), Real.pi_pos]
  · exact (mul_lt_mul_of_pos_left (hsmono (by decide : (0 : Fin 4) < 1))
      (by positivity)).le
  · exact (mul_lt_mul_of_pos_left (hsmono (by decide : (1 : Fin 4) < 2))
      (by positivity)).le


/-- Every directed closed arc is transported exactly by a positive cyclic homeomorphism.
The reverse containment uses both complementary arcs and their endpoint-only intersection,
so no order-preservation hypothesis on the inverse homeomorphism is assumed. -/
lemma positiveClosedCircleArc_image
    (e : Circle ≃ₜ Circle)
    (he : ∀ q : Fin 4 → Circle, PositiveCircleFour q → PositiveCircleFour (e ∘ q))
    (u v : Circle) (huv : u ≠ v) :
    e '' {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc u v} =
      {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc (e u) (e v)} := by
  refine (positiveClosedCircleArc_mapsTo e he u v huv).image_subset.antisymm ?_
  intro z hz
  let x := e.symm z
  have hex : e x = z := e.apply_symm_apply z
  have hx : (x : ℂ) ∈ PositiveClosedCircleArc u v := by
    by_contra hx
    have hxr : x ∈ range (Circle.path u v) ∪ range (Circle.path v u) := by
      rw [Circle.range_path_union_range_path huv]
      trivial
    have hxopp : x ∈ {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc v u} := by
      rw [positiveClosedCircleArc_eq_range_path v u huv.symm]
      exact hxr.resolve_left (by
        rw [← positiveClosedCircleArc_eq_range_path u v huv]
        exact hx)
    have hzopp := positiveClosedCircleArc_mapsTo e he v u huv.symm hxopp
    rw [hex] at hzopp
    have heuv : e u ≠ e v := fun h ↦ huv (e.injective h)
    have hzpair : z ∈ ({e u, e v} : Set Circle) := by
      rw [← Circle.range_path_inter_range_path heuv]
      constructor
      · simpa only [← positiveClosedCircleArc_eq_range_path (e u) (e v) heuv] using hz
      · simpa only [← positiveClosedCircleArc_eq_range_path (e v) (e u) heuv.symm]
          using hzopp
    have hxp : x = u ∨ x = v := by
      simpa only [mem_insert_iff, mem_singleton_iff, ← hex, e.injective.eq_iff] using hzpair
    apply hx
    rw [show (x : ℂ) ∈ PositiveClosedCircleArc u v ↔
      x ∈ range (Circle.path u v) from
      Set.ext_iff.mp (positiveClosedCircleArc_eq_range_path u v huv) x]
    rcases hxp with hxu | hxv
    · rw [hxu]; exact (Circle.path u v).source_mem_range
    · rw [hxv]; exact (Circle.path u v).target_mem_range
  exact ⟨x, hx, hex⟩

/-- Strict single-turn angle lifts give distinct marks by native exponential injectivity.
Source: Lyubich §1.11, pp.53–54. -/
lemma positiveCircleFour_injective {u : Fin 4 → Circle} (hu : PositiveCircleFour u) :
    Function.Injective u := by
  obtain ⟨t, ht, hspan, heq⟩ := hu
  have hmem (i : Fin 4) : 2 * Real.pi * t i ∈ Ico (2 * Real.pi * t 0)
      (2 * Real.pi * t 0 + 2 * Real.pi) := by
    constructor
    · exact mul_le_mul_of_nonneg_left (ht.monotone (Fin.zero_le _)) (by positivity)
    · have hle := ht.monotone (show i ≤ 3 by omega)
      nlinarith [Real.pi_pos]
  intro i j hij
  have he : Circle.exp (2 * Real.pi * t i) = Circle.exp (2 * Real.pi * t j) := by
    simpa only [heq, circlePhase] using hij
  have he' := Circle.exp_injOn_Ico (a := 2 * Real.pi * t 0)
    (b := 2 * Real.pi * t 0 + 2 * Real.pi) (by linarith) (hmem i) (hmem j) he
  exact ht.injective (mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) he')

/-- Exact whole-arc transport for four positively ordered circle marks.
Source: the boundary-side correspondence in Tao Exercise 21(ii), proved by the native
complementary path ranges and the strictly increasing angle lifts above. -/
lemma positiveCircleFour_arc_image
    (e : Circle ≃ₜ Circle)
    (he : ∀ q : Fin 4 → Circle, PositiveCircleFour q → PositiveCircleFour (e ∘ q))
    (u : Fin 4 → Circle) (hu : PositiveCircleFour u) (i : Fin 4) :
    e '' {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))} =
      {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc (e (u i)) (e (u (i + 1)))} := by
  apply positiveClosedCircleArc_image e he
  exact fun h ↦ (by fin_cases i <;> decide : i ≠ i + 1) (positiveCircleFour_injective hu h)


namespace RectangleModelPreparation

/-- The closure is the literal coordinatewise closed rectangle. Source: Tao Exercise 21,
using Mathlib's product closure and real interval closure formulas. -/
theorem closure_openRectangle {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    closure (OpenRectangle a b) = ClosedRectangle a b := by
  change closure (Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Ioo 0 a ×ˢ Ioo 0 b)) =
    Complex.equivRealProdCLM.toHomeomorph ⁻¹' (Icc 0 a ×ˢ Icc 0 b)
  rw [← Complex.equivRealProdCLM.toHomeomorph.preimage_closure,
    closure_prod_eq, closure_Ioo ha.ne, closure_Ioo hb.ne]

/-- The open rectangle is open in the original complex plane. -/
theorem isOpen_openRectangle (a b : ℝ) : IsOpen (OpenRectangle a b) :=
  (isOpen_Ioo.prod isOpen_Ioo).preimage Complex.equivRealProdCLM.continuous

/-- Each named closed side lies in the literal closed rectangle. -/
theorem side_subset {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin 4) :
    ClosedRectangleSide a b i ⊆ ClosedRectangle a b := by
  intro z hz
  fin_cases i <;>
    simp [ClosedRectangleSide, Complex.reProdIm, Set.mem_preimage, Set.mem_inter_iff] at hz
  · exact ⟨hz.1, by simpa [hz.2] using And.intro (le_refl (0 : ℝ)) hb.le⟩
  · exact ⟨by simpa [hz.1] using And.intro ha.le (le_refl a), hz.2⟩
  · exact ⟨hz.1, by simpa [hz.2] using And.intro hb.le (le_refl b)⟩
  · exact ⟨by simpa [hz.1] using And.intro (le_refl (0 : ℝ)) ha.le, hz.2⟩

/-- The identity rectangle model uses the actual equality of closed rectangle and closure.
Source: Ahlfors p.21; the side equality includes both endpoints. -/
theorem identity_rectangle (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    DifferentiableOn ℂ (id : ℂ → ℂ) (OpenRectangle a b) ∧
    BijOn (id : ℂ → ℂ) (OpenRectangle a b) (OpenRectangle a b) ∧
    ∃ e : ClosedRectangle a b ≃ₜ closure (OpenRectangle a b),
      (∀ z : ClosedRectangle a b, (e z : ℂ) = z) ∧
      (∀ (i : Fin 4) (z : ClosedRectangle a b),
        (z : ℂ) = RectangleCorner a b i → (e z : ℂ) = RectangleCorner a b i) ∧
      ∀ i : Fin 4,
        (fun z : ClosedRectangle a b ↦ (e z : ℂ)) ''
          {z | (z : ℂ) ∈ ClosedRectangleSide a b i} = ClosedRectangleSide a b i := by
  let e := Homeomorph.setCongr (closure_openRectangle ha hb).symm
  refine ⟨differentiableOn_id, bijOn_id _, e, fun _ ↦ rfl, ?_, ?_⟩
  · intro i z hz
    exact hz
  · intro i
    apply Set.ext
    intro z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, side_subset ha hb i hz⟩, hz, rfl⟩

/-- An inverse of the interior map agrees with the inverse of its same-map closure extension.
Source: the inverse identities in Tao Theorem 20 and Exercise 21. No boundary inverse
regularity is assumed: injectivity of the actual closure homeomorphism gives the equality. -/
theorem closure_inverse_agrees {A U Q : Set ℂ} (hUA : U ⊆ A)
    (G H : ℂ → ℂ) (e : A ≃ₜ closure Q)
    (he : ∀ z : A, (z : ℂ) ∈ U → (e z : ℂ) = G z)
    (hH : MapsTo H Q U) (hGH : ∀ w ∈ Q, G (H w) = w)
    (w : ℂ) (hw : w ∈ Q) :
    (e.symm ⟨w, subset_closure hw⟩ : ℂ) = H w := by
  let z : A := ⟨H w, hUA (hH hw)⟩
  have hz : e z = ⟨w, subset_closure hw⟩ := by
    apply Subtype.ext
    exact (he z (hH hw)).trans (hGH w hw)
  have h := congrArg e.symm hz
  exact congrArg Subtype.val (by simpa [z] using h.symm)

/-- Whole-side image equalities pass through the same actual intermediate boundary set.
Source: Tao Exercise 21(ii). This is a set-theoretic consequence of the two closure
homeomorphisms, preserving both endpoints and surjectivity of each full side. -/
theorem transported_side_image {D : Type*} [TopologicalSpace D] {R Q : Set ℂ}
    (e₁ : D ≃ₜ R) (e₂ : D ≃ₜ Q) (C : Set D) (S J : Set ℂ)
    (hS : (fun z : D ↦ (e₁ z : ℂ)) '' C = S)
    (hJ : (fun z : D ↦ (e₂ z : ℂ)) '' C = J) :
    (fun z : R ↦ ((e₁.symm.trans e₂) z : ℂ)) ''
      {z | (z : ℂ) ∈ S} = J := by
  rw [← hJ]
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← hS] at hz
    obtain ⟨u, hu, he⟩ := hz
    have hzu : z = e₁ u := Subtype.ext he.symm
    subst z
    exact ⟨u, hu, by simp⟩
  · rintro ⟨u, hu, rfl⟩
    refine ⟨e₁ u, ?_, by simp⟩
    rw [← hS]
    exact ⟨u, hu, rfl⟩

/-- The literal corners lie in the closed rectangle whenever both widths are positive. -/
theorem corner_mem {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin 4) :
    RectangleCorner a b i ∈ ClosedRectangle a b := by
  fin_cases i <;> simp [RectangleCorner, ClosedRectangle, Complex.reProdIm, ha.le, hb.le]

/-- Any two same-mark rectangle models differ by the positive dilation in the source
rectangle-rigidity theorem. Source: Tao Exercise 21(iii), Ahlfors p.21. The composite
inverse is evaluated only in the original region, and the boundary composite uses the
actual two supplied extensions, so no global inverse or boundary differentiability is added. -/
theorem unique_model {Q : Set ℂ} {a b A B : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hA : 0 < A) (hB : 0 < B)
    (p : Fin 4 → ℂ) (F G H : ℂ → ℂ)
    (hF : DifferentiableOn ℂ F (OpenRectangle a b))
    (hH : DifferentiableOn ℂ H Q)
    (hFbij : BijOn F (OpenRectangle a b) Q)
    (hGbij : BijOn G (OpenRectangle A B) Q)
    (hHmaps : MapsTo H Q (OpenRectangle A B))
    (hHG : ∀ z ∈ OpenRectangle A B, H (G z) = z)
    (hGH : ∀ w ∈ Q, G (H w) = w)
    (eF : ClosedRectangle a b ≃ₜ closure Q)
    (eG : ClosedRectangle A B ≃ₜ closure Q)
    (heF : ∀ z : ClosedRectangle a b,
      (z : ℂ) ∈ OpenRectangle a b → (eF z : ℂ) = F z)
    (heG : ∀ z : ClosedRectangle A B,
      (z : ℂ) ∈ OpenRectangle A B → (eG z : ℂ) = G z)
    (hpF : ∀ (i : Fin 4) (z : ClosedRectangle a b),
      (z : ℂ) = RectangleCorner a b i → (eF z : ℂ) = p i)
    (hpG : ∀ (i : Fin 4) (z : ClosedRectangle A B),
      (z : ℂ) = RectangleCorner A B i → (eG z : ℂ) = p i) :
    ∃ c : ℝ, 0 < c ∧ A = c * a ∧ B = c * b ∧
      (∀ z ∈ OpenRectangle a b, H (F z) = (c : ℂ) * z) ∧ A / B = a / b := by
  let e : ClosedRectangle a b ≃ₜ ClosedRectangle A B := eF.trans eG.symm
  have hUA : OpenRectangle A B ⊆ ClosedRectangle A B := by
    rw [← closure_openRectangle hA hB]
    exact subset_closure
  have he : ∀ z : ClosedRectangle a b,
      (z : ℂ) ∈ OpenRectangle a b → (e z : ℂ) = (H ∘ F) z := by
    intro z hz
    have h := closure_inverse_agrees hUA G H eG heG hHmaps hGH (F z) (hFbij.mapsTo hz)
    have heq : eF z = ⟨F z, subset_closure (hFbij.mapsTo hz)⟩ :=
      Subtype.ext (heF z hz)
    change (eG.symm (eF z) : ℂ) = H (F z)
    rw [heq]
    exact h
  have hcorn : ∀ i : Fin 4,
      (e ⟨RectangleCorner a b i, corner_mem ha hb i⟩ : ℂ) = RectangleCorner A B i := by
    intro i
    let z : ClosedRectangle a b := ⟨RectangleCorner a b i, corner_mem ha hb i⟩
    let w : ClosedRectangle A B := ⟨RectangleCorner A B i, corner_mem hA hB i⟩
    have hh : eF z = eG w := Subtype.ext ((hpF i z rfl).trans (hpG i w rfl).symm)
    change (eG.symm (eF z) : ℂ) = RectangleCorner A B i
    rw [hh, eG.symm_apply_apply]
  have hHbij : BijOn H Q (OpenRectangle A B) := hGbij.symm ⟨hGH, hHG⟩
  obtain ⟨c, hc, hlin, hca, hcb, hratio⟩ :=
    MarkedRectangleG3RectangleRigidity.rectangle_rigidity ha hb hA hB (H ∘ F)
      (hH.comp hF hFbij.mapsTo) (hHbij.comp hFbij) e he
      (hcorn 0)
      (hcorn 1)
      (hcorn 2)
      (hcorn 3)
  exact ⟨c, hc, hca, hcb, hlin, hratio.symm⟩

/-- Compose the two supplied disk maps and their literal closure extensions. Source:
Tao Theorem 20 and Exercise 21(ii)-(iii). The side correspondence is supplied as the
same circle arc on both extensions; the conclusion introduces no global inverse data. -/
theorem model_of_disk_maps {Q : Set ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (p : Fin 4 → ℂ) (J : Fin 4 → Set ℂ) (ζ : Fin 4 → ℂ)
    (hcircle : ∀ i, ‖ζ i‖ = 1)
    (φ ψ S T : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1))
    (hψ : DifferentiableOn ℂ ψ Q)
    (hφbij : BijOn φ (Metric.ball (0 : ℂ) 1) Q)
    (hψmaps : MapsTo ψ Q (Metric.ball (0 : ℂ) 1))
    (hψφ : ∀ z ∈ Metric.ball (0 : ℂ) 1, ψ (φ z) = z)
    (hφψ : ∀ w ∈ Q, φ (ψ w) = w)
    (hS : DifferentiableOn ℂ S (Metric.ball (0 : ℂ) 1))
    (hT : DifferentiableOn ℂ T (OpenRectangle a b))
    (hSbij : BijOn S (Metric.ball (0 : ℂ) 1) (OpenRectangle a b))
    (hTmaps : MapsTo T (OpenRectangle a b) (Metric.ball (0 : ℂ) 1))
    (hTS : ∀ z ∈ Metric.ball (0 : ℂ) 1, T (S z) = z)
    (hST : ∀ w ∈ OpenRectangle a b, S (T w) = w)
    (Φ : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure Q)
    (sigma : Metric.closedBall (0 : ℂ) 1 ≃ₜ ClosedRectangle a b)
    (hΦ : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → (Φ z : ℂ) = φ z)
    (hsigma : ∀ z : Metric.closedBall (0 : ℂ) 1, ‖(z : ℂ)‖ < 1 → (sigma z : ℂ) = S z)
    (hpΦ : ∀ i, (Φ ⟨ζ i, by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ : ℂ) = p i)
    (hpsigma : ∀ i, (sigma ⟨ζ i, by simpa [Metric.mem_closedBall] using (hcircle i).le⟩ : ℂ) =
      RectangleCorner a b i)
    (hsideΦ : ∀ i,
      (fun z : Metric.closedBall (0 : ℂ) 1 ↦ (Φ z : ℂ)) ''
        {z | (z : ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i + 1))} = J i)
    (hsidesigma : ∀ i,
      (fun z : Metric.closedBall (0 : ℂ) 1 ↦ (sigma z : ℂ)) ''
        {z | (z : ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i + 1))} =
          ClosedRectangleSide a b i) :
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
          (∀ i : Fin 4,
            (fun z : ClosedRectangle a b ↦ (boundaryExtension z : ℂ)) ''
              {z | (z : ℂ) ∈ ClosedRectangleSide a b i} = J i) ∧
          (∀ (A B : ℝ), 0 < A → 0 < B →
            ∀ G G_inv : ℂ → ℂ,
              DifferentiableOn ℂ G (OpenRectangle A B) →
              DifferentiableOn ℂ G_inv Q →
              BijOn G (OpenRectangle A B) Q →
              MapsTo G_inv Q (OpenRectangle A B) →
              (∀ z ∈ OpenRectangle A B, G_inv (G z) = z) →
              (∀ w ∈ Q, G (G_inv w) = w) →
              ∀ otherExtension : ClosedRectangle A B ≃ₜ closure Q,
                (∀ z : ClosedRectangle A B,
                  (z : ℂ) ∈ OpenRectangle A B → (otherExtension z : ℂ) = G z) →
                (∀ (i : Fin 4) (z : ClosedRectangle A B),
                  (z : ℂ) = RectangleCorner A B i → (otherExtension z : ℂ) = p i) →
                (∀ i : Fin 4,
                  (fun z : ClosedRectangle A B ↦ (otherExtension z : ℂ)) ''
                    {z | (z : ℂ) ∈ ClosedRectangleSide A B i} = J i) →
                ∃ c : ℝ, 0 < c ∧ A = c * a ∧ B = c * b ∧
                  (∀ z ∈ OpenRectangle a b, G_inv (F z) = (c : ℂ) * z) ∧
                  A / B = a / b) := by
  let F := φ ∘ T
  let F_inv := S ∘ ψ
  let e : ClosedRectangle a b ≃ₜ closure Q := sigma.symm.trans Φ
  have hTbij : BijOn T (OpenRectangle a b) (Metric.ball (0 : ℂ) 1) :=
    hSbij.symm ⟨hST, hTS⟩
  have hF : DifferentiableOn ℂ F (OpenRectangle a b) := hφ.comp hT hTmaps
  have hFinv : DifferentiableOn ℂ F_inv Q := hS.comp hψ hψmaps
  have hFbij : BijOn F (OpenRectangle a b) Q := hφbij.comp hTbij
  have hFinvmaps : MapsTo F_inv Q (OpenRectangle a b) := hSbij.mapsTo.comp hψmaps
  have he : ∀ z : ClosedRectangle a b,
      (z : ℂ) ∈ OpenRectangle a b → (e z : ℂ) = F z := by
    intro z hz
    let t : Metric.closedBall (0 : ℂ) 1 :=
      ⟨T z, Metric.ball_subset_closedBall (hTmaps hz)⟩
    have hnorm : ‖(t : ℂ)‖ < 1 := by simpa [t, Metric.mem_ball] using hTmaps hz
    have htz : sigma t = z := Subtype.ext ((hsigma t hnorm).trans (hST z hz))
    change (Φ (sigma.symm z) : ℂ) = φ (T z)
    rw [show sigma.symm z = t from by rw [← htz, sigma.symm_apply_apply]]
    exact hΦ t hnorm
  have hp : ∀ (i : Fin 4) (z : ClosedRectangle a b),
      (z : ℂ) = RectangleCorner a b i → (e z : ℂ) = p i := by
    intro i z hz
    let t : Metric.closedBall (0 : ℂ) 1 :=
      ⟨ζ i, by simpa [Metric.mem_closedBall] using (hcircle i).le⟩
    have htz : sigma t = z := Subtype.ext ((hpsigma i).trans hz.symm)
    change (Φ (sigma.symm z) : ℂ) = p i
    rw [← htz, sigma.symm_apply_apply]
    exact hpΦ i
  refine ⟨F, F_inv, hF, hFinv, hFbij, hFinvmaps, ?_, ?_, e, he, hp, ?_, ?_⟩
  · intro z hz
    change S (ψ (φ (T z))) = z
    rw [hψφ _ (hTmaps hz), hST z hz]
  · intro w hw
    change φ (T (S (ψ w))) = w
    rw [hTS _ (hψmaps hw), hφψ w hw]
  · intro i
    exact transported_side_image sigma Φ _ _ _ (hsidesigma i) (hsideΦ i)
  · intro A B hA hB G G_inv _ hGinv hGbij hGinvmaps hGinvG hGGinv otherExtension
      hother hpother _
    exact unique_model ha hb hA hB p F G G_inv hF hGinv hFbij hGbij hGinvmaps
      hGinvG hGGinv e otherExtension he hother hp hpother

/-- Translate the period-one angle convention to the literal circle-map angle convention.
Source: Lyubich positive cyclic order, with Mathlib's exponential parametrization. -/
theorem circle_four_cyclic {u : Fin 4 → Circle} (hu : PositiveCircleFour u) :
    PositiveCircleCyclicOrder (fun i ↦ (u i : ℂ)) := by
  obtain ⟨t, ht, hturn, hu⟩ := hu
  refine ⟨fun i ↦ 2 * Real.pi * t i, ?_, ?_, ?_⟩
  · intro i j hij
    exact mul_lt_mul_of_pos_left (ht hij) (by positivity)
  · nlinarith [Real.pi_pos]
  · intro i
    simp [hu i, circlePhase, circleMap, Circle.coe_exp]

/-- Strict positive cyclic order excludes coincident circle marks. Source: the same
single-turn angle lifts and Mathlib's injectivity of the circle exponential on a short interval. -/
theorem circle_four_injective {u : Fin 4 → Circle} (hu : PositiveCircleFour u) :
    Function.Injective (fun i ↦ (u i : ℂ)) := by
  intro i j hij
  exact positiveCircleFour_ne_coe hu i j hij

/-- Every point of a positive circle arc has unit norm, including its endpoints. -/
theorem arc_norm {u v z : ℂ} (hz : z ∈ PositiveClosedCircleArc u v) : ‖z‖ = 1 := by
  obtain ⟨α, β, _, _, _, _, θ, _, rfl⟩ := hz
  simp

end RectangleModelPreparation

/-- Assemble the Jordan model from the exact named source providers and a circle arc
transport theorem. The extra argument here is an explicitly isolated general circle theorem,
not a premise of the public result. Source: Tao Theorem 20 and Exercise 21(ii)-(iii). -/
theorem model_from_arc_transport
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) (q : ℂ)
    (hq : q ∉ range γ)
    (hbounded : Bornology.IsBounded (connectedComponentIn (range γ)ᶜ q))
    (p : Fin 4 → ℂ) (J : Fin 4 → Set ℂ)
    (h_arcs : ∃ β : Circle ≃ₜ frontier (connectedComponentIn (range γ)ᶜ q),
      PositiveBoundaryParametrization (connectedComponentIn (range γ)ᶜ q) β ∧
      ∃ u : Fin 4 → Circle, PositiveCircleFour u ∧
        (∀ i, (β (u i) : ℂ) = p i) ∧
        ∀ i, J i = (fun ζ : Circle ↦ (β ζ : ℂ)) ''
          {ζ | (ζ : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))})
    (hat : ∀ (e : Circle ≃ₜ Circle),
      (∀ v : Fin 4 → Circle, PositiveCircleFour v → PositiveCircleFour (e ∘ v)) →
      ∀ (u : Fin 4 → Circle), PositiveCircleFour u → ∀ i : Fin 4,
        e '' {z | (z : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))} =
          {z : Circle | (z : ℂ) ∈ PositiveClosedCircleArc (e (u i)) (e (u (i + 1)))}) :
    let Q : Set ℂ := connectedComponentIn (range γ)ᶜ q
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧
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
          (∀ i : Fin 4,
            (fun z : ClosedRectangle a b ↦ (boundaryExtension z : ℂ)) ''
              {z | (z : ℂ) ∈ ClosedRectangleSide a b i} = J i) ∧
          (∀ (A B : ℝ), 0 < A → 0 < B →
            ∀ G G_inv : ℂ → ℂ,
              DifferentiableOn ℂ G (OpenRectangle A B) →
              DifferentiableOn ℂ G_inv Q →
              BijOn G (OpenRectangle A B) Q →
              MapsTo G_inv Q (OpenRectangle A B) →
              (∀ z ∈ OpenRectangle A B, G_inv (G z) = z) →
              (∀ w ∈ Q, G (G_inv w) = w) →
              ∀ otherExtension : ClosedRectangle A B ≃ₜ closure Q,
                (∀ z : ClosedRectangle A B,
                  (z : ℂ) ∈ OpenRectangle A B → (otherExtension z : ℂ) = G z) →
                (∀ (i : Fin 4) (z : ClosedRectangle A B),
                  (z : ℂ) = RectangleCorner A B i → (otherExtension z : ℂ) = p i) →
                (∀ i : Fin 4,
                  (fun z : ClosedRectangle A B ↦ (otherExtension z : ℂ)) ''
                    {z | (z : ℂ) ∈ ClosedRectangleSide A B i} = J i) →
                ∃ c : ℝ, 0 < c ∧ A = c * a ∧ B = c * b ∧
                  (∀ z ∈ OpenRectangle a b, G_inv (F z) = (c : ℂ) * z) ∧
                  A / B = a / b)) ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      DifferentiableOn ℂ (id : ℂ → ℂ) (OpenRectangle a b) ∧
      BijOn (id : ℂ → ℂ) (OpenRectangle a b) (OpenRectangle a b) ∧
      ∃ identityExtension : ClosedRectangle a b ≃ₜ closure (OpenRectangle a b),
        (∀ z : ClosedRectangle a b, (identityExtension z : ℂ) = z) ∧
        (∀ (i : Fin 4) (z : ClosedRectangle a b),
          (z : ℂ) = RectangleCorner a b i →
            (identityExtension z : ℂ) = RectangleCorner a b i) ∧
        ∀ i : Fin 4,
          (fun z : ClosedRectangle a b ↦ (identityExtension z : ℂ)) ''
            {z | (z : ℂ) ∈ ClosedRectangleSide a b i} = ClosedRectangleSide a b i) := by
  classical
  let Q : Set ℂ := connectedComponentIn (range γ)ᶜ q
  obtain ⟨hne, hbd, hopen, _, hfront, hsimply⟩ :=
    markedRectangleG3JordanRegionSimplyConnected γ hγ q hq hbounded
  let : SimplyConnectedSpace Q := hsimply
  obtain ⟨z₀, hz₀⟩ := hne
  have hne : Q.Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨φ, ψ, hφ, hψ, hφbij, hψmaps, hψφ, hφψ, _, _, _⟩ :=
    bounded_riemann_map Q hne hbd hopen z₀ hz₀
  have hjordan : HasJordanBoundary Q := ⟨γ, hγ, hfront.symm⟩
  obtain ⟨Φ₀, hΦ₀, _, hboundary, hfour⟩ :=
    caratheodory_same_map Q hne hopen hbd hsimply hjordan φ
      (by simpa [unitDisk, Metric.ball, dist_zero_right] using hφ)
      (by simpa [unitDisk, Metric.ball, dist_zero_right] using hφbij)
  obtain ⟨β₁, hβ₁, _⟩ := hboundary
  obtain ⟨β, hβ, u, hu, hp, hJ⟩ := h_arcs
  let e : Circle ≃ₜ Circle := β.trans β₁.symm
  have he : ∀ v : Fin 4 → Circle,
      PositiveCircleFour v → PositiveCircleFour (e ∘ v) := by
    intro v hv
    obtain ⟨w, hw, hpw⟩ := hfour (fun i ↦ (β (v i) : ℂ)) ⟨β, hβ, v, hv, fun _ ↦ rfl⟩
    have hwv : w = e ∘ v := by
      funext i
      apply β₁.injective
      apply Subtype.ext
      change (β₁ (w i) : ℂ) = (β₁ (β₁.symm (β (v i))) : ℂ)
      rw [β₁.apply_symm_apply]
      exact (hβ₁ (w i)).trans (hpw i)
    exact hwv ▸ hw
  let ζ : Fin 4 → ℂ := fun i ↦ (e (u i) : ℂ)
  have hζcircle : ∀ i, ‖ζ i‖ = 1 := by intro i; simp [ζ]
  have hζfour : PositiveCircleFour (e ∘ u) := he u hu
  obtain ⟨a, b, ha, hb, S, T, hS, hT, hSbij, hTmaps, hTS, hST,
      sigma, hsigma, hpsigma, hssigma⟩ :=
    exists_disk_rectangle_map ζ hζcircle
      (RectangleModelPreparation.circle_four_injective hζfour)
      (RectangleModelPreparation.circle_four_cyclic hζfour)
  let disk : Metric.closedBall (0 : ℂ) 1 ≃ₜ closedUnitDisk :=
    Homeomorph.setCongr (by ext z; simp [closedUnitDisk, Metric.mem_closedBall])
  let Φ : Metric.closedBall (0 : ℂ) 1 ≃ₜ closure Q := disk.trans Φ₀
  have hΦ : ∀ z : Metric.closedBall (0 : ℂ) 1,
      ‖(z : ℂ)‖ < 1 → (Φ z : ℂ) = φ z := by
    intro z hz
    exact hΦ₀ z hz
  have hΦcircle : ∀ w : Circle,
      (Φ ⟨(w : ℂ), by simp [Metric.mem_closedBall]⟩ : ℂ) = (β₁ w : ℂ) := by
    intro w
    exact (hβ₁ w).symm
  have hpΦ : ∀ i,
      (Φ ⟨ζ i, by simpa [Metric.mem_closedBall] using (hζcircle i).le⟩ : ℂ) = p i := by
    intro i
    rw [hΦcircle (e (u i))]
    change (β₁ (β₁.symm (β (u i))) : ℂ) = p i
    rw [β₁.apply_symm_apply]
    exact hp i
  have hsideΦ : ∀ i,
      (fun z : Metric.closedBall (0 : ℂ) 1 ↦ (Φ z : ℂ)) ''
        {z | (z : ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i + 1))} = J i := by
    intro i
    rw [hJ i]
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      let v : Circle := ⟨z, by simpa [Submonoid.unitSphere, Metric.mem_sphere] using
        RectangleModelPreparation.arc_norm hz⟩
      have hv : v ∈ e '' {z | (z : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))} := by
        rw [hat e he u hu i]
        exact hz
      obtain ⟨v₀, hv₀, hvv⟩ := hv
      refine ⟨v₀, hv₀, ?_⟩
      have hh := hΦcircle v
      have hback : β₁ v = β v₀ := by rw [← hvv]; simp [e]
      exact (congrArg Subtype.val hback).symm.trans hh.symm
    · rintro ⟨v, hv, rfl⟩
      have hev : (e v : ℂ) ∈ PositiveClosedCircleArc (ζ i) (ζ (i + 1)) := by
        have hm : e v ∈ e '' {z | (z : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))} :=
          ⟨v, hv, rfl⟩
        rw [hat e he u hu i] at hm
        exact hm
      refine ⟨⟨(e v : ℂ), by simp [Metric.mem_closedBall]⟩, hev, ?_⟩
      exact (hΦcircle (e v)).trans (by simp [e])
  refine ⟨⟨a, b, ha, hb, ?_⟩, RectangleModelPreparation.identity_rectangle⟩
  exact RectangleModelPreparation.model_of_disk_maps ha hb p J ζ hζcircle φ ψ S T
    hφ hψ hφbij hψmaps hψφ hφψ hS hT hSbij hTmaps hTS hST Φ sigma hΦ hsigma hpΦ
    hpsigma hsideΦ hssigma

/-- Every positively marked Jordan quadrilateral has a same-map closed rectangle model,
unique up to a positive dilation fixing the four ordered corner labels.

Source: Ahlfors (1966), Chapter II A, p.21 (the marked modulus convention);
Tao 246C Notes 2, §2, Theorem 20 and Exercise 21(i)–(iii). The complete parent deduction
is relative to the five genuine Jordan-region, Riemann-map, Carathéodory, marked disk
Schwarz–Christoffel and rectangle-rigidity obligations in the DAG. Their proofs are not
silently supplied by this Stage2 declaration.

The hypothesis about J is a literal definition of the four GIVEN positive closed boundary
arcs, using a positive boundary homeomorphism and four angle-ordered distinct points.
It is independent of the orientation chosen for the original embedding γ. Indices in Fin 4
are cyclic, so i+1 wraps from the fourth mark to the first. The positive parameter order
fixes p0,p1,p2,p3 as 0,a,a+ib,ib; the distinguished b-arcs are J1 and J3 in zero-based notation.
The corner clauses quantify over actual subtype points, avoiding any extra corner-membership
premise. Positivity of the widths puts each of the four named corners in the closed rectangle.

Complete natural-language proof from the node, relative to its named providers:

1. The Jordan-region topology child supplies that Q is nonempty bounded open and simply connected,
with boundary γ(S¹). Apply the bounded Riemann-map child at any z₀∈Q to obtain a specific
holomorphic bijection φ:D→Q and its holomorphic inverse. This step neither assumes a disk
homeomorphism as extra target data nor uses Carathéodory to justify the simple-connectedness
premise that its own Riemann map requires.

2. Apply the same-map Carathéodory child to this φ. It gives a closure homeomorphism Φ whose interior
restriction is literally φ, and positive boundary orientation. Define ζ_j=Φ⁻¹(p_j). Boundary
restriction bijectivity makes the ζ_j distinct, and its positive orientation makes them positively
cyclic. The four positive closed circle arcs are exactly Φ⁻¹(J_j). No piecewise smoothness of γ or
its arcs is needed.

3. The marked disk Schwarz–Christoffel child applied to ζ₁,…,ζ₄ supplies a,b>0, a holomorphic
bijection S:D→R_(a,b), its holomorphic inverse, and its closure homeomorphism Σ. Define F=φ∘S⁻¹
and F̄=Φ∘Σ⁻¹. These compositions are a biholomorphism and a closure homeomorphism respectively,
and agree on the open rectangle because both closure maps extend the named interior maps. The four
corner equations are F̄(0)=p₁, F̄(a)=p₂, F̄(a+ib)=p₃ and F̄(ib)=p₄. The closed-side image
equations follow from the exact circle-arc equations in the two children, so the vertical sides
correspond precisely to J₂,J₄.

4. For a second model G:R_(A,B)→Q, form T=G⁻¹∘F and its closure map Ḡ⁻¹∘F̄. Holomorphicity of the
inverse is supplied by the model and, equivalently, the existing inverse theorem. This is a
conformal rectangle bijection whose closure extension maps each of 0,a,a+ib,ib to its
corresponding target corner 0,A,A+iB,iB. The rigidity child therefore gives T(z)=cz with c>0, A=ca
and B=cb, hence A/B=a/b. This proves uniqueness up to the specified similarity with fixed corner
labels; no rotation swapping the distinguished side pairs is allowed.

5. Ahlfors p.21 defines the modulus using distinguished b-arcs: vertical sides have length b, the
horizontal sides length a, so m(Q)=a/b. Tao uses mod(Q)=b/a for his a-side labels p₁p₂,p₃p₄; with
the explicit corner convention of this statement, his numerical modulus is the reciprocal of the
Ahlfors modulus. Both conventions reciprocate under a one-corner cyclic relabeling, but the label
order here is fixed. For a marked source rectangle use F(z)=z and the identity closure
homeomorphism; its positive widths a,b and side/corner equations hold directly.


For the type below, represent the bounded Jordan region by the component containing q, with
q outside the embedded curve and that component bounded. The Jordan provider supplies its
openness, nonemptiness, and entire boundary, so these are not additional hypotheses. The
positive boundary parametrization in h_arcs is exactly the prescribed positive cyclic
marking; its images of the directed circle arcs are the J_i in the source. Both closure maps
from the proof preserve these entire arcs, giving the stated whole-side image equalities.
An ambient inverse F_inv is holomorphic on Q, maps Q back to the source rectangle, and has
both inverse identities there. Its arbitrary off-domain values do not enter the statement.
The second-model clause uses its own inverse on Q and its own literal boundary extension.
It gives the positive similarity and equal ratios for every competing model, hence defines
the numerical modulus independently of the choice. The final clause supplies the identity
model on every positive rectangle: both interior maps are id, its boundary map is the actual
identity inclusion into the closure, and its corner and whole-side images are prescribed.
Coincident marks are excluded by positive cyclic order; zero widths are excluded explicitly.
No empty-region, nonrectifiable-boundary, reflection-across-Q, or global QC premise is added.
-/
theorem qc_signed_distortion_modulus_rectangle_conformal_model
    (γ : Circle → ℂ) (hγ : Topology.IsEmbedding γ) (q : ℂ)
    (hq : q ∉ range γ)
    (hbounded : Bornology.IsBounded (connectedComponentIn (range γ)ᶜ q))
    (p : Fin 4 → ℂ) (J : Fin 4 → Set ℂ)
    (h_arcs : ∃ β : Circle ≃ₜ frontier (connectedComponentIn (range γ)ᶜ q),
      PositiveBoundaryParametrization (connectedComponentIn (range γ)ᶜ q) β ∧
      ∃ u : Fin 4 → Circle, PositiveCircleFour u ∧
        (∀ i, (β (u i) : ℂ) = p i) ∧
        ∀ i, J i = (fun ζ : Circle ↦ (β ζ : ℂ)) ''
          {ζ | (ζ : ℂ) ∈ PositiveClosedCircleArc (u i) (u (i + 1))}) :
    let Q : Set ℂ := connectedComponentIn (range γ)ᶜ q
    (∃ a b : ℝ, 0 < a ∧ 0 < b ∧
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
          (∀ i : Fin 4,
            (fun z : ClosedRectangle a b ↦ (boundaryExtension z : ℂ)) ''
              {z | (z : ℂ) ∈ ClosedRectangleSide a b i} = J i) ∧
          (∀ (A B : ℝ), 0 < A → 0 < B →
            ∀ G G_inv : ℂ → ℂ,
              DifferentiableOn ℂ G (OpenRectangle A B) →
              DifferentiableOn ℂ G_inv Q →
              BijOn G (OpenRectangle A B) Q →
              MapsTo G_inv Q (OpenRectangle A B) →
              (∀ z ∈ OpenRectangle A B, G_inv (G z) = z) →
              (∀ w ∈ Q, G (G_inv w) = w) →
              ∀ otherExtension : ClosedRectangle A B ≃ₜ closure Q,
                (∀ z : ClosedRectangle A B,
                  (z : ℂ) ∈ OpenRectangle A B → (otherExtension z : ℂ) = G z) →
                (∀ (i : Fin 4) (z : ClosedRectangle A B),
                  (z : ℂ) = RectangleCorner A B i → (otherExtension z : ℂ) = p i) →
                (∀ i : Fin 4,
                  (fun z : ClosedRectangle A B ↦ (otherExtension z : ℂ)) ''
                    {z | (z : ℂ) ∈ ClosedRectangleSide A B i} = J i) →
                ∃ c : ℝ, 0 < c ∧ A = c * a ∧ B = c * b ∧
                  (∀ z ∈ OpenRectangle a b, G_inv (F z) = (c : ℂ) * z) ∧
                  A / B = a / b)) ∧
    (∀ a b : ℝ, 0 < a → 0 < b →
      DifferentiableOn ℂ (id : ℂ → ℂ) (OpenRectangle a b) ∧
      BijOn (id : ℂ → ℂ) (OpenRectangle a b) (OpenRectangle a b) ∧
      ∃ identityExtension : ClosedRectangle a b ≃ₜ closure (OpenRectangle a b),
        (∀ z : ClosedRectangle a b, (identityExtension z : ℂ) = z) ∧
        (∀ (i : Fin 4) (z : ClosedRectangle a b),
          (z : ℂ) = RectangleCorner a b i →
            (identityExtension z : ℂ) = RectangleCorner a b i) ∧
        ∀ i : Fin 4,
          (fun z : ClosedRectangle a b ↦ (identityExtension z : ℂ)) ''
            {z | (z : ℂ) ∈ ClosedRectangleSide a b i} = ClosedRectangleSide a b i) := by
  exact model_from_arc_transport γ hγ q hq hbounded p J h_arcs
    (fun e he u hu i ↦ positiveCircleFour_arc_image e he u hu i)


end HolomorphicAnosov.Analysis.MarkedRectangle
