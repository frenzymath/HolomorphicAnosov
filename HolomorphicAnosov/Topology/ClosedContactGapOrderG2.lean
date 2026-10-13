import HolomorphicAnosov.Topology.ClosedContactAffineGapOrder
import Mathlib.Tactic

open Set
namespace HolomorphicAnosov

lemma contact_gap_endpoints_unique_g2 {E : Type*} [LinearOrder E] (F : Set E) {a b c d x : E}
    (ha : a ∈ F) (hb : b ∈ F) (hc : c ∈ F) (hd : d ∈ F)
    (hab : Disjoint (Ioo a b) F) (hcd : Disjoint (Ioo c d) F)
    (hx : x ∈ Ioo a b) (hx' : x ∈ Ioo c d) : a=c ∧ b=d := by
  constructor
  · apply le_antisymm
    · by_contra hn
      exact disjoint_left.mp hcd ⟨lt_of_not_ge hn,lt_trans hx.1 hx'.2⟩ ha
    · by_contra hn
      exact disjoint_left.mp hab ⟨lt_of_not_ge hn,lt_trans hx'.1 hx.2⟩ hc
  · apply le_antisymm
    · by_contra hn
      exact disjoint_left.mp hab ⟨lt_trans hx.1 hx'.2,lt_of_not_ge hn⟩ hd
    · by_contra hn
      exact disjoint_left.mp hcd ⟨lt_trans hx'.1 hx.2,lt_of_not_ge hn⟩ hb

/-- The disjointness hypothesis in affine gap filling follows from contact-free
target gaps and injectivity on contacts. Source: Cairns (1951), §3(E), p.863;
agent-written order expansion. Two intersecting intervals with endpoints in a
fixed closed contact image and interiors missing it have identical endpoints:
otherwise an endpoint of one is inside the other. The unordered endpoint images
therefore agree. Injectivity gives identical source endpoint pairs, or the reversed
pair; the latter contradicts the increasing order of both source pairs. Thus
images of distinct source gaps are disjoint, and the existing affine-filling
order theorem applies. -/
theorem closed_contact_gap_order_g2
    (F : Set ℝ) (f : ℝ → ℝ) (hclosed : IsClosed F) (hsub : F ⊆ Icc (0:ℝ) 1)
    (hzero : (0:ℝ) ∈ F) (hone : (1:ℝ) ∈ F)
    (hcont : ContinuousOn f F) (hinj : InjOn f F) (hrange : MapsTo f F (Icc (0:ℝ) 1))
    (hfzero : f 0=0) (hfone : f 1=1)
    (havoid : ∀ l r : ℝ, l ∈ F → r ∈ F → l<r → Disjoint (Ioo l r) F →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r))) (f '' F)) :
    StrictMonoOn f F := by
  have hdisj : ∀ l r l' r' : ℝ,
      l ∈ F → r ∈ F → l<r → Disjoint (Ioo l r) F →
      l' ∈ F → r' ∈ F → l'<r' → Disjoint (Ioo l' r') F → (l,r) ≠ (l',r') →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r)))
        (Ioo (min (f l') (f r')) (max (f l') (f r'))) := by
    intro l r l' r' hl hr hlr hg hl' hr' hlr' hg' hne
    apply disjoint_left.mpr
    intro x hx hx'
    have hmin (s t : ℝ) (hs : s ∈ F) (ht : t ∈ F) : min (f s) (f t) ∈ f '' F := by
      rcases le_total (f s) (f t) with he | he
      · rw [min_eq_left he]; exact mem_image_of_mem f hs
      · rw [min_eq_right he]; exact mem_image_of_mem f ht
    have hmax (s t : ℝ) (hs : s ∈ F) (ht : t ∈ F) : max (f s) (f t) ∈ f '' F := by
      rcases le_total (f s) (f t) with he | he
      · rw [max_eq_right he]; exact mem_image_of_mem f ht
      · rw [max_eq_left he]; exact mem_image_of_mem f hs
    obtain ⟨hemin,hemax⟩ := contact_gap_endpoints_unique_g2 (f '' F)
      (hmin l r hl hr) (hmax l r hl hr) (hmin l' r' hl' hr') (hmax l' r' hl' hr')
      (havoid l r hl hr hlr hg) (havoid l' r' hl' hr' hlr' hg') hx hx'
    rcases le_total (f l) (f r) with he | he <;>
      rcases le_total (f l') (f r') with he' | he'
    · rw [min_eq_left he,min_eq_left he'] at hemin
      rw [max_eq_right he,max_eq_right he'] at hemax
      exact hne (Prod.ext (hinj hl hl' hemin) (hinj hr hr' hemax))
    · rw [min_eq_left he,min_eq_right he'] at hemin
      rw [max_eq_right he,max_eq_left he'] at hemax
      have hlr'e := hinj hl hr' hemin
      have hrl'e := hinj hr hl' hemax
      linarith
    · rw [min_eq_right he,min_eq_left he'] at hemin
      rw [max_eq_left he,max_eq_right he'] at hemax
      have hrl'e := hinj hr hl' hemin
      have hlr'e := hinj hl hr' hemax
      linarith
    · rw [min_eq_right he,min_eq_right he'] at hemin
      rw [max_eq_left he,max_eq_left he'] at hemax
      exact hne (Prod.ext (hinj hl hl' hemax) (hinj hr hr' hemin))
  obtain ⟨g,hg,hgf,hfill,hunique,hmono,hgaps,hbij⟩ := closed_contact_interval_affine_gap_order
    F f hclosed hsub hzero hone hcont hinj hrange hfzero hfone havoid hdisj
  exact hmono

lemma closed_contact_unitInterval_order_g2
    (F : Set unitInterval) (f : unitInterval → unitInterval) (hclosed : IsClosed F)
    (hzero : (0:unitInterval) ∈ F) (hone : (1:unitInterval) ∈ F)
    (hcont : ContinuousOn f F) (hinj : InjOn f F) (hfzero : f 0=0) (hfone : f 1=1)
    (havoid : ∀ l r : unitInterval, l ∈ F → r ∈ F → l<r → Disjoint (Ioo l r) F →
      Disjoint (Ioo (min (f l) (f r)) (max (f l) (f r))) (f '' F)) :
    StrictMonoOn f F := by
  let R : Set ℝ := Subtype.val '' F
  let g : ℝ → ℝ := fun t ↦ (f (projIcc 0 1 zero_le_one t) : ℝ)
  have hR : IsClosed R := (hclosed.isCompact.image continuous_subtype_val).isClosed
  have hRsub : R ⊆ Icc (0:ℝ) 1 := by rintro x ⟨t,ht,rfl⟩; exact t.property
  have hgeval (t : unitInterval) : g (t:ℝ)=(f t:ℝ) := by simp [g]
  have hRproj : ∀ t ∈ R, projIcc 0 1 zero_le_one t ∈ F := by
    rintro t ⟨s,hs,rfl⟩
    simpa only [projIcc_val] using hs
  have hgcont : ContinuousOn g R := continuous_subtype_val.comp_continuousOn
    (hcont.comp continuous_projIcc.continuousOn hRproj)
  have hginj : InjOn g R := by
    rintro x ⟨u,hu,rfl⟩ y ⟨v,hv,rfl⟩ he
    rw [hgeval,hgeval] at he
    exact congrArg Subtype.val (hinj hu hv (Subtype.ext he))
  have hgrange : MapsTo g R (Icc (0:ℝ) 1) := fun t ht ↦ (f (projIcc 0 1 zero_le_one t)).property
  have hgzero : g 0=0 := by simpa [hfzero] using hgeval 0
  have hgone : g 1=1 := by simpa [hfone] using hgeval 1
  have hgavoid : ∀ l r : ℝ, l ∈ R → r ∈ R → l<r → Disjoint (Ioo l r) R →
      Disjoint (Ioo (min (g l) (g r)) (max (g l) (g r))) (g '' R) := by
    rintro l r ⟨u,hu,rfl⟩ ⟨v,hv,rfl⟩ huv hgap
    have hgap' : Disjoint (Ioo u v) F := by
      apply disjoint_left.mpr
      intro t ht htF
      exact disjoint_left.mp hgap ht (mem_image_of_mem Subtype.val htF)
    have hd := havoid u v hu hv huv hgap'
    apply disjoint_left.mpr
    rintro x hx ⟨y,⟨t,ht,rfl⟩,he⟩
    rw [hgeval] at he
    rw [← he,hgeval,hgeval] at hx
    have hh : f t ∈ Ioo (min (f u) (f v)) (max (f u) (f v)) := by exact_mod_cast hx
    exact disjoint_left.mp hd hh (mem_image_of_mem f ht)
  have hm := closed_contact_gap_order_g2 R g hR hRsub
    (show (0:ℝ) ∈ R from ⟨0,hzero,rfl⟩) (show (1:ℝ) ∈ R from ⟨1,hone,rfl⟩)
    hgcont hginj hgrange hgzero hgone hgavoid
  intro x hx y hy hxy
  have hh := hm (mem_image_of_mem Subtype.val hx) (mem_image_of_mem Subtype.val hy) hxy
  change (f x:ℝ)<(f y:ℝ)
  simpa only [hgeval] using hh

end HolomorphicAnosov
