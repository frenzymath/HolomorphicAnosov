import HolomorphicAnosov.Topology.CairnsResidualStarRefinement

namespace HolomorphicAnosov.Topology.Plane
open Set CairnsStar CairnsRefinement

/-- The provider's contact-gap parametrization covers every noncontact point
of its actual front by the affine coordinate used in the literal recurrence.
Source: Cairns (1951), §3(E) and §4(A), pp.863–864. A noncontact front point
lies in its complementary component; its interval parameter lies strictly
between the two endpoint contacts. The front-gap theorem identifies this
interval with the open endpoint chord, and the ordered gap correspondence
identifies those endpoints on the original parameter arc. -/
theorem cairns_front_coordinate_coverage
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (qs : I ≃ₜ b.front)
    (hpairs : gapPairs (fun t ↦ σ (g.parameter t)) (b.front ∩ range σ) =
      gapPairs (fun t ↦ (qs t : ℂ)) (b.front ∩ range σ))
    (hchords : ∀ l r : I, l < r → (qs l : ℂ) ∈ b.front ∩ range σ →
      (qs r : ℂ) ∈ b.front ∩ range σ →
      (∀ t : I, l < t → t < r → (qs t : ℂ) ∉ b.front ∩ range σ) →
      (fun t : I ↦ (qs t : ℂ)) '' {t : I | l < t ∧ t < r} =
        openSegment ℝ (qs l : ℂ) (qs r : ℂ))
    (hcomponents : ∀ x ∈ b.front \ (b.front ∩ range σ), ∃ l r : I,
      l < r ∧ (qs l : ℂ) ∈ b.front ∩ range σ ∧
      (qs r : ℂ) ∈ b.front ∩ range σ ∧
      (∀ t : I, l < t → t < r → (qs t : ℂ) ∉ b.front ∩ range σ) ∧
      connectedComponentIn (b.front \ (b.front ∩ range σ)) x =
        (fun t : I ↦ (qs t : ℂ)) '' {t : I | l < t ∧ t < r}) :
    ∀ z ∈ b.front, z ∉ range σ → ∃ w, b.FrontCoordinate z w := by
  intro z hz hzc
  have hz' : z ∈ b.front \ (b.front ∩ range σ) := ⟨hz, fun hc ↦ hzc hc.2⟩
  obtain ⟨l,r,hlr,hl,hr,hgap,hcomp⟩ := hcomponents z hz'
  have hpair : ((qs l : ℂ), (qs r : ℂ)) ∈
      gapPairs (fun t ↦ σ (g.parameter t)) (b.front ∩ range σ) := by
    rw [hpairs]
    exact ⟨l,r,hlr,hl,hr,hgap,rfl⟩
  have hzch : z ∈ openSegment ℝ (qs l : ℂ) (qs r : ℂ) := by
    rw [← hchords l r hlr hl hr hgap, ← hcomp]
    exact mem_connectedComponentIn hz'
  obtain ⟨u,v,huv,hu,hv,hmissing,heq⟩ := hpair
  have hfirst := congrArg Prod.fst heq
  have hlast := congrArg Prod.snd heq
  dsimp only at hfirst hlast
  rw [hfirst, hlast] at hzch
  rw [openSegment_eq_image] at hzch
  obtain ⟨t,ht,htz⟩ := hzch
  refine ⟨(u,v,⟨t,le_of_lt ht.1,le_of_lt ht.2⟩), ?_, ?_⟩
  · exact ⟨u,v,huv,hu,hv,hmissing,rfl⟩
  · exact htz.symm

/-- The literal front map agrees with any map having the prescribed contact
values and affine values on front chords. No arbitrary coordinate choices can
change those values. -/
theorem cairns_frontMap_eq_of_affine
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) (F : ℂ → ℂ)
    (hcoverage : ∀ z ∈ b.front, z ∉ range σ → ∃ w, b.FrontCoordinate z w)
    (hboundary : ∀ z ∈ b.front, ∀ hz : z ∈ range σ,
      F z = (h ⟨z,hz⟩ : ℂ))
    (haffine : ∀ z ∈ b.front, ∀ w, b.FrontCoordinate z w →
      F z = (1 - (w.2.2 : ℝ)) •
          (h ⟨σ (g.parameter w.1), ⟨g.parameter w.1,rfl⟩⟩ : ℂ) +
        (w.2.2 : ℝ) •
          (h ⟨σ (g.parameter w.2.1), ⟨g.parameter w.2.1,rfl⟩⟩ : ℂ)) :
    ∀ z ∈ b.front, b.frontMap h z = F z := by
  classical
  intro z hz
  unfold StarChoice.frontMap
  split_ifs with hc hw
  · exact (hboundary z hz hc).symm
  · exact (haffine z hz _ (Classical.choose_spec hw)).symm
  · exact (hw (hcoverage z hz hc)).elim

/-- The recurrence's literal radial patch agrees with a geometric extension
having its contact, center, and radial formulas. Source: Cairns (1951), §4(A),
formulas (4.1)–(4.2). Coverage excludes the totalization branch, and each other
branch is the corresponding formula of the extension. -/
theorem cairns_patchMap_eq_of_radial
    {σ : Circle → ℂ} {a : Set ℂ} {g : CairnsCircleGap}
    (b : StarChoice σ a g) (h : range σ ≃ₜ Circle) (S : Set ℂ) (F F₀ : ℂ → ℂ)
    (hfront : ∀ z ∈ b.front, b.frontMap h z = F₀ z)
    (hcoverage : ∀ z ∈ S, z ∈ range σ ∨ z = b.center ∨ ∃ w, b.RadialCoordinate z w)
    (hboundary : ∀ z ∈ S, ∀ hz : z ∈ range σ, F z = (h ⟨z,hz⟩ : ℂ))
    (hcenter : b.center ∈ S → F b.center = b.targetCenter h)
    (hradial : ∀ z ∈ S, ∀ w, b.RadialCoordinate z w →
      F z = (1 - (w.2 : ℝ)) • b.targetCenter h + (w.2 : ℝ) • F₀ w.1) :
    ∀ z ∈ S, b.patchMap h z = F z := by
  classical
  intro z hz
  unfold StarChoice.patchMap
  split_ifs with hc hm hw
  · exact (hboundary z hz hc).symm
  · subst z
    exact (hcenter hz).symm
  · have hh := Classical.choose_spec hw
    dsimp only
    rw [hfront _ hh.1]
    exact (hradial z hz _ hh).symm
  · exact ((hcoverage z hz).elim hc (fun hh ↦ hh.elim hm hw)).elim

/-- Radial interpolation from a chord midpoint agrees with affine
interpolation on the whole base when both endpoint rays have their prescribed
values. Source: Cairns §4(A), (4.1)–(4.2). Split the affine parameter at one
half and rewrite it as a radial parameter on the corresponding half-chord. -/
theorem cairns_midpoint_radial_base_affine
    (p q P Q : ℂ) (F : ℂ → ℂ)
    (hp : ∀ t : I, F ((1 - (t : ℝ)) • ((p + q) / 2) + (t : ℝ) • p) =
      (1 - (t : ℝ)) • ((P + Q) / 2) + (t : ℝ) • P)
    (hq : ∀ t : I, F ((1 - (t : ℝ)) • ((p + q) / 2) + (t : ℝ) • q) =
      (1 - (t : ℝ)) • ((P + Q) / 2) + (t : ℝ) • Q) :
    ∀ t : I, F ((1 - (t : ℝ)) • p + (t : ℝ) • q) =
      (1 - (t : ℝ)) • P + (t : ℝ) • Q := by
  have hmid (a b : ℂ) : (a + b) / 2 = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b := by
    simp [Complex.real_smul,div_eq_mul_inv,add_mul,mul_comm]
  intro t
  by_cases ht : (t : ℝ) ≤ 1 / 2
  · let u : I := ⟨1 - 2 * (t : ℝ),by constructor <;> linarith [t.property.1]⟩
    have hs (a b : ℂ) : (1 - (u : ℝ)) • ((a + b) / 2) + (u : ℝ) • a =
        (1 - (t : ℝ)) • a + (t : ℝ) • b := by
      rw [hmid]
      dsimp only [u]
      module
    simpa only [hs] using hp u
  · let u : I := ⟨2 * (t : ℝ) - 1,by constructor <;> linarith [t.property.2]⟩
    have hs (a b : ℂ) : (1 - (u : ℝ)) • ((a + b) / 2) + (u : ℝ) • b =
        (1 - (t : ℝ)) • a + (t : ℝ) • b := by
      rw [hmid]
      dsimp only [u]
      module
    simpa only [hs] using hq u

end HolomorphicAnosov.Topology.Plane

