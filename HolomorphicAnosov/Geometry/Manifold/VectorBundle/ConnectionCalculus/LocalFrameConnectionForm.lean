import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientLineConnection
import HolomorphicAnosov.Geometry.Manifold.VectorBundle.HolomorphicQuotientTangentLine.ExistsLocalData
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Analysis.Calculus.FDeriv.Mul

open Bundle Set _root_.Topology TopologicalSpace
open scoped Manifold ContDiff
attribute [local instance] HolomorphicAnosov.complex_isManifold_real
noncomputable section
namespace HolomorphicAnosov.ConnectionCalculus
universe u
variable {d : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel d) X] [IsManifold (complexModel d) ∞ X]

/-! This file defines connection forms relative to a fixed quotient frame and proves their gauge law
and preservation of type (1,0). (Demailly, V §§1–2, pp.253–255; Zhang, §2.1, (3), p.4) -/

/-- Scalar coefficients in two line-bundle frames are related by the frame transition coefficient.
(Demailly, V §1, pp.253–254) -/
theorem frame_coefficient_change
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (s : (x : X) → QuotientLineConnection.Fibre P x)
    (x : X) (hx : x ∈ V) (hx' : x ∈ W) :
    e.coefficient s x = e.coefficient e'.sectionValue x * e'.coefficient s x := by
  have hs : s x = e'.coefficient s x • e'.sectionValue x := by
    apply (e'.coordinate x hx').injective
    simp only [QuotientLineConnection.HolomorphicFrame.coefficient, dite_eq_left hx',
      map_smul, e'.normalized, smul_eq_mul, mul_one]
  unfold QuotientLineConnection.HolomorphicFrame.coefficient
  simp only [dite_eq_left hx, dite_eq_left hx']
  calc
    _ = (e.coordinate x hx) (e'.coefficient s x • e'.sectionValue x) := congrArg _ hs
    _ = _ := by
      simp only [map_smul, smul_eq_mul, QuotientLineConnection.HolomorphicFrame.coefficient,
        dite_eq_left hx']
      ring

/-- Line-bundle frame transition coefficients are nonzero on overlaps. (Demailly, V §1, pp.253–254) -/
theorem frame_transition_nonzero
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (x : X) (hx : x ∈ V) (hx' : x ∈ W) :
    e.coefficient e'.sectionValue x ≠ 0 := by
  intro h
  have hz : e'.sectionValue x = 0 := (e.coordinate x hx).injective (by
    simpa only [QuotientLineConnection.HolomorphicFrame.coefficient,
      dite_eq_left hx, map_zero] using h)
  have hn := e'.normalized x hx'
  rw [hz, map_zero] at hn
  exact zero_ne_one hn

/-- The coefficient of a holomorphic quotient section in a holomorphic quotient frame is holomorphic
on the overlap. (Demailly, V §11, (11.1), p.267 and §14, (14.1), p.273) -/
theorem frame_coefficient_holomorphic
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (s : (x : X) → QuotientLineConnection.Fibre P x)
    (hs : QuotientLineConnection.IsHolomorphicSection P W s) :
    ContMDiffOn (complexModel d) 𝓘(ℂ, ℂ) ∞ (e.coefficient s) ((V : Set X) ∩ W) := by
  intro x hx
  obtain ⟨D, hxD⟩ := exists_quotient_local_data P hP hline x
  obtain ⟨O, t, hO, hxO, hOV, ht, hte⟩ := e.holomorphic x hx.1
  obtain ⟨Q, u, hQ, hxQ, hQW, hu, hus⟩ := hs x hx.2
  have ht' := (D.hscalar ⟨x, t x⟩ hxD).comp x (ht.contMDiffAt (hO.mem_nhds hxO))
  have hu' := (D.hscalar ⟨x, u x⟩ hxD).comp x (hu.contMDiffAt (hQ.mem_nhds hxQ))
  have htne : D.θ x (t x) ≠ 0 := by
    rw [← D.apply_mk x hxD, hte x hxO]
    intro h
    have he0 : e.sectionValue x = 0 := (D.L x hxD).injective (by simpa using h)
    have hn := e.normalized x hx.1
    rw [he0, map_zero] at hn
    exact zero_ne_one hn
  have hratio := hu'.div₀ ht' htne
  apply (hratio.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hO.mem_nhds hxO, hQ.mem_nhds hxQ, D.V.isOpen.mem_nhds hxD]
    with y hyO hyQ hyD
  have hyV : y ∈ V := hOV hyO
  have hyW : y ∈ W := hQW hyQ
  have he0 : e.sectionValue y ≠ 0 := by
    intro h
    have hn := e.normalized y hyV
    rw [h, map_zero] at hn
    exact zero_ne_one hn
  have hden : D.θ y (t y) ≠ 0 := by
    rw [← D.apply_mk y hyD, hte y hyO]
    exact fun h ↦ he0 ((D.L y hyD).injective (by simpa using h))
  have hclass : s y = e.coefficient s y • e.sectionValue y := by
    apply (e.coordinate y hyV).injective
    simp only [QuotientLineConnection.HolomorphicFrame.coefficient, dite_eq_left hyV,
      map_smul, e.normalized, smul_eq_mul, mul_one]
  change e.coefficient s y = D.θ y (u y) / D.θ y (t y)
  apply (eq_div_iff hden).mpr
  rw [← D.apply_mk y hyD, ← D.apply_mk y hyD, hus y hyQ, hte y hyO, hclass]
  simp

/-- The coefficient of a holomorphic quotient section in a holomorphic frame is real differentiable
at every point of the overlap. (Demailly, I §3.C, p.23 and V §11, p.267) -/
theorem frame_coefficient_real_differentiableAt
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (s : (x : X) → QuotientLineConnection.Fibre P x)
    (hs : QuotientLineConnection.IsHolomorphicSection P W s)
    (x : X) (hx : x ∈ V) (hx' : x ∈ W) :
    MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (e.coefficient s) x := by
  have h := (frame_coefficient_holomorphic hP hline V W e s hs).contMDiffAt
    ((V.isOpen.inter W.isOpen).mem_nhds ⟨hx, hx'⟩)
  obtain ⟨hc, hd⟩ := contMDiffAt_iff.mp h
  have hr : ContMDiffAt (realModel d) 𝓘(ℝ, ℂ) ∞ (e.coefficient s) x :=
    contMDiffAt_iff.mpr ⟨hc, hd.restrict_scalars ℝ⟩
  exact hr.mdifferentiableAt (by simp)

omit [IsManifold (complexModel d) ∞ X] in
/-- The real differential of a product of scalar functions satisfies the Leibniz rule. (Demailly, V
§2, (2.1), p.255) -/
theorem realDifferential_mul (f g : X → ℂ) (x : X)
    (hf : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) f x)
    (hg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) g x) :
    QuotientLineConnection.realDifferential (d := d) (fun y ↦ f y * g y) x =
      f x • QuotientLineConnection.realDifferential g x +
        g x • QuotientLineConnection.realDifferential f x := by
  ext v
  change ComplexModel d at v
  simp only [QuotientLineConnection.realDifferential]
  have hfg : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) (fun y ↦ f y * g y) x :=
    hf.mul hg
  rw [hfg.mfderiv_abuse, hf.mfderiv_abuse, hg.mfderiv_abuse]
  have hf' := hf.differentiableWithinAt_writtenInExtChartAt
  have hg' := hg.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt, mfld_simps] at hf' hg' ⊢
  let c := chartAt (ComplexModel d) x
  change DifferentiableWithinAt ℝ (fun z ↦ f (c.symm z)) Set.univ (c x) at hf'
  change DifferentiableWithinAt ℝ (fun z ↦ g (c.symm z)) Set.univ (c x) at hg'
  change (fderivWithin ℝ (fun z ↦ f (c.symm z) * g (c.symm z)) Set.univ (c x)) v =
    f x * (fderivWithin ℝ (fun z ↦ g (c.symm z)) Set.univ (c x)) v +
      g x * (fderivWithin ℝ (fun z ↦ f (c.symm z)) Set.univ (c x)) v
  rw [fderivWithin_fun_mul uniqueDiffWithinAt_univ hf' hg']
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [c.left_inv (mem_chart_source _ x)]

/-- The form `A + g⁻¹dg` in a quotient frame, where `A` is the form in a fixed normalized frame and
`g` is the coefficient of the receiving frame in that frame. (Zhang, (3), p.4; Demailly, V §2,
(2.1)–(2.3), p.255) -/
def localFrameConnectionForm
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)}
    {O : Opens X} (e₀ : QuotientLineConnection.HolomorphicFrame P O)
    (A : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V) (x : X) :
    TangentSpace (realModel d) x →L[ℝ] ℂ :=
  A x + (e₀.coefficient e.sectionValue x)⁻¹ •
    QuotientLineConnection.realDifferential (e₀.coefficient e.sectionValue) x

/-- Connection forms obtained from a fixed local frame satisfy the gauge law on its domain. (Zhang,
(3), p.4; Demailly, V §2, (2.1)–(2.3), p.255) -/
theorem localFrameConnectionForm_gauge
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    {O : Opens X} (e₀ : QuotientLineConnection.HolomorphicFrame P O)
    (A : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (e' : QuotientLineConnection.HolomorphicFrame P W)
    (x : X) (hxO : x ∈ O) (hxV : x ∈ V) (hxW : x ∈ W) :
    localFrameConnectionForm e₀ A W e' x = localFrameConnectionForm e₀ A V e x +
      (e.coefficient e'.sectionValue x)⁻¹ •
        QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x := by
  let g := e₀.coefficient e.sectionValue
  let h := e.coefficient e'.sectionValue
  let k := e₀.coefficient e'.sectionValue
  have hg : g x ≠ 0 := frame_transition_nonzero O V e₀ e x hxO hxV
  have hh : h x ≠ 0 := frame_transition_nonzero V W e e' x hxV hxW
  have heq : k =ᶠ[nhds x] fun y ↦ g y * h y := by
    filter_upwards [O.isOpen.mem_nhds hxO, V.isOpen.mem_nhds hxV] with y hyO hyV
    exact frame_coefficient_change O V e₀ e e'.sectionValue y hyO hyV
  have hd : QuotientLineConnection.realDifferential (d := d) k x =
      g x • QuotientLineConnection.realDifferential h x +
        h x • QuotientLineConnection.realDifferential g x := by
    have hm : QuotientLineConnection.realDifferential (d := d) k x =
        QuotientLineConnection.realDifferential (fun y ↦ g y * h y) x := by
      unfold QuotientLineConnection.realDifferential
      rw [heq.eq_of_nhds, heq.mfderiv_eq]
      rfl
    rw [hm]
    exact realDifferential_mul g h x
      (frame_coefficient_real_differentiableAt hP hline O V e₀ e.sectionValue e.holomorphic x hxO hxV)
      (frame_coefficient_real_differentiableAt hP hline V W e e'.sectionValue e'.holomorphic x hxV hxW)
  change A x + (k x)⁻¹ • QuotientLineConnection.realDifferential (d := d) k x =
    A x + (g x)⁻¹ • QuotientLineConnection.realDifferential g x +
      (h x)⁻¹ • QuotientLineConnection.realDifferential h x
  rw [hd, heq.eq_of_nhds]
  ext v
  simp only [add_apply, smul_apply, smul_eq_mul]
  field_simp
  ring

omit [IsManifold (complexModel d) ∞ X] in
/-- The real differential of a holomorphic scalar function is complex linear. (Demailly, I §3.C,
p.23) -/
theorem realDifferential_I_smul_of_holomorphic
    (f : X → ℂ) (x : X)
    (hf : MDifferentiableAt (complexModel d) 𝓘(ℂ, ℂ) f x)
    (hr : MDifferentiableAt (realModel d) 𝓘(ℝ, ℂ) f x)
    (v : TangentSpace (complexModel d) x) :
    QuotientLineConnection.realDifferential f x (complexTangentToReal d x (Complex.I • v)) =
      Complex.I * QuotientLineConnection.realDifferential f x (complexTangentToReal d x v) := by
  change ComplexModel d at v
  unfold QuotientLineConnection.realDifferential
  rw [hr.mfderiv_abuse]
  have hd := hf.differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt, mfld_simps] at hd ⊢
  change DifferentiableWithinAt ℂ (fun z ↦ f ((chartAt (ComplexModel d) x).symm z))
    Set.univ (chartAt (ComplexModel d) x x) at hd
  change fderivWithin ℝ (fun z ↦ f ((chartAt (ComplexModel d) x).symm z))
    Set.univ (chartAt (ComplexModel d) x x) (Complex.I • v) =
    Complex.I * fderivWithin ℝ (fun z ↦ f ((chartAt (ComplexModel d) x).symm z))
      Set.univ (chartAt (ComplexModel d) x x) v
  rw [← hd.restrictScalars_fderivWithin ℝ uniqueDiffWithinAt_univ]
  change (fderivWithin ℂ _ _ _) (Complex.I • v) = _
  rw [map_smul]
  rfl

/-- Gauge transformation by a holomorphic frame transition preserves the type (1,0) of a local
connection form. (Zhang, Definition 2.1 and (3), p.4; Demailly, V §11, p.267) -/
theorem localFrameConnectionForm_type_one
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    {O : Opens X} (e₀ : QuotientLineConnection.HolomorphicFrame P O)
    (A : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
    (x : X) (hxO : x ∈ O) (hxV : x ∈ V)
    (hA : ∀ v : TangentSpace (complexModel d) x,
      A x (complexTangentToReal d x (Complex.I • v)) =
        Complex.I * A x (complexTangentToReal d x v))
    (v : TangentSpace (complexModel d) x) :
    localFrameConnectionForm e₀ A V e x (complexTangentToReal d x (Complex.I • v)) =
      Complex.I * localFrameConnectionForm e₀ A V e x (complexTangentToReal d x v) := by
  have hc := ((frame_coefficient_holomorphic hP hline O V e₀ e.sectionValue
    e.holomorphic).contMDiffAt ((O.isOpen.inter V.isOpen).mem_nhds ⟨hxO, hxV⟩)).mdifferentiableAt
      (by simp)
  have hr := frame_coefficient_real_differentiableAt hP hline O V e₀ e.sectionValue
    e.holomorphic x hxO hxV
  simp only [localFrameConnectionForm, add_apply, smul_apply, smul_eq_mul, hA v,
    realDifferential_I_smul_of_holomorphic _ x hc hr v]
  ring

/-- A local form of type (1,0) determines forms of type (1,0) in overlapping holomorphic frames that
satisfy the connection gauge law. (Demailly, V §2, (2.3), p.255 and §11, p.267; Zhang, (3), p.4) -/
theorem local_frame_forms_gauge_and_type_one
    {P : (x : X) → Submodule ℂ (TangentSpace (complexModel d) x)} {r : ℕ}
    (hP : IsHolomorphicTangentSubbundle r P) (hline : IsQuotientTangentLine P)
    {O : Opens X} (e₀ : QuotientLineConnection.HolomorphicFrame P O)
    (A : (x : X) → TangentSpace (realModel d) x →L[ℝ] ℂ)
    (hA : ∀ x, x ∈ O → ∀ v : TangentSpace (complexModel d) x,
      A x (complexTangentToReal d x (Complex.I • v)) =
        Complex.I * A x (complexTangentToReal d x v)) :
    (∀ (V W : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V)
      (e' : QuotientLineConnection.HolomorphicFrame P W) (x : X),
      x ∈ O → x ∈ V → x ∈ W →
      localFrameConnectionForm e₀ A W e' x = localFrameConnectionForm e₀ A V e x +
        (e.coefficient e'.sectionValue x)⁻¹ •
          QuotientLineConnection.realDifferential (e.coefficient e'.sectionValue) x) ∧
    (∀ (V : Opens X) (e : QuotientLineConnection.HolomorphicFrame P V) (x : X),
      x ∈ O → x ∈ V → ∀ v : TangentSpace (complexModel d) x,
      localFrameConnectionForm e₀ A V e x (complexTangentToReal d x (Complex.I • v)) =
        Complex.I * localFrameConnectionForm e₀ A V e x (complexTangentToReal d x v)) := by
  exact ⟨localFrameConnectionForm_gauge hP hline e₀ A,
    fun V e x hxO hxV v ↦
      localFrameConnectionForm_type_one hP hline e₀ A V e x hxO hxV (hA x hxO) v⟩

end HolomorphicAnosov.ConnectionCalculus
