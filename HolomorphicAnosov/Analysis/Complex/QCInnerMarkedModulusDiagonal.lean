import HolomorphicAnosov.Analysis.Complex.QCInsideMarkedModulusContinuity
import HolomorphicAnosov.Analysis.Complex.QCScaledRectangleModel
import HolomorphicAnosov.Analysis.Complex.QCCompactBoundaryTransport
import HolomorphicAnosov.Analysis.Complex.QCMarkedModelPositive
import HolomorphicAnosov.Analysis.Complex.QCPositiveMarkedModulus
import HolomorphicAnosov.Analysis.Complex.QCLimitWinding
import Mathlib.Analysis.SpecificLimits.Basic
import HolomorphicAnosov.Analysis.Complex.QCLimitInsideDiagonal


namespace HolomorphicAnosov
open Set Filter _root_.Topology Analysis.MarkedRectangle

/-- Compatible inner marked models along a locally uniformly convergent sequence of
positively oriented homeomorphisms, after any prescribed initial index.

Source: Lehto--Virtanen, Quasiconformal Mappings in the Plane (1973), I.Lemmas
4.3--4.4, pp.26--27, and the diagonal construction in I.Theorem 5.2, p.29.
Local source: literature/Lehto-Virtanen-Quasiconformal-Mappings-in-the-Plane-supplied.txt,
sections 4.7, 4.8, and 5.2. This is the geometric part of that proof, independent
of the distortion constant or any modulus inequality for the sequence.

Proof. Contract the given rectangle model about its center by
r_j = 1 - 1/(j+2). The resulting compact inner quadrilaterals have the same
modulus m; their literal closure parametrizations converge uniformly to the
original one. Choose a strictly increasing diagonal after N for which each
selected image closure lies inside g(Q), with uniform map error tending to
zero. Composing the parametrizations gives uniform convergence of image
closures and their marked boundaries.

The source rectangle corners are positive: the radial gauge chart gives a
positive rectangle boundary, and the holomorphic disk argument principle,
followed by a confined Jordan homotopy, transports this orientation through
the given conformal model. The assumed circle orientation for g transports
it further to g(Q). Uniform convergence of the selected boundary loops and
one interior omitted point makes their winding numbers eventually one.
Path connectedness propagates positivity to every interior point. Discard
that finite initial segment and use the marked rectangle existence theorem
to obtain the selected image moduli nu_j.

The image closure homeomorphisms match the four literal marks and converge
uniformly to the identity on closure g(Q). Inside marked modulus continuity
therefore gives nu_j tending to m'. To establish that continuity, apply the
fixed inverse rectangle chart. Compact uniform continuity and topological
side correspondence put the four inner sides in strips of width epsilon.
The normalized Rengel estimates bound their moduli between
(M-2epsilon)^2/M and M/(1-2epsilon)^2, which both approach M.
The source modulus sequence is constant. Shifting all sequences by the same
finite index preserves strict monotonicity, the lower bound N, compact
containment, and both limits.
-/
theorem qc_inner_marked_modulus_diagonal
    (U : Set ℂ) (_hU : IsOpen U) (_hU_connected : IsConnected U)
    (gSeq : ℕ → OpenPartialHomeomorph ℂ ℂ) (g : OpenPartialHomeomorph ℂ ℂ)
    (hSeq_source : ∀ n, (gSeq n).source = U) (hg_source : g.source = U)
    (_hSeq_derivative : ∀ n z, z ∈ U → ∃ A : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt (gSeq n) (A : ℂ →L[ℝ] ℂ) z ∧ 0 < (A : ℂ →L[ℝ] ℂ).det)
    (hLocallyUniform : TendstoLocallyUniformlyOn (fun n z ↦ gSeq n z) g atTop U)
    (hg_positive : ∀ a : ℂ, ∀ r : ℝ, 0 < r → Metric.closedBall a r ⊆ U →
      ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          let c := a + (r : ℂ) * Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
          Complex.exp (((θ t : ℝ) : ℂ) * Complex.I) = (g c - g a) / (‖g c - g a‖ : ℂ)) ∧
        θ 1 = θ 0 + 2 * Real.pi)
    (Q : Set ℂ) (p : Fin 4 → ℂ) (m m' : ℝ)
    (hQcompact : IsCompact (closure Q)) (hQinside : closure Q ⊆ U)
    (hQmod : HasMarkedConformalModulus Q p m)
    (hImageMod : HasMarkedConformalModulus (g '' Q) (fun i ↦ g (p i)) m') (N : ℕ) :
    ∃ (φ : ℕ → ℕ) (Qinner : ℕ → Set ℂ)
      (pinner : ℕ → Fin 4 → ℂ) (μ ν : ℕ → ℝ),
      StrictMono φ ∧
      (∀ j, N ≤ φ j ∧ IsCompact (closure (Qinner j)) ∧
        closure (Qinner j) ⊆ U ∧
        HasMarkedConformalModulus (Qinner j) (pinner j) (μ j) ∧
        HasMarkedConformalModulus (gSeq (φ j) '' Qinner j)
          (fun i ↦ gSeq (φ j) (pinner j i)) (ν j)) ∧
      Tendsto μ atTop (𝓝 m) ∧ Tendsto ν atTop (𝓝 m') := by
  classical
  let r : ℕ → ℝ := fun n ↦ 1 - 1 / ((n : ℝ) + 2)
  have hr (n : ℕ) : 0 < r n := by
    dsimp [r]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : 1 < (n : ℝ) + 2 := by linarith
    have hdiv : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr hden
    linarith
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp [r]
    have hdiv : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have hzero : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      by
        have h := (tendsto_add_atTop_iff_nat 2).2
          (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
        simpa only [Nat.cast_add, Nat.cast_ofNat] using h
    simpa only [sub_zero] using tendsto_const_nhds.sub hzero
  obtain ⟨a, b, ha, hb, e, P, q, E, hecorner, heinterior, hP, hElim⟩ :=
    qc_scaled_rectangle_family hQmod r hr hr1 hrlim
  have hQgeom := qc_marked_model_geometry hQmod hQcompact
  have hQsrc : Q ⊆ g.source := fun z hz ↦ hg_source.symm ▸ hQinside (subset_closure hz)
  have hclsrc : closure Q ⊆ g.source := hg_source.symm ▸ hQinside
  have hgc : ContinuousOn g (closure Q) := g.continuousOn.mono hclsrc
  have hVopen : IsOpen (g '' Q) := g.isOpen_image_of_subset_source hQgeom.1 hQsrc
  have hPcl (j : ℕ) : closure (P j) ⊆ closure Q := (hP j).2.1.trans subset_closure
  obtain ⟨φ, hφ, hφdata⟩ := qc_limit_inside_diagonal hQcompact hQinside hgc
    (fun j ↦ (hP j).1) hPcl hVopen
    (fun j z hz ↦ ⟨z, (hP j).2.1 hz, rfl⟩) hLocallyUniform
    (fun j ↦ 1 / ((j : ℝ) + 2)) (fun j ↦ by positivity) N
  have hFQ : TendstoUniformlyOn (fun j z ↦ gSeq (φ j) z) g atTop (closure Q) := by
    have h := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hQcompact).mp
      (hLocallyUniform.mono hQinside)
    exact fun s hs ↦ hφ.tendsto_atTop.eventually (h s hs)
  have himages : TendstoUniformly (fun j z ↦ gSeq (φ j) (E j z))
      (fun z ↦ g (e z)) atTop :=
    qc_uniform_compact_parametrizations hQcompact hgc hFQ
      (fun z ↦ (e z).property) (fun j z ↦ hPcl j (E j z).property) hElim
  have hPopen (j : ℕ) : IsOpen (P j) :=
    (qc_marked_model_geometry (hP j).2.2.1 (hP j).1).1
  have hPpath (j : ℕ) : IsPathConnected (P j) :=
    (qc_marked_model_geometry (hP j).2.2.1 (hP j).1).2.1
  have hPnsource (j : ℕ) : closure (P j) ⊆ (gSeq (φ j)).source := by
    rw [hSeq_source]
    exact (hPcl j).trans hQinside
  have himageOpen (j : ℕ) : IsOpen (gSeq (φ j) '' P j) :=
    (gSeq (φ j)).isOpen_image_of_subset_source (hPopen j)
      (subset_closure.trans (hPnsource j))
  have himagePath (j : ℕ) : IsPathConnected (gSeq (φ j) '' P j) :=
    (hPpath j).image' ((gSeq (φ j)).continuousOn.mono (subset_closure.trans (hPnsource j)))
  have himageCompact (j : ℕ) : IsCompact (closure (gSeq (φ j) '' P j)) := by
    have hcont := (gSeq (φ j)).continuousOn.mono (hPnsource j)
    have hc := (hP j).1.image_of_continuousOn hcont
    have heq : closure (gSeq (φ j) '' P j) = gSeq (φ j) '' closure (P j) :=
      Subset.antisymm (closure_minimal (image_mono subset_closure) hc.isClosed) hcont.image_closure
    exact heq.symm ▸ hc
  obtain ⟨β, hβpos, u, hu, hup⟩ := qc_marked_model_positive hQmod hQcompact
  let γ₀ : Circle → ℂ := fun z ↦ (β z : ℂ)
  have hγ₀ : _root_.Topology.IsEmbedding γ₀ := _root_.Topology.IsEmbedding.subtypeVal.comp β.isEmbedding
  have hfront : frontier Q = range γ₀ := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw⟩ := β.surjective ⟨z, hz⟩
      exact ⟨w, congrArg Subtype.val hw⟩
    · rintro ⟨w, rfl⟩
      exact (β w).property
  obtain ⟨H, hHQ, hHcl⟩ := qc_positive_boundary_bounded_component Q hQgeom.2.1.nonempty
    hQgeom.1 hQgeom.2.1.isConnected hQgeom.2.2 γ₀ hγ₀ hfront β hβpos
  obtain ⟨bg, hbg⟩ := qc_compact_boundary_transport hQgeom.1 hQcompact hgc
    (g.injOn.mono hclsrc) hVopen
  let βg := β.trans bg
  have hβg : PositiveBoundaryParametrization (g '' Q) βg := by
    apply qc_positive_jordan_boundary g Q hQgeom.1 hgc (g.injOn.mono hclsrc)
      β hβpos H hHQ hHcl βg (fun z ↦ hbg (β z))
    intro c r hr hball
    exact hg_positive c r hr (hball.trans (subset_closure.trans hQinside))
  let d (j : ℕ) : closure Q ≃ₜ closure (P j) := e.symm.trans (E j)
  have hd (j : ℕ) (z : closure Q) : (d j z : ℂ) ∈ P j ↔ (z : ℂ) ∈ Q := by
    change (E j (e.symm z) : ℂ) ∈ P j ↔ (z : ℂ) ∈ Q
    rw [(hP j).2.2.2.2]
    exact (heinterior (e.symm z)).symm.trans (by simp)
  choose binner hbinner using fun j ↦ qc_frontier_homeomorph_of_closure
    hQgeom.1 (hPopen j) (d j) (hd j)
  choose bimage hbimage using fun j ↦ qc_compact_boundary_transport (hPopen j) (hP j).1
    ((gSeq (φ j)).continuousOn.mono (hPnsource j))
    ((gSeq (φ j)).injOn.mono (hPnsource j)) (himageOpen j)
  let βn (j : ℕ) : Circle ≃ₜ frontier (gSeq (φ j) '' P j) :=
    β.trans ((binner j).trans (bimage j))
  let zβ (z : Circle) : ClosedRectangle a b :=
    e.symm ⟨β z, frontier_subset_closure (β z).property⟩
  have hβn (j : ℕ) (z : Circle) : (βn j z : ℂ) = gSeq (φ j) (E j (zβ z)) := by
    change (bimage j (binner j (β z)) : ℂ) = _
    rw [hbimage, hbinner]
    rfl
  have hβgval (z : Circle) : (βg z : ℂ) = g (e (zβ z)) := by
    change (bg (β z) : ℂ) = _
    rw [hbg]
    simp [zβ]
  let Γ : ComplexLoop := ⟨fun z ↦ (βg z : ℂ), continuous_subtype_val.comp βg.continuous⟩
  let Γn (j : ℕ) : ComplexLoop :=
    ⟨fun z ↦ (βn j z : ℂ), continuous_subtype_val.comp (βn j).continuous⟩
  have hΓlim : TendstoUniformly (fun j z ↦ Γn j z) Γ atTop := by
    have h := himages.comp zβ
    simpa only [Function.comp_def, ← hβn, ← hβgval, Γn, Γ, ContinuousMap.coe_mk] using h
  obtain ⟨c, hc⟩ := hQgeom.2.1.nonempty
  let zc : ClosedRectangle a b := e.symm ⟨c, subset_closure hc⟩
  have hzc : (zc : ℂ) ∈ OpenRectangle a b := (heinterior zc).mp (by simpa [zc] using hc)
  let cn : ℕ → ℂ := fun j ↦ gSeq (φ j) (E j zc)
  have hcnin (j : ℕ) : cn j ∈ gSeq (φ j) '' P j :=
    ⟨E j zc, ((hP j).2.2.2.2 zc).mpr hzc, rfl⟩
  have hclim : Tendsto cn atTop (𝓝 (g c)) := by
    simpa [cn, zc] using himages.tendsto_at zc
  have havoid (z : Circle) : Γ z ≠ g c := by
    intro heq
    have hz := (βg z).property
    have hz' : (βg z : ℂ) ∈ closure (g '' Q) \ (g '' Q) := by
      simpa only [hVopen.frontier_eq] using hz
    exact hz'.2 (by change (βg z : ℂ) = g c at heq; rw [heq]; exact ⟨c, hc, rfl⟩)
  have hnavoid (j : ℕ) (z : Circle) : Γn j z ≠ cn j := by
    intro heq
    have hz := (βn j z).property
    have hz' : (βn j z : ℂ) ∈ closure (gSeq (φ j) '' P j) \ (gSeq (φ j) '' P j) := by
      simpa only [(himageOpen j).frontier_eq] using hz
    exact hz'.2 (by change (βn j z : ℂ) = cn j at heq; rw [heq]; exact hcnin j)
  have hwind := (windsOncePositively_iff_loopWinding_eq_one Γ (g c) havoid).mp
    (hβg (g c) ⟨c, hc, rfl⟩)
  have hevent := qc_limit_loop_winding Γ Γn (g c) cn havoid hnavoid hΓlim hclim
  have hposEvent : ∀ᶠ j in atTop, PositiveBoundaryParametrization (gSeq (φ j) '' P j) (βn j) := by
    filter_upwards [hevent] with j hj
    apply positive_boundary_of_one_point _ (himageOpen j) (himagePath j) (βn j) (cn j) (hcnin j)
    exact (windsOncePositively_iff_loopWinding_eq_one (Γn j) (cn j) (hnavoid j)).mpr
      (hj.trans hwind)
  have hmodEvent : ∀ᶠ j in atTop, ∃ v : ℝ,
      HasMarkedConformalModulus (gSeq (φ j) '' P j) (fun i ↦ gSeq (φ j) (q j i)) v := by
    filter_upwards [hposEvent] with j hj
    apply qc_positive_marked_modulus (himageOpen j) (himagePath j).isConnected
      ((himageCompact j).isBounded.subset subset_closure)
    refine ⟨βn j, hj, u, hu, ?_⟩
    intro i
    rw [hβn]
    congr 1
    have hz : zβ (u i) = ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩ := by
      apply e.injective
      apply Subtype.ext
      change (e (e.symm _) : ℂ) = _
      rw [e.apply_symm_apply, hecorner]
      exact hup i
    rw [hz]
    exact (hP j).2.2.2.1 i
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hmodEvent
  choose ν hν using fun j ↦ hJ (j + J) (Nat.le_add_left J j)
  obtain ⟨eg, heg, hegint⟩ := qc_partial_homeomorph_closure g hQcompact hclsrc
  choose egn hegn hegnint using fun j ↦
    qc_partial_homeomorph_closure (gSeq (φ j)) (hP j).1 (hPnsource j)
  let h (j : ℕ) : closure (g '' Q) ≃ₜ closure (gSeq (φ j) '' P j) :=
    eg.symm.trans ((d j).trans (egn j))
  have hhval (j : ℕ) (z : closure (g '' Q)) :
      (h j z : ℂ) = gSeq (φ j) (E j (e.symm (eg.symm z))) := by
    exact hegn j _
  have hhint (j : ℕ) (z : closure (g '' Q)) :
      (h j z : ℂ) ∈ gSeq (φ j) '' P j ↔ (z : ℂ) ∈ g '' Q := by
    change (egn j (d j (eg.symm z)) : ℂ) ∈ gSeq (φ j) '' P j ↔ _
    rw [hegnint, hd, ← hegint, eg.apply_symm_apply]
  have hhlim : TendstoUniformly (fun j z ↦ (h j z : ℂ)) (fun z ↦ (z : ℂ)) atTop := by
    have h' := himages.comp (fun z : closure (g '' Q) ↦ e.symm (eg.symm z))
    have heq (z : closure (g '' Q)) : g (e (e.symm (eg.symm z))) = (z : ℂ) := by
      rw [e.apply_symm_apply, ← heg, eg.apply_symm_apply]
    simpa only [Function.comp_def, ← hhval, heq] using h'
  have hpcl (i : Fin 4) : p i ∈ closure Q := by
    rw [← hecorner i]
    exact (e _).property
  have hgpcl (i : Fin 4) : g (p i) ∈ closure (g '' Q) := by
    rw [← heg ⟨p i, hpcl i⟩]
    exact (eg _).property
  have hhmarks (j : ℕ) (i : Fin 4) : (h j ⟨g (p i), hgpcl i⟩ : ℂ) = gSeq (φ j) (q j i) := by
    rw [hhval]
    congr 1
    have hgp : eg.symm ⟨g (p i), hgpcl i⟩ = ⟨p i, hpcl i⟩ := by
      apply eg.injective
      apply Subtype.ext
      rw [eg.apply_symm_apply, heg]
    rw [hgp]
    have hep : e.symm ⟨p i, hpcl i⟩ =
        ⟨RectangleCorner a b i, RectangleModelPreparation.corner_mem ha hb i⟩ := by
      apply e.injective
      apply Subtype.ext
      rw [e.apply_symm_apply, hecorner]
    rw [hep]
    exact (hP j).2.2.2.1 i
  have hVcompact : IsCompact (closure (g '' Q)) := by
    have hc := hQcompact.image_of_continuousOn hgc
    have heq : g '' closure Q = closure (g '' Q) := by
      apply Subset.antisymm hgc.image_closure
      exact closure_minimal (image_mono subset_closure) hc.isClosed
    exact heq ▸ hc
  have hJmono : StrictMono (fun j : ℕ ↦ j + J) := fun i j hij ↦ Nat.add_lt_add_right hij J
  have hνlim : Tendsto ν atTop (𝓝 m') := by
    apply qc_inside_marked_modulus_continuity hVcompact hImageMod
      (fun j ↦ gSeq (φ (j + J)) '' P (j + J))
      (fun j i ↦ gSeq (φ (j + J)) (q (j + J) i)) ν ?_ hν
      (fun j ↦ h (j + J)) (fun j ↦ hhint (j + J)) hgpcl
      (fun j ↦ hhmarks (j + J)) ?_
    · intro j z hz
      obtain ⟨w, hw⟩ := (egn (j + J)).surjective ⟨z, hz⟩
      have heq := congrArg Subtype.val hw
      have heq' : gSeq (φ (j + J)) w = z := (hegn (j + J) w).symm.trans heq
      exact heq' ▸ (hφdata (j + J)).2.2.1 w.property
    · intro s hs
      exact hJmono.tendsto_atTop.eventually (hhlim s hs)
  refine ⟨fun j ↦ φ (j + J), fun j ↦ P (j + J), fun j ↦ q (j + J),
    fun _ ↦ m, ν, hφ.comp hJmono, ?_, tendsto_const_nhds, hνlim⟩
  intro j
  exact ⟨(hφdata (j + J)).1, (hP (j + J)).1,
    (hPcl (j + J)).trans hQinside, (hP (j + J)).2.2.1, hν j⟩

end HolomorphicAnosov

