import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankAtlasFrameContinuity
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphAtlasOperations
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphParameterInverseContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphWeightedLimitContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageStep
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimagePointComparison
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphCarrierMetric
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Homeomorph.TransferInstance

/-!
# Continuity of parameter graph transforms and their fixed graphs

Hirsch–Pugh–Shub, Invariant Manifolds, pp.54–57 and 62. All continuity is in
the original finite-rank bundle topology, and every estimate uses its original norms.
-/

noncomputable section
open Set Filter Topology
namespace HolomorphicAnosov

section Carrier
variable {A : Type*} [TopologicalSpace A] {E F : A → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]

/-- A carrier limit of continuous graphs is continuous. Its pointwise error is
bounded by carrier distance times the original input norm, so the weighted-limit
continuity theorem applies with the continuous weight `‖x‖`. HPS pp.54–55,62. -/
theorem parameter_graph_carrier_limit_continuous
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (q : ℕ → ParameterGraphCarrier E F) (s : ParameterGraphCarrier E F)
    (hq : ∀ n, Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F (q n) z.1 z.2⟩ : Sigma F)))
    (hlim : Tendsto q atTop (𝓝 s)) :
    Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F s z.1 z.2⟩ : Sigma F)) := by
  apply parameter_graph_weighted_limit_continuity f (fun z : Sigma E ↦ z.1)
    (parameter_graph_atlas_projection_continuous e)
    (fun n z ↦ parameterGraphValue E F (q n) z.1 z.2)
    (fun z ↦ parameterGraphValue E F s z.1 z.2) hq
    (fun z : Sigma E ↦ ‖z.2‖) e.continuous_norm (fun _ ↦ norm_nonneg _)
    (fun n ↦ ‖q n - s‖) (fun _ ↦ norm_nonneg _)
  · simpa using (hlim.sub (tendsto_const_nhds (x := s))).norm
  · intro n z
    exact (parameter_graph_carrier_norm_le_iff E F (q n) s _ (norm_nonneg _)).mp
      le_rfl z.1 z.2

/-- Any fixed point of a strict carrier contraction preserving continuous graphs
is continuous if one continuous starting graph is available. Iterate that graph;
the contraction gives convergence to the fixed point. Apply the preceding weighted
limit theorem. This is HPS's parameter Picard argument on p.62. -/
theorem parameter_graph_carrier_fixed_continuous
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (Φ : {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F} →
      {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F})
    (k : NNReal) (hΦ : ContractingWith k Φ)
    (hpres : ∀ q, Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F q.1 z.1 z.2⟩ : Sigma F)) →
      Continuous (fun z : Sigma E ↦
        (⟨z.1, parameterGraphValue E F (Φ q).1 z.1 z.2⟩ : Sigma F)))
    (s₀ s : {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F})
    (hs₀ : Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F s₀.1 z.1 z.2⟩ : Sigma F)))
    (hs : Φ s = s) :
    Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F s.1 z.1 z.2⟩ : Sigma F)) := by
  apply parameter_graph_carrier_limit_continuous e f (fun n ↦ (Φ^[n] s₀).1) s.1
  · intro n
    induction n with
    | zero => exact hs₀
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hpres (Φ^[n] s₀) ih
  · apply continuous_subtype_val.tendsto s |>.comp
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hb (n : ℕ) : dist (Φ^[n] s₀) s ≤ (k : ℝ)^n * dist s₀ s := by
      have hh := (hΦ.toLipschitzWith.iterate n).dist_le_mul s₀ s
      simpa only [((show Function.IsFixedPt Φ s from hs).iterate n).eq, NNReal.coe_pow] using hh
    apply squeeze_zero (fun _ ↦ dist_nonneg) hb
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one k.coe_nonneg
      (show (k : ℝ) < 1 from hΦ.1)).mul_const (dist s₀ s)
/-- Start Picard iteration at the zero graph, whose continuity follows from the
original bundle atlas. Thus continuity preservation alone suffices for continuity
of any fixed carrier. Source: HPS pp.54–55,62. -/
theorem parameter_graph_carrier_fixed_continuous_zero
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (Φ : {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F} →
      {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F})
    (k : NNReal) (hΦ : ContractingWith k Φ)
    (hpres : ∀ q, Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F q.1 z.1 z.2⟩ : Sigma F)) →
      Continuous (fun z : Sigma E ↦
        (⟨z.1, parameterGraphValue E F (Φ q).1 z.1 z.2⟩ : Sigma F)))
    (s : {q : ParameterGraphCarrier E F // q ∈ parameterGraphUnitSet E F})
    (hs : Φ s = s) :
    Continuous (fun z : Sigma E ↦
      (⟨z.1, parameterGraphValue E F s.1 z.1 z.2⟩ : Sigma F)) := by
  classical
  have hvalue : ∀ p x, parameterGraphValue E F 0 p x = 0 := by
    intro p x
    simp [parameterGraphValue]
  have hzero : (0 : ParameterGraphCarrier E F) ∈ parameterGraphUnitSet E F := by
    intro p
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro x y
    simp only [hvalue, sub_self, norm_zero, NNReal.coe_one, one_mul]
    exact norm_nonneg _
  apply parameter_graph_carrier_fixed_continuous e f Φ k hΦ hpres ⟨0, hzero⟩ s _ hs
  simpa only [hvalue] using parameter_graph_atlas_zero_continuous f
    (fun z : Sigma E ↦ z.1) (parameter_graph_atlas_projection_continuous e)
end Carrier

section Inverse
variable {A : Type*} [TopologicalSpace A] {E F : A → Type*}
  [∀ p, NormedAddCommGroup (E p)] [∀ p, NormedSpace ℝ (E p)]
  [∀ p, NormedAddCommGroup (F p)] [∀ p, NormedSpace ℝ (F p)]
  [TopologicalSpace (Sigma E)] [TopologicalSpace (Sigma F)]

/-- A continuous family of fibre homeomorphisms with one uniform inverse estimate
has a continuous total inverse over a homeomorphism of the base. On the pullback
of the receiving bundle, subtract the continuous target from forward evaluations
on a fixed source frame. Their norms are continuous, so the parameter inverse
estimate gives the solution's total continuity. Reindex to the receiving bundle.
This is the horizontal parameter inversion argument of HPS p.62. -/
theorem parameter_graph_fibre_homeomorph_inverse_continuous
    (e : FiniteRankNormedAtlas (E := E)) (f : FiniteRankNormedAtlas (E := F))
    (h : A ≃ₜ A) (H : ∀ p, E p ≃ₜ F (h p))
    (hH : Continuous (fun z : Sigma E ↦ (⟨h z.1, H z.1 z.2⟩ : Sigma F)))
    (K : ℝ) (hK : ∀ p u v, ‖(H p).symm u - (H p).symm v‖ ≤ K * ‖u - v‖) :
    Continuous ((Equiv.sigmaCongrRight (fun p ↦ (H p).toEquiv)).trans
      (Equiv.sigmaCongrLeft h.toEquiv)).symm := by
  let R : (Σ p, F (h p)) ≃ Sigma F := Equiv.sigmaCongrLeft h.toEquiv
  let : TopologicalSpace (Σ p, F (h p)) := R.topologicalSpace
  let Rhome : (Σ p, F (h p)) ≃ₜ Sigma F := R.homeomorph
  have hbase : Continuous (fun z : (Σ p, F (h p)) ↦ z.1) := by
    have hc := h.symm.continuous.comp
      ((parameter_graph_atlas_projection_continuous f).comp Rhome.continuous)
    apply hc.congr
    intro z
    exact h.symm_apply_apply z.1
  have hsolution : Continuous (fun z : (Σ p, F (h p)) ↦
      (⟨z.1, (H z.1).symm z.2⟩ : Sigma E)) := by
    apply parameter_graph_inverse_solution_continuous e
      (fun z : (Σ p, F (h p)) ↦ z.1) (fun z ↦ h z.1) hbase
      (fun z ↦ H z.1) (fun z ↦ z.2) (fun z ↦ (H z.1).symm z.2) K
    · intro z u v
      simpa only [Homeomorph.symm_apply_apply] using hK z.1 (H z.1 u) (H z.1 v)
    · intro z
      exact (H z.1).apply_symm_apply z.2
    · intro i v
      let U := {z : (Σ p, F (h p)) // z.1 ∈ (e.chart i).baseSet}
      have hframe : Continuous (fun z : U ↦
          (⟨z.val.1, (e.coordinates i z.val.1 z.property).symm v⟩ : Sigma E)) :=
        (atlas_frame_continuous e i).comp
          (((hbase.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property)).prodMk continuous_const)
      have hsub := parameter_graph_atlas_sub_continuous f
        (fun z : U ↦ h z.val.1) (h.continuous.comp (hbase.comp continuous_subtype_val))
        (fun z ↦ H z.val.1 ((e.coordinates i z.val.1 z.property).symm v))
        (fun z ↦ z.val.2) (hH.comp hframe)
        (Rhome.continuous.comp continuous_subtype_val)
      exact f.continuous_norm.comp hsub
  exact hsolution.comp Rhome.symm.continuous
end Inverse

section Transforms
variable {A : Type*} [TopologicalSpace A] {E₁ E₂ : A → Type*}
  [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
  [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
  [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
  [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]

/-- The image graph transform preserves total continuity. Its horizontal map is
a fibre homeomorphism with a uniform inverse bound. The preceding parameter inverse
theorem makes its total inverse continuous. Compose it with the original graph,
the ambient map and the receiving vertical projection. The exact graph-image identity
identifies this continuous map with the given output graph. HPS pp.54–55,62. -/
theorem parameter_graph_image_continuous_of_inverse
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, G z.1 z.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p))))
    (s t : ∀ p, E₁ p → E₂ p)
    (hs : Continuous (fun z : Sigma E₁ ↦ (⟨z.1, s z.1 z.2⟩ : Sigma E₂)))
    (H : ∀ p, E₁ p ≃ₜ E₁ (h p))
    (hH : ∀ p x, H p x = (G p (x, s p x)).1)
    (K : ℝ) (hK : ∀ p u v, ‖(H p).symm u - (H p).symm v‖ ≤ K * ‖u - v‖)
    (hgraph : ∀ p, G p '' range (fun x ↦ (x, s p x)) =
      range (fun x ↦ (x, t (h p) x))) :
    Continuous (fun z : Sigma E₁ ↦ (⟨z.1, t z.1 z.2⟩ : Sigma E₂)) := by
  let D : Sigma E₁ ≃ Sigma E₁ :=
    (Equiv.sigmaCongrRight (fun p ↦ (H p).toEquiv)).trans
      (Equiv.sigmaCongrLeft h.toEquiv)
  have hpair := parameter_graph_atlas_pair_continuous e (fun z : Sigma E₁ ↦ z.1)
    (fun z ↦ z.2) (fun z ↦ s z.1 z.2) continuous_id hs
  have hg := hG.comp hpair
  have hproj := parameter_graph_atlas_split_projections_continuous e
  have hfirst : Continuous (fun z : Sigma E₁ ↦ (⟨h z.1, H z.1 z.2⟩ : Sigma E₁)) := by
    simpa only [Function.comp_def, hH] using hproj.1.comp hg
  have hinv : Continuous D.symm :=
    parameter_graph_fibre_homeomorph_inverse_continuous e.first e.first h H hfirst K hK
  have hout := (hproj.2.comp hg).comp hinv
  apply hout.congr
  intro z
  obtain ⟨w, rfl⟩ := D.surjective z
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hmem : G w.1 (w.2, s w.1 w.2) ∈ range (fun x ↦ (x, t (h w.1) x)) := by
    rw [← hgraph w.1]
    exact ⟨_, ⟨w.2, rfl⟩, rfl⟩
  obtain ⟨u, hu⟩ := hmem
  have hu₁ : u = H w.1 w.2 := (congrArg Prod.fst hu).trans (hH w.1 w.2).symm
  have hu₂ := congrArg Prod.snd hu
  dsimp only at hu₂
  rw [hu₁] at hu₂
  exact congrArg (fun v ↦ (⟨h w.1, v⟩ : Sigma E₂)) hu₂.symm

/-- The preimage graph transform preserves total continuity whenever its horizontal
residual has a uniform inverse estimate. For each vertical input, solve
`G₁(x,y)-t(G₂(x,y))=0`. The full preimage identity gives this equation for the
output graph. Continuous graph and ambient values make every fixed-frame residual
continuous; apply parameter inversion. Only the horizontal equation is inverted.
Source: HPS pp.56–57,62. -/
theorem parameter_graph_preimage_continuous_of_inverse
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, G z.1 z.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p))))
    (t s : ∀ p, E₂ p → E₁ p)
    (ht : Continuous (fun z : Sigma E₂ ↦ (⟨z.1, t z.1 z.2⟩ : Sigma E₁)))
    (K : ℝ)
    (hK : ∀ p y x x', ‖x - x'‖ ≤ K *
      ‖((G p (x,y)).1 - t (h p) (G p (x,y)).2) -
        ((G p (x',y)).1 - t (h p) (G p (x',y)).2)‖)
    (hgraph : ∀ p, G p ⁻¹' range (fun y ↦ (t (h p) y, y)) =
      range (fun y ↦ (s p y, y))) :
    Continuous (fun z : Sigma E₂ ↦ (⟨z.1, s z.1 z.2⟩ : Sigma E₁)) := by
  have hb := parameter_graph_atlas_projection_continuous e.second
  have hproj := parameter_graph_atlas_split_projections_continuous e
  apply parameter_graph_inverse_solution_continuous e.first
    (fun z : Sigma E₂ ↦ z.1) (fun z ↦ h z.1) hb
    (fun z x ↦ (G z.1 (x,z.2)).1 - t (h z.1) (G z.1 (x,z.2)).2)
    (fun _ ↦ 0) (fun z ↦ s z.1 z.2) K
  · intro z x x'
    exact hK z.1 z.2 x x'
  · intro z
    have hmem : G z.1 (s z.1 z.2,z.2) ∈ range (fun y ↦ (t (h z.1) y,y)) := by
      change (s z.1 z.2,z.2) ∈ G z.1 ⁻¹' range (fun y ↦ (t (h z.1) y,y))
      rw [hgraph z.1]
      exact ⟨z.2, rfl⟩
    obtain ⟨y, hy⟩ := hmem
    rw [← hy]
    exact sub_self _
  · intro i v
    let U := {z : Sigma E₂ // z.1 ∈ (e.first.chart i).baseSet}
    have hframe : Continuous (fun z : U ↦
        (⟨z.val.1, (e.first.coordinates i z.val.1 z.property).symm v⟩ : Sigma E₁)) :=
      (atlas_frame_continuous e.first i).comp
        (((hb.comp continuous_subtype_val).subtype_mk (fun z ↦ z.property)).prodMk continuous_const)
    have hpair := parameter_graph_atlas_pair_continuous e (fun z : U ↦ z.val.1)
      (fun z ↦ (e.first.coordinates i z.val.1 z.property).symm v)
      (fun z ↦ z.val.2) hframe continuous_subtype_val
    have hg := hG.comp hpair
    have hsub := parameter_graph_atlas_sub_continuous e.first
      (fun z : U ↦ h z.val.1) (h.continuous.comp (hb.comp continuous_subtype_val))
      (fun z ↦ (G z.val.1 ((e.first.coordinates i z.val.1 z.property).symm v,z.val.2)).1)
      (fun z ↦ t (h z.val.1)
        (G z.val.1 ((e.first.coordinates i z.val.1 z.property).symm v,z.val.2)).2)
      (hproj.1.comp hg) (ht.comp (hproj.2.comp hg))
    simpa only [Function.comp_def, sub_zero] using e.first.continuous_norm.comp hsub
/-- The image transform is continuous under the original HPS block estimates.
The single-fibre image theorem supplies the horizontal homeomorphism with inverse
bound `a/(1-aε)`, uniformly over the base. Apply total inverse continuity and the
exact graph identity. No continuity of a separately chosen inverse is assumed.
Source: HPS Sublemma 5.2 and parameter insertion, pp.54–55,62. -/
theorem parameter_graph_image_continuous
    [∀ p, CompleteSpace (E₁ p)]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, G z.1 z.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p))))
    (hzero : ∀ p, G p 0 = 0)
    (a k ε : NNReal)
    (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖T₂ p‖ ≤ k)
    (hsmall : (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) ≤ 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (s t : ∀ p, E₁ p → E₂ p)
    (hs0 : ∀ p, s p 0 = 0) (hslip : ∀ p, LipschitzWith 1 (s p))
    (hs : Continuous (fun z : Sigma E₁ ↦ (⟨z.1, s z.1 z.2⟩ : Sigma E₂)))
    (hgraph : ∀ p, G p '' range (fun x ↦ (x, s p x)) =
      range (fun x ↦ (x, t (h p) x))) :
    Continuous (fun z : Sigma E₁ ↦ (⟨z.1, t z.1 z.2⟩ : Sigma E₂)) := by
  choose H r hH hH0 hInv hr0 hrlip hrgraph using
    fun p ↦ parameter_graph_image_step (T₁ p) (T₂ p) (G p) (hzero p) a k ε
      (ha p) (hk p) hsmall hslope (hR p) (s p) (hs0 p) (hslip p)
  exact parameter_graph_image_continuous_of_inverse e h G hG s t hs H hH
    ((a : ℝ) / (1 - (a : ℝ) * ε)) hInv hgraph

/-- The preimage transform is continuous under the original block estimates.
To bound arbitrary horizontal residuals, translate the receiving unit-slope graph
by each residual so the two tested points satisfy exact graph equations. The
single-point comparison gives inverse factor `a/(1-2aε)`; translations cancel in
their difference. Parameter inversion then proves total continuity. This is the
horizontal estimate of HPS pp.56–57 with the parameter argument on p.62. -/
theorem parameter_graph_preimage_continuous
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, G z.1 z.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p))))
    (a ε : NNReal)
    (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (t s : ∀ p, E₂ p → E₁ p) (htlip : ∀ p, LipschitzWith 1 (t p))
    (ht : Continuous (fun z : Sigma E₂ ↦ (⟨z.1, t z.1 z.2⟩ : Sigma E₁)))
    (hgraph : ∀ p, G p ⁻¹' range (fun y ↦ (t (h p) y, y)) =
      range (fun y ↦ (s p y, y))) :
    Continuous (fun z : Sigma E₂ ↦ (⟨z.1, s z.1 z.2⟩ : Sigma E₁)) := by
  apply parameter_graph_preimage_continuous_of_inverse e h G hG t s ht
    ((a : ℝ) / (1 - 2 * (a : ℝ) * ε)) _ hgraph
  intro p y x x'
  let u := (G p (x,y)).1 - t (h p) (G p (x,y)).2
  let v := (G p (x',y)).1 - t (h p) (G p (x',y)).2
  have heq : (G p (x,y)).1 = t (h p) (G p (x,y)).2 + u := by dsimp [u]; abel
  have heq' : (G p (x',y)).1 = t (h p) (G p (x',y)).2 + v := by dsimp [v]; abel
  have hb := parameter_graph_preimage_point_comparison (T₁ p) (T₂ p) (G p)
    a ε (ha p) hsmall (hR p) (fun z ↦ t (h p) z + u) (fun z ↦ t (h p) z + v)
    (by
      apply lipschitzWith_iff_norm_sub_le.mpr
      intro z z'
      simpa only [add_sub_add_right_eq_sub] using (htlip (h p)).norm_sub_le z z')
    x x' y heq heq'
  simpa only [add_sub_add_left_eq_sub] using hb
end Transforms

section FixedTransforms
variable {A : Type*} [TopologicalSpace A] {E₁ E₂ : A → Type*}
  [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
  [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
  [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
  [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]

/-- The actual fixed carrier of the image transform defines a continuous graph.
Each Picard iterate of the zero graph is continuous by horizontal parameter
inversion. The carrier contraction converges in the original weighted norm;
weighted-limit continuity gives the claimed original total-space continuity.
Source: HPS pp.54–55,62. -/
theorem parameter_graph_image_fixed_continuous
    [∀ p, CompleteSpace (E₁ p)]
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, G z.1 z.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p))))
    (hzero : ∀ p, G p 0 = 0) (a k ε q : NNReal)
    (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hk : ∀ p, ‖T₂ p‖ ≤ k) (hsmall : (a : ℝ) * ε < 1)
    (hslope : (a : ℝ) * ((k : ℝ) + 2 * ε) ≤ 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (Φ : {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂} →
      {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂})
    (hΦ : ContractingWith q Φ)
    (hΦgraph : ∀ s p,
      G p '' range (fun x ↦ (x, parameterGraphValue E₁ E₂ s.1 p x)) =
        range (fun x ↦ (x, parameterGraphValue E₁ E₂ (Φ s).1 (h p) x)))
    (s : {s : ParameterGraphCarrier E₁ E₂ // s ∈ parameterGraphUnitSet E₁ E₂})
    (hs : Φ s = s) :
    Continuous (fun z : Sigma E₁ ↦
      (⟨z.1, parameterGraphValue E₁ E₂ s.1 z.1 z.2⟩ : Sigma E₂)) := by
  apply parameter_graph_carrier_fixed_continuous_zero e.first e.second Φ q hΦ _ s hs
  intro u hu
  exact parameter_graph_image_continuous e h T₁ T₂ G hG hzero a k ε ha hk hsmall hslope hR
    (parameterGraphValue E₁ E₂ u.1) (parameterGraphValue E₁ E₂ (Φ u).1)
    (fun p ↦ by simp [parameterGraphValue]) u.2 hu (hΦgraph u)

/-- The actual fixed carrier of the full preimage transform defines a continuous
graph. Its iterates preserve continuity by the residual inverse estimate and
converge from the zero graph in the original weighted norm. This argument uses
no inverse of the vertical block. Source: HPS pp.56–57,62. -/
theorem parameter_graph_preimage_fixed_continuous
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p)) (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : Continuous (fun z : Sigma (fun p ↦ E₁ p × E₂ p) ↦
      (⟨h z.1, G z.1 z.2⟩ : Sigma (fun p ↦ E₁ p × E₂ p))))
    (a ε q : NNReal) (ha : ∀ p, ‖(T₁ p).symm.toContinuousLinearMap‖ ≤ a)
    (hsmall : 2 * (a : ℝ) * ε < 1)
    (hR : ∀ p, LipschitzWith ε (fun z ↦ G p z - (T₁ p z.1, T₂ p z.2)))
    (Φ : {t : ParameterGraphCarrier E₂ E₁ // t ∈ parameterGraphUnitSet E₂ E₁} →
      {t : ParameterGraphCarrier E₂ E₁ // t ∈ parameterGraphUnitSet E₂ E₁})
    (hΦ : ContractingWith q Φ)
    (hΦgraph : ∀ t p,
      G p ⁻¹' range (fun y ↦ (parameterGraphValue E₂ E₁ t.1 (h p) y,y)) =
        range (fun y ↦ (parameterGraphValue E₂ E₁ (Φ t).1 p y,y)))
    (t : {t : ParameterGraphCarrier E₂ E₁ // t ∈ parameterGraphUnitSet E₂ E₁})
    (ht : Φ t = t) :
    Continuous (fun z : Sigma E₂ ↦
      (⟨z.1, parameterGraphValue E₂ E₁ t.1 z.1 z.2⟩ : Sigma E₁)) := by
  apply parameter_graph_carrier_fixed_continuous_zero e.second e.first Φ q hΦ _ t ht
  intro u hu
  exact parameter_graph_preimage_continuous e h T₁ T₂ G hG a ε ha hsmall hR
    (parameterGraphValue E₂ E₁ u.1) (parameterGraphValue E₂ E₁ (Φ u).1)
    u.2 hu (hΦgraph u)
end FixedTransforms


end HolomorphicAnosov
