import HolomorphicAnosov.Geometry.FirstExitTopologicalG18
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import HolomorphicAnosov.Geometry.FirstExitPieceVectorCoordinateG18
import HolomorphicAnosov.Geometry.FirstExitTelescopingG18
import HolomorphicAnosov.Geometry.HermitianLeafPathDistance
import HolomorphicAnosov.Geometry.IntrinsicPiecewiseC1PathGlobalizationG18

/-! First-exit and length estimates in intrinsic coordinate charts. -/

open Set MeasureTheory Metric
open scoped ContDiff Manifold ENNReal
noncomputable section
namespace HolomorphicAnosov

/-- A path leaving a coordinate ball first reaches its coordinate sphere while remaining in the same intrinsic chart. -/
theorem first_exit_compact_chart
    {X E : Type*} [TopologicalSpace X] [T2Space X]
    [MetricSpace E] [ProperSpace E]
    (e : OpenPartialHomeomorph X E) (a : E) {R : ℝ}
    (hR : 0 < R) (hbuffer : closedBall a R ⊆ e.target)
    {γ : ℝ → X} (hγ : ContinuousOn γ (Icc 0 1))
    (hsource : γ 0 ∈ e.source) (hcenter : e (γ 0) = a)
    (hend : γ 1 ∉ e.source ∩ e ⁻¹' ball a R) :
    ∃ τ ∈ Ioc (0 : ℝ) 1,
      γ τ ∈ e.source ∧ dist (e (γ τ)) a = R ∧
      ∀ t ∈ Icc (0 : ℝ) τ,
        γ t ∈ e.source ∧ dist (e (γ t)) a ≤ R := by
  let S := e.source ∩ e ⁻¹' ball a R
  have hopen : IsOpen S := e.continuousOn.isOpen_inter_preimage e.open_source isOpen_ball
  have hstart : γ 0 ∈ S := ⟨hsource, by simpa only [mem_preimage, hcenter] using mem_ball_self hR⟩
  let K := e.symm '' closedBall a R
  have hcompact : IsCompact K :=
    (isCompact_closedBall a R).image_of_continuousOn (e.symm.continuousOn.mono hbuffer)
  have hSK : S ⊆ K := by
    intro x hx
    exact ⟨e x, ball_subset_closedBall hx.2, e.left_inv hx.1⟩
  have hclK : closure S ⊆ K := closure_minimal hSK hcompact.isClosed
  have hK (x : X) (hx : x ∈ K) : x ∈ e.source ∧ dist (e x) a ≤ R := by
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨e.map_target (hbuffer hz), by simpa only [e.right_inv (hbuffer hz)] using (mem_closedBall.mp hz)⟩
  obtain ⟨τ, hτ, hτpos, hfront, hbefore⟩ :=
    exists_first_exit_time hopen (by norm_num : (0 : ℝ) < 1) hγ hstart hend
  have hτK := hK (γ τ) (hclK hfront.1)
  have hτdist : dist (e (γ τ)) a = R := by
    apply le_antisymm hτK.2
    by_contra hn
    have hmem : γ τ ∈ S := ⟨hτK.1, lt_of_not_ge hn⟩
    exact hfront.2 (hopen.interior_eq.symm ▸ hmem)
  refine ⟨τ, ⟨hτpos, hτ.2⟩, hτK.1, hτdist, ?_⟩
  intro t ht
  by_cases heq : t = τ
  · subst t
    exact hτK
  · exact hK (γ t) (hSK (hbefore t ht heq))


/-- The coordinate displacement up to any time in a piecewise C¹ path is bounded by its full length whenever coordinate derivatives on that prefix satisfy the stated speed bound. -/
theorem intrinsic_path_prefix_coordinate_length
    {r : ℕ} {L : Type*} [TopologicalSpace L]
    [ChartedSpace (Fin r → ℝ) L] {x y : L}
    (p : IntrinsicPiecewiseC1Path (r := r) x y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : L → E) (γ : ℝ → L)
    (hγ : ∀ i : Fin (p.n+1), ∀ t ∈ p.pieceInterval i, γ t = p.piece i t)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (speed : Fin (p.n+1) → ℝ → ℝ) (m : ℝ) (hm : 0 < m)
    (hc : ∀ i : Fin (p.n+1), ContDiffOn ℝ 1 (c ∘ p.piece i)
      (Icc (p.time i.castSucc) (min (p.time i.succ) τ)))
    (hbound : ∀ (i : Fin (p.n+1)), p.time i.castSucc < τ → ∀ t,
      t ∈ Icc (p.time i.castSucc) (min (p.time i.succ) τ) →
      m * ‖derivWithin (c ∘ p.piece i)
        (Icc (p.time i.castSucc) (min (p.time i.succ) τ)) t‖ ≤ speed i t) :
    ENNReal.ofReal (m * ‖c (γ τ) - c (γ 0)‖) ≤
      ∑ i : Fin (p.n+1), ∫⁻ t in p.pieceInterval i, ENNReal.ofReal (speed i t) := by
  let start := fun i : Fin (p.n+1) ↦ c (γ (min (p.time i.castSucc) τ))
  let finish := fun i : Fin (p.n+1) ↦ c (γ (min (p.time i.succ) τ))
  have htel : ‖c (γ τ) - c (γ 0)‖ ≤
      ∑ i : Fin (p.n+1), ‖finish i - start i‖ := by
    have h := norm_sub_le_sum_norm_sub_junction p.n start finish (fun _ ↦ rfl)
    simpa only [start, finish, Fin.castSucc_zero, Fin.succ_last, p.time_zero, p.time_one, min_eq_left hτ.1,
      min_eq_right hτ.2] using h
  have hpiece (i : Fin (p.n+1)) : ENNReal.ofReal (m * ‖finish i - start i‖) ≤
      ∫⁻ t in p.pieceInterval i, ENNReal.ofReal (speed i t) := by
    by_cases hi : p.time i.castSucc < τ
    · have hab : p.time i.castSucc < min (p.time i.succ) τ :=
        lt_min (p.time_strictMono i.castSucc_lt_succ) hi
      have hstart : start i = c (p.piece i (p.time i.castSucc)) := by
        dsimp only [start]
        rw [min_eq_left hi.le, hγ i _ ⟨le_rfl, (p.time_strictMono i.castSucc_lt_succ).le⟩]
      have hfinish : finish i = c (p.piece i (min (p.time i.succ) τ)) := by
        dsimp only [finish]
        rw [hγ i _ ⟨hab.le, min_le_left _ _⟩]
      rw [hstart, hfinish]
      have hb := first_exit_piece_vector_coordinate_lower_bound E
        (ContinuousLinearMap.id ℝ E) hab (hc i) hm (fun t ht ↦ hbound i hi t ht)
      simp only [ContinuousLinearMap.id_apply, Function.comp_apply] at hb
      exact hb.trans (lintegral_mono_set (Icc_subset_Icc le_rfl (min_le_left _ _)))
    · have hle : τ ≤ p.time i.castSucc := le_of_not_gt hi
      have hle' : τ ≤ p.time i.succ := hle.trans (p.time_strictMono i.castSucc_lt_succ).le
      simp only [start, finish, min_eq_right hle, min_eq_right hle', sub_self,
        norm_zero, mul_zero, ENNReal.ofReal_zero, zero_le]
  calc
    ENNReal.ofReal (m * ‖c (γ τ) - c (γ 0)‖) ≤
        ENNReal.ofReal (∑ i : Fin (p.n+1), m * ‖finish i - start i‖) := by
      apply ENNReal.ofReal_le_ofReal
      simpa only [Finset.mul_sum] using mul_le_mul_of_nonneg_left htel hm.le
    _ = ∑ i : Fin (p.n+1), ENNReal.ofReal (m * ‖finish i - start i‖) :=
      ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)
    _ ≤ _ := Finset.sum_le_sum (fun i _ ↦ hpiece i)


/-- The prefix displacement estimate using the differential of a smooth intrinsic coordinate and the original within-piece manifold velocity. -/
theorem intrinsic_path_prefix_mfderiv_length
    {r : ℕ} {L : Type*} [TopologicalSpace L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) 1 L]
    {x y : L} (p : IntrinsicPiecewiseC1Path (r := r) x y)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : L → E) (S : Set L) (hS : IsOpen S)
    (hc : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) 1 c S)
    (γ : ℝ → L)
    (hγ : ∀ i : Fin (p.n+1), ∀ t ∈ p.pieceInterval i, γ t = p.piece i t)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) 1)
    (hmaps : ∀ t ∈ Icc (0 : ℝ) τ, γ t ∈ S)
    (speed : ∀ z : L, TangentSpace 𝓘(ℝ, Fin r → ℝ) z → ℝ)
    (m : ℝ) (hm : 0 < m)
    (hbound : ∀ z ∈ S, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (c z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) c z v)‖ ≤ speed z v) :
    ENNReal.ofReal (m * ‖c (γ τ) - c (γ 0)‖) ≤
      ∑ i : Fin (p.n+1), ∫⁻ t in p.pieceInterval i,
        ENNReal.ofReal (speed (p.piece i t) (p.velocity i t)) := by
  have hsub (i : Fin (p.n+1)) :
      Icc (p.time i.castSucc) (min (p.time i.succ) τ) ⊆ p.pieceInterval i :=
    Icc_subset_Icc le_rfl (min_le_left _ _)
  have hmap (i : Fin (p.n+1)) :
      MapsTo (p.piece i) (Icc (p.time i.castSucc) (min (p.time i.succ) τ)) S := by
    intro t ht
    rw [← hγ i t (hsub i ht)]
    apply hmaps t
    refine ⟨?_, ht.2.trans (min_le_right _ _)⟩
    calc
      0 = p.time 0 := p.time_zero.symm
      _ ≤ p.time i.castSucc := p.time_strictMono.monotone (Fin.zero_le _)
      _ ≤ t := ht.1
  apply intrinsic_path_prefix_coordinate_length p c γ hγ τ hτ
    (fun i t ↦ speed (p.piece i t) (p.velocity i t)) m hm
  · intro i
    exact contMDiffOn_iff_contDiffOn.mp
      (hc.comp ((p.piece_c1 i).mono (hsub i)) (hmap i))
  · intro i hi t ht
    have hab : p.time i.castSucc < min (p.time i.succ) τ :=
      lt_min (p.time_strictMono i.castSucc_lt_succ) hi
    have hu : UniqueMDiffWithinAt 𝓘(ℝ) 
        (Icc (p.time i.castSucc) (min (p.time i.succ) τ)) t :=
      uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_Icc hab t ht)
    have hp := ((p.piece_c1 i).mdifferentiableOn one_ne_zero t (hsub i ht))
    have hcd := (hc.contMDiffAt (hS.mem_nhds (hmap i ht))).mdifferentiableAt one_ne_zero
    have hchain := mfderiv_comp_mfderivWithin t hcd (hp.mono (hsub i)) hu
    have hrestrict := hp.mfderivWithin_mono hu (hsub i)
    have hd : derivWithin (c ∘ p.piece i)
        (Icc (p.time i.castSucc) (min (p.time i.succ) τ)) t =
        (tangentSpaceCastModel 𝓘(ℝ, E) (c (p.piece i t)))
          (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) c (p.piece i t) (p.velocity i t)) := by
      rw [derivWithin, ← mfderivWithin_eq_fderivWithin, hchain, hrestrict]
      rfl
    rw [hd]
    exact hbound _ (hmap i ht) _


/-- Every original intrinsic piecewise C¹ path that leaves a buffered chart ball has length at least mR, measured with the supplied original tangent speed. -/
theorem intrinsic_chart_first_exit_length
    {r : ℕ} {L : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) 1 L]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : OpenPartialHomeomorph L E)
    (he : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) 1 e e.source)
    (a : E) (R : ℝ) (hR : 0 < R) (hbuffer : closedBall a R ⊆ e.target)
    (speed : ∀ z : L, TangentSpace 𝓘(ℝ, Fin r → ℝ) z → ℝ)
    (m : ℝ) (hm : 0 < m)
    (hbound : ∀ z ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) e z v)‖ ≤ speed z v)
    {x y : L} (hx : x ∈ e.source) (hxa : e x = a)
    (hy : y ∉ e.source ∩ e ⁻¹' ball a R)
    (p : IntrinsicPiecewiseC1Path (r := r) x y) :
    ENNReal.ofReal (m*R) ≤
      ∑ i : Fin (p.n+1), ∫⁻ t in p.pieceInterval i,
        ENNReal.ofReal (speed (p.piece i t) (p.velocity i t)) := by
  obtain ⟨γ, hγcont, hγ0, hγ1, hγpiece⟩ := intrinsicPiecewiseC1Path_global_representative p
  obtain ⟨τ, hτ, hsource, hdist, hbefore⟩ := first_exit_compact_chart e a hR hbuffer
    hγcont (by simpa only [hγ0] using hx) (by simpa only [hγ0] using hxa)
    (by simpa only [hγ1] using hy)
  have hlength := intrinsic_path_prefix_mfderiv_length p e e.source e.open_source he γ
    hγpiece τ ⟨hτ.1.le, hτ.2⟩ (fun t ht ↦ (hbefore t ht).1) speed m hm hbound
  have hnorm : ‖e (γ τ) - e (γ 0)‖ = R := by
    rw [hγ0, hxa, ← dist_eq_norm]
    exact hdist
  simpa only [hnorm] using hlength

/-- A distance defined by the infimum of these actual piecewise lengths has its strict mR-ball contained in the same intrinsic coordinate ball. -/
theorem intrinsic_chart_ball_of_length_inf_lt
    {r : ℕ} {L : Type*} [TopologicalSpace L] [T2Space L]
    [ChartedSpace (Fin r → ℝ) L] [IsManifold 𝓘(ℝ, Fin r → ℝ) 1 L]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : OpenPartialHomeomorph L E)
    (he : ContMDiffOn 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) 1 e e.source)
    (a : E) (R : ℝ) (hR : 0 < R) (hbuffer : closedBall a R ⊆ e.target)
    (speed : ∀ z : L, TangentSpace 𝓘(ℝ, Fin r → ℝ) z → ℝ)
    (m : ℝ) (hm : 0 < m)
    (hbound : ∀ z ∈ e.source, ∀ v : TangentSpace 𝓘(ℝ, Fin r → ℝ) z,
      m * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e z))
        (mfderiv 𝓘(ℝ, Fin r → ℝ) 𝓘(ℝ, E) e z v)‖ ≤ speed z v)
    {x y : L} (hx : x ∈ e.source) (hxa : e x = a)
    (hd : (⨅ p : IntrinsicPiecewiseC1Path (r := r) x y,
      ∑ i : Fin (p.n+1), ∫⁻ t in p.pieceInterval i,
        ENNReal.ofReal (speed (p.piece i t) (p.velocity i t))) < ENNReal.ofReal (m*R)) :
    y ∈ e.source ∩ e ⁻¹' ball a R := by
  by_contra hy
  have hle : ENNReal.ofReal (m*R) ≤
      ⨅ p : IntrinsicPiecewiseC1Path (r := r) x y,
        ∑ i : Fin (p.n+1), ∫⁻ t in p.pieceInterval i,
          ENNReal.ofReal (speed (p.piece i t) (p.velocity i t)) := by
    refine le_iInf fun p ↦ ?_
    exact intrinsic_chart_first_exit_length e he a R hR hbuffer speed m hm hbound hx hxa hy p
  exact (not_lt_of_ge hle) hd

end HolomorphicAnosov
