import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphBoundedForcing
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphInvariantSectionDerivative

noncomputable section
open Filter Topology
namespace HolomorphicAnosov

/-- HPS pp.32–33: bounded forcing gives uniform fibrewise Lipschitz estimates
for an invariant section even though the return changes the parameter fibre.
Iterate the comparison n times along the same base orbit. The bounded-section
error is at most 2 M q^n, while the Lipschitz forcing forms a geometric series
with ratio qc<1. Letting n tend to infinity gives L/(1−qc). The source spaces
may be closed metric discs; no linear structure or return inverse is needed. -/
theorem parameter_graph_fibre_bounded_forcing
    {I : Type*} (X Y : I → Type*) [∀p,PseudoMetricSpace (X p)]
    [∀p,PseudoMetricSpace (Y p)]
    (h : I → I) (R : ∀p,X p→X (h p)) (P : ∀p,X p→Y p)
    (y₀ : ∀p,Y p) (q c L : NNReal) (M : ℝ)
    (hq : (q:ℝ)<1) (hqc : (q:ℝ)*c<1)
    (hR : ∀p,LipschitzWith c (R p))
    (hP : ∀p x,dist (P p x) (y₀ p)≤M)
    (hstep : ∀p x y,dist (P p x) (P p y) ≤
      (q:ℝ)*dist (P (h p) (R p x)) (P (h p) (R p y)) + (L:ℝ)*dist x y) :
    ∀p x y,dist (P p x) (P p y) ≤ (L:ℝ)/(1-(q:ℝ)*c)*dist x y := by
  let K : ℝ := (L : ℝ) / (1 - (q : ℝ) * c)
  have hK : 0 ≤ K := div_nonneg L.2 (sub_pos.mpr hqc).le
  have hKeq : (q : ℝ) * c * K + L = K := by
    dsimp [K]
    field_simp [ne_of_gt (sub_pos.mpr hqc)]
    ring
  have hi : ∀ n : ℕ, ∀ p (x y : X p), dist (P p x) (P p y) ≤
      2 * M * (q : ℝ) ^ n + K * dist x y := by
    intro n
    induction n with
    | zero =>
      intro p x y
      have hb : dist (P p x) (P p y) ≤ 2 * M := calc
        _ ≤ dist (P p x) (y₀ p) + dist (y₀ p) (P p y) := dist_triangle _ _ _
        _ ≤ M + M := add_le_add (hP p x) (by simpa only [dist_comm] using hP p y)
        _ = _ := by ring
      simpa only [pow_zero, mul_one] using
        hb.trans (le_add_of_nonneg_right (mul_nonneg hK dist_nonneg))
    | succ n ih =>
      intro p x y
      calc
        _ ≤ (q : ℝ) * dist (P (h p) (R p x)) (P (h p) (R p y)) + (L : ℝ) * dist x y := hstep p x y
        _ ≤ (q : ℝ) * (2 * M * (q : ℝ) ^ n + K * dist (R p x) (R p y)) +
            (L : ℝ) * dist x y := add_le_add
              (mul_le_mul_of_nonneg_left (ih (h p) _ _) q.2) le_rfl
        _ ≤ (q : ℝ) * (2 * M * (q : ℝ) ^ n + K * ((c : ℝ) * dist x y)) +
            (L : ℝ) * dist x y := by
          gcongr
          exact (hR p).dist_le_mul x y
        _ = 2 * M * (q : ℝ) ^ (n+1) + ((q : ℝ) * c * K + L) * dist x y := by
          rw [pow_succ]
          ring
        _ = _ := by rw [hKeq]
  intro p x y
  have hlim : Tendsto (fun n : ℕ ↦ 2 * M * (q : ℝ)^n + K * dist x y)
      atTop (𝓝 (K * dist x y)) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one q.2 hq).const_mul (2*M)).add_const
      (K * dist x y)
  exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall (fun n ↦ hi n p x y))

/-- The same estimate on forward-invariant subsets, expressed in the original
fibre metric. Restrict both the return and section to each domain subtype and
apply the dependent-metric estimate. This is the inward-disc preparation for
the local invariant-section derivative theorem. -/
theorem parameter_graph_fibre_lipschitzOn_of_bounded_forcing
    {I : Type*} (X Y : I → Type*) [∀p,PseudoMetricSpace (X p)]
    [∀p,PseudoMetricSpace (Y p)]
    (h : I → I) (R : ∀p,X p→X (h p)) (P : ∀p,X p→Y p)
    (U : ∀p,Set (X p)) (hRU : ∀p,Set.MapsTo (R p) (U p) (U (h p)))
    (y₀ : ∀p,Y p) (q c L : NNReal) (M : ℝ)
    (hq : (q:ℝ)<1) (hqc : (q:ℝ)*c<1)
    (hR : ∀p,LipschitzOnWith c (R p) (U p))
    (hP : ∀p x,x∈U p → dist (P p x) (y₀ p)≤M)
    (hstep : ∀p x,x∈U p → ∀y,y∈U p → dist (P p x) (P p y) ≤
      (q:ℝ)*dist (P (h p) (R p x)) (P (h p) (R p y)) + (L:ℝ)*dist x y) :
    ∀p,LipschitzOnWith ⟨(L:ℝ)/(1-(q:ℝ)*c),
      div_nonneg L.2 (sub_pos.mpr hqc).le⟩ (P p) (U p) := by
  let R' : ∀p,U p → U (h p) := fun p x ↦ ⟨R p x,hRU p x.2⟩
  have hR' (p : I) : LipschitzWith c (R' p) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    exact (hR p).dist_le_mul x x.2 y y.2
  have hest := parameter_graph_fibre_bounded_forcing (fun p ↦ U p) Y h R'
    (fun p x ↦ P p x) y₀ q c L M hq hqc hR'
    (fun p x ↦ hP p x x.2) (fun p x y ↦ hstep p x x.2 y y.2)
  intro p
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  exact hest p ⟨x,hx⟩ ⟨y,hy⟩

/-- Bounded forcing followed by local affine-jet identification gives the actual
first derivative on invariant open domains. The section is assumed bounded,
not differentiable or Lipschitz. The comparison first proves its uniform
Lipschitz estimate; the independent horizontal and vertical derivative bounds
then construct and identify its bounded derivative. This is the full local
first-step mechanism in HPS pp.32–35. -/
theorem parameter_graph_bounded_invariant_section_differentiable_on
    {A : Type*} (X Y : A → Type*)
    [∀ p, NormedAddCommGroup (X p)] [∀ p, NormedSpace ℝ (X p)]
    [∀ p, NormedAddCommGroup (Y p)] [∀ p, NormedSpace ℝ (Y p)]
    [∀ p, CompleteSpace (Y p)]
    (h : A → A) (R : ∀ p, X p → X (h p))
    (F : ∀ p, X p × Y (h p) → Y p) (P : ∀ p, X p → Y p)
    (U : ∀ p, Set (X p)) (hU : ∀ p, IsOpen (U p))
    (hRU : ∀ p, Set.MapsTo (R p) (U p) (U (h p)))
    (B q c L : NNReal) (M : ℝ) (hq : (q:ℝ)<1) (hqc : (q:ℝ)*c<1)
    (hP : ∀p x,x∈U p → ‖P p x‖≤M)
    (hR : ∀ p, LipschitzOnWith c (R p) (U p))
    (hstep : ∀p x,x∈U p → ∀y,y∈U p → dist (P p x) (P p y) ≤
      (q:ℝ)*dist (P (h p) (R p x)) (P (h p) (R p y)) + (L:ℝ)*dist x y)
    (hinv : ∀ p x, x ∈ U p → P p x = F p (x,P (h p) (R p x)))
    (dR : ∀ p, X p → X p →L[ℝ] X (h p))
    (hdR : ∀ p x, x ∈ U p → HasFDerivAt (R p) (dR p x) x)
    (dF : ∀ p, X p → X p × Y (h p) →L[ℝ] Y p)
    (hdF : ∀ p x, x ∈ U p → HasFDerivAt (F p) (dF p x) (x,P (h p) (R p x)))
    (hvert : ∀ p x, x ∈ U p → ‖(dF p x).comp (ContinuousLinearMap.inr ℝ (X p) (Y (h p)))‖ ≤ q)
    (hhor : ∀ p x, x ∈ U p → ‖(dF p x).comp (ContinuousLinearMap.inl ℝ (X p) (Y (h p)))‖ ≤ B) :
    (∀ p x, x ∈ U p → DifferentiableAt ℝ (P p) x) ∧
      ∀ p x, x ∈ U p → ‖fderiv ℝ (P p) x‖ ≤ (B : ℝ)/(1-(q : ℝ)*c) := by
  let K : NNReal := ⟨(L:ℝ)/(1-(q:ℝ)*c),div_nonneg L.2 (sub_pos.mpr hqc).le⟩
  have hPL : ∀p,LipschitzOnWith K (P p) (U p) :=
    parameter_graph_fibre_lipschitzOn_of_bounded_forcing X Y h R P U hRU
      (fun _ ↦ 0) q c L M hq hqc hR
      (fun p x hx ↦ by simpa only [dist_zero_right] using hP p x hx) hstep
  exact parameter_graph_invariant_section_differentiable_on X Y h R F P U hU hRU
    K B q c hPL hR hinv dR hdR dF hdF hvert hhor hqc

end HolomorphicAnosov
