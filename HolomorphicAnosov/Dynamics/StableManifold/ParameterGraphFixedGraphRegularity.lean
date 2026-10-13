import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageC1
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageC1
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageSlopeRegularityData
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphImageSlopeRegularityData
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphC1
import HolomorphicAnosov.Dynamics.StableManifold.FiniteRankSplitBundleFibreRegularity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphFixedGraphDifferentiability
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphTaylorJetTransport
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphSlopeTransform
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphUnitSectionFixedPoint
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointC1Criterion
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphWeightedLimitContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphParameterInverseContinuity
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphJointDerivativeEvaluation
import HolomorphicAnosov.Dynamics.StableManifold.ParameterGraphPreimageHigherRegularity

noncomputable section
namespace HolomorphicAnosov

/-- Fixed graph transforms preserve the marked origin.  This is the explicit
normalization clause used before the higher regularity argument in HPS Theorem 5.5. -/
theorem parameter_graph_fixed_origin
    {A : Type*} [TopologicalSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedAddCommGroup (E₂ p)]
    (s : ∀ p, E₁ p → E₂ p) (t : ∀ p, E₂ p → E₁ p)
    (hs : ∀ p, s p 0 = 0 ∧ LipschitzWith 1 (s p))
    (ht : ∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p)) :
    (∀ p, s p 0 = 0) ∧ (∀ p, t p 0 = 0) := by
  exact ⟨fun p ↦ (hs p).1, fun p ↦ (ht p).1⟩

/-- HPS Theorem 5.5, pp.33–35 and 54–62: regularity of the actual
parameter graph fixed points under the original norm contraction bounds.

STATEMENT-DISPUTED (original statement, now corrected): identity dynamics on
ℝ×ℝ preserves the centred unit-Lipschitz graph |x|, so graph invariance alone
does not imply differentiability. The repaired statement includes the omitted
quantitative horizontal/vertical gap and small nonlinear remainder, compactness
of the parameter base, continuous graph evaluation, and the appropriate strong
return contraction. The sole caller supplies every added premise from its
original threshold and carrier construction; its theorem statement is unchanged.

Proof. Apply the continuous invariant-slope construction in both branches. The
slope Picard iterates have original operator error bounded by q^n, and their
continuous evaluations converge with weight ‖v‖. Taylor-defect transport
identifies the limit as the actual derivative, proving joint C¹. In the strong
branch the spatial return contracts. On finite local chart discs, differentiate
the invariant slope equation repeatedly: its top-order homogeneous part has
bound q c^m<1 and lower derivatives form continuous bounded forcing. The affine
section contraction constructs each next jet; difference quotients satisfy the
same contraction modulo a little-o remainder, so the jet is the actual next
derivative. Compact base and finite-dimensional closed discs supply uniform
bounds for the lower-order forcing locally. Iterate through r, using the actual
linear chart chain rules for parameter continuity, and propagate the germ to
all fibre points along finite contracting-return histories. No inverse of the
vertical block is used. -/
theorem parameter_graph_fixed_graph_regularity
    {A : Type*} [TopologicalSpace A] [CompactSpace A]
    {E₁ E₂ : A → Type*}
    [∀ p, NormedAddCommGroup (E₁ p)] [∀ p, NormedSpace ℝ (E₁ p)]
    [∀ p, NormedAddCommGroup (E₂ p)] [∀ p, NormedSpace ℝ (E₂ p)]
    [TopologicalSpace (Sigma E₁)] [TopologicalSpace (Sigma E₂)]
    [TopologicalSpace (Sigma (fun p ↦ E₁ p × E₂ p))]
    (r : ℕ) (hr : 1 ≤ r) (ρ : ℝ)
    (e : SplitFiniteRankNormedAtlas (E₁ := E₁) (E₂ := E₂)) (h : A ≃ₜ A)
    (T₁ : ∀ p, E₁ p ≃L[ℝ] E₁ (h p))
    (T₂ : ∀ p, E₂ p →L[ℝ] E₂ (h p))
    (G : ∀ p, E₁ p × E₂ p → E₁ (h p) × E₂ (h p))
    (hG : JointFiberContDiff e.total e.total h r G)
    (hzero : ∀ p, G p 0 = 0)
    (_hderiv : ∀ p, fderiv ℝ (G p) 0 =
      (T₁ p).toContinuousLinearMap.prodMap (T₂ p))
    (a k ε : NNReal)
    (ha : ∀p,‖(T₁ p).symm.toContinuousLinearMap‖≤a) (hk : ∀p,‖T₂ p‖≤k)
    (hsmall : 2*(a:ℝ)*ε<1)
    (hjet : (a:ℝ)*(k+2*ε)/(1-2*(a:ℝ)*ε)<1)
    (hslope : (a:ℝ)*(k+2*ε)≤1)
    (hinverse : ((k:ℝ)+2*ε)*((a:ℝ)/(1-(a:ℝ)*ε))<1)
    (hstrongImage : 1≤ρ → (a:ℝ)/(1-(a:ℝ)*ε)<1)
    (hstrongPreimage : ρ≤1 → (k:ℝ)+ε<1)
    (hR : ∀p,LipschitzWith ε (fun z ↦ G p z-(T₁ p z.1,T₂ p z.2)))
    (s : ∀ p, E₁ p → E₂ p) (t : ∀ p, E₂ p → E₁ p)
    (hs : ∀ p, s p 0 = 0 ∧ LipschitzWith 1 (s p))
    (ht : ∀ p, t p 0 = 0 ∧ LipschitzWith 1 (t p))
    (hsc : Continuous (fun z : Sigma E₁ ↦ (⟨z.1,s z.1 z.2⟩ : Sigma E₂)))
    (htc : Continuous (fun z : Sigma E₂ ↦ (⟨z.1,t z.1 z.2⟩ : Sigma E₁)))
    (hsgraph : ∀ p, G p '' Set.range (fun x ↦ (x, s p x)) =
      Set.range (fun x ↦ (x, s (h p) x)))
    (htgraph : ∀ p, G p ⁻¹' Set.range (fun y ↦ (t (h p) y, y)) =
      Set.range (fun y ↦ (t p y, y))) :
    JointFiberContDiff e.first e.second id 1 s ∧
    JointFiberContDiff e.second e.first id 1 t ∧
    (1 ≤ ρ → JointFiberContDiff e.first e.second id r s) ∧
    (ρ ≤ 1 → JointFiberContDiff e.second e.first id r t) := by
  have hC1 := parameter_graph_fixed_graph_c1 e r hr h T₁ T₂ G hG hzero
    a k ε ha hk hsmall hjet hslope hinverse hR s t hs ht hsc htc hsgraph htgraph
  let : ∀p,CompleteSpace (E₁ p) := fun p ↦ parameter_graph_fibre_complete e.first p
  let : ∀p,CompleteSpace (E₂ p) := fun p ↦ parameter_graph_fibre_complete e.second p
  have hpreimage : ∀p y,(G p (t p y,y)).1=t (h p) (G p (t p y,y)).2 := by
    intro p y
    have hm : (t p y,y)∈G p ⁻¹' Set.range (fun y ↦ (t (h p) y,y)) := by
      rw [htgraph]
      exact ⟨y,rfl⟩
    obtain ⟨v,hv⟩ := hm
    simp only [← hv]
  have hGle (m:ℕ) (hm:m≤r) : JointFiberContDiff e.total e.total h m G :=
    ⟨fun p ↦ (hG.1 p).of_le (by exact_mod_cast hm),
      fun i j k hk ↦ hG.2 i j k (hk.trans hm)⟩
  refine ⟨hC1.1,hC1.2,?_,?_⟩
  · intro hρ
    have hstep : ∀m,1≤m → m≤r → JointFiberContDiff e.first e.second id m s := by
      intro m hm
      induction m,hm using Nat.le_induction with
      | base => exact fun _ ↦ hC1.1
      | succ n hn ih =>
          intro hnr
          exact ParameterGraphImageSlopeData.regularity_step e h G s n hn (hGle (n+1) hnr)
            (ih (Nat.le_trans (Nat.le_succ n) hnr)) hzero hs hsgraph T₁ T₂ a k ε ha hk
            hsmall hslope hjet (hstrongImage hρ) hR
    exact hstep r hr (le_refl r)
  · intro hρ
    have hstep : ∀m,1≤m → m≤r → JointFiberContDiff e.second e.first id m t := by
      intro m hm
      induction m,hm using Nat.le_induction with
      | base => exact fun _ ↦ hC1.2
      | succ n hn ih =>
          intro hnr
          exact parameter_graph_preimage_regularity_step e h h.continuous T₁ T₂ G t n hn
            (hGle (n+1) hnr) (ih (Nat.le_trans (Nat.le_succ n) hnr)) hzero
            (fun p ↦ (ht p).1) (fun p ↦ (ht p).2) hpreimage a k ε ha hk hsmall hjet
            (hstrongPreimage hρ) hR
    exact hstep r hr (le_refl r)

end HolomorphicAnosov
