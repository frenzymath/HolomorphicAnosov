import HolomorphicAnosov.Analysis.Regularity.JourneLeafZeroSampleRemainder
import HolomorphicAnosov.Analysis.Regularity.JourneBlockMonomialSpace
import HolomorphicAnosov.Analysis.Regularity.JourneSmallSlopeIntersection

noncomputable section
namespace HolomorphicAnosov.JourneLeafPolynomialApproximation
open Set

/-- A residual vanishing on a crossed leaf grid is controlled at any point
whose second-family leaf meets all sampled first-family leaves in the common
scale domain. Apply the leaf Taylor/interpolation estimate to each sampled
first-family leaf. These estimates bound the samples on the second-family
leaf; a second application bounds the target. Thus one obtains a whole-region
residual bound, rather than estimates only at the next interpolation grid. -/
theorem crossed_grid_remainder
    {X ι κ : Type*} {p q n : ℕ} (hn : 1 ≤ n)
    {S₁ : Set (Block p)} {S₂ : Set (Block q)}
    (hS₁ : IsOpen S₁) (hc₁ : Convex ℝ S₁) (h0₁ : (0:Block p) ∈ S₁)
    (hS₂ : IsOpen S₂) (hc₂ : Convex ℝ S₂) (h0₂ : (0:Block q) ∈ S₂)
    {α K R L : ℝ} (hα : 0 ≤ α) (hK : 0 ≤ K) (hR : 0 ≤ R) (hL : 0 ≤ L)
    (f : X → ℝ) (Q : ι → Block p → X) (V : Block q → X)
    (a : ι → κ → Block p) (u : ι → Block p) (b : ι → Block q) (y : Block q)
    (hQ : ∀ i, ContDiffOn ℝ n (f ∘ Q i) S₁)
    (hQH : ∀ i, ∀ x ∈ S₁, ∀ y ∈ S₁,
      ‖iteratedFDeriv ℝ n (f ∘ Q i) x-iteratedFDeriv ℝ n (f ∘ Q i) y‖ ≤ K*‖x-y‖^α)
    (hV : ContDiffOn ℝ n (f ∘ V) S₂)
    (hVH : ∀ x ∈ S₂, ∀ y ∈ S₂,
      ‖iteratedFDeriv ℝ n (f ∘ V) x-iteratedFDeriv ℝ n (f ∘ V) y‖ ≤ K*‖x-y‖^α)
    (ha : ∀ i k, a i k ∈ S₁) (haR : ∀ i k, ‖a i k‖ ≤ R)
    (hu : ∀ i, u i ∈ S₁) (huR : ∀ i, ‖u i‖ ≤ R)
    (hb : ∀ i, b i ∈ S₂) (hbR : ∀ i, ‖b i‖ ≤ R)
    (hy : y ∈ S₂) (hyR : ‖y‖ ≤ R)
    (hzero : ∀ i k, f (Q i (a i k)) = 0)
    (hcross : ∀ i, V (b i) = Q i (u i))
    (hinterp₁ : ∀ i (P : MvPolynomial (Fin p) ℝ), P.totalDegree ≤ n →
      ∀ M : ℝ, 0 ≤ M → (∀ k, |MvPolynomial.eval (fun j ↦ a i k j) P| ≤ M) →
        |MvPolynomial.eval (fun j ↦ u i j) P| ≤ L*M)
    (hinterp₂ : ∀ P : MvPolynomial (Fin q) ℝ, P.totalDegree ≤ n →
      ∀ M : ℝ, 0 ≤ M → (∀ i, |MvPolynomial.eval (fun j ↦ b i j) P| ≤ M) →
        |MvPolynomial.eval (fun j ↦ y j) P| ≤ L*M) :
    |f (V y)| ≤ (L+1)^2*K*R^((n:ℝ)+α) := by
  have hfirst (i : ι) : |f (V (b i))| ≤ (L+1)*K*R^((n:ℝ)+α) := by
    rw [hcross i]
    have H := leaf_sample_remainder hn hS₁ hc₁ h0₁ hα hK (f ∘ Q i) (hQ i) (hQH i)
      (a i) (u i) R L hR hL (ha i) (hu i) (haR i) (huR i) 0 le_rfl
      (fun k ↦ by simp [hzero]) (hinterp₁ i)
    simpa only [Function.comp_apply,mul_zero,zero_add] using H
  have H := leaf_sample_remainder hn hS₂ hc₂ h0₂ hα hK (f ∘ V) hV hVH
    b y R L hR hL hb hy hbR hyR ((L+1)*K*R^((n:ℝ)+α)) (by positivity)
    hfirst hinterp₂
  calc
    |f (V y)| ≤ L*((L+1)*K*R^((n:ℝ)+α))+(L+1)*K*R^((n:ℝ)+α) := H
    _ = _ := by ring

/-- Stable block sampling and actual small-slope graph intersections provide
a crossed grid controlling the residual throughout the inner product ball.
The constants depend only on the normalized sample grids and the radius.
The target may lie on any second-family graph satisfying the same slope and
leaf-regularity bounds; it need not lie on one of the sampled graphs. -/
theorem small_slope_grid_remainder
    {I J : Type*} [Fintype I] [Fintype J] {p q n : ℕ} (hn : 1 ≤ n)
    (a : I → Block p) (b : J → Block q)
    (E₁ : (BlockDegreeIndex p n → ℝ) ≃L[ℝ] (I → ℝ))
    (E₂ : (BlockDegreeIndex q n → ℝ) ≃L[ℝ] (J → ℝ))
    (hE₁ : ∀ c k, E₁ c k = ∑ i, c i * MvPolynomial.eval (fun j ↦ a k j)
      (MvPolynomial.monomial i.val (1:ℝ)))
    (hE₂ : ∀ c k, E₂ c k = ∑ i, c i * MvPolynomial.eval (fun j ↦ b k j)
      (MvPolynomial.monomial i.val (1:ℝ)))
    (R : ℝ) (hR : 0 < R) (ha : ∀ i, ‖a i‖ ≤ R/2) (hb : ∀ j, ‖b j‖ ≤ R/2) :
    ∃ ε L : ℝ, 0 < ε ∧ ε ≤ 1/4 ∧ 0 ≤ L ∧
      ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ ε → ∀ (φ : J → Block p → Block q) (ψ : I → Block q → Block p),
      (∀ j, φ j 0 = 0) → (∀ i, ψ i 0 = 0) →
      (∀ j, ∀ u ∈ Metric.closedBall (0:Block p) R, ∀ v ∈ Metric.closedBall 0 R,
        ‖φ j u-φ j v‖ ≤ ε'*‖u-v‖) →
      (∀ i, ∀ u ∈ Metric.closedBall (0:Block q) R, ∀ v ∈ Metric.closedBall 0 R,
        ‖ψ i u-ψ i v‖ ≤ ε'*‖u-v‖) →
      ∃ z : I × J → Block p × Block q,
        (∀ i j, (z (i,j)).1 = a i+ψ i (z (i,j)).2 ∧
          (z (i,j)).2 = b j+φ j (z (i,j)).1) ∧
        ‖z-(fun ij ↦ (a ij.1,b ij.2))‖ ≤ ε'*R ∧
        ∀ (f : Block p × Block q → ℝ) (α K : ℝ), 0 ≤ α → 0 ≤ K →
        (∀ i j, f (z (i,j)) = 0) →
        (∀ j, ContDiffOn ℝ n (fun u ↦ f (u,b j+φ j u)) (Metric.ball 0 (2*R))) →
        (∀ j, ∀ u ∈ Metric.ball (0:Block p) (2*R), ∀ v ∈ Metric.ball 0 (2*R),
          ‖iteratedFDeriv ℝ n (fun u ↦ f (u,b j+φ j u)) u-
            iteratedFDeriv ℝ n (fun u ↦ f (u,b j+φ j u)) v‖ ≤ K*‖u-v‖^α) →
        ∀ w : Block p × Block q, ‖w‖ ≤ R/4 →
        ∀ Ψ : Block q → Block p, Ψ 0 = 0 →
        (∀ u ∈ Metric.closedBall (0:Block q) R, ∀ v ∈ Metric.closedBall 0 R,
          ‖Ψ u-Ψ v‖ ≤ ε'*‖u-v‖) →
        let V := fun v ↦ (w.1-Ψ w.2+Ψ v,v)
        ContDiffOn ℝ n (f ∘ V) (Metric.ball 0 (2*R)) →
        (∀ u ∈ Metric.ball (0:Block q) (2*R), ∀ v ∈ Metric.ball 0 (2*R),
          ‖iteratedFDeriv ℝ n (f ∘ V) u-iteratedFDeriv ℝ n (f ∘ V) v‖ ≤ K*‖u-v‖^α) →
        |f w| ≤ (L+1)^2*K*R^((n:ℝ)+α) := by
  classical
  obtain ⟨δ₁,L₁,hδ₁,hL₁,H₁⟩ := block_polynomial_sampling_bound a E₁ hE₁ R
  obtain ⟨δ₂,L₂,hδ₂,hL₂,H₂⟩ := block_polynomial_sampling_bound b E₂ hE₂ R
  let ε := min (1/4) (min (δ₁/(2*R)) (δ₂/(2*R)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεq : ε ≤ 1/4 := min_le_left _ _
  have hδ₁' : ε*R < δ₁ := by
    have H := (le_div_iff₀ (by positivity : 0 < 2*R)).mp
      ((min_le_right (1/4:ℝ) _).trans (min_le_left (δ₁/(2*R)) (δ₂/(2*R))))
    change ε*(2*R) ≤ δ₁ at H
    nlinarith
  have hδ₂' : ε*R < δ₂ := by
    have H := (le_div_iff₀ (by positivity : 0 < 2*R)).mp
      ((min_le_right (1/4:ℝ) _).trans (min_le_right (δ₁/(2*R)) (δ₂/(2*R))))
    change ε*(2*R) ≤ δ₂ at H
    nlinarith
  let L := max L₁ L₂
  have hL : 0 ≤ L := hL₁.trans (le_max_left _ _)
  refine ⟨ε,L,hε,hεq,hL,?_⟩
  intro ε' hε' hε'le φ ψ hφ0 hψ0 hφ hψ
  have hε'q : ε' ≤ 1/4 := hε'le.trans hεq
  have hδ₁small : ε'*R < δ₁ := (mul_le_mul_of_nonneg_right hε'le hR.le).trans_lt hδ₁'
  have hδ₂small : ε'*R < δ₂ := (mul_le_mul_of_nonneg_right hε'le hR.le).trans_lt hδ₂'
  obtain ⟨z,hz,hd,hrow,hcol⟩ := small_slope_crossed_grid φ ψ a b R ε' hR hε' hε'q
    ha hb hφ0 hψ0 hφ hψ
  refine ⟨z,fun i j ↦ ⟨(hz i j).2.2.1,(hz i j).2.2.2⟩,hd,?_⟩
  intro f α K hα hK hzero hQ hQH w hw Ψ hΨ0 hΨ V₀ hV hVH
  obtain ⟨a',ha',hw',v,hv,hvb⟩ := small_slope_target_crossings φ Ψ b w R ε' hR hε' hε'q
    hb hw hφ0 hΨ0 hφ hΨ
  have ha'eq : a' = w.1-Ψ w.2 := by rw [hw']; abel
  let Q := fun j (u : Block p) ↦ (u,b j+φ j u)
  let V := fun u : Block q ↦ (w.1-Ψ w.2+Ψ u,u)
  have hmem₁ {u : Block p} (hu : ‖u‖ ≤ R) : u ∈ Metric.ball 0 (2*R) := by
    simp only [Metric.mem_ball,dist_zero_right]; linarith
  have hmem₂ {u : Block q} (hu : ‖u‖ ≤ R) : u ∈ Metric.ball 0 (2*R) := by
    simp only [Metric.mem_ball,dist_zero_right]; linarith
  have hw₂ : ‖w.2‖ ≤ R := by have := (le_max_right _ _).trans hw; linarith
  have H := crossed_grid_remainder hn Metric.isOpen_ball (convex_ball _ _)
    (Metric.mem_ball_self (by positivity : 0 < 2*R))
    Metric.isOpen_ball (convex_ball _ _) (Metric.mem_ball_self (by positivity : 0 < 2*R))
    hα hK hR.le hL f Q V (fun j i ↦ (z (i,j)).1)
    (fun j ↦ (v j).1) (fun j ↦ (v j).2) w.2 hQ hQH hV hVH
    (fun j i ↦ hmem₁ (hz i j).1) (fun j i ↦ (hz i j).1)
    (fun j ↦ hmem₁ (hv j).1) (fun j ↦ (hv j).1)
    (fun j ↦ hmem₂ (hv j).2.1) (fun j ↦ (hv j).2.1)
    (hmem₂ hw₂) hw₂
    (fun j i ↦ by
      have heq : Q j (z (i,j)).1 = z (i,j) := Prod.ext rfl (hz i j).2.2.2.symm
      rw [heq]; exact hzero i j)
    (fun j ↦ by
      apply Prod.ext
      · exact ((hv j).2.2.1.trans (by rw [ha'eq])).symm
      · exact (hv j).2.2.2)
    (fun j P hP M hM hs ↦ by
      have H := H₁ (fun i ↦ (z (i,j)).1) ((hrow j).trans_lt hδ₁small) 1 P hP M hM
        (by simpa only [one_smul] using hs) (v j).1 (hv j).1
      simp only [one_smul] at H
      exact H.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hM))
    (fun P hP M hM hs ↦ by
      have H := H₂ (fun j ↦ (v j).2) (hvb.trans_lt hδ₂small) 1 P hP M hM
        (by simpa only [one_smul] using hs) w.2 hw₂
      simp only [one_smul] at H
      exact H.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hM))
  have hVw : V w.2 = w := by
    apply Prod.ext
    · dsimp [V]; abel
    · rfl
  rw [hVw] at H
  exact H

end HolomorphicAnosov.JourneLeafPolynomialApproximation
