import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Connected

namespace HolomorphicAnosov
open Set Metric

/-- The punctured complex disk is preconnected; this is the domain for rescaled
omitted-value families.  The proof transports the complement of one point in the
real two-dimensional complex vector space through the standard ball homeomorph. -/
theorem punctured_ball_preconnected_g9 (r : ℝ) (hr : 0 < r) :
    IsPreconnected (ball (0 : ℂ) r \ {0}) := by
  let e : OpenPartialHomeomorph ℂ ℂ := OpenPartialHomeomorph.univBall 0 r
  have heS : e.source = (univ : Set ℂ) := OpenPartialHomeomorph.univBall_source 0 r
  have heT : e.target = ball 0 r := OpenPartialHomeomorph.univBall_target 0 hr
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank]
    rw [Module.finrank_eq_card_basis Complex.basisOneI]
    norm_num
  let q : ℂ := e.symm 0
  have hconn : IsConnected ({q}ᶜ : Set ℂ) :=
    isConnected_compl_singleton_of_one_lt_rank hrank q
  have hzeroT : (0 : ℂ) ∈ e.target := by
    rw [heT]
    exact mem_ball.mpr (by simp [hr])
  have heq : e (e.symm 0) = 0 := e.right_inv hzeroT
  have himage : e '' ({q}ᶜ : Set ℂ) = ball (0 : ℂ) r \ {0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨heT ▸ e.map_source (heS ▸ mem_univ x), ?_⟩
      intro hzero
      have hz : e x = 0 := by simpa using hzero
      have hx0 : x = q := e.injOn (heS ▸ mem_univ x)
          (heS ▸ mem_univ q) (hz.trans heq.symm)
      exact hx hx0
    · rintro ⟨hy, hy0⟩
      refine ⟨e.symm y, ?_, e.right_inv (heT ▸ hy)⟩
      intro hq
      apply hy0
      have hq' : e.symm y = q := by simpa using hq
      have : y = 0 := by
        calc
          y = e (e.symm y) := (e.right_inv (heT ▸ hy)).symm
          _ = e q := congrArg e hq'
          _ = 0 := by simpa [q] using heq
      simpa using this
  rw [← himage]
  exact hconn.isPreconnected.image e (e.continuousOn.mono (fun x hx => heS ▸ mem_univ x))

end HolomorphicAnosov
