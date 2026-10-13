import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Tendsto

/-! # Telescoping a finite strip of germ squares  Nisoli, Theorem 1.3.8, printed pp.24–25: the successive local square identities intertwine the two row words, leaving just the two endpoint transverse maps.    The spaces at successive vertices may be different intrinsic leaf carriers. -/

namespace HolomorphicAnosov
open Filter
open scoped Topology _root_.Topology
universe u v

/-- The chronological finite word of maps between successive carriers. (Nisoli) -/
def transportWord (X : ℕ → Type u) (edge : ∀ n, X n → X (n + 1)) :
    ∀ n, X 0 → X n
  | 0 => id
  | n + 1 => edge n ∘ transportWord X edge n

/-- Local square identities telescope across a finite strip of varying carriers. (Nisoli, Theorem 1.3.8) -/
theorem germ_transport_strip
    (X : ℕ → Type u) (Y : ℕ → Type v) [∀ n, TopologicalSpace (X n)]
    (x : ∀ n, X n)
    (bottom : ∀ n, X n → X (n + 1)) (top : ∀ n, Y n → Y (n + 1))
    (vertical : ∀ n, X n → Y n)
    (hbottom : ∀ n, Tendsto (bottom n) (𝓝 (x n)) (𝓝 (x (n + 1))))
    (hsquare : ∀ n, (fun z ↦ vertical (n + 1) (bottom n z)) =ᶠ[𝓝 (x n)]
      (fun z ↦ top n (vertical n z))) :
    ∀ n, (fun z ↦ vertical n (transportWord X bottom n z)) =ᶠ[𝓝 (x 0)]
      (fun z ↦ transportWord Y top n (vertical 0 z)) := by
  have hprefix : ∀ n, Tendsto (transportWord X bottom n) (𝓝 (x 0)) (𝓝 (x n)) := by
    intro n
    induction n with
    | zero => exact tendsto_id
    | succ n ih => exact (hbottom n).comp ih
  intro n
  induction n with
  | zero => exact Eventually.of_forall (fun _ ↦ rfl)
  | succ n ih =>
    filter_upwards [(hprefix n).eventually (hsquare n), ih] with z hz he
    change vertical (n + 1) (bottom n (transportWord X bottom n z)) =
      top n (transportWord Y top n (vertical 0 z))
    exact hz.trans (congrArg (top n) he)

end HolomorphicAnosov
