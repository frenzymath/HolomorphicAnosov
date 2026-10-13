import HolomorphicAnosov.Dynamics.Bowen.BowenBasicSetMarkovCoding

namespace HolomorphicAnosov

open Set

/-- The parent ambient-open formulation is actual subspace transitivity of the
same restricted original homeomorphism. Source: Bowen coding p.725 (restriction
to the basic set); lift each subspace-open set to an ambient-open set, apply the
original transitivity hypothesis, and use the literal restriction iterate formula. -/
theorem restricted_transitivity_of_ambient
    {X : Type*} [TopologicalSpace X] (F : X ≃ₜ X) (K : Set X)
    (hK : ∀ x : X, x ∈ K ↔ F x ∈ K)
    (htrans : ∀ P Q : Set X, IsOpen P → IsOpen Q →
      (K ∩ P).Nonempty → (K ∩ Q).Nonempty →
      ∃ n : ℕ, ∃ x ∈ K ∩ P, (F : X → X)^[n] x ∈ Q) :
    let FK := BowenBasicSetCoding.restrictedDynamics F K hK
    ∀ U V : Set K, IsOpen U → U.Nonempty → IsOpen V → V.Nonempty →
      ∃ n : ℕ, (((FK ^ n : K ≃ₜ K) : K → K) '' U ∩ V).Nonempty := by
  dsimp only
  let FK := BowenBasicSetCoding.restrictedDynamics F K hK
  have hpow : ∀ n : ℕ, ∀ y : K, ((FK ^ n) y).val = (F : X → X)^[n] y.val := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih =>
      intro y
      rw [pow_succ, Homeomorph.mul_apply, ih, Function.iterate_succ_apply]
      rfl
  intro U V hU hUne hV hVne
  obtain ⟨P, hP, hUP⟩ := hU.image_val
  obtain ⟨Q, hQ, hVQ⟩ := hV.image_val
  have hKP : (K ∩ P).Nonempty := by
    obtain ⟨u, hu⟩ := hUne
    have huP : u.val ∈ P ∩ K := by rw [← hUP]; exact ⟨u, hu, rfl⟩
    exact ⟨u.val, huP.2, huP.1⟩
  have hKQ : (K ∩ Q).Nonempty := by
    obtain ⟨v, hv⟩ := hVne
    have hvQ : v.val ∈ Q ∩ K := by rw [← hVQ]; exact ⟨v, hv, rfl⟩
    exact ⟨v.val, hvQ.2, hvQ.1⟩
  obtain ⟨n, x, ⟨hxK, hxP⟩, hfxQ⟩ := htrans P Q hP hQ hKP hKQ
  let xK : K := ⟨x, hxK⟩
  have hxU : xK ∈ U := by
    have hximage : x ∈ Subtype.val '' U := by rw [hUP]; exact ⟨hxP, hxK⟩
    obtain ⟨u, hu, hux⟩ := hximage
    have hueq : u = xK := Subtype.ext hux
    exact hueq ▸ hu
  refine ⟨n, (FK ^ n) xK, ⟨xK, hxU, rfl⟩, ?_⟩
  have hfximage : ((FK ^ n) xK).val ∈ Subtype.val '' V := by
    rw [hVQ]
    exact ⟨by simpa only [hpow] using hfxQ, ((FK ^ n) xK).property⟩
  obtain ⟨v, hv, hvx⟩ := hfximage
  have hveq : v = (FK ^ n) xK := Subtype.ext hvx
  exact hveq ▸ hv

end HolomorphicAnosov
