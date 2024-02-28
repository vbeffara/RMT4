import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic

open Topology Filter Metric

variable {𝕜 : Type*} [IsROrC 𝕜] {f f₁ f₂ F1 F2 : 𝕜 → 𝕜} {z z₀ : 𝕜} {s : Set 𝕜} {U : Set 𝕜}

lemma isConst_nhds_of_hasDerivAt (h : ∀ᶠ w in 𝓝 z, HasDerivAt f 0 w) : ∀ᶠ w in 𝓝 z, f w = f z := by
  obtain ⟨r, hr, hf⟩ := eventually_nhds_iff_ball.1 h
  refine eventually_nhds_iff_ball.2 ⟨r, hr, λ w hw => ?_⟩
  have l1 : DifferentiableOn 𝕜 f (ball z r) :=
    λ w hw => (hf w hw).differentiableAt.differentiableWithinAt
  have l2 (w) (hw : w ∈ ball z r) : fderivWithin 𝕜 f (ball z r) w = 0 := by
    have l3 : UniqueDiffWithinAt 𝕜 (ball z r) w := isOpen_ball.uniqueDiffWithinAt hw
    have l4 := (hf w hw).hasFDerivAt.hasFDerivWithinAt.fderivWithin l3
    rw [l4] ; ext1 ; simp
  exact (convex_ball z r).is_const_of_fderivWithin_eq_zero l1 l2 hw (mem_ball_self hr)

lemma eventuallyEq_of_hasDeriv' (h1 : ∀ᶠ w in 𝓝 z, HasDerivAt F1 (f w) w)
    (h2 : ∀ᶠ w in 𝓝 z, HasDerivAt F2 (f w) w) : ∀ᶠ w in 𝓝 z, F2 w - F2 z = F1 w - F1 z := by
  have : ∀ᶠ w in 𝓝 z, HasDerivAt (F2 - F1) 0 w := by
    filter_upwards [h1, h2] with w h1 h2 ; simpa using h2.sub h1
  filter_upwards [isConst_nhds_of_hasDerivAt this] with w h
  simpa [sub_eq_sub_iff_sub_eq_sub] using h

lemma eventuallyEq_of_hasDeriv (h1 : ∀ᶠ w in 𝓝 z, HasDerivAt F1 (f w) w)
    (h2 : ∀ᶠ w in 𝓝 z, HasDerivAt F2 (f w) w) (h3 : F1 z = F2 z) : ∀ᶠ w in 𝓝 z, F2 w = F1 w := by
  filter_upwards [eventuallyEq_of_hasDeriv' h1 h2] with a ha
  simpa [h3, sub_left_inj] using ha

lemma isLocallyConstant_of_deriv_eq_zero (hU : IsOpen U) (h : DifferentiableOn 𝕜 f U)
    (hf : U.EqOn (deriv f) 0) :
    IsLocallyConstant (U.restrict f) := by
  refine (IsLocallyConstant.iff_exists_open _).2 (λ ⟨z, hz⟩ => ?_)
  obtain ⟨ε, L1, L2⟩ := isOpen_iff.1 hU z hz
  refine ⟨ball ⟨z, hz⟩ ε, isOpen_ball, mem_ball_self L1, λ ⟨z', _⟩ hz' => ?_⟩
  refine (convex_ball z ε).is_const_of_fderivWithin_eq_zero (h.mono L2) ?_ hz' (mem_ball_self L1)
  intro x hx
  rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hx)]
  · exact ContinuousLinearMap.ext_ring (hf (L2 hx))
  · exact h.differentiableAt (hU.mem_nhds (L2 hx))

lemma isLocallyConstant_of_hasDeriv (hs : IsOpen s) (hf : ∀ x ∈ s, HasDerivAt f 0 x) :
    IsLocallyConstant (s.restrict f) := by
  apply isLocallyConstant_of_deriv_eq_zero hs
  · exact λ x hx => (hf x hx).differentiableAt.differentiableWithinAt
  · exact λ x hx => (hf x hx).deriv

lemma IsPreconnected.apply_eq_of_hasDeriv_zero (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : ∀ x ∈ s, HasDerivAt f 0 x) : ∀ x ∈ s, ∀ y ∈ s, f x = f y := by
  have l0 : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.1 hs'
  have l1 := isLocallyConstant_of_hasDeriv hs hf
  have l2 : IsPreconnected (Set.univ : Set s) := preconnectedSpace_iff_univ.mp l0
  intro x hx y hy
  simpa using
    l1.apply_eq_of_isPreconnected l2 (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (Set.mem_univ _) (Set.mem_univ _)

lemma IsPreconnected.apply_eq_of_hasDeriv_eq (hs' : IsPreconnected s) (hs : IsOpen s) (hz₀ : z₀ ∈ s)
    (hf₁ : ∀ x ∈ s, HasDerivAt f₁ (f x) x) (hf₂ : ∀ x ∈ s, HasDerivAt f₂ (f x) x)
    (h : f₁ z₀ = f₂ z₀) : Set.EqOn f₁ f₂ s := by
  have l1 (x) (hx : x ∈ s) : HasDerivAt (f₁ - f₂) 0 x := by simpa using (hf₁ x hx).sub (hf₂ x hx)
  intro x hx
  simpa [h, sub_eq_zero] using hs'.apply_eq_of_hasDeriv_zero hs l1 x hx z₀ hz₀
