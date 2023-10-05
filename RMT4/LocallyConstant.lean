import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.LocallyConstant.Basic

open Topology Filter Metric

variable [IsROrC 𝕜] {f : 𝕜 → 𝕜} {z : 𝕜}

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

lemma eventuallyEq_of_hasDeriv (h1 : ∀ᶠ w in 𝓝 z, HasDerivAt F1 (f w) w)
    (h2 : ∀ᶠ w in 𝓝 z, HasDerivAt F2 (f w) w) : ∀ᶠ w in 𝓝 z, F2 w - F2 z = F1 w - F1 z := by
  have : ∀ᶠ w in 𝓝 z, HasDerivAt (F2 - F1) 0 w := by
    filter_upwards [h1, h2] with w h1 h2 ; simpa using h2.sub h1
  filter_upwards [isConst_nhds_of_hasDerivAt this] with w h
  simpa [sub_eq_sub_iff_sub_eq_sub] using h

lemma isLocallyConstant_of_deriv_eq_zero (hU : IsOpen U) {f : ℂ → ℂ} (h : DifferentiableOn ℂ f U)
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

lemma isLocallyConstant_of_hasDeriv (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s)
    (hf : ∀ x ∈ s, HasDerivAt f 0 x) : IsLocallyConstant (s.restrict f) := by
  apply isLocallyConstant_of_deriv_eq_zero hs
  · exact λ x hx => (hf x hx).differentiableAt.differentiableWithinAt
  · exact λ x hx => (hf x hx).deriv

lemma IsPreconnected.apply_eq_of_hasDeriv (f : ℂ → ℂ) (s : Set ℂ) (hs : IsOpen s) (hs' : IsPreconnected s)
    (hf : ∀ x ∈ s, HasDerivAt f 0 x) : ∀ x ∈ s, ∀ y ∈ s, f x = f y := by
  have l0 : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.1 hs'
  have l1 := isLocallyConstant_of_hasDeriv f s hs hf
  have l2 : IsPreconnected (Set.univ : Set s) := preconnectedSpace_iff_univ.mp l0
  intro x hx y hy
  simpa using
    l1.apply_eq_of_isPreconnected l2 (x := ⟨x, hx⟩) (y := ⟨y, hy⟩) (Set.mem_univ _) (Set.mem_univ _)
