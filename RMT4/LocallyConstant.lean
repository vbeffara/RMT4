import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue

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
