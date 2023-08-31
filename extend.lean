import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Order.Interval
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.PathConnected
import RMT4.to_mathlib

open intervalIntegral Set

lemma toto {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) {n : ℕ} (h : ContDiffOn ℝ n f (Icc a b)) :
    ∃ g : ℝ → ℝ, (ContDiff ℝ n g) ∧ (EqOn g f (Icc a b)) := by
  induction n generalizing f
  · case zero =>
    simp only [CharP.cast_eq_zero, contDiff_zero, contDiffOn_zero] at h ⊢
    refine ⟨IccExtend hab.le (restrict (Icc a b) f), h.restrict.Icc_extend', ?_⟩
    exact λ t ht => IccExtend_of_mem _ _ ht
  · case succ n ih =>
    have h1 : ContDiffOn ℝ n (derivWithin f (Icc a b)) (Icc a b) :=
      h.derivWithin (uniqueDiffOn_Icc hab) le_rfl
    obtain ⟨gg, h2, h3⟩ := ih h1
    refine ⟨λ t => f a + ∫ u in a..t, gg u, ?_, ?_⟩
    · rw [contDiff_succ_iff_deriv]
      constructor
      · refine differentiableOn_univ.1 ((differentiableOn_integral_of_continuous ?_ h2.continuous).const_add _)
        simp [h2.continuous.intervalIntegrable]
      · convert h2
        ext t
        simp [deriv_const_add, h2.continuous.deriv_integral]
    · intro t ht
      dsimp
      have l6 : Icc a t ⊆ Icc a b := Icc_subset_Icc_right ht.2
      have l9 : EqOn gg (derivWithin f (Icc a b)) (uIcc a t) := h3.mono (by simp [uIcc, ht.1, l6])
      have l10 := integral_eq_sub_of_contDiffOn'' hab.le ht h.one_of_succ
      simp [integral_congr l9, l10]

lemma toto' {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (h : ContDiffOn ℝ n f (uIcc a b)) :
    ∃ g : ℝ → ℝ, (ContDiff ℝ n g) ∧ (EqOn g f (uIcc a b)) := by
  cases eq_or_ne a b
  · case inl hab => exact ⟨λ _ => f a, by simp [hab, contDiff_const]⟩
  · case inr hab => exact toto (min_lt_max.2 hab) h
