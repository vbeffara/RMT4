import Mathlib.Tactic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Convex.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Order.Interval
import RMT4.to_mathlib

open Set BigOperators Metric Filter MeasureTheory intervalIntegral

variable {f : ℂ → ℂ} {z₀ z w : ℂ} {ε δ t a b : ℝ} {K U : Set ℂ}

lemma mem_segment (ht : t ∈ Icc (0 : ℝ) 1) : (1 - t) • z₀ + t • z ∈ segment ℝ z₀ z :=
  ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩

lemma continuous_bary : Continuous (λ t : ℝ => (1 - t) • z₀ + t • z) := by continuity

lemma differentiable_bary : Differentiable ℂ (λ z : ℂ => (1 - t) • z₀ + t • z) :=
  (differentiable_const _).add (differentiable_id.const_smul _)

lemma has_deriv_at_bary : HasDerivAt (λ t : ℝ => (1 - t) • z₀ + t • z) (z - z₀) t := by
  have h0 : HasDerivAt (1 - ·) (-1) t := by
    simpa using (hasDerivAt_const t 1).sub (hasDerivAt_id t)
  have h1 : HasDerivAt (λ t : ℝ => (1 - t) • z₀) (-z₀) t := by
    simpa using h0.smul_const z₀
  have h2 : HasDerivAt (· • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  convert h1.add h2 using 1 ; ring

lemma hasDerivAt_bary' : HasDerivAt (λ z => (1 - t) • z₀ + t • z) t z := by
  simpa using (hasDerivAt_const z ((1 - t) • z₀)).add ((hasDerivAt_id z).const_smul t)

lemma StarConvex.bary (hU : StarConvex ℝ z₀ U) (hz : z ∈ U) :
    MapsTo (λ t : ℝ => (1 - t) • z₀ + t • z) (Icc 0 1) U :=
  λ _ ht => hU.segment_subset hz (mem_segment ht)

noncomputable def primitive (f : ℂ → ℂ) (z₀ z : ℂ) : ℂ :=
  (z - z₀) * ∫ t in (0:ℝ)..1, f ((1 - t) • z₀ + t • z)

-- lemma primitive_eq_curvint : primitive f z₀ z = curvint 0 1 f (λ t, (1 - t) • z₀ + t • z) :=
-- by simpa only [curvint, has_deriv_at_bary.deriv]
--   using (interval_integral.integral_const_mul _ _).symm

namespace detail

noncomputable abbrev φ (f : ℂ → ℂ) (z₀ z : ℂ) (t : ℝ) : ℂ := f ((1 - t) • z₀ + t • z)

noncomputable abbrev ψ (f : ℂ → ℂ) (z₀ z : ℂ) (t : ℝ) : ℂ := t • deriv f ((1 - t) • z₀ + t • z)

end detail

open detail

lemma DifferentiableOn.exists_primitive (f_holo : DifferentiableOn ℂ f U)
    (hU : StarConvex ℝ z₀ U) (hU' : IsOpen U) (hz : z ∈ U) :
    HasDerivAt (primitive f z₀) (f z) z := by

  let φ := φ f z₀
  let ψ := ψ f z₀
  let I : Set ℝ := Icc 0 1

  have f_cont : ContinuousOn f U := f_holo.continuousOn
  have f_deri : ∀ ⦃z⦄ (_ : z ∈ U), HasDerivAt f (_root_.deriv f z) z :=
    λ z hz => f_holo.hasDerivAt (hU'.mem_nhds hz)
  have f_cder : ContinuousOn (_root_.deriv f) U := (f_holo.analyticOn hU').deriv.continuousOn

  have φ_cont {z} (hz : z ∈ U) : ContinuousOn (φ z) I :=
    f_cont.comp continuous_bary.continuousOn (hU.bary hz)
  have φ_diff {t} (ht : t ∈ I) : DifferentiableOn ℂ (λ w => φ w t) U :=
    f_holo.comp differentiable_bary.differentiableOn (λ z hz => hU.bary hz ht)
  have φ_derz {z} (hz : z ∈ U) {t} (ht : t ∈ I) : HasDerivAt (λ x => φ x t) (ψ z t) z := by
    convert (f_deri (hU.bary hz ht)).comp z hasDerivAt_bary' ; simp ; ring
  have φ_dert {t} (ht : t ∈ I) : HasDerivAt (φ z) ((z - z₀) * _root_.deriv f ((1 - t) • z₀ + t • z)) t := by
    convert (f_deri (hU.bary hz ht)).comp t has_deriv_at_bary using 1 ; ring
  have ψ_cont : ContinuousOn (ψ z) I :=
    continuousOn_id.smul (f_cder.comp continuous_bary.continuousOn (hU.bary hz))

  have step1 : HasDerivAt (λ z => ∫ t in (0:ℝ)..1, φ z t) (∫ t in (0:ℝ)..1, ψ z t) z := by
    obtain ⟨δ, δ_pos, K_subs⟩ :=
      isCompact_segment.exists_cthickening_subset_open hU' (hU.segment_subset hz)
    let K := cthickening δ (segment ℝ z₀ z)
    have hz₀ : z₀ ∈ K := self_subset_cthickening _ ⟨1, 0, zero_le_one, le_rfl, by ring, by simp⟩
    have K_cpct : IsCompact K := isCompact_of_isClosed_isBounded isClosed_cthickening
      isCompact_segment.isBounded.cthickening
    have K_conv : Convex ℝ K := (convex_segment _ _).cthickening _
    have K_ball : ball z δ ⊆ K := ball_subset_closedBall.trans
      (closedBall_subset_cthickening (right_mem_segment _ _ _) δ)
    obtain ⟨C, hC⟩ := K_cpct.exists_bound_of_continuousOn (f_cder.mono K_subs)
    have C_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀)

    have key : ∀ t ∈ I, LipschitzOnWith (Real.nnabs C) (φ · t) K := by
      refine λ t ht => lipschitzOnWith_iff_norm_sub_le.mpr (λ x hx y hy => ?_)
      refine K_conv.norm_image_sub_le_of_norm_deriv_le (f := (φ · t)) (λ w hw => ?_) ?_ hy hx
      · exact (φ_diff ht).differentiableAt (hU'.mem_nhds (K_subs hw))
      · rintro w hw
        rw [(φ_derz (K_subs hw) ht).deriv]
        have f_bary := hC _ ((K_conv.starConvex hz₀).bary hw ht)
        have ht' : |t| ≤ 1 := by { rw [abs_le] ; constructor <;> linarith [ht.1, ht.2] }
        simpa [abs_eq_self.2 C_nonneg] using mul_le_mul ht' f_bary (by simp) (by simp)

    apply has_deriv_at_integral_of_continuous_of_lip zero_le_one δ_pos
    · exact eventually_of_mem (hU'.mem_nhds hz) (λ _ => φ_cont)
    · exact λ t ht => φ_derz hz (Ioc_subset_Icc_self ht)
    · exact λ t ht => (key t (Ioc_subset_Icc_self ht)).mono K_ball
    · exact ψ_cont.mono Ioc_subset_Icc_self

  have step2 : (∫ t in (0:ℝ)..1, φ z t) + (z - z₀) * (∫ t in (0:ℝ)..1, ψ z t) = f z := by
    let g (t : ℝ) : ℂ := t • φ z t
    let h (t : ℝ) : ℂ := φ z t + (z - z₀) * ψ z t

    have g_cont : ContinuousOn g I := continuousOn_id.smul (φ_cont hz)
    have g_dert : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt g (h t) t := by
      rintro t ht
      convert (hasDerivAt_id t).smul (φ_dert (Ioo_subset_Icc_self ht)) using 1
      simp [add_comm] ; ring
    have h_intg : IntervalIntegrable h volume (0:ℝ) 1 := by
      apply ContinuousOn.intervalIntegrable
      simp only [Interval, min_eq_left, zero_le_one, max_eq_right]
      convert (φ_cont hz).add (continuousOn_const.mul ψ_cont) ; simp

    convert ← integral_eq_sub_of_hasDerivAt_of_le zero_le_one g_cont g_dert h_intg using 1
    · simp only
      rw [intervalIntegral.integral_add]
      · simp
      · apply ContinuousOn.intervalIntegrable ; convert φ_cont hz ; simp [Interval]
      · apply ContinuousOn.intervalIntegrable
        refine continuousOn_const.mul ?_
        convert ψ_cont
        simp
    · simp [detail.φ]

  have : HasDerivAt (primitive f z₀)
      ((∫ t in (0:ℝ)..1, φ z t) + (z - z₀) * ∫ t in (0:ℝ)..1, ψ z t) z := by
    convert ((hasDerivAt_id z).sub (hasDerivAt_const z z₀)).mul step1 using 1
    simp

  exact step2 ▸ this
