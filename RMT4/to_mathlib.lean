import Mathlib.Analysis.Calculus.ParametricIntegral
import RMT4.cindex

open Metric Topology Filter Set MeasureTheory

lemma is_compact_segment
  [OrderedRing 𝕜] [TopologicalSpace 𝕜] [TopologicalAddGroup 𝕜] [CompactIccSpace 𝕜]
  [TopologicalSpace E] [AddCommGroup E] [ContinuousAdd E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] {x y : E} : IsCompact (segment 𝕜 x y) :=
(segment_eq_image 𝕜 x y).symm ▸ isCompact_Icc.image (by continuity)

lemma mem_closed_ball_neg_iff_mem_neg_closed_ball [SeminormedAddCommGroup V]
    (u v : V) (r : ℝ) : u ∈ closedBall (-v) r ↔ -u ∈ closedBall v r := by
  rw [← neg_closedBall r v]; rfl

lemma DifferentiableAt.deriv_eq_deriv_pow_div_pow {n : ℕ} (n_pos : 0 < n) {f g : ℂ → ℂ} ⦃z : ℂ⦄
    (hg : ∀ᶠ z in 𝓝 z, f z = HPow.hPow (g z) n) (g_diff : DifferentiableAt ℂ g z) (fz_nonzero : f z ≠ 0) :
    deriv g z = deriv f z / (n * HPow.hPow (g z) (n - 1)) := by
  have h1 : g z ≠ 0 := λ h => fz_nonzero (by simp [Eventually.self_of_nhds hg, h, n_pos])
  have h2 : ↑n * HPow.hPow (g z) (n - 1) ≠ 0 := by simp [pow_ne_zero, h1, n_pos.ne.symm]
  rw [(EventuallyEq.deriv hg).self_of_nhds, deriv_pow'' _ g_diff, eq_div_iff h2]
  ring

lemma Set.injOn_of_injOn_comp (hfg : InjOn (f ∘ g) s) : InjOn g s :=
  λ _ hx _ hy => hfg hx hy ∘ congr_arg f

lemma has_deriv_at_integral_of_continuous_of_lip
    {φ : ℂ → ℝ → ℂ} {ψ : ℝ → ℂ} {z₀ : ℂ} {a b C δ : ℝ} (hab : a ≤ b) (δ_pos : 0 < δ)
    (φ_cts : ∀ᶠ z in 𝓝 z₀, ContinuousOn (φ z) (Icc a b))
    (φ_der : ∀ t ∈ Ioc a b, HasDerivAt (λ x => φ x t) (ψ t) z₀)
    (φ_lip : ∀ t ∈ Ioc a b, LipschitzOnWith (Real.nnabs C) (λ x => φ x t) (ball z₀ δ))
    (ψ_cts : ContinuousOn ψ (Ioc a b)) :
    HasDerivAt (λ z => ∫ t in a..b, φ z t) (∫ t in a..b, ψ t) z₀ := by
  let μ : Measure ℝ := volume.restrict (Ioc a b)
  have h1 : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (φ z) μ :=
    φ_cts.mono (λ z h => (h.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc)
  have h2 : Integrable (φ z₀) μ :=
    φ_cts.self_of_nhds.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have h3 : AEStronglyMeasurable ψ μ := ψ_cts.aestronglyMeasurable measurableSet_Ioc
  have h4 : ∀ᵐ t ∂μ, LipschitzOnWith (Real.nnabs C) (λ z => φ z t) (ball z₀ δ) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (eventually_of_forall φ_lip)
  have h5 : Integrable (λ _ => C) μ := integrable_const _
  have h6 : ∀ᵐ t ∂μ, HasDerivAt (λ z => φ z t) (ψ t) z₀ :=
    (ae_restrict_iff' measurableSet_Ioc).mpr (eventually_of_forall φ_der)

  simpa [intervalIntegral, hab] using
    (hasDerivAt_integral_of_dominated_loc_of_lip δ_pos h1 h2 h3 h4 h5 h6).2
