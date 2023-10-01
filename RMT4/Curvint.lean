import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Order.Interval
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.PathConnected
import RMT4.to_mathlib

open intervalIntegral Real MeasureTheory Filter Topology Set Metric

section definitions

/-- We start with a basic definition of the integral of a function along a path, which makes sense
  when the path is differentiable -/

noncomputable def curvint (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
  ∫ t in t₁..t₂, deriv γ t • f (γ t)

/-- Version with `deriv_within` is useful -/

noncomputable def curvint' (t₁ t₂ : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
  ∫ t in t₁..t₂, derivWithin γ (Set.uIcc t₁ t₂) t • f (γ t)

lemma curvint'_eq_curvint {f : ℂ → ℂ} {γ : ℝ → ℂ} : curvint' a b f γ = curvint a b f γ :=
  integral_congr_uIoo (λ _ ht => congr_arg₂ _ (derivWithin_of_mem_uIoo ht) rfl)

end definitions

section derivcurvint

variable
  {t₁ t₂ : ℝ} {F F' : ℂ → ℂ → ℂ}

theorem hasDerivAt_curvint (ht : t₁ < t₂)
    (γ_diff : ContDiffOn ℝ 1 γ (Icc t₁ t₂))
    (F_cont : ∀ᶠ i in 𝓝 i₀, ContinuousOn (F i) (γ '' Icc t₁ t₂))
    (F_deri : ∀ᶠ i in 𝓝 i₀, ∀ t ∈ Icc t₁ t₂, HasDerivAt (λ i => F i (γ t)) (F' i (γ t)) i)
    (F'_cont : ContinuousOn (F' i₀) (γ '' Icc t₁ t₂))
    (F'_norm : ∀ᶠ i in 𝓝 i₀, ∀ t ∈ Icc t₁ t₂, ‖F' i (γ t)‖ ≤ C)
    :
    HasDerivAt (λ i => curvint t₁ t₂ (F i) γ) (curvint t₁ t₂ (F' i₀) γ) i₀ := by
  simp_rw [← curvint'_eq_curvint]
  set μ : Measure ℝ := volume.restrict (Ioc t₁ t₂)
  set φ : ℂ → ℝ → ℂ := λ i t => derivWithin γ (Icc t₁ t₂) t • F i (γ t)
  set ψ : ℂ → ℝ → ℂ := λ i t => derivWithin γ (Icc t₁ t₂) t • F' i (γ t)
  obtain ⟨δ, hδ, h_in_δ⟩ := eventually_nhds_iff_ball.mp (F_deri.and F'_norm)
  simp only [curvint']

  have γ'_cont : ContinuousOn (derivWithin γ (Icc t₁ t₂)) (Icc t₁ t₂) :=
    γ_diff.continuousOn_derivWithin (uniqueDiffOn_Icc ht) le_rfl
  obtain ⟨C', h⟩ := (isCompact_Icc.image_of_continuousOn γ'_cont).isBounded.subset_ball 0

  have φ_cont : ∀ᶠ i in 𝓝 i₀, ContinuousOn (φ i) (Icc t₁ t₂) := by
    filter_upwards [F_cont] with i h
    exact γ'_cont.smul (h.comp γ_diff.continuousOn (mapsTo_image _ _))

  have φ_meas : ∀ᶠ i in 𝓝 i₀, AEStronglyMeasurable (φ i) μ := by
    filter_upwards [φ_cont] with i h
    exact (h.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc

  have φ_intg : Integrable (φ i₀) μ :=
    φ_cont.self_of_nhds.integrableOn_Icc.mono_set Ioc_subset_Icc_self

  have φ_deri : ∀ᵐ t ∂μ, ∀ i ∈ ball i₀ δ, HasDerivAt (λ j => φ j t) (ψ i t) i := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (eventually_of_forall ?_)
    intro t ht i hi
    apply ((h_in_δ i hi).1 t (Ioc_subset_Icc_self ht)).const_smul

  have ψ_cont : ContinuousOn (ψ i₀) (Icc t₁ t₂) :=
    γ'_cont.smul (F'_cont.comp γ_diff.continuousOn (mapsTo_image _ _))

  have ψ_meas : AEStronglyMeasurable (ψ i₀) μ :=
    (ψ_cont.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc

  have ψ_norm : ∀ᵐ t ∂μ, ∀ x ∈ ball i₀ δ, ‖ψ x t‖ ≤ C' * C := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (eventually_of_forall (λ t ht w hw => ?_))
    rw [norm_smul]
    have e1 := mem_closedBall_zero_iff.mp $
      ball_subset_closedBall (h (mem_image_of_mem _ (Ioc_subset_Icc_self ht)))
    have e2 := (h_in_δ w hw).2 t (Ioc_subset_Icc_self ht)
    exact mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)

  have hC : Integrable (λ (_ : ℝ) => C' * C) μ := integrable_const _

  simpa [curvint', intervalIntegral, ht.le] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le hδ φ_meas φ_intg ψ_meas ψ_norm hC φ_deri).2

end derivcurvint

section bla

variable {γ : ℝ → ℂ} {φ φ' : ℝ → ℝ} {f : ℂ → ℂ}

theorem cdv
    (φ_diff : ContDiffOn ℝ 1 φ (uIcc a b))
    (φ_maps : φ '' uIcc a b = uIcc (φ a) (φ b))
    (γ_diff : ContDiffOn ℝ 1 γ (uIcc (φ a) (φ b)))
    (f_cont : ContinuousOn f (γ '' uIcc (φ a) (φ b)))
    :
    curvint (φ a) (φ b) f γ = curvint a b f (γ ∘ φ) := by
  have l1 : ContinuousOn (fun x => derivWithin γ (uIcc (φ a) (φ b)) x • f (γ x)) (φ '' uIcc a b) := by
    have e1 := γ_diff.continuousOn_derivWithin'' le_rfl
    have e2 := f_cont.comp γ_diff.continuousOn (mapsTo_image _ _)
    simpa only [φ_maps] using e1.smul e2
  simp_rw [← curvint'_eq_curvint, curvint', ← φ_diff.integral_derivWithin_smul_comp l1]
  refine integral_congr_uIoo (λ t ht => ?_)
  have l2 : MapsTo φ (uIcc a b) (uIcc (φ a) (φ b)) := φ_maps ▸ mapsTo_image _ _
  have l6 : t ∈ uIcc a b := uIoo_subset_uIcc ht
  have l3 : DifferentiableWithinAt ℝ γ (uIcc (φ a) (φ b)) (φ t) := γ_diff.differentiableOn le_rfl (φ t) (l2 l6)
  have l4 : DifferentiableWithinAt ℝ φ (uIcc a b) t := (φ_diff t l6).differentiableWithinAt le_rfl
  have l5 : UniqueDiffWithinAt ℝ (uIcc a b) t := uniqueDiffWithinAt_of_mem_nhds (uIcc_mem_nhds ht)
  simp [derivWithin.scomp t l3 l4 l2 l5] ; ring

end bla

namespace holo

noncomputable def f1 (f : ℂ → ℂ) (Γ : ℂ → ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  deriv (Γ w) t * f (Γ w t)

noncomputable def f2 (f f' : ℂ → ℂ) (Γ Γ' : ℂ → ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  deriv (Γ' w) t * f (Γ w t) + Γ' w t * deriv (Γ w) t * f' (Γ w t)

noncomputable def f3 (f : ℂ → ℂ) (Γ Γ' : ℂ → ℝ → ℂ) (w : ℂ) (t : ℝ) : ℂ :=
  Γ' w t * f (Γ w t)

structure setup (f f' : ℂ → ℂ) (Γ Γ' : ℂ → ℝ → ℂ) where
  df : Differentiable ℂ f
  dΓ : Differentiable ℝ (Γ w)
  dΓ' : Differentiable ℝ (Γ' w)
  dfΓ : Differentiable ℝ (λ t => f (Γ w t))
  cdΓ : Continuous (deriv (Γ w₀))
  cdΓ' : Continuous (deriv (Γ' w₀))
  cfΓ : Continuous (λ t => f (Γ w₀ t))
  cf'Γ : Continuous (λ t => f' (Γ w₀ t))
  ff' : f' = deriv f
  ΓΓ' : deriv (λ w => Γ w t) w = Γ' w t
  L : LipschitzOnWith 1 (fun x => f1 f Γ x t) (ball w₀ 1)
  key : HasDerivAt (fun x => f1 f Γ x t) (f2 f f' Γ Γ' w₀ t) w₀

variable {a b : ℝ} {f f' : ℂ → ℂ} {Γ Γ' : ℂ → ℝ → ℂ}

theorem main_step (hab : a ≤ b) (S : setup f f' Γ Γ') :
    HasDerivAt (fun w => ∫ (t : ℝ) in a..b, f1 f Γ w t)
      (∫ (t : ℝ) in a..b, f2 f f' Γ Γ' w₀ t) w₀ := by

    apply has_deriv_at_integral_of_continuous_of_lip (C := 1) hab -- or whatever
    · exact zero_lt_one
    · apply eventually_of_forall (λ z => Continuous.continuousOn ?_)
      simp [f1]
      exact S.cdΓ.mul S.cfΓ
    · intro t _ ; exact S.key
    · intro t _ ; convert S.L ; simp
    · simp [f2]
      apply Continuous.continuousOn
      apply Continuous.add
      · apply Continuous.mul
        · exact S.cdΓ'
        · exact S.dfΓ.continuous
      · apply Continuous.mul
        · apply Continuous.mul
          · exact S.dΓ'.continuous
          · exact S.cdΓ
        · exact S.cf'Γ

lemma identity (S : setup f f' Γ Γ') : deriv (f3 f Γ Γ' w) t = f2 f f' Γ Γ' w t := by
  simp [f2, f3]
  rw [deriv_mul (S.dΓ').differentiableAt S.dfΓ.differentiableAt]
  simp only [add_right_inj]
  change Γ' w t * deriv (f ∘ Γ w) t = Γ' w t * deriv (Γ w) t * f' (Γ w t)
  rw [S.ff', deriv.comp _ S.df.differentiableAt (S.dΓ).differentiableAt]
  ring

theorem holo (hab : a ≤ b) (S : setup f f' Γ Γ') :
    HasDerivAt (fun w => curvint a b f (Γ w))
      (Γ' w₀ b * f (Γ w₀ b) - Γ' w₀ a * f (Γ w₀ a)) w₀ := by
  have : HasDerivAt (fun w => ∫ (t : ℝ) in a..b, f1 f Γ w t)
    (∫ (t : ℝ) in a..b, f2 f f' Γ Γ' w₀ t) w₀ := main_step hab S
  convert ← this
  simp only [← identity S, f3]
  apply intervalIntegral.integral_deriv_eq_sub' _ rfl
  · exact λ t _ => (S.dΓ' _).mul (S.dfΓ _)
  · apply Continuous.continuousOn
    have : deriv (fun t => Γ' w₀ t * f (Γ w₀ t)) =
      (λ t => deriv (Γ' w₀) t * f (Γ w₀ t) + Γ' w₀ t * deriv (Γ w₀) t * f' (Γ w₀ t)) := by
      ext1 t ; exact identity S
    rw [this]
    apply Continuous.add
    · apply Continuous.mul
      · exact S.cdΓ'
      · exact S.dfΓ.continuous
    · apply Continuous.mul
      · apply Continuous.mul
        · exact S.dΓ'.continuous
        · exact S.cdΓ
      · exact S.cf'Γ

end holo