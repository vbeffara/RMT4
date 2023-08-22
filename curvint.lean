import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Interval
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.PathConnected

variable [TopologicalSpace 𝕜] [NormedAddCommGroup 𝕜] [NormedSpace ℝ 𝕜] [HSMul 𝕜 E E] [NormedAddCommGroup E]
  [NormedSpace ℝ E]

open intervalIntegral Real MeasureTheory Filter Topology

/-- We start with a basic definition of the integral of a function along a path, which makes sense
  when the path is differentiable -/

noncomputable def pintegral (t₁ t₂ : ℝ) (f : 𝕜 → E) (γ : ℝ → 𝕜) : E :=
  ∫ t in t₁..t₂, deriv γ t • f (γ t)

-- the definition is defeq to `circleIntegral` when appropriate:
lemma circleIntegral_eq_pintegral2 {f : ℂ → ℂ} :
    (∮ z in C(c, R), f z) = (pintegral 0 (2 * π) f (circleMap c R)) := rfl

-- a version using `Path` (but it loses all the Path API):
noncomputable def pintegral2 (f : 𝕜 → E) {x y : 𝕜} (γ : Path x y) : E :=
    pintegral 0 1 f γ.extend

-- integral against a `Path`, has the Path API but is tedious to use

noncomputable def pderiv {x y : 𝕜} (γ : Path x y) (t : unitInterval) : 𝕜 := deriv γ.extend t

noncomputable def pintegral1' (f : 𝕜 → E) {x y : 𝕜} (γ : Path x y) : E :=
  ∫ t, pderiv γ t • f (γ t)

/-- Some plumbing -/

noncomputable def circlePath (c : ℂ) (R : ℝ) : Path (c + R) (c + R) where
  toFun := λ t => circleMap c R (2 * π * t)
  source' := by simp [circleMap]
  target' := by simp [circleMap]

noncomputable def toPath (t₁ t₂ : ℝ) (γ : ℝ → 𝕜) (h1 : ContinuousOn γ (Set.Icc t₁ t₂)) (h2 : t₁ < t₂) :
    Path (γ t₁) (γ t₂) where
  toFun := λ t => γ ((iccHomeoI t₁ t₂ h2).symm t)
  continuous_toFun := by
    apply h1.comp_continuous
    · exact continuous_subtype_val.comp (iccHomeoI t₁ t₂ h2).symm.continuous_toFun
    · exact λ t => Subtype.mem _
  source' := by simp
  target' := by simp

example {c : ℂ} {R : ℝ} : (circlePath c R).cast (by simp [circleMap]) (by simp [circleMap]) =
    toPath 0 (2 * π) (circleMap c R) (continuous_circleMap c R).continuousOn two_pi_pos := by
  ext1; simp [toPath, circlePath]

/-- Version with `deriv_within` is useful -/

-- noncomputable def curvint' (f : 𝕜 → E) (γ : contour 𝕜) : E :=
-- ∫ t in 0..γ.ℓ, deriv_within γ (interval 0 γ.ℓ) t • f (γ t)

noncomputable def pintegral' (t₁ t₂ : ℝ) (f : 𝕜 → E) (γ : ℝ → 𝕜) : E :=
  ∫ t in t₁..t₂, derivWithin γ (Set.uIcc t₁ t₂) t • f (γ t)

lemma pintegral'_eq_pintegral : (pintegral' : ℝ → ℝ → (𝕜 → E) → (ℝ → 𝕜) → E) = pintegral := by
  ext t₁ t₂ f γ
  apply intervalIntegral.integral_congr_ae
  apply eventually_of_mem (U := {t₁, t₂}ᶜ)
  · rw [mem_ae_iff, compl_compl]
    apply measure_union_null volume_singleton volume_singleton
  · intro t ht1 ht2
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_insert_iff] at ht1
    simp [Set.uIoc] at ht2
    push_neg at ht1
    simp only [derivWithin, ge_iff_le, deriv]
    congr
    apply fderivWithin_of_mem_nhds
    apply Icc_mem_nhds
    · cases ht2.1
      · apply inf_le_left.trans_lt
        assumption
      · apply inf_le_right.trans_lt
        assumption
    · cases ht2.2
      · refine lt_of_le_of_lt' le_sup_left ?_
        apply lt_of_le_of_ne _ ht1.1
        assumption
      · refine lt_of_le_of_lt' le_sup_right ?_
        apply lt_of_le_of_ne _ ht1.2
        assumption

-- @[simp] lemma curvint'_eq_curvint : (curvint' : (𝕜 → E) → contour 𝕜 → E) = curvint :=
-- begin
--   ext f γ,
--   have h1 : ({ 0, γ.ℓ }ᶜ : set ℝ) ∈ volume.ae,
--   { rw [measure_theory.mem_ae_iff, compl_compl],
--     exact measure_theory.measure_union_null real.volume_singleton real.volume_singleton },
--   refine interval_integral.integral_congr_ae (eventually_of_mem h1 (λ x hx hx', _)),
--   simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff] at hx,
--   push_neg at hx,
--   simp only [deriv, deriv_within],
--   congr,
--   refine fderiv_within_of_mem_nhds (Icc_mem_nhds hx'.1 (lt_of_le_of_ne hx'.2 _)),
--   cases le_or_lt 0 γ.ℓ,
--   { simp [h, hx] },
--   { simp [h.le, hx] }
-- end


-- lemma toto : pintegral t₁ t₂ f γ = p

-- import analysis.calculus.parametric_integral
-- import analysis.complex.cauchy_integral
-- import analysis.complex.removable_singularity
-- import measure_theory.group.integration
-- import analysis.calculus.deriv
-- import topology.path_connected
-- import analysis.complex.locally_uniform_limit

-- open set metric measure_theory filter complex interval_integral
-- open_locale real topological_space unit_interval

-- section

-- variables {𝕜 E F : Type*} {s t : set 𝕜} {x x₀ : 𝕜} {z z₀ : E} {g : 𝕜 → E} {f : E → F}
--   [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
--   [normed_add_comm_group F] [normed_space 𝕜 F]

-- lemma has_fderiv_at_apply_neg (z : E) : has_fderiv_at (λ z, -z) (-continuous_linear_map.id 𝕜 E) z :=
-- (has_fderiv_at_id z).neg

-- lemma has_fderiv_at_const_sub (z : E) :
--   has_fderiv_at (λ z, z₀ - z) (-continuous_linear_map.id 𝕜 E) z :=
-- (has_fderiv_at_id z).const_sub z₀

-- @[simp] lemma differentiable_at_neg_id : differentiable_at 𝕜 (λ z : E, -z) z :=
-- (has_fderiv_at_apply_neg z).differentiable_at

-- @[simp] lemma differentiable_at_const_sub : differentiable_at 𝕜 (λ z : E, z₀ - z) z :=
-- (has_fderiv_at_const_sub z).differentiable_at

-- lemma has_fderiv_at.comp_neg {f' : E →L[𝕜] F} (hf : has_fderiv_at f f' (-z)) :
--   has_fderiv_at (λ z, f (-z)) (-f') z :=
-- by simpa using hf.comp z (has_fderiv_at_apply_neg z)

-- lemma has_fderiv_at.comp_const_sub {f' : E →L[𝕜] F} (hf : has_fderiv_at f f' (z₀ - z)) :
--   has_fderiv_at (λ z, f (z₀ - z)) (-f') z :=
-- by simpa using hf.comp z (has_fderiv_at_const_sub z)

-- lemma has_fderiv_at.comp_neg' {f' : E →L[𝕜] F} (hf : has_fderiv_at f f' z) :
--   has_fderiv_at (λ z, f (-z)) (-f') (-z) :=
-- has_fderiv_at.comp_neg ((neg_neg z).symm ▸ hf)

-- lemma has_fderiv_at.comp_const_sub' {f' : E →L[𝕜] F} (hf : has_fderiv_at f f' z) :
--   has_fderiv_at (λ z, f (z₀ - z)) (-f') (z₀ - z) :=
-- has_fderiv_at.comp_const_sub (by simpa only [sub_sub_cancel] using hf)

-- lemma differentiable_at.comp_neg (hf : differentiable_at 𝕜 f (-z)) :
--   differentiable_at 𝕜 (λ z, f (-z)) z :=
-- hf.comp z differentiable_at_neg_id

-- lemma differentiable_at.comp_const_sub (hf : differentiable_at 𝕜 f (z₀ - z)) :
--   differentiable_at 𝕜 (λ z, f (z₀ - z)) z :=
-- hf.comp z differentiable_at_const_sub

-- lemma differentiable_at.comp_neg' (hf : differentiable_at 𝕜 f z) :
--   differentiable_at 𝕜 (λ z, f (-z)) (-z) :=
-- differentiable_at.comp_neg ((neg_neg z).symm ▸ hf)

-- lemma differentiable_at.comp_const_sub' (hf : differentiable_at 𝕜 f z) :
--   differentiable_at 𝕜 (λ z, f (z₀ - z)) (z₀ - z) :=
-- differentiable_at.comp_const_sub (by simpa only [sub_sub_cancel] using hf)

-- @[simp] lemma fderiv_apply_neg : fderiv 𝕜 (λ z, f (-z)) z = - fderiv 𝕜 f (-z) :=
-- begin
--   by_cases differentiable_at 𝕜 f (-z),
--   { simpa using fderiv.comp z h differentiable_at_neg_id },
--   { have h3 : ¬ differentiable_at 𝕜 (λ z, f (-z)) z := λ h', by simpa using h'.comp_neg',
--     simp only [differentiable_at] at h h3,
--     simp [fderiv, h, h3] }
-- end

-- @[simp] lemma fderiv_apply_comp_sub_id : fderiv 𝕜 (λ z, f (z₀ - z)) z = - fderiv 𝕜 f (z₀ - z) :=
-- begin
--   by_cases differentiable_at 𝕜 f (z₀ - z),
--   { simpa [(has_fderiv_at_const_sub z).fderiv] using fderiv.comp z h differentiable_at_const_sub },
--   { have h3 : ¬ differentiable_at 𝕜 (λ z, f (z₀ - z)) z :=
--     by { intro h1,
--       have : differentiable_at 𝕜 (λ z, (λ z, f (z₀ - z)) (z₀ - z)) (z₀ - z) := h1.comp_const_sub',
--       simpa using this },
--     simp only [differentiable_at] at h h3,
--     simp [fderiv, h, h3] }
-- end

-- @[simp] lemma deriv_apply_neg : deriv (λ x, g (-x)) x = - deriv g (-x) :=
-- by simp only [deriv, fderiv_apply_neg, continuous_linear_map.neg_apply]

-- @[simp] lemma deriv_apply_comp_sub_id : deriv (λ x, g (x₀ - x)) x = - deriv g (x₀ - x) :=
-- by simp only [deriv, fderiv_apply_comp_sub_id, continuous_linear_map.neg_apply]

-- end

-- section

-- @[ext] structure contour (𝕜 : Type*) := (ℓ : ℝ) (to_fun : ℝ → 𝕜)

-- variables {𝕜 E : Type*} {a b c t : ℝ} {x y z : 𝕜} {γ : contour 𝕜} {f : 𝕜 → E}
--   [normed_field 𝕜] [normed_add_comm_group E] [complete_space E]
--   [normed_space ℝ 𝕜] [normed_space 𝕜 E] [normed_space ℝ E]

-- instance : has_coe_to_fun (contour 𝕜) (λ _, ℝ → 𝕜) := ⟨contour.to_fun⟩

-- noncomputable def contour.append (γ₁ γ₂ : contour 𝕜) : contour 𝕜 :=
-- {
--   ℓ := γ₁.ℓ + γ₂.ℓ,
--   to_fun := λ t, if t ≤ γ₁.ℓ then γ₁ t else γ₂ (t - γ₁.ℓ)
-- }

-- noncomputable instance : has_append (contour 𝕜) := ⟨contour.append⟩

-- def contour.reverse (γ : contour 𝕜) : contour 𝕜 :=
-- ⟨γ.ℓ, λ t, γ (γ.ℓ - t)⟩

-- instance : has_neg (contour 𝕜) := ⟨contour.reverse⟩

-- lemma contour.apply : γ t = γ.to_fun t := rfl
-- @[simp] lemma contour.minus_ℓ : (-γ).ℓ = γ.ℓ := rfl
-- @[simp] lemma contour.minus_apply : (- γ) t = γ (γ.ℓ - t) := rfl
-- @[simp] lemma contour.minus_to_fun : coe_fn (- γ) = λ t, γ (γ.ℓ - t) := rfl

-- def contour.continuous (γ : contour 𝕜) : Prop :=
--   continuous_on γ (interval 0 γ.ℓ)

-- lemma contour.reverse_reverse : γ.reverse.reverse = γ :=
-- by simp [contour.reverse, contour.apply]; ext; refl

-- noncomputable def curvint (f : 𝕜 → E) (γ : contour 𝕜) : E :=
-- ∫ t in 0..γ.ℓ, deriv γ t • f (γ t)

-- noncomputable def curvint' (f : 𝕜 → E) (γ : contour 𝕜) : E :=
-- ∫ t in 0..γ.ℓ, deriv_within γ (interval 0 γ.ℓ) t • f (γ t)

-- @[simp] lemma curvint_swap : curvint f (-γ) = - curvint f γ :=
-- by simp only [curvint, contour.minus_to_fun, deriv_apply_comp_sub_id, neg_smul, contour.minus_ℓ,
--   interval_integral.integral_neg, sub_self, tsub_zero,
--   interval_integral.integral_comp_sub_left (λ t, deriv γ t • f (γ t)) γ.ℓ]

-- @[simp] lemma curvint'_eq_curvint : (curvint' : (𝕜 → E) → contour 𝕜 → E) = curvint :=
-- begin
--   ext f γ,
--   have h1 : ({ 0, γ.ℓ }ᶜ : set ℝ) ∈ volume.ae,
--   { rw [measure_theory.mem_ae_iff, compl_compl],
--     exact measure_theory.measure_union_null real.volume_singleton real.volume_singleton },
--   refine interval_integral.integral_congr_ae (eventually_of_mem h1 (λ x hx hx', _)),
--   simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff] at hx,
--   push_neg at hx,
--   simp only [deriv, deriv_within],
--   congr,
--   refine fderiv_within_of_mem_nhds (Icc_mem_nhds hx'.1 (lt_of_le_of_ne hx'.2 _)),
--   cases le_or_lt 0 γ.ℓ,
--   { simp [h, hx] },
--   { simp [h.le, hx] }
-- end

-- lemma curvint'_swap : curvint' f (-γ) = - curvint' f γ :=
-- by simp

-- end

-- section

-- variables {E : Type*} {c : ℂ} {R : ℝ} {f : ℂ → E}
--   [normed_add_comm_group E] [complete_space E] [normed_space ℂ E]

-- noncomputable def circle_path (c : ℂ) (R : ℝ) : contour ℂ := ⟨2 * π, circle_map c R⟩

-- lemma circle_integral_eq_curvint : ∮ z in C(c, R), f z = curvint f (circle_path c R) :=
-- rfl

-- end

-- section

-- variables {𝕜 E : Type*} {C : ℝ} {γ : contour 𝕜} {U : set 𝕜} {w₀ : 𝕜} {F F' : 𝕜 → 𝕜 → E}
--   [is_R_or_C 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E] [normed_space ℝ E] [complete_space E]

-- -- TODO: perhaps `U` is not useful here
-- lemma has_deriv_at_curvint (hab : 0 < γ.ℓ)
--   (γ_diff : cont_diff_on ℝ 1 γ (Icc 0 γ.ℓ))
--   (γ_maps : maps_to γ (Icc 0 γ.ℓ) U)
--   (F_cont : ∀ᶠ w in 𝓝 w₀, continuous_on (F w) U)
--   (F_deri : ∀ᶠ w in 𝓝 w₀, ∀ t ∈ Icc 0 γ.ℓ, has_deriv_at (λ w, F w (γ t)) (F' w (γ t)) w)
--   (F'_cont : continuous_on (F' w₀) U)
--   (F'_norm : ∀ᶠ w in 𝓝 w₀, ∀ t ∈ Icc 0 γ.ℓ, ‖F' w (γ t)‖ ≤ C) :
--   has_deriv_at (λ w, curvint (F w) γ) (curvint (F' w₀) γ) w₀ :=
-- begin
--   rw [← curvint'_eq_curvint],
--   let μ : measure ℝ := volume.restrict (Ioc 0 γ.ℓ),
--   let φ : 𝕜 → ℝ → E := λ w t, deriv_within γ (Icc 0 γ.ℓ) t • F w (γ t),
--   let ψ : 𝕜 → ℝ → E := λ w t, deriv_within γ (Icc 0 γ.ℓ) t • F' w (γ t),
--   obtain ⟨δ, hδ, h_in_δ⟩ := eventually_nhds_iff_ball.mp (F_deri.and F'_norm),

--   have γ'_cont : continuous_on (deriv_within γ (Icc 0 γ.ℓ)) (Icc 0 γ.ℓ),
--     from γ_diff.continuous_on_deriv_within (unique_diff_on_Icc hab) le_rfl,
--   obtain ⟨C', h⟩ := (is_compact_Icc.image_of_continuous_on γ'_cont).bounded.subset_ball 0,

--   have φ_cont : ∀ᶠ w in 𝓝 w₀, continuous_on (φ w) (Icc 0 γ.ℓ),
--     by { filter_upwards [F_cont] with w h,
--       exact γ'_cont.smul (h.comp γ_diff.continuous_on γ_maps) },
--   have φ_meas : ∀ᶠ w in 𝓝 w₀, ae_strongly_measurable (φ w) μ,
--     by { filter_upwards [φ_cont] with w h,
--       exact (h.mono Ioc_subset_Icc_self).ae_strongly_measurable measurable_set_Ioc },
--   have φ_intg : integrable (φ w₀) μ,
--     from φ_cont.self_of_nhds.integrable_on_Icc.mono_set Ioc_subset_Icc_self,
--   have φ_deri : ∀ᵐ t ∂μ, ∀ w ∈ ball w₀ δ, has_deriv_at (λ w, φ w t) (ψ w t) w := by {
--     refine (ae_restrict_iff' measurable_set_Ioc).mpr (eventually_of_forall _),
--     rintro t ht w hw,
--     exact ((h_in_δ w hw).1 t (Ioc_subset_Icc_self ht)).const_smul _},

--   have ψ_cont : continuous_on (ψ w₀) (Icc 0 γ.ℓ),
--     from γ'_cont.smul (F'_cont.comp γ_diff.continuous_on γ_maps),
--   have ψ_meas : ae_strongly_measurable (ψ w₀) μ,
--     from (ψ_cont.mono Ioc_subset_Icc_self).ae_strongly_measurable measurable_set_Ioc,
--   have ψ_norm : ∀ᵐ t ∂μ, ∀ x ∈ ball w₀ δ, ‖ψ x t‖ ≤ C' * C,
--     by { refine (ae_restrict_iff' measurable_set_Ioc).mpr (eventually_of_forall (λ t ht w hw, _)),
--       rw norm_smul,
--       have e1 := mem_closed_ball_zero_iff.mp (h (mem_image_of_mem _ (Ioc_subset_Icc_self ht))),
--       have e2 := (h_in_δ w hw).2 t (Ioc_subset_Icc_self ht),
--       exact mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1) },

--   have hC : integrable (λ (t : ℝ), C' * C) μ := integrable_const _,
--   have := (has_deriv_at_integral_of_dominated_loc_of_deriv_le hδ φ_meas φ_intg ψ_meas ψ_norm hC φ_deri).2,
--   simpa [curvint', interval_integral, hab.le] using
--     (has_deriv_at_integral_of_dominated_loc_of_deriv_le hδ φ_meas φ_intg ψ_meas ψ_norm hC φ_deri).2
-- end

-- end

-- section

-- variables {E : Type*} [normed_add_comm_group E] [normed_space ℂ E] [complete_space E]
--   {x y z : ℂ} {γ : path x y} {f : ℂ → ℂ} {t : unit_interval}

-- noncomputable def pderiv (γ : path x y) (t : unit_interval) : ℂ := deriv γ.extend t

-- lemma min_max {t : ℝ} : min 1 (max 0 t) = max 0 (min 1 t) :=
-- begin
--   simp [min, max, inf_sup_left],
-- end

-- lemma min_max' {t : ℝ} :
--   1 - max 0 (min 1 t) = max 0 (min 1 (1 - t)) :=
-- begin
--   rw [← min_sub_sub_left 1 0 (min 1 t), ← max_sub_sub_left 1 1 t, ← min_max],
--   simp only [tsub_zero, sub_self]
-- end

-- lemma symm_sub {t : ℝ} : σ (proj_Icc 0 1 zero_le_one t) = proj_Icc 0 1 zero_le_one (1 - t) :=
-- subtype.ext min_max'

-- @[simp] lemma path.symm_extend {t : ℝ} : γ.symm.extend t = γ.extend (1 - t) :=
-- begin
--   simp only [path.extend, path.symm, Icc_extend, symm_sub, path.coe_mk, function.comp_app],
-- end

-- @[simp] lemma pderiv.symm : pderiv γ.symm t = - pderiv γ (σ t) :=
-- begin
--   dsimp [pderiv],
--   convert deriv_apply_comp_sub_id,
--   ext1 t,
--   simp,
-- end

-- noncomputable def cint (γ : path x y) (f : ℂ → E) : E :=
-- ∫ t : unit_interval, (pderiv γ t • f (γ t))

-- lemma cint_swap : cint γ.symm f = - cint γ f :=
-- begin
--   simp [cint],
--   -- have := measure_theory.integral_image_eq_integral_abs_deriv_smul,
--   sorry
-- end

-- end