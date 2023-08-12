-- import analysis.complex.cauchy_integral
-- import to_mathlib

-- noncomputable theory

-- def complex.as_continuous_linear_equiv {a : ℂ} (ha : a ≠ 0) : ℂ ≃L[ℂ] ℂ :=
-- (linear_map.linear_equiv_of_injective (linear_map.mul_left ℂ a)
--     (linear_map.mul_left_injective ha) rfl).to_continuous_linear_equiv

-- def complex.as_continuous_linear_map (a : ℂ) : ℂ →L[ℂ] ℂ :=
-- ⟨linear_map.mul_left ℂ a, linear_map.continuous_of_finite_dimensional (linear_map.mul_left ℂ a)⟩

-- lemma complex.as_continuous_linear_equiv_eq_as_continuous_linear_map {a : ℂ} (ha : a ≠ 0) :
--   (complex.as_continuous_linear_equiv ha).to_continuous_linear_map = a.as_continuous_linear_map :=
-- rfl

-- @[simp] lemma complex.continuous_linear_map_one_as_continuous_linear_map (A : ℂ →L[ℂ] ℂ) :
--   (A 1).as_continuous_linear_map = A :=
-- by { ext1, simp only [complex.as_continuous_linear_map, continuous_linear_map.coe_mk',
--                       linear_map.mul_left_apply, mul_one], }

-- @[simp] lemma complex.as_continuous_linear_map_zero :
--   (0 : ℂ).as_continuous_linear_map = 0 :=
-- begin
--   ext1,
--   simp only [complex.as_continuous_linear_map, linear_map.mul_left_zero_eq_zero,
--              continuous_linear_map.coe_mk', linear_map.zero_apply,
--              continuous_linear_map.zero_apply],
-- end

-- lemma complex.as_continuous_linear_map_add (a b : ℂ) :
--   (a+b).as_continuous_linear_map = a.as_continuous_linear_map + b.as_continuous_linear_map :=
-- begin
--   ext1,
--   simp only [complex.as_continuous_linear_map, continuous_linear_map.coe_mk',
--              linear_map.mul_left_apply, mul_one, continuous_linear_map.add_apply],
-- end

-- lemma complex.as_continuous_linear_map_mul (c a : ℂ) :
--   (c*a).as_continuous_linear_map = c • a.as_continuous_linear_map :=
-- begin
--   ext1,
--   simp_rw [complex.as_continuous_linear_map],
--   simp only [linear_map.mul_left_mul, mul_one, algebra.id.smul_eq_mul,
--              linear_map.mul_left_apply, mul_eq_mul_left_iff, true_or, eq_self_iff_true,
--              function.comp_app, linear_map.coe_comp, continuous_linear_map.coe_mk',
--              pi.smul_apply, continuous_linear_map.coe_smul'],
-- end

-- def complex.to_continuous_linear_map : ℂ →ₗ[ℂ] (ℂ →L[ℂ] ℂ) :=
-- { to_fun := complex.as_continuous_linear_map,
--   map_add' := complex.as_continuous_linear_map_add,
--   map_smul' := complex.as_continuous_linear_map_mul, }

-- lemma differentiable_on_complex_domain_has_fderiv_at {U : set ℂ} (U_open : is_open U)
--   {f : ℂ → ℂ} (f_hol : differentiable_on ℂ f U) {z : ℂ} (z_in_U : z ∈ U) :
--   has_strict_fderiv_at f ((deriv f z).as_continuous_linear_map) z :=
-- begin
--   have f_cont_diff : cont_diff_on ℂ (0 + 1) f U := (f_hol.cont_diff_on U_open).of_le le_top,
--   have key := ((f_cont_diff.cont_diff_within_at z_in_U).cont_diff_at
--                 (U_open.mem_nhds z_in_U)).has_strict_fderiv_at (by simp only [zero_add, le_refl]),
--   convert key,
--   have aux₁ := key.has_fderiv_at.has_deriv_at,
--   have aux₂ := (f_hol.differentiable_at (U_open.mem_nhds z_in_U)).has_deriv_at,
--   simp [congr_arg complex.as_continuous_linear_map ((has_deriv_at.unique aux₂ aux₁))],
-- end
