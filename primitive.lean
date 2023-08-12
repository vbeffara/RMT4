-- import analysis.convex.star
-- import to_mathlib
-- import curvint

-- open filter metric measure_theory set interval_integral affine_map
-- open_locale topological_space big_operators

-- variables {f : ℂ → ℂ} {z₀ z w : ℂ} {ε δ t a b : ℝ} {K U : set ℂ}

-- lemma mem_segment (ht : t ∈ Icc (0 : ℝ) 1) : (1 - t) • z₀ + t • z ∈ segment ℝ z₀ z :=
-- ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩

-- lemma continuous_bary : continuous (λ t : ℝ, (1 - t) • z₀ + t • z) := by continuity

-- lemma differentiable_bary : differentiable ℂ (λ z : ℂ, (1 - t) • z₀ + t • z) := by simp

-- lemma has_deriv_at_bary : has_deriv_at (λ t : ℝ, (1 - t) • z₀ + t • z) (z - z₀) t :=
-- begin
--   have h0 : has_deriv_at (λ t : ℝ, 1 - t) (-1) t,
--     by simpa using (has_deriv_at_const t 1).sub (has_deriv_at_id t),
--   have h1 : has_deriv_at (λ t : ℝ, (1 - t) • z₀) (-z₀) t,
--     by simpa using h0.smul_const z₀,
--   have h2 : has_deriv_at (λ t : ℝ, t • z) z t,
--     by simpa using (has_deriv_at_id t).smul_const z,
--   convert h1.add h2; ring
-- end

-- lemma has_deriv_at_bary' : has_deriv_at (λ z : ℂ, (1 - t) • z₀ + t • z) t z :=
-- by simpa using (has_deriv_at_const z ((1 - t) • z₀)).add ((has_deriv_at_id z).const_smul t)

-- lemma star_convex.bary (hU : star_convex ℝ z₀ U) (hz : z ∈ U) :
--   maps_to (λ t : ℝ, (1 - t) • z₀ + t • z) (Icc 0 1) U :=
-- λ t ht, hU.segment_subset hz (mem_segment ht)

-- noncomputable def primitive (f : ℂ → ℂ) (z₀ z : ℂ) : ℂ :=
--   (z - z₀) * ∫ t in 0..1, f ((1 - t) • z₀ + t • z)

-- -- lemma primitive_eq_curvint : primitive f z₀ z = curvint 0 1 f (λ t, (1 - t) • z₀ + t • z) :=
-- -- by simpa only [curvint, has_deriv_at_bary.deriv]
-- --   using (interval_integral.integral_const_mul _ _).symm

-- lemma differentiable_on.exists_primitive (f_holo : differentiable_on ℂ f U)
--   (hU : star_convex ℝ z₀ U) (hU' : is_open U) ⦃z : ℂ⦄ (hz : z ∈ U) :
--   has_deriv_at (primitive f z₀) (f z) z :=
-- begin
--   let φ : ℂ → ℝ → ℂ := λ z t, f ((1 - t) • z₀ + t • z),
--   let ψ : ℂ → ℝ → ℂ := λ z t, t • deriv f ((1 - t) • z₀ + t • z),
--   let I : set ℝ := Icc 0 1,

--   have f_cont : continuous_on f U := f_holo.continuous_on,
--   have f_deri : ∀ ⦃z⦄ (hz : z ∈ U), has_deriv_at f (deriv f z) z,
--     from λ z hz, f_holo.has_deriv_at (hU'.mem_nhds hz),
--   have f_cder : continuous_on (deriv f) U := (f_holo.analytic_on hU').deriv.continuous_on,

--   have φ_cont : ∀ ⦃z⦄, z ∈ U → continuous_on (φ z) I,
--     from λ z hz, f_cont.comp continuous_bary.continuous_on (hU.bary hz),
--   have φ_diff : ∀ ⦃t⦄, t ∈ I → differentiable_on ℂ (λ w, φ w t) U,
--     from λ t ht, f_holo.comp differentiable_bary.differentiable_on (λ z hz, hU.bary hz ht),
--   have φ_derz : ∀ ⦃z⦄ (hz : z ∈ U) ⦃t⦄ (ht : t ∈ I), has_deriv_at (λ x, φ x t) (ψ z t) z,
--     from λ z hz t ht, by simpa [φ, ψ, mul_comm] using
--       (f_deri (hU.bary hz ht)).comp z has_deriv_at_bary',
--   have φ_dert : ∀ ⦃t⦄ (ht : t ∈ I), has_deriv_at (φ z) ((z - z₀) * deriv f ((1 - t) • z₀ + t • z)) t,
--     from λ t ht, by simpa [φ, mul_comm] using (f_deri (hU.bary hz ht)).comp t has_deriv_at_bary,
--   have ψ_cont : continuous_on (ψ z) I,
--     from continuous_on_id.smul (f_cder.comp continuous_bary.continuous_on (hU.bary hz)),

--   have step1 : has_deriv_at (λ z, ∫ t in 0..1, φ z t) (∫ t in 0..1, ψ z t) z,
--   by {
--     obtain ⟨δ, δ_pos, K_subs⟩ :=
--       isCompact_segment.exists_cthickening_subset_open hU' (hU.segment_subset hz),
--     set K := cthickening δ (segment ℝ z₀ z),
--     have hz₀ : z₀ ∈ K := self_subset_cthickening _ ⟨1, 0, zero_le_one, le_rfl, by ring, by simp⟩,
--     have K_cpct : is_compact K := is_compact_of_is_closed_bounded is_closed_cthickening
--       isCompact_segment.bounded.cthickening,
--     have K_conv : convex ℝ K := (convex_segment _ _).cthickening _,
--     have K_ball : ball z δ ⊆ K := ball_subset_closed_ball.trans
--       (closed_ball_subset_cthickening (right_mem_segment _ _ _) δ),
--     obtain ⟨C, hC⟩ := K_cpct.exists_bound_of_continuous_on (f_cder.mono K_subs),
--     have C_nonneg : 0 ≤ C := (norm_nonneg _).trans (hC z₀ hz₀),

--     have key : ∀ ⦃t⦄ (ht : t ∈ I), lipschitz_on_with (real.nnabs C) (λ x, φ x t) K,
--       by { refine λ t ht, lipschitz_on_with_iff_norm_sub_le.mpr (λ x hx y hy, _),
--         refine K_conv.norm_image_sub_le_of_norm_deriv_le (λ w hw, _) _ hy hx,
--         { exact (φ_diff ht).differentiable_at (hU'.mem_nhds (K_subs hw)) },
--         { rintro w hw,
--           have h := (φ_derz (K_subs hw) ht).deriv,
--           have h_bary : (1 - t) • z₀ + t • w ∈ K := (K_conv.star_convex hz₀).bary hw ht,
--           have f_bary := hC _ h_bary,
--           have ht' : |t| ≤ 1 := by { rw [abs_le]; split; linarith [ht.1, ht.2] },
--           simpa [h, ψ, norm_nonneg, abs_of_nonneg C_nonneg] using mul_le_mul ht' f_bary } },

--     apply has_deriv_at_integral_of_continuous_of_lip zero_le_one δ_pos,
--     { exact eventually_of_mem (hU'.mem_nhds hz) φ_cont },
--     { exact λ t ht, φ_derz hz (Ioc_subset_Icc_self ht) },
--     { exact λ t ht, (key (Ioc_subset_Icc_self ht)).mono K_ball },
--     { exact ψ_cont.mono Ioc_subset_Icc_self } },

--   have step2 : (∫ t in 0..1, φ z t) + (z - z₀) * (∫ t in 0..1, ψ z t) = f z,
--     by { let g : ℝ → ℂ := λ t, t • φ z t,
--       let h : ℝ → ℂ := λ t, φ z t + (z - z₀) * ψ z t,

--       have g_cont : continuous_on g I := continuous_on_id.smul (φ_cont hz),
--       have g_dert : ∀ t ∈ Ioo (0:ℝ) 1, has_deriv_at g (h t) t,
--         by { rintro t ht,
--           convert (has_deriv_at_id t).smul (φ_dert (Ioo_subset_Icc_self ht)),
--           simp [h, add_comm] },
--       have h_intg : interval_integrable h volume 0 1,
--         by { apply continuous_on.interval_integrable,
--           simp only [interval, min_eq_left, zero_le_one, max_eq_right],
--           have := (φ_cont hz).add (continuous_on_const.mul ψ_cont),
--           convert this; simp },

--       convert ← integral_eq_sub_of_has_deriv_at_of_le zero_le_one g_cont g_dert h_intg,

--       { simp only [h],
--         rw [interval_integral.integral_add],
--         { simp only [←mul_assoc, mul_comm _ z, complex.real_smul, add_right_inj,
--             integral_const_mul, integral_const_mul, add_right_inj] },
--         { apply continuous_on.interval_integrable, convert φ_cont hz, simp [interval] },
--         { apply continuous_on.interval_integrable, refine continuous_on_const.mul _,
--           simp [interval, ψ_cont] } },
--       { simp [g, φ, - complex.real_smul] } },

--   have : has_deriv_at (primitive f z₀) ((∫ t in 0..1, φ z t) + (z - z₀) * ∫ t in 0..1, ψ z t) z,
--     by simpa using ((has_deriv_at_id z).sub (has_deriv_at_const z z₀)).mul step1,
--   exact step2 ▸ this
-- end
