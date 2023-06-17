import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Real Complex Function TopologicalSpace Filter Topology Metric MeasureTheory Nat

-- open complex set function metric interval_integral
-- open_locale real topological_space

noncomputable def cindex (z₀ : ℂ) (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ z in C(z₀, r), deriv f z / f z

section basic

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {p : FormalMultilinearSeries ℂ ℂ E}

lemma DifferentiableOn.deriv {f : ℂ → E} (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) :
    DifferentiableOn ℂ (deriv f) U :=
  (hf.analyticOn hU).deriv.differentiableOn

lemma HasFPowerSeriesAt.eventually_differentiable_at (hp : HasFPowerSeriesAt f p z₀) :
    ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ f z := by
  let ⟨r, hp⟩ := hp
  exact hp.differentiableOn.eventually_differentiableAt (EMetric.ball_mem_nhds _ hp.r_pos)

end basic

section circle_integral

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E}

lemma ContinuousOn.interval_integrable' (hf : ContinuousOn f (sphere c r)) (hr : 0 ≤ r) :
    IntervalIntegrable (λ x => (circleMap 0 r x * I) • f (circleMap c r x)) MeasureSpace.volume 0 (2 * π) := by
  apply Continuous.intervalIntegrable
  apply ((continuous_circleMap 0 r).mul continuous_const).smul
  exact hf.comp_continuous (continuous_circleMap c r) (circleMap_mem_sphere _ hr)

lemma circleIntegral.add (hr : 0 ≤ r) (hf : ContinuousOn f (sphere c r)) (hg : ContinuousOn g (sphere c r)) :
    (∮ z in C(c, r), f z + g z) = (∮ z in C(c, r), f z) + (∮ z in C(c, r), g z) := by
  simp [circleIntegral, smul_add, integral_add, ContinuousOn.interval_integrable', *]

lemma circleIntegral.sub (hr : 0 ≤ r) (hf : ContinuousOn f (sphere c r)) (hg : ContinuousOn g (sphere c r)) :
    (∮ z in C(c, r), f z - g z) = (∮ z in C(c, r), f z) - (∮ z in C(c, r), g z) := by
  simp [circleIntegral, smul_sub, integral_sub, ContinuousOn.interval_integrable', *]

lemma circle_integral_eq_zero (hU : IsOpen U) (hr : 0 < r) (hcr : closedBall c r ⊆ U)
      (f_hol : DifferentiableOn ℂ f U) :
    (∮ z in C(c, r), f z) = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
    (f_hol.continuousOn.mono hcr)
    (λ _ hz => f_hol.differentiableAt (hU.mem_nhds (hcr (ball_subset_closedBall (Set.diff_subset _ _ hz)))))

lemma circle_integral_sub_center_inv_smul {v : E} (hr : 0 < r) :
    (∮ z in C(c, r), (z - c)⁻¹ • v) = (2 * π * I : ℂ) • v := by
  simp [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hr)]

end circle_integral

section dslope

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E}
  {p : FormalMultilinearSeries ℂ ℂ E}

lemma DifferentiableOn.iterate_dslope (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hc : c ∈ U) :
    DifferentiableOn ℂ (iterate (swap dslope c) n f) U := by
  induction n generalizing f
  case zero => exact hf
  case succ n_ih => exact n_ih ((differentiableOn_dslope (hU.mem_nhds hc)).mpr hf)

lemma HasFPowerSeriesAt.dslope_order_eventually_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, iterate (swap dslope z₀) p.order f z ≠ 0 := by
  refine ContinuousAt.eventually_ne ?h (hp.iterate_dslope_fslope_ne_zero h)
  obtain ⟨r, hf⟩ := hp
  have hr : 0 < r := hf.r_pos
  refine ContinuousOn.continuousAt ?h1 (EMetric.ball_mem_nhds _ hr)
  have hh : DifferentiableOn ℂ (iterate (swap dslope z₀) p.order f) (EMetric.ball z₀ r) :=
    DifferentiableOn.iterate_dslope hf.differentiableOn EMetric.isOpen_ball (EMetric.mem_ball_self hr)
  exact hh.continuousOn

end dslope

variable {f g : ℂ → ℂ} {p : FormalMultilinearSeries ℂ ℂ ℂ}

lemma deriv_div_self_eq_div_add_deriv_div_self (hg : DifferentiableAt ℂ g z) (hgz : g z ≠ 0)
    (hfg : f =ᶠ[𝓝 z] λ w => HPow.hPow (w - z₀) n * g w) (hz : z ≠ z₀) :
    deriv f z / f z = n / (z - z₀) + deriv g z / g z := by
  have h1 : DifferentiableAt ℂ (λ y => HPow.hPow (y - z₀) n) z :=
    ((differentiable_id'.sub_const z₀).pow n).differentiableAt
  have h4 : DifferentiableAt ℂ (λ y => y - z₀) z := (differentiable_id'.sub_const z₀).differentiableAt
  have h5 : deriv (fun y => y - z₀) z = 1 := by
    simp only [deriv_sub_const, deriv_id'']
  simp [hfg.deriv_eq, hfg.self_of_nhds, deriv_mul h1 hg, _root_.add_div, deriv_pow'' n h4, deriv_sub_const, h5]
  cases n
  case zero => simp
  case succ n =>
    field_simp [_root_.pow_succ, sub_ne_zero.mpr hz]
    ring

-- begin
--   rw [hfg.deriv_eq, hfg.self_of_nhds, deriv_mul h1 hg, add_div, mul_div_mul_right _ _ hgz,
--     mul_div_mul_left _ _ h3, add_left_inj],
--   simp only [deriv_pow'', differentiable_at_sub_const_iff, differentiable_at_id', deriv_sub,
--     differentiable_at_const, deriv_id'', deriv_const', sub_zero, mul_one],
--   cases n,
--   { simp only [algebra_map.coe_zero, zero_mul, zero_div] },
--   { field_simp [pow_succ]; ring }
-- end

-- lemma eventually_deriv_div_self_eq (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
--   let g := (swap dslope z₀^[p.order]) f in
--   ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → deriv f z / f z = p.order / (z - z₀) + deriv g z / g z :=
-- begin
--   intro g,
--   obtain ⟨r, hp'⟩ := id hp,
--   have lh1 := (hp.has_fpower_series_iterate_dslope_fslope p.order).eventually_differentiable_at,
--   have lh2 := hp.dslope_order_eventually_ne_zero h,
--   have lh3 := eventually_eventually_nhds.mpr hp.eq_pow_order_mul_iterate_dslope,
--   filter_upwards [lh1, lh2, lh3] using λ z, deriv_div_self_eq_div_add_deriv_div_self
-- end

-- lemma differentiable_on.cont_diff_on {U : set ℂ} (hf : differentiable_on ℂ f U) (hU : IsOpen U) :
--   cont_diff_on ℂ ⊤ f U :=
-- (hf.analytic_on hU).cont_diff_on

-- lemma cindex_eq_zero (hU : IsOpen U) (hr : 0 < r) (hcr : closed_ball c r ⊆ U)
--   (f_hol : differentiable_on ℂ f U) (hf : ∀ z ∈ closed_ball c r, f z ≠ 0) :
--   cindex c r f = 0 :=
-- begin
--   obtain ⟨V, h1, h2, h3, h4⟩ : ∃ V ⊆ U, IsOpen V ∧ closed_ball c r ⊆ V ∧ ∀ z ∈ V, f z ≠ 0,
--   { set s := {z ∈ U | f z ≠ 0},
--     have e1 : is_compact (closed_ball c r) := is_compact_closed_ball _ _,
--     have e2 : IsOpen s,
--       by convert f_hol.continuous_on.preimage_open_of_open hU IsOpen_compl_singleton,
--     have e3 : closed_ball c r ⊆ s := λ z hz, ⟨hcr hz, hf z hz⟩,
--     obtain ⟨δ, e4, e5⟩ := e1.exists_thickening_subset_open e2 e3,
--     refine ⟨thickening δ (closed_ball c r), _, IsOpen_thickening, self_subset_thickening e4 _, _⟩,
--     { exact (e5.trans $ sep_subset _ _) },
--     { exact λ z hz, (e5 hz).2 } },
--   simp [cindex, circle_integral_eq_zero h2 hr h3 (((f_hol.mono h1).deriv h2).div (f_hol.mono h1) h4)]
-- end

-- -- TODO: off-center using `integral_sub_inv_of_mem_ball`

-- lemma cindex_eq_order_aux (hU : IsOpen U) (hr : 0 < r) (h0 : closed_ball z₀ r ⊆ U)
--   (h1 : differentiable_on ℂ g U) (h2 : ∀ z ∈ closed_ball z₀ r, g z ≠ 0)
--   (h3 : ∀ {z}, z ∈ sphere z₀ r → deriv f z / f z = c / (z - z₀) + deriv g z / g z) :
--   cindex z₀ r f = c :=
-- begin
--   have e1 : closed_ball z₀ r ⊆ U := h0,
--   have e2 : sphere z₀ r ⊆ U := sphere_subset_closed_ball.trans e1,
--   have e4 : ∮ z in C(z₀,r), deriv f z / f z = ∮ z in C(z₀,r), c / (z - z₀) + deriv g z / g z,
--   { refine circle_integral.integral_congr hr.le (λ z hz, _),
--     exact h3 hz },
--   have e5 : ∮ z in C(z₀,r), c / (z - z₀) + deriv g z / g z =
--     (∮ z in C(z₀, r), c / (z - z₀)) + (∮ z in C(z₀, r), deriv g z / g z),
--   { refine circle_integral.add hr.le _ _,
--     { refine continuous_on.div continuous_on_const (continuous_on_id.sub continuous_on_const) _,
--       exact λ z hz, sub_ne_zero.mpr (ne_of_mem_sphere hz hr.ne.symm) },
--     { refine continuous_on.div _ (h1.continuous_on.mono e2) (λ z hz, h2 _ (sphere_subset_closed_ball hz)),
--       have := (h1.cont_diff_on hU).continuous_on_deriv_of_open hU le_top,
--       exact this.mono e2 } },
--   have e6 : ∮ z in C(z₀, r), deriv g z / g z = 0,
--   { have := cindex_eq_zero hU hr e1 h1 h2,
--     simpa [cindex, real.pi_ne_zero, I_ne_zero] using this },
--   have e7 : ∮ z in C(z₀, r), c / (z - z₀) = 2 * π * I * c,
--   { have := @circle_integral_sub_center_inv_smul ℂ _ _ _ _ _ _ hr,
--     simpa [div_eq_mul_inv, mul_comm _ _⁻¹] using this },
--   field_simp [cindex, e4, e5, e6, e7, real.pi_ne_zero, I_ne_zero, two_ne_zero]; ring
-- end

-- lemma exists_cindex_eq_order' (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
--   ∃ R > (0 : ℝ), ∀ r ∈ Ioo 0 R, cindex z₀ r f = p.order :=
-- begin
--   let g : ℂ → ℂ := (swap dslope z₀^[p.order]) f,
--   have lh1 : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hp.dslope_order_eventually_ne_zero h,
--   have lh2 : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ → deriv f z / f z = p.order / (z - z₀) + deriv g z / g z,
--     from eventually_deriv_div_self_eq hp h,
--   have lh3 : ∀ᶠ z in 𝓝 z₀, differentiable_at ℂ g z,
--     from (hp.has_fpower_series_iterate_dslope_fslope p.order).eventually_differentiable_at,
--   obtain ⟨R, hR₁, hh⟩ := metric.mem_nhds_iff.mp (lh1.and (lh2.and lh3)),
--   refine ⟨R, hR₁, λ r hr, _⟩,
--   refine cindex_eq_order_aux IsOpen_ball hr.1 (closed_ball_subset_ball hr.2)
--     (λ z hz, (hh hz).2.2.differentiable_within_at)
--     (λ z hz, (hh (closed_ball_subset_ball hr.2 hz)).1) (λ z hz, _),
--   refine (hh (sphere_subset_closed_ball.trans (closed_ball_subset_ball hr.2) hz)).2.1 _,
--   exact ne_of_mem_sphere hz hr.1.ne.symm,
-- end

-- lemma exists_cindex_eq_order (hp : HasFPowerSeriesAt f p z₀) :
--   ∃ R > (0 : ℝ), ∀ r ∈ Ioo 0 R, cindex z₀ r f = p.order :=
-- begin
--   by_cases p = 0, swap, exact exists_cindex_eq_order' hp h,
--   subst_vars,
--   obtain ⟨R, hR, hf⟩ := metric.eventually_nhds_iff.mp (hp.locally_zero_iff.mpr rfl),
--   refine ⟨R, hR, λ r hr, _⟩,
--   have : eq_on (λ z, deriv f z / f z) 0 (sphere z₀ r),
--     from λ z hz, by simp [hf (show dist z z₀ < R, from hz.symm ▸hr.2)],
--   simp [cindex, circle_integral, circle_integral.integral_congr hr.1.le this]
-- end

-- lemma cindex_eventually_eq_order (hp : HasFPowerSeriesAt f p z₀) :
--   ∀ᶠ r in 𝓝[>] 0, cindex z₀ r f = p.order :=
-- begin
--   rw [eventually_nhds_within_iff, metric.eventually_nhds_iff],
--   obtain ⟨R, hR, hf⟩ := exists_cindex_eq_order hp,
--   exact ⟨R, hR, λ r hr1 hr2, hf r ⟨hr2, by simpa using lt_of_abs_lt hr1⟩⟩
-- end