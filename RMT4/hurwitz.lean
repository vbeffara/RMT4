-- import analysis.analytic.isolated_zeros
-- import analysis.complex.cauchy_integral
-- import analysis.complex.removable_singularity
-- import measure_theory.integral.circle_integral
-- import topology.uniform_space.uniform_convergence
-- import analysis.complex.locally_uniform_limit

import RMT4.uniform
import RMT4.cindex

open Filter Topology Set Metric Uniformity

-- open filter metric complex function set interval_integral
-- open_locale interval nnreal ennreal topological_space big_operators filter uniformity

section filter

variable {P : α → Prop} {p : Filter α} {φ : ℝ → Set α}

lemma mem_iff_eventually_subset (hp : p.HasBasis (λ t : ℝ => 0 < t) φ) (hφ : Monotone φ) :
    s ∈ p ↔ (∀ᶠ t in 𝓝[>] 0, φ t ⊆ s) := by
  rw [(nhdsWithin_hasBasis nhds_basis_closedBall (Ioi (0 : ℝ))).eventually_iff]
  simp_rw [hp.mem_iff, ← exists_prop, mem_inter_iff, mem_closedBall_zero_iff]
  refine exists₂_congr (λ ε hε => ⟨λ h r h' => (hφ (le_of_abs_le h'.1)).trans h,
    λ h => h ⟨Eq.le (abs_eq_self.mpr hε.le), hε⟩⟩)

lemma eventually_nhds_iff_eventually_ball [PseudoMetricSpace α] :
  (∀ᶠ z in 𝓝 z₀, P z) ↔ (∀ᶠ r in 𝓝[>] 0, ∀ z ∈ ball z₀ r, P z) :=
mem_iff_eventually_subset nhds_basis_ball (λ _ _ => ball_subset_ball)

lemma eventually_nhds_iff_eventually_closed_ball [PseudoMetricSpace α] :
  (∀ᶠ z in 𝓝 z₀, P z) ↔ (∀ᶠ r in 𝓝[>] 0, ∀ z ∈ closedBall z₀ r, P z) :=
mem_iff_eventually_subset nhds_basis_closedBall (λ _ _ => closedBall_subset_closedBall)

end filter

section unifops

variable [NormedField 𝕜] {F G : ι → α → 𝕜} {f g : α → 𝕜} {x y : 𝕜} {η η' : ℝ}
-- variables {ι α 𝕜 : Type*} [normed_field 𝕜] {p : filter ι} [ne_bot p] {K s : set α} {m mf mg : ℝ}

lemma dist_inv_le_dist_div (hη : 0 < η) (hη' : 0 < η')
    (hx : x ∉ ball (0 : 𝕜) η) (hy : y ∉ ball (0 : 𝕜) η') :
    dist x⁻¹ y⁻¹ ≤ dist x y / (η * η') := by
  have h1 : x ≠ 0 := by contrapose! hx; simp [hx, hη]
  have h2 : y ≠ 0 := by contrapose! hy; simp [hy, hη']
  simp [dist_eq_norm] at hx hy
  rw [dist_eq_norm, inv_sub_inv h1 h2, norm_div, norm_mul, dist_comm, dist_eq_norm]
  exact div_le_div (norm_nonneg _) le_rfl (mul_pos hη hη') (mul_le_mul hx hy hη'.le (norm_nonneg _))

lemma titi {p q : Filter 𝕜} (hp : p ⊓ 𝓝 0 = ⊥) (hq : q ⊓ 𝓝 0 = ⊥) :
    map (λ x : 𝕜 × 𝕜 => (x.1⁻¹, x.2⁻¹)) (𝓤 𝕜 ⊓ (Filter.prod p q)) ≤ 𝓤 𝕜 := by
  obtain ⟨U, hU, V, hV, hUV⟩ := inf_eq_bot_iff.mp hp
  obtain ⟨U', hU', V', hV', hUV'⟩ := inf_eq_bot_iff.mp hq
  obtain ⟨η, hη, hV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨η', hη', hV'⟩ := Metric.mem_nhds_iff.mp hV'
  have hηη' : 0 < η * η' := mul_pos hη hη'
  intro u hu
  obtain ⟨ε, hε, hu⟩ := mem_uniformity_dist.mp hu
  rw [mem_map_iff_exists_image]
  refine ⟨_, inter_mem_inf (dist_mem_uniformity (mul_pos hε hηη')) (prod_mem_prod hU hU'), ?_⟩
  rintro z ⟨x, ⟨hx1, hx2⟩, rfl⟩
  have hx'1 : x.1 ∉ ball (0 : 𝕜) η :=
    λ h => (Set.nonempty_of_mem (mem_inter hx2.1 (hV h))).ne_empty hUV
  have hx'2 : x.2 ∉ ball (0 : 𝕜) η' :=
    λ h => (Set.nonempty_of_mem (mem_inter hx2.2 (hV' h))).ne_empty hUV'
  refine hu ((dist_inv_le_dist_div hη hη' hx'1 hx'2).trans_lt ?_)
  convert (div_lt_div_right hηη').mpr hx1
  field_simp [hη.lt.ne.symm, hη'.lt.ne.symm]

lemma uniform_continuous_on_inv {s : Set 𝕜} (hs : 𝓟 s ⊓ 𝓝 0 = ⊥) :
    UniformContinuousOn (λ x => x⁻¹) s := by
  simpa only [UniformContinuousOn, Tendsto, ← prod_principal_principal] using titi hs hs

example (hη : 0 < η) : UniformContinuousOn (λ x => x⁻¹) ((ball (0 : 𝕜) η)ᶜ) := by
  apply uniform_continuous_on_inv
  simpa only [inf_comm, inf_principal_eq_bot, compl_compl] using ball_mem_nhds _ hη

lemma TendstoUniformlyOn.inv (hF : TendstoUniformlyOn F f p s) (hf : 𝓟 (f '' s) ⊓ 𝓝 0 = ⊥) :
    TendstoUniformlyOn F⁻¹ f⁻¹ p s := by
  have : 𝓝ᵘ (f '' s) ⊓ 𝓝 0 = ⊥ := by
    rw [inf_comm] at hf ⊢
    exact UniformSpace.nhds_inf_uniform_nhds_eq_bot hf
  have h1 := lemma1 hF
  rw [tendstoUniformlyOn_iff_tendsto] at hF ⊢
  refine (Filter.map_mono (le_inf hF h1)).trans (titi hf this)

-- lemma lxyab {x y a b : 𝕜} : x * a - y * b = (x - y) * a + y * (a - b) := by ring

-- lemma TendstoUniformlyOn.mul_of_le
--   (hF : TendstoUniformlyOn F f p s) (hG : TendstoUniformlyOn G g p s)
--   (hf : ∀ᶠ i in p, ∀ x ∈ s, ‖F i x‖ ≤ mf) (hg : ∀ᶠ i in p, ∀ x ∈ s, ‖G i x‖ ≤ mg) :
--   TendstoUniformlyOn (F * G) (f * g) p s :=
-- begin
--   set Mf : ℝ := |mf| + 1,
--   have hMf : 0 < Mf := by { simp only [Mf], positivity },
--   replace hf : ∀ᶠ i in p, ∀ x ∈ s, ‖F i x‖ ≤ Mf := by filter_upwards [hf] with i hF x hx
--     using (hF x hx).trans ((le_abs_self mf).trans (lt_add_one _).le),
--   set Mg : ℝ := |mg| + 1,
--   have hMg : 0 < Mg := by { simp only [Mg], positivity },
--   replace hg : ∀ᶠ i in p, ∀ x ∈ s, ‖G i x‖ ≤ Mg := by filter_upwards [hg] with i hG x hx
--     using (hG x hx).trans ((le_abs_self mg).trans (lt_add_one _).le),
--   have h1 : ∀ x ∈ s, ‖g x‖ ≤ Mg,
--   { rintro x hx,
--     refine le_of_tendsto ((continuous_norm.tendsto (g x)).comp (hG.tendsto_at hx)) _,
--     filter_upwards [hg] with i hg using hg x hx },
--   simp_rw [Metric.TendstoUniformlyOn_iff, dist_eq_norm] at ⊢ hF hG,
--   rintro ε hε,
--   filter_upwards [hf, hF (ε / (2 * Mg)) (by positivity), hG (ε / (2 * Mf)) (by positivity)]
--     with i hf hF hG x hx,
--   have h2 : ‖(f x - F i x) * g x‖ < ε / 2,
--   { rw [norm_mul],
--     by_cases g x = 0, rw [h], simp, exact half_pos hε,
--     convert mul_lt_mul (hF x hx) (h1 x hx) (norm_pos_iff.mpr h) (by positivity),
--     simp only [div_mul, mul_div_cancel, hMg.ne.symm, ne.def, not_false_iff]},
--   have h3 : ‖F i x * (g x - G i x)‖ < ε / 2,
--   { rw [norm_mul],
--     by_cases F i x = 0, rw [h], simp, exact half_pos hε,
--     convert mul_lt_mul' (hf x hx) (hG x hx) (norm_nonneg _) hMf,
--     field_simp [hMf.ne.symm], ring },
--   simp_rw [pi.mul_apply, lxyab],
--   exact (norm_add_le _ _).trans_lt (add_halves' ε ▸ add_lt_add h2 h3)
-- end

-- lemma TendstoUniformlyOn.mul_of_bound
--   (hF : TendstoUniformlyOn F f p s) (hG : TendstoUniformlyOn G g p s)
--   (hf : ∀ x ∈ s, ‖f x‖ ≤ mf) (hg : ∀ x ∈ s, ‖g x‖ ≤ mg) :
--   TendstoUniformlyOn (F * G) (f * g) p s :=
-- begin
--   have h1 : ∀ᶠ i in p, ∀ x ∈ s, ‖F i x‖ ≤ mf + 1,
--   { simp_rw [Metric.TendstoUniformlyOn_iff, dist_eq_norm] at hF,
--     filter_upwards [hF 1 zero_lt_one] with i hF x hx,
--     have : ‖F i x‖ ≤ ‖f x - F i x‖ + ‖f x‖,
--       by simpa [← norm_neg (F i x - f x)] using norm_add_le (F i x - f x) (f x),
--     linarith [hF x hx, hf x hx] },
--   have h2 : ∀ᶠ i in p, ∀ x ∈ s, ‖G i x‖ ≤ mg + 1,
--   { simp_rw [Metric.TendstoUniformlyOn_iff, dist_eq_norm] at hG,
--     filter_upwards [hG 1 zero_lt_one] with i hG x hx,
--     have : ‖G i x‖ ≤ ‖g x - G i x‖ + ‖g x‖,
--       by simpa [← norm_neg (G i x - g x)] using norm_add_le (G i x - g x) (g x),
--     linarith [hG x hx, hg x hx] },
--   exact hF.mul_of_le hG h1 h2
-- end

-- variables [topological_space α]

-- lemma TendstoUniformlyOn.inv_of_compact (hF : TendstoUniformlyOn F f p K)
--   (hf : continuous_on f K) (hK : is_compact K) (hfz : ∀ x ∈ K, f x ≠ 0) :
--   TendstoUniformlyOn F⁻¹ f⁻¹ p K :=
-- begin
--   refine hF.inv _,
--   rw [inf_comm, inf_principal_eq_bot],
--   exact (hK.image_of_continuous_on hf).is_closed.compl_mem_nhds (λ ⟨z, h1, h2⟩, hfz z h1 h2)
-- end

-- lemma TendstoUniformlyOn.mul_of_compact
--   (hF : TendstoUniformlyOn F f p K) (hG : TendstoUniformlyOn G g p K)
--   (hf : continuous_on f K) (hg : continuous_on g K) (hK : is_compact K) :
--   TendstoUniformlyOn (F * G) (f * g) p K :=
-- begin
--   by_cases h1 : K = ∅,
--   { simpa only [h1] using TendstoUniformlyOn_empty },
--   replace h1 : K.nonempty := set.nonempty_iff_ne_empty.2 h1,
--   have h2 : continuous_on (norm ∘ f) K := continuous_norm.comp_continuous_on hf,
--   have h3 : continuous_on (norm ∘ g) K := continuous_norm.comp_continuous_on hg,
--   obtain ⟨xf, hxf, h4⟩ : ∃ x ∈ K, ∀ y ∈ K, ‖f y‖ ≤ ‖f x‖ := hK.exists_forall_ge h1 h2,
--   obtain ⟨xg, hxg, h5⟩ : ∃ x ∈ K, ∀ y ∈ K, ‖g y‖ ≤ ‖g x‖ := hK.exists_forall_ge h1 h3,
--   exact hF.mul_of_bound hG h4 h5
-- end

-- lemma TendstoUniformlyOn.div_of_compact
--   (hF : TendstoUniformlyOn F f p K) (hG : TendstoUniformlyOn G g p K)
--   (hf : continuous_on f K) (hg : continuous_on g K) (hgK : ∀ z ∈ K, g z ≠ 0) (hK : is_compact K) :
--   TendstoUniformlyOn (F / G) (f / g) p K :=
-- by simpa [div_eq_mul_inv] using hF.mul_of_compact (hG.inv_of_compact hg hK hgK) hf (hg.inv₀ hgK) hK

end unifops

-- variables {ι : Type*} {F : ι → ℂ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {p : filter ι} [ne_bot p]
--   {U s : set ℂ} {r : ℝ}

-- lemma filter.eventually.exists' {P : ℝ → Prop} {t₀} (h : ∀ᶠ t in 𝓝[>] t₀, P t) :
--   ∃ t > t₀, P t :=
-- by simpa [and_comm, exists_prop] using (frequently_nhds_within_iff.mp h.frequently).exists

-- lemma order_eq_zero_iff {p : formal_multilinear_series ℂ ℂ ℂ}
--   (hp : has_fpower_series_at f p z₀) (hz₀ : f z₀ = 0) :
--   p.order = 0 ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 :=
-- begin
--   rw [hp.locally_zero_iff],
--   by_cases p = 0, { subst p, simp },
--   simp [formal_multilinear_series.order_eq_zero_iff h, h],
--   ext1,
--   simp [hp.coeff_zero, hz₀],
-- end

-- lemma order_pos_iff {p : formal_multilinear_series ℂ ℂ ℂ}
--   (hp : has_fpower_series_at f p z₀) (hz₀ : f z₀ = 0) :
--   0 < p.order ↔ ∃ᶠ z in 𝓝 z₀, f z ≠ 0 :=
-- by simp [pos_iff_ne_zero, (order_eq_zero_iff hp hz₀).not]

-- lemma cindex_pos (h1 : analytic_at ℂ f z₀) (h2 : f z₀ = 0) (h3 : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) :
--   ∀ᶠ r in 𝓝[>] 0, cindex z₀ r f ≠ 0 :=
-- begin
--   rcases h1 with ⟨p, hp⟩,
--   filter_upwards [cindex_eventually_eq_order hp] with r h,
--   simpa [cindex, h, real.pi_ne_zero, I_ne_zero, order_eq_zero_iff hp h2] using
--     h3.frequently.filter_mono nhds_within_le_nhds
-- end

-- -- TODO: this can be generalized a lot
-- lemma hurwitz2_1 {K : set ℂ} (hK : is_compact K) (F_conv : TendstoUniformlyOn F f p K)
--   (hf1 : continuous_on f K) (hf2 : ∀ z ∈ K, f z ≠ 0) :
--   ∀ᶠ n in p, ∀ z ∈ K, F n z ≠ 0 :=
-- begin
--   by_cases (K = ∅),
--   { simp [h] },
--   { obtain ⟨z₀, h1, h2⟩ : ∃ z₀ ∈ K, ∀ z ∈ K, ‖f z₀‖ ≤ ‖f z‖,
--       from hK.exists_forall_le (nonempty_iff_ne_empty.2 h) (continuous_norm.comp_continuous_on hf1),
--     have h3 := TendstoUniformlyOn_iff.1 F_conv (‖f z₀‖) (norm_pos_iff.2 (hf2 _ h1)),
--     filter_upwards [h3] with n hn z hz h,
--     specialize hn z hz,
--     specialize h2 z hz,
--     simp only [h, norm_eq_abs, dist_zero_right] at hn h2,
--     linarith },
-- end

-- lemma TendstoUniformlyOn.tendsto_circle_integral
--   [p.ne_bot]
--   (hr : 0 < r)
--   (F_cont : ∀ᶠ n in p, continuous_on (F n) (sphere z₀ r))
--   (F_conv : TendstoUniformlyOn F f p (sphere z₀ r))
--   :
--   filter.tendsto (λ i, ∮ z in C(z₀, r), F i z) p (𝓝 ∮ z in C(z₀, r), f z)
--   :=
-- begin
--   have f_cont : continuous_on f (sphere z₀ r) := F_conv.continuous_on F_cont,
--   rw [Metric.tendsto_nhds],
--   rintro ε hε,
--   have twopir_ne_zero : 2 * real.pi * r ≠ 0 := by simp [real.pi_ne_zero, hr.ne.symm],
--   have : (2 * real.pi * r)⁻¹ * ε > 0,
--     from mul_pos (inv_pos.mpr (mul_pos (mul_pos two_pos real.pi_pos) hr)) hε.lt,
--   filter_upwards [TendstoUniformlyOn_iff.mp F_conv ((2 * real.pi * r)⁻¹ * ε) this, F_cont] with n h h',
--   simp_rw [dist_comm (f _) _, complex.dist_eq, ← norm_eq_abs] at h,
--   rw [complex.dist_eq, ← circle_integral.sub hr.le h' f_cont, ← norm_eq_abs],
--   have : ∃ (x ∈ sphere z₀ r), ‖F n x - f x‖ < (2 * real.pi * r)⁻¹ * ε := by {
--     have : z₀ + r ∈ sphere z₀ r := by simp [hr.le, real.norm_eq_abs],
--     exact ⟨z₀ + r, this, h _ this⟩ },
--   convert circle_integral.norm_integral_lt_of_norm_le_const_of_lt hr
--     (h'.sub f_cont) (λ z hz, (h z hz).le) this,
--   field_simp [hr.ne, real.pi_ne_zero, two_ne_zero]; ring
-- end

-- lemma hurwitz2_2 [p.ne_bot] (hU : is_open U) (hF : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (hf : tendsto_locally_uniformly_on F f p U) (hr1 : 0 < r) (hr2 : sphere z₀ r ⊆ U)
--   (hf1 : ∀ (z : ℂ), z ∈ sphere z₀ r → f z ≠ 0) :
--   tendsto (cindex z₀ r ∘ F) p (𝓝 (cindex z₀ r f)) :=
-- begin
--   have H1 : is_compact (sphere z₀ r) := is_compact_sphere z₀ r,
--   have H2 : TendstoUniformlyOn F f p (sphere z₀ r),
--     from (tendsto_locally_uniformly_on_iff_forall_is_compact hU).1 hf _ hr2 H1,
--   have H3 : differentiable_on ℂ f U := hf.differentiable_on hF hU,
--   have H4 : continuous_on (λ (z : ℂ), f z) (sphere z₀ r) := H3.continuous_on.mono hr2,
--   have H5 : ∀ᶠ n in p, continuous_on (F n) (sphere z₀ r),
--   { filter_upwards [hF] with n h using h.continuous_on.mono hr2 },
--   have H6 : ∀ᶠ n in p, continuous_on (deriv (F n)) (sphere z₀ r),
--   { filter_upwards [hF] with n h using (h.deriv hU).continuous_on.mono hr2 },
--   have H7 : TendstoUniformlyOn (deriv ∘ F) (deriv f) p (sphere z₀ r),
--     from (tendsto_locally_uniformly_on_iff_forall_is_compact hU).1 (hf.deriv hF hU) _ hr2 H1,
--   have H8 : continuous_on (λ (z : ℂ), deriv f z) (sphere z₀ r),
--     from (H3.deriv hU).continuous_on.mono hr2,
--   change tendsto (λ n, cindex z₀ r (F n)) p (𝓝 (cindex z₀ r f)),
--   refine tendsto.const_mul _ (TendstoUniformlyOn.tendsto_circle_integral hr1 _ _),
--   { filter_upwards [hurwitz2_1 H1 H2 H4 hf1, H6, H5] with n hn H6 H5 using continuous_on.div H6 H5 hn },
--   { exact TendstoUniformlyOn.div_of_compact H7 H2 H8 H4 hf1 H1 }
-- end

-- lemma hurwitz2
--   (hU : is_open U)
--   (hF : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (hf : tendsto_locally_uniformly_on F f p U)
--   (hr1 : 0 < r)
--   (hr2 : closed_ball z₀ r ⊆ U)
--   (hf1 : ∀ z ∈ sphere z₀ r, f z ≠ 0)
--   (hf2 : cindex z₀ r f ≠ 0)
--   :
--   ∀ᶠ n in p, ∃ z ∈ ball z₀ r, F n z = 0
--   :=
-- begin
--   by_cases p.ne_bot, swap, { simp at h, simp [h] }, haveI : p.ne_bot := h,
--   have H1 : is_compact (sphere z₀ r) := is_compact_sphere z₀ r,
--   have H2 : sphere z₀ r ⊆ U := sphere_subset_closed_ball.trans hr2,
--   have H3 : TendstoUniformlyOn F f p (sphere z₀ r),
--     from (tendsto_locally_uniformly_on_iff_forall_is_compact hU).1 hf _ H2 H1,
--   have H4 : continuous_on (λ (z : ℂ), f z) (sphere z₀ r),
--     from (hf.differentiable_on hF hU).continuous_on.mono H2,
--   have H5 : ∀ᶠ n in p, ∀ z ∈ sphere z₀ r, F n z ≠ 0 := hurwitz2_1 H1 H3 H4 hf1,
--   filter_upwards [(hurwitz2_2 hU hF hf hr1 H2 hf1).eventually_ne hf2, H5, hF] with n h h' hF,
--   contrapose! h,
--   have : ∀ (z : ℂ), z ∈ ball z₀ r ∪ sphere z₀ r → F n z ≠ 0 := λ z hz, hz.cases_on (h z) (h' z),
--   refine cindex_eq_zero hU hr1 hr2 hF (by rwa [← ball_union_sphere])
-- end

-- lemma hurwitz3
--   (hU : is_open U)
--   (hF : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (hf : tendsto_locally_uniformly_on F f p U)
--   (hz₀ : z₀ ∈ U)
--   (h1 : f z₀ = 0)
--   (h2 : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0)
--   (hs : s ∈ 𝓝 z₀)
--   :
--   ∀ᶠ n in p, ∃ z ∈ s, F n z = 0
--   :=
-- begin
--   have H1 := (hf.differentiable_on hF hU).analytic_at (hU.mem_nhds hz₀),
--   have H5 := cindex_pos H1 h1 h2,
--   rw [eventually_nhds_within_iff] at h2,
--   have h3 := eventually_nhds_iff_eventually_closed_ball.1 h2,
--   have h4 : ∀ᶠ r in 𝓝[>] 0, closed_ball z₀ r ⊆ U :=
--     (eventually_closed_ball_subset (hU.mem_nhds hz₀)).filter_mono nhds_within_le_nhds,
--   have h4' : ∀ᶠ r in 𝓝[>] 0, closed_ball z₀ r ⊆ s :=
--     (eventually_closed_ball_subset hs).filter_mono nhds_within_le_nhds,
--   obtain ⟨r, hr, h5, h6, h7, h9⟩ := (h3.and (h4.and (H5.and h4'))).exists',
--   have h8 : ∀ z ∈ sphere z₀ r, f z ≠ 0,
--   { exact λ z hz, h5 z (sphere_subset_closed_ball hz) (ne_of_mem_sphere hz hr.lt.ne.symm) },
--   refine (hurwitz2 hU hF hf hr h6 h8 h7).mono _,
--   rintro n ⟨z, hz, hFnz⟩,
--   refine ⟨z, h9 (ball_subset_closed_ball hz), hFnz⟩,
-- end

-- ------------------

-- theorem local_hurwitz
--   (hU : is_open U)
--   (F_holo : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (F_noz : ∀ n, ∀ z ∈ U, F n z ≠ 0)
--   (F_conv : tendsto_locally_uniformly_on F f p U)
--   (hz₀ : z₀ ∈ U)
--   (hfz₀ : f z₀ = 0)
--   :
--   ∀ᶠ z in 𝓝 z₀, f z = 0 :=
-- begin
--   have H1 := (F_conv.differentiable_on F_holo hU).analytic_at (hU.mem_nhds hz₀),
--   cases H1.eventually_eq_zero_or_eventually_ne_zero, assumption,
--   obtain ⟨pf, hp⟩ : analytic_at ℂ f z₀ := H1,
--   by_contra' hh, simp at hh,
--   have h1 := (order_pos_iff hp hfz₀).2 hh,
--   obtain ⟨r, h1, h2, h3, h4⟩ : ∃ r > 0, (closed_ball z₀ r ⊆ U) ∧ (∀ z ∈ sphere z₀ r, f z ≠ 0) ∧
--     (cindex z₀ r f ≠ 0),
--   { rw [eventually_nhds_within_iff, eventually_nhds_iff_eventually_closed_ball] at h,
--     have h4 := cindex_eventually_eq_order hp,
--     have h5 : ∀ᶠ r in 𝓝[>] 0, closed_ball z₀ r ⊆ U :=
--       (eventually_closed_ball_subset (hU.mem_nhds hz₀)).filter_mono nhds_within_le_nhds,
--     obtain ⟨r, h6, h7, h8, h9⟩ := (h.and (h4.and h5)).exists',
--     refine ⟨r, h6, h9, _, _⟩,
--     { exact λ z hz, h7 z (sphere_subset_closed_ball hz) (ne_of_mem_sphere hz h6.lt.ne.symm) },
--     { simp [h8, h1.ne.symm] } },
--   obtain ⟨n, z, h5, h6⟩ := (hurwitz2 hU F_holo F_conv h1 h2 h3 h4).exists,
--   cases F_noz n z (h2 (ball_subset_closed_ball (mem_ball.mpr h5))) h6
-- end

-- theorem hurwitz
--   (hU : is_open U)
--   (hU' : is_preconnected U)
--   (F_holo : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (F_noz : ∀ n, ∀ z ∈ U, F n z ≠ 0)
--   (F_conv : tendsto_locally_uniformly_on F f p U)
--   (hz₀ : z₀ ∈ U)
--   (hfz₀ : f z₀ = 0)
--   :
--   ∀ z ∈ U, f z = 0 :=
-- begin
--   have := local_hurwitz hU F_holo F_noz F_conv hz₀ hfz₀,
--   have h1 : differentiable_on ℂ f U := F_conv.differentiable_on F_holo hU,
--   have h2 := h1.analytic_on hU,
--   exact h2.eq_on_zero_of_preconnected_of_eventually_eq_zero hU' hz₀ this,
-- end

-- theorem hurwitz'
--   (hU : is_open U)
--   (hU' : is_preconnected U)
--   (F_holo : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (F_noz : ∀ n, ∀ z ∈ U, F n z ≠ 0)
--   (F_conv : tendsto_locally_uniformly_on F f p U)
--   :
--   (∀ z ∈ U, f z ≠ 0) ∨ (∀ z ∈ U, f z = 0) :=
-- begin
--   refine or_iff_not_imp_left.mpr (λ h, _),
--   push_neg at h,
--   obtain ⟨z₀, h1, h2⟩ := h,
--   exact hurwitz hU hU' F_holo F_noz F_conv h1 h2
-- end

-- lemma hurwitz_1 (hU : is_open U) (hU' : is_preconnected U) (hf : differentiable_on ℂ f U) :
--   (eq_on f 0 U) ∨ (∀ z₀ ∈ U, ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) :=
-- begin
--   refine or_iff_not_imp_right.2 (λ h, _),
--   obtain ⟨z₀, h1, h2⟩ : ∃ z₀ ∈ U, ∃ᶠ z in 𝓝[≠] z₀, f z = 0 := by simpa only [not_forall] using h,
--   exact (hf.analytic_on hU).eq_on_zero_of_preconnected_of_frequently_eq_zero hU' h1 h2,
-- end

-- lemma hurwitz4 {ι α β γ : Type*} [topological_space α] [uniform_space β] [uniform_space γ]
--   {F : ι → α → β} {f : α → β} {p : filter ι} {φ : β → γ} {U : set α}
--   (hf : tendsto_locally_uniformly_on F f p U) (hφ : uniform_continuous φ) :
--   tendsto_locally_uniformly_on (λ n, φ ∘ (F n)) (φ ∘ f) p U :=
-- λ u hu z hz, hf _ (mem_map.1 (hφ hu)) z hz

-- theorem hurwitz_inj
--   (hU : is_open U)
--   (hU' : is_preconnected U)
--   (hF : ∀ᶠ n in p, differentiable_on ℂ (F n) U)
--   (hf : tendsto_locally_uniformly_on F f p U)
--   (hi : ∃ᶠ n in p, inj_on (F n) U)
--   :
--   (∃ w, ∀ z ∈ U, f z = w) ∨ (inj_on f U)
--   :=
-- begin
--   refine or_iff_not_imp_right.2 (λ h, _),
--   obtain ⟨x, hx, y, hy, hfxy, hxy⟩ : ∃ x ∈ U, ∃ y ∈ U, f x = f y ∧ x ≠ y,
--     by rw [inj_on] at h; simpa using h,
--   --
--   set g : ℂ → ℂ := λ z, f z - f x,
--   set G : ι → ℂ → ℂ := λ n z, F n z - f x,
--   have key : ∀ {n a b}, G n a = G n b → F n a = F n b := by simp [G],
--   have hG : ∀ᶠ n in p, differentiable_on ℂ (G n) U,
--     by filter_upwards [hF] with n hF using hF.sub (differentiable_on_const _),
--   have hg : tendsto_locally_uniformly_on G g p U,
--     from hurwitz4 hf (uniform_continuous_id.sub uniform_continuous_const),
--   have hgi : ∃ᶠ n in p, inj_on (G n) U := hi.mono (λ n h a ha b hb h', h ha hb (key h')),
--   have hgx : g x = 0 := sub_self _,
--   have hgy : g y = 0 := by simp only [g, hfxy, sub_self],
--   suffices : ∀ z ∈ U, g z = 0,
--     from ⟨f x, λ z hz, sub_eq_zero.mp (this z hz)⟩,
--   --
--   contrapose hi; simp only [not_frequently, inj_on, not_forall],
--   have h1 : differentiable_on ℂ g U := hg.differentiable_on hG hU,
--   have h2 : ∀ z₀ ∈ U, ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 := (hurwitz_1 hU hU' h1).resolve_left hi,
--   obtain ⟨u, v, hu, hv, huv⟩ := t2_separation_nhds hxy,
--   have h3 := hurwitz3 hU hG hg hx hgx (h2 x hx) (inter_mem hu (hU.mem_nhds hx)),
--   have h4 := hurwitz3 hU hG hg hy hgy (h2 y hy) (inter_mem hv (hU.mem_nhds hy)),
--   filter_upwards [h3.and h4] with n hn,
--   obtain ⟨⟨xn, hxn, hGxn⟩, ⟨yn, hyn, hGyn⟩⟩ := hn,
--   refine ⟨xn, hxn.2, yn, hyn.2, _, huv.ne_of_mem hxn.1 hyn.1⟩,
--   simpa [G] using hGxn.trans hGyn.symm
-- end