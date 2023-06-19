import Mathlib.Analysis.Complex.LocallyUniformLimit
import RMT4.uniform
import RMT4.cindex

open Filter Topology Set Metric Uniformity

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
    map (λ x : 𝕜 × 𝕜 => (x.1⁻¹, x.2⁻¹)) (𝓤 𝕜 ⊓ (p ×ˢ q)) ≤ 𝓤 𝕜 := by
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

lemma uniform_ContinuousOn_inv {s : Set 𝕜} (hs : 𝓟 s ⊓ 𝓝 0 = ⊥) :
    UniformContinuousOn (λ x => x⁻¹) s := by
  simpa only [UniformContinuousOn, Tendsto, ← prod_principal_principal] using titi hs hs

example (hη : 0 < η) : UniformContinuousOn (λ x => x⁻¹) ((ball (0 : 𝕜) η)ᶜ) := by
  apply uniform_ContinuousOn_inv
  simpa only [inf_comm, inf_principal_eq_bot, compl_compl] using ball_mem_nhds _ hη

lemma TendstoUniformlyOn.inv (hF : TendstoUniformlyOn F f p s) (hf : 𝓟 (f '' s) ⊓ 𝓝 0 = ⊥) :
    TendstoUniformlyOn F⁻¹ f⁻¹ p s := by
  have : 𝓝ᵘ (f '' s) ⊓ 𝓝 0 = ⊥ := by
    rw [inf_comm] at hf ⊢
    exact UniformSpace.nhds_inf_uniform_nhds_eq_bot hf
  have h1 := lemma1 hF
  rw [tendstoUniformlyOn_iff_tendsto] at hF ⊢
  refine (Filter.map_mono (le_inf hF h1)).trans (titi hf this)

lemma lxyab {x y a b : 𝕜} : x * a - y * b = (x - y) * a + y * (a - b) := by ring

lemma TendstoUniformlyOn.mul_of_le
    (hF : TendstoUniformlyOn F f p s) (hG : TendstoUniformlyOn G g p s)
    (hf : ∀ᶠ i in p, ∀ x ∈ s, ‖F i x‖ ≤ mf) (hg : ∀ᶠ i in p, ∀ x ∈ s, ‖G i x‖ ≤ mg) :
    TendstoUniformlyOn (F * G) (f * g) p s := by
  by_cases NeBot p
  case neg => simp at h; simp [h, TendstoUniformlyOn]
  case pos =>
    set Mf := |mf| + 1
    set Mg := |mg| + 1
    have hMf : 0 < Mf := by positivity
    have hMg : 0 < Mg := by positivity
    replace hf : ∀ᶠ i in p, ∀ x ∈ s, ‖F i x‖ ≤ Mf := by
      filter_upwards [hf] with i hF x hx using (hF x hx).trans ((le_abs_self mf).trans (lt_add_one _).le)
    replace hg : ∀ᶠ i in p, ∀ x ∈ s, ‖G i x‖ ≤ Mg := by
      filter_upwards [hg] with i hG x hx using (hG x hx).trans ((le_abs_self mg).trans (lt_add_one _).le)
    have h1 : ∀ x ∈ s, ‖g x‖ ≤ Mg := by
      intro x hx
      refine le_of_tendsto ((continuous_norm.tendsto (g x)).comp (hG.tendsto_at hx)) ?_
      filter_upwards [hg] with i hg using hg x hx
    simp_rw [Metric.tendstoUniformlyOn_iff, dist_eq_norm] at hF hG ⊢
    intro ε hε
    filter_upwards [hf, hF (ε / (2 * Mg)) (by positivity), hG (ε / (2 * Mf)) (by positivity)] with i hf hF hG x hx
    have h2 : ‖(f x - F i x) * g x‖ < ε / 2 := by
      rw [norm_mul]
      by_cases g x = 0
      case pos => simp [h, half_pos hε]
      case neg =>
        convert mul_lt_mul (hF x hx) (h1 x hx) (norm_pos_iff.mpr h) (by positivity) using 1
        simp only [div_mul, mul_div_cancel, hMg.ne.symm, Ne.def, not_false_iff]
    have h3 : ‖F i x * (g x - G i x)‖ < ε / 2 := by
      rw [norm_mul]
      by_cases F i x = 0
      case pos => simp [h, half_pos hε]
      case neg =>
        convert mul_lt_mul' (hf x hx) (hG x hx) (norm_nonneg _) hMf using 1
        field_simp [hMf.ne.symm]; ring
    simp_rw [Pi.mul_apply, lxyab]
    exact (norm_add_le _ _).trans_lt (add_halves' ε ▸ add_lt_add h2 h3)

lemma TendstoUniformlyOn.mul_of_bound
    (hF : TendstoUniformlyOn F f p s) (hG : TendstoUniformlyOn G g p s)
    (hf : ∀ x ∈ s, ‖f x‖ ≤ mf) (hg : ∀ x ∈ s, ‖g x‖ ≤ mg) :
    TendstoUniformlyOn (F * G) (f * g) p s := by
  have h1 : ∀ᶠ i in p, ∀ x ∈ s, ‖F i x‖ ≤ mf + 1 := by
    simp_rw [Metric.tendstoUniformlyOn_iff, dist_eq_norm] at hF
    filter_upwards [hF 1 zero_lt_one] with i hF x hx
    have : ‖F i x‖ ≤ ‖f x - F i x‖ + ‖f x‖ := by
      simpa [← norm_neg (F i x - f x)] using norm_add_le (F i x - f x) (f x)
    linarith [hF x hx, hf x hx]
  have h2 : ∀ᶠ i in p, ∀ x ∈ s, ‖G i x‖ ≤ mg + 1 := by
    simp_rw [Metric.tendstoUniformlyOn_iff, dist_eq_norm] at hG
    filter_upwards [hG 1 zero_lt_one] with i hG x hx
    have : ‖G i x‖ ≤ ‖g x - G i x‖ + ‖g x‖ := by
      simpa [← norm_neg (G i x - g x)] using norm_add_le (G i x - g x) (g x)
    linarith [hG x hx, hg x hx]
  exact hF.mul_of_le hG h1 h2

variable [TopologicalSpace α]

lemma TendstoUniformlyOn.inv_of_compact (hF : TendstoUniformlyOn F f p K)
    (hf : ContinuousOn f K) (hK : IsCompact K) (hfz : ∀ x ∈ K, f x ≠ 0) :
    TendstoUniformlyOn F⁻¹ f⁻¹ p K := by
  apply hF.inv
  rw [inf_comm, inf_principal_eq_bot]
  exact (hK.image_of_continuousOn hf).isClosed.compl_mem_nhds (λ ⟨z, h1, h2⟩ => hfz z h1 h2)

lemma TendstoUniformlyOn.mul_of_compact
    (hF : TendstoUniformlyOn F f p K) (hG : TendstoUniformlyOn G g p K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hK : IsCompact K) :
    TendstoUniformlyOn (F * G) (f * g) p K := by
  by_cases K = ∅
  case pos => simpa only [h] using tendstoUniformlyOn_empty
  case neg =>
    replace h : K.Nonempty := Set.nonempty_iff_ne_empty.2 h
    have h2 : ContinuousOn (norm ∘ f) K := continuous_norm.comp_continuousOn hf
    have h3 : ContinuousOn (norm ∘ g) K := continuous_norm.comp_continuousOn hg
    obtain ⟨xf, _, h4⟩ : ∃ x ∈ K, ∀ y ∈ K, ‖f y‖ ≤ ‖f x‖ := hK.exists_forall_ge h h2
    obtain ⟨xg, _, h5⟩ : ∃ x ∈ K, ∀ y ∈ K, ‖g y‖ ≤ ‖g x‖ := hK.exists_forall_ge h h3
    exact hF.mul_of_bound hG h4 h5

lemma TendstoUniformlyOn.div_of_compact
    (hF : TendstoUniformlyOn F f p K) (hG : TendstoUniformlyOn G g p K)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K) (hgK : ∀ z ∈ K, g z ≠ 0) (hK : IsCompact K) :
    TendstoUniformlyOn (F / G) (f / g) p K := by
  simpa [div_eq_mul_inv] using hF.mul_of_compact (hG.inv_of_compact hg hK hgK) hf (hg.inv₀ hgK) hK

end unifops

variable {F : ι → ℂ → ℂ} {f : ℂ → ℂ}
--   {U s : set ℂ} {r : ℝ}

lemma Filter.Eventually.exists' {P : ℝ → Prop} {t₀} (h : ∀ᶠ t in 𝓝[>] t₀, P t) :
    ∃ t > t₀, P t := by
  simpa [and_comm, exists_prop] using (frequently_nhdsWithin_iff.mp h.frequently).exists

lemma order_eq_zero_iff {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p z₀) (hz₀ : f z₀ = 0) :
    p.order = 0 ↔ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  rw [hp.locally_zero_iff]
  by_cases p = 0
  case pos => simp [h]
  case neg =>
    simp [FormalMultilinearSeries.order_eq_zero_iff h, h]
    ext1
    rw [hp.coeff_zero, hz₀]; rfl

lemma order_pos_iff {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p z₀) (hz₀ : f z₀ = 0) :
    0 < p.order ↔ ∃ᶠ z in 𝓝 z₀, f z ≠ 0 := by
  simp [pos_iff_ne_zero, (order_eq_zero_iff hp hz₀).not]

lemma cindex_pos (h1 : AnalyticAt ℂ f z₀) (h2 : f z₀ = 0) (h3 : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) :
    ∀ᶠ r in 𝓝[>] 0, cindex z₀ r f ≠ 0 := by
  obtain ⟨p, hp⟩ := h1
  filter_upwards [cindex_eventually_eq_order hp] with r h4
  simpa [h4, order_eq_zero_iff hp h2] using h3.frequently.filter_mono nhdsWithin_le_nhds

-- TODO: this can be generalized a lot
lemma hurwitz2_1 {K : Set ℂ} (hK : IsCompact K) (F_conv : TendstoUniformlyOn F f p K)
    (hf1 : ContinuousOn f K) (hf2 : ∀ z ∈ K, f z ≠ 0) :
    ∀ᶠ n in p, ∀ z ∈ K, F n z ≠ 0 := by
  by_cases K = ∅
  case pos => simp [h]
  case neg =>
    obtain ⟨z₀, h1, h2⟩ : ∃ z₀ ∈ K, ∀ z ∈ K, ‖f z₀‖ ≤ ‖f z‖ :=
      hK.exists_forall_le (nonempty_iff_ne_empty.2 h) (continuous_norm.comp_continuousOn hf1)
    have h3 := tendstoUniformlyOn_iff.1 F_conv (‖f z₀‖) (norm_pos_iff.2 (hf2 _ h1))
    filter_upwards [h3] with n hn z hz h
    specialize hn z hz
    specialize h2 z hz
    simp [h] at hn h2
    linarith

lemma TendstoUniformlyOn.tendsto_circle_integral (hr : 0 < r)
    (F_cont : ∀ᶠ n in p, ContinuousOn (F n) (sphere z₀ r))
    (F_conv : TendstoUniformlyOn F f p (sphere z₀ r)) :
    Filter.Tendsto (λ i => ∮ z in C(z₀, r), F i z) p (𝓝 (∮ z in C(z₀, r), f z))
    := by
  by_cases NeBot p
  case neg => simp at h; simp [h]
  case pos =>
    have f_cont : ContinuousOn f (sphere z₀ r) := F_conv.continuousOn F_cont
    rw [Metric.tendsto_nhds]
    intro ε hε
    have twopir_ne_zero : 2 * Real.pi * r ≠ 0 := by simp [Real.pi_ne_zero, hr.ne.symm]
    have : (2 * Real.pi * r)⁻¹ * ε > 0 :=
      mul_pos (inv_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) hr)) hε.lt
    filter_upwards [tendstoUniformlyOn_iff.mp F_conv ((2 * Real.pi * r)⁻¹ * ε) this, F_cont] with n h h'
    simp_rw [dist_comm (f _) _, Complex.dist_eq, ← Complex.norm_eq_abs] at h
    rw [Complex.dist_eq, ← circleIntegral.sub hr.le h' f_cont, ← Complex.norm_eq_abs]
    have : ∃ x ∈ sphere z₀ r, ‖F n x - f x‖ < (2 * Real.pi * r)⁻¹ * ε := by
      have : z₀ + r ∈ sphere z₀ r := by simp [hr.le, Real.norm_eq_abs]
      exact ⟨z₀ + r, this, h _ this⟩
    convert circleIntegral.norm_integral_lt_of_norm_le_const_of_lt hr (h'.sub f_cont) (λ z hz => (h z hz).le) this
    field_simp [hr.ne, Real.pi_ne_zero, two_ne_zero]; ring

lemma hurwitz2_2 (hU : IsOpen U) (hF : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (hf : TendstoLocallyUniformlyOn F f p U) (hr1 : 0 < r) (hr2 : sphere z₀ r ⊆ U)
    (hf1 : ∀ (z : ℂ), z ∈ sphere z₀ r → f z ≠ 0) :
    Tendsto (cindex z₀ r ∘ F) p (𝓝 (cindex z₀ r f)) := by
  by_cases NeBot p
  case neg => simp at h; simp [h]
  case pos =>
    have H1 : IsCompact (sphere z₀ r) := isCompact_sphere z₀ r
    have H2 : TendstoUniformlyOn F f p (sphere z₀ r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hf _ hr2 H1
    have H3 : DifferentiableOn ℂ f U := hf.differentiableOn hF hU
    have H4 : ContinuousOn f (sphere z₀ r) := H3.continuousOn.mono hr2
    have H5 : ∀ᶠ n in p, ContinuousOn (F n) (sphere z₀ r) := by
      filter_upwards [hF] with n h using h.continuousOn.mono hr2
    have H6 : ∀ᶠ n in p, ContinuousOn (deriv (F n)) (sphere z₀ r) := by
      filter_upwards [hF] with n h using (h.deriv hU).continuousOn.mono hr2
    have H7 : TendstoUniformlyOn (deriv ∘ F) (deriv f) p (sphere z₀ r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 (hf.deriv hF hU) _ hr2 H1
    have H8 : ContinuousOn (deriv f) (sphere z₀ r) :=
      (H3.deriv hU).continuousOn.mono hr2
    refine Tendsto.const_mul _ (TendstoUniformlyOn.tendsto_circle_integral hr1 ?_ ?_)
    { filter_upwards [hurwitz2_1 H1 H2 H4 hf1, H6, H5] with n hn H6 H5 using ContinuousOn.div H6 H5 hn }
    { exact TendstoUniformlyOn.div_of_compact H7 H2 H8 H4 hf1 H1 }

lemma hurwitz2
    (hU : IsOpen U)
    (hF : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (hf : TendstoLocallyUniformlyOn F f p U)
    (hr1 : 0 < r)
    (hr2 : closedBall z₀ r ⊆ U)
    (hf1 : ∀ z ∈ sphere z₀ r, f z ≠ 0)
    (hf2 : cindex z₀ r f ≠ 0)
    :
    ∀ᶠ n in p, ∃ z ∈ ball z₀ r, F n z = 0
    := by
  by_cases NeBot p
  case neg => simp at h; simp [h]
  case pos =>
    have H1 : IsCompact (sphere z₀ r) := isCompact_sphere z₀ r
    have H2 : sphere z₀ r ⊆ U := sphere_subset_closedBall.trans hr2
    have H3 : TendstoUniformlyOn F f p (sphere z₀ r) :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hf _ H2 H1
    have H4 : ContinuousOn f (sphere z₀ r) :=
      (hf.differentiableOn hF hU).continuousOn.mono H2
    have H5 : ∀ᶠ n in p, ∀ z ∈ sphere z₀ r, F n z ≠ 0 := hurwitz2_1 H1 H3 H4 hf1
    filter_upwards [(hurwitz2_2 hU hF hf hr1 H2 hf1).eventually_ne hf2, H5, hF] with n h h' hF
    contrapose! h
    have : ∀ (z : ℂ), z ∈ ball z₀ r ∪ sphere z₀ r → F n z ≠ 0 := λ z hz => hz.casesOn (h z) (h' z)
    refine cindex_eq_zero hU hr1 hr2 hF (by rwa [← ball_union_sphere])

lemma hurwitz3
    (hU : IsOpen U)
    (hF : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (hf : TendstoLocallyUniformlyOn F f p U)
    (hz₀ : z₀ ∈ U)
    (h1 : f z₀ = 0)
    (h2 : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0)
    (hs : s ∈ 𝓝 z₀)
    :
    ∀ᶠ n in p, ∃ z ∈ s, F n z = 0
    := by
  by_cases NeBot p
  case neg => simp at h; simp [h]
  case pos =>
    have H1 := (hf.differentiableOn hF hU).analyticAt (hU.mem_nhds hz₀)
    have H5 := cindex_pos H1 h1 h2
    rw [eventually_nhdsWithin_iff] at h2
    have h3 := eventually_nhds_iff_eventually_closed_ball.1 h2
    have h4 : ∀ᶠ r in 𝓝[>] 0, closedBall z₀ r ⊆ U :=
      (eventually_closedBall_subset (hU.mem_nhds hz₀)).filter_mono nhdsWithin_le_nhds
    have h4' : ∀ᶠ r in 𝓝[>] 0, closedBall z₀ r ⊆ s :=
      (eventually_closedBall_subset hs).filter_mono nhdsWithin_le_nhds
    obtain ⟨r, hr, h5, h6, h7, h9⟩ := (h3.and (h4.and (H5.and h4'))).exists'
    have h8 : ∀ z ∈ sphere z₀ r, f z ≠ 0 := by
      exact λ z hz => h5 z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz hr.lt.ne.symm)
    refine (hurwitz2 hU hF hf hr h6 h8 h7).mono ?_
    rintro n ⟨z, hz, hFnz⟩
    refine ⟨z, h9 (ball_subset_closedBall hz), hFnz⟩

----------------

theorem local_hurwitz [NeBot p]
    (hU : IsOpen U)
    (F_holo : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (F_noz : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (F_conv : TendstoLocallyUniformlyOn F f p U)
    (hz₀ : z₀ ∈ U)
    (hfz₀ : f z₀ = 0)
    :
    ∀ᶠ z in 𝓝 z₀, f z = 0 := by
  have H1 := (F_conv.differentiableOn F_holo hU).analyticAt (hU.mem_nhds hz₀)
  cases H1.eventually_eq_zero_or_eventually_ne_zero
  case inl => assumption
  case inr h =>
    obtain ⟨pf, hp⟩ := H1
    by_contra' hh
    rw [Filter.not_eventually] at hh
    have h1 := (order_pos_iff hp hfz₀).2 hh
    obtain ⟨r, h1, h2, h3, h4⟩ :
        ∃ r > 0, (closedBall z₀ r ⊆ U) ∧ (∀ z ∈ sphere z₀ r, f z ≠ 0) ∧ (cindex z₀ r f ≠ 0) := by
      rw [eventually_nhdsWithin_iff, eventually_nhds_iff_eventually_closed_ball] at h
      have h4 := cindex_eventually_eq_order hp
      have h5 : ∀ᶠ r in 𝓝[>] 0, closedBall z₀ r ⊆ U :=
        (eventually_closedBall_subset (hU.mem_nhds hz₀)).filter_mono nhdsWithin_le_nhds
      obtain ⟨r, h6, h7, h8, h9⟩ := (h.and (h4.and h5)).exists'
      refine ⟨r, h6, h9, ?_, ?_⟩
      { exact λ z hz => h7 z (sphere_subset_closedBall hz) (ne_of_mem_sphere hz h6.lt.ne.symm) }
      { simp [h8, h1.ne.symm] }
    obtain ⟨n, z, h5, h6⟩ := (hurwitz2 hU F_holo F_conv h1 h2 h3 h4).exists
    cases F_noz n z (h2 (ball_subset_closedBall (mem_ball.mpr h5))) h6

theorem hurwitz [NeBot p]
    (hU : IsOpen U)
    (hU' : IsPreconnected U)
    (F_holo : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (F_noz : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (F_conv : TendstoLocallyUniformlyOn F f p U)
    (hz₀ : z₀ ∈ U)
    (hfz₀ : f z₀ = 0)
    :
    ∀ z ∈ U, f z = 0 := by
  have := local_hurwitz hU F_holo F_noz F_conv hz₀ hfz₀
  have h1 : DifferentiableOn ℂ f U := F_conv.differentiableOn F_holo hU
  have h2 := h1.analyticOn hU
  exact h2.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU' hz₀ this

theorem hurwitz' [NeBot p]
    (hU : IsOpen U)
    (hU' : IsPreconnected U)
    (F_holo : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (F_noz : ∀ n, ∀ z ∈ U, F n z ≠ 0)
    (F_conv : TendstoLocallyUniformlyOn F f p U)
    :
    (∀ z ∈ U, f z ≠ 0) ∨ (∀ z ∈ U, f z = 0) := by
  refine or_iff_not_imp_left.mpr (λ h => ?_)
  push_neg at h
  obtain ⟨z₀, h1, h2⟩ := h
  exact hurwitz hU hU' F_holo F_noz F_conv h1 h2

lemma hurwitz_1 (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U) :
    (EqOn f 0 U) ∨ (∀ z₀ ∈ U, ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0) := by
  refine or_iff_not_imp_right.2 (λ h => ?_)
  obtain ⟨z₀, h1, h2⟩ : ∃ z₀ ∈ U, ∃ᶠ z in 𝓝[≠] z₀, f z = 0 := by simpa [not_forall] using h
  exact (hf.analyticOn hU).eqOn_zero_of_preconnected_of_frequently_eq_zero hU' h1 h2

lemma hurwitz4 [TopologicalSpace α] [UniformSpace β] [UniformSpace γ]
    {F : ι → α → β} {f : α → β} {φ : β → γ}
    (hf : TendstoLocallyUniformlyOn F f p U) (hφ : UniformContinuous φ) :
    TendstoLocallyUniformlyOn (λ n => φ ∘ F n) (φ ∘ f) p U :=
  λ _ hu z hz => hf _ (mem_map.1 (hφ hu)) z hz

theorem hurwitz_inj [NeBot p]
    (hU : IsOpen U)
    (hU' : IsPreconnected U)
    (hF : ∀ᶠ n in p, DifferentiableOn ℂ (F n) U)
    (hf : TendstoLocallyUniformlyOn F f p U)
    (hi : ∃ᶠ n in p, InjOn (F n) U)
    :
    (∃ w, ∀ z ∈ U, f z = w) ∨ (InjOn f U)
    := by
  refine or_iff_not_imp_right.2 (λ h => ?_)
  obtain ⟨x, hx, y, hy, hfxy, hxy⟩ : ∃ x ∈ U, ∃ y ∈ U, f x = f y ∧ x ≠ y := by
    simp [InjOn] at h
    obtain ⟨x, h1, y, h2, h3, h4⟩ := h
    refine ⟨x, h1, y, h3, h2, h4⟩
  --
  set g : ℂ → ℂ := λ z => f z - f x
  set G : ι → ℂ → ℂ := λ n z => F n z - f x
  have hG : ∀ᶠ n in p, DifferentiableOn ℂ (G n) U := by
    filter_upwards [hF] with n hF using hF.sub (differentiableOn_const _)
  have hg : TendstoLocallyUniformlyOn G g p U :=
    hurwitz4 hf (uniformContinuous_id.sub uniformContinuous_const)
  have hgx : g x = 0 := sub_self _
  have hgy : g y = 0 := by simp [hfxy]
  suffices : ∀ z ∈ U, g z = 0
  { exact ⟨f x, by simpa [sub_eq_zero] using this⟩ }
  --
  contrapose hi; simp only [not_frequently, InjOn, not_forall]
  have h1 : DifferentiableOn ℂ g U := hg.differentiableOn hG hU
  have h2 : ∀ z₀ ∈ U, ∀ᶠ z in 𝓝[≠] z₀, g z ≠ 0 := (hurwitz_1 hU hU' h1).resolve_left hi
  obtain ⟨u, v, hu, hv, huv⟩ := t2_separation_nhds hxy
  have h3 := hurwitz3 hU hG hg hx hgx (h2 x hx) (inter_mem hu (hU.mem_nhds hx))
  have h4 := hurwitz3 hU hG hg hy hgy (h2 y hy) (inter_mem hv (hU.mem_nhds hy))
  filter_upwards [h3.and h4] with n hn
  obtain ⟨⟨xn, hxn, hGxn⟩, ⟨yn, hyn, hGyn⟩⟩ := hn
  refine ⟨xn, hxn.2, yn, hyn.2, ?_, huv.ne_of_mem hxn.1 hyn.1⟩
  rw [sub_eq_zero] at hGxn hGyn
  rw [hGxn, hGyn]
