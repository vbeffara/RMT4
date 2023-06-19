import Mathlib.Analysis.Complex.Schwarz
import RMT4.defs
import RMT4.to_mathlib

-- import analysis.calculus.deriv
-- import data.complex.basic
-- import analysis.complex.schwarz

open Complex ComplexConjugate Set Metric

namespace RMT

-- open complex metric
-- open_locale complex_conjugate topological_space

variable (U : Set ℂ) [good_domain U]

lemma one_sub_mul_conj_ne_zero (hu : u ∈ 𝔻) (hz : z ∈ 𝔻) : 1 - z * conj u ≠ 0 := by
  rw [mem_𝔻_iff] at hu hz
  refine sub_ne_zero.mpr (mt (congr_arg Complex.abs) (ne_comm.mp (ne_of_lt ?_)))
  simpa using mul_lt_mul'' hz hu (norm_nonneg z) (norm_nonneg u)

lemma one_sub_mul_conj_add_mul_conj_ne_zero (hu : u ∈ 𝔻) :
    1 - z * conj u + (z - u) * conj u ≠ 0 := by
  have h1 := one_sub_mul_conj_ne_zero hu hu
  ring_nf
  simp [h1, mul_comm]

lemma normSq_sub_normSq : normSq (z - u) - normSq (1 - z * conj u) = (normSq z - 1) * (1 - normSq u) := by
  field_simp [← ofReal_inj, normSq_eq_conj_mul_self]; ring

noncomputable def pre_φ (u z : ℂ) : ℂ := (z - u) / (1 - z * conj u)

lemma pre_φ_inv (hu : u ∈ 𝔻) : LeftInvOn (pre_φ (-u)) (pre_φ u) 𝔻 := by
  rintro z hz
  field_simp [pre_φ, one_sub_mul_conj_ne_zero hu hz, one_sub_mul_conj_add_mul_conj_ne_zero hu]
  ring

noncomputable def φ (hu : u ∈ 𝔻) : embedding 𝔻 𝔻 :=
{
  to_fun := λ z => (z - u) / (1 - z * conj u),
  is_diff := (differentiableOn_id.sub (differentiableOn_const u)).div
    ((differentiableOn_const 1).sub (differentiableOn_id.mul (differentiableOn_const _)))
    (λ _ => one_sub_mul_conj_ne_zero hu),
  is_inj := (pre_φ_inv hu).injOn,
  maps_to := by
    rintro z hz
    simp only [mem_𝔻_iff, map_div₀, norm_div]
    refine (div_lt_iff (norm_pos_iff.mpr (one_sub_mul_conj_ne_zero hu hz))).mpr ?_
    rw [one_mul]
    apply lt_of_pow_lt_pow 2 (norm_nonneg _)
    simp only [norm_eq_abs]
    rw [← normSq_eq_abs, ← normSq_eq_abs, ← sub_lt_zero, normSq_sub_normSq, normSq_eq_abs, normSq_eq_abs]
    apply mul_neg_of_neg_of_pos
    { simpa [norm_eq_abs] using mem_𝔻_iff.mp hz }
    { simpa [norm_eq_abs] using mem_𝔻_iff.mp hu }
}

lemma φ_deriv (hu : u ∈ 𝔻) (hz : z ∈ 𝔻) : deriv (φ hu) z = (1 - u * conj u) / ((1 - z * conj u) ^ 2) := by
  have h1 : DifferentiableAt ℂ (fun z => z - u) z := by simp
  have h2 : DifferentiableAt ℂ (fun z => 1 - z * conj u) z := by simp [DifferentiableAt.mul_const]
  have h3 : 1 - z * conj u ≠ 0 := one_sub_mul_conj_ne_zero hu hz
  have h4 : deriv (fun z => z - u) z = 1 := by simp [deriv_sub_const]
  have h5 : deriv (fun z => 1 - z * conj u) z = - conj u := by simp [deriv_const_sub]
  simp [φ, deriv_div h1 h2 h3, h4, h5]
  field_simp [h3]; ring

lemma φ_inv (hu : u ∈ 𝔻) (hz : z ∈ 𝔻) : φ (neg_in_𝔻 hu) (φ hu z) = z :=
  pre_φ_inv hu hz

lemma non_injective_schwarz {f : ℂ → ℂ} (f_diff : DifferentiableOn ℂ f 𝔻)
    (f_img : MapsTo f 𝔻 𝔻) (f_noninj : ¬ InjOn f 𝔻) : ‖deriv f 0‖ < 1 := by
  set u := f 0
  have u_in_𝔻 : u ∈ 𝔻 := f_img (mem_ball_self zero_lt_one)
  let g := φ u_in_𝔻 ∘ f
  have g_diff : DifferentiableOn ℂ g 𝔻 := (φ u_in_𝔻).is_diff.comp f_diff f_img
  have g_maps : MapsTo g 𝔻 𝔻 := (φ u_in_𝔻).maps_to.comp f_img
  have g_0_eq_0 : g 0 = 0 := by simp [φ]
  by_cases ‖deriv g 0‖ = 1
  case pos =>
    have g_lin : EqOn g (λ (z : ℂ) => z • deriv g 0) (ball 0 1) := by
      have h2 : MapsTo g (ball 0 1) (ball (g 0) 1) := by rwa [g_0_eq_0]
      have h1 : Set.EqOn g (fun z => g 0 + (z - 0) • dslope g 0 0) (Metric.ball 0 1) := by
        apply affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div g_diff h2 (mem_ball_self zero_lt_one)
        rwa [dslope_same, div_one]
      convert h1 using 1
      ext1 z
      rw [g_0_eq_0, zero_add, sub_zero, dslope_same]
    have g'0_ne_0 : deriv g 0 ≠ 0 := λ h' => by simp [h'] at h
    have g_inj : InjOn g 𝔻 := λ x hx y hy => by
      rw [g_lin hx, g_lin hy]
      simp [g'0_ne_0]
    cases f_noninj (injOn_of_injOn_comp g_inj)
  case neg =>
    rw [norm_eq_abs] at h
    have g'0_le_1 := abs_deriv_le_one_of_mapsTo_ball g_diff g_maps g_0_eq_0 zero_lt_one
    have g'0_lt_1 : abs (deriv g 0) < 1 := Ne.lt_of_le h g'0_le_1
    have g'0_eq_mul : deriv g 0 = deriv (φ u_in_𝔻) u * deriv f 0 :=
      deriv.comp 0 ((φ u_in_𝔻).is_diff.differentiableAt (isOpen_ball.mem_nhds u_in_𝔻))
        (f_diff.differentiableAt (ball_mem_nhds _ zero_lt_one))
    have e1 : 1 - (normSq u : ℂ) ≠ 0 := by
      simpa [normSq_eq_conj_mul_self, mul_comm] using one_sub_mul_conj_ne_zero u_in_𝔻 u_in_𝔻
    have φ'u_u : deriv (φ u_in_𝔻) u = 1 / (1 - normSq u) := by
      set w := 1 - conj u * u with hw
      have : w ≠ 0 := by simpa [normSq_eq_conj_mul_self, mul_comm u] using e1
      rw [φ_deriv u_in_𝔻 u_in_𝔻, normSq_eq_conj_mul_self, mul_comm u, ← hw]
      field_simp; ring
    have e2 : 0 ≤ normSq u := normSq_nonneg _
    have e3 : normSq u < 1 := by
      rw [normSq_eq_abs]
      have : abs u < 1 := mem_𝔻_iff.mp u_in_𝔻
      simp only [sq_lt_one_iff_abs_lt_one, Complex.abs_abs, this]
    simp [normSq_eq_abs, ← mem_𝔻_iff]
    simp only [φ'u_u, one_div] at g'0_eq_mul
    rw [eq_comm, inv_mul_eq_iff_eq_mul₀ e1] at g'0_eq_mul
    rw [← norm_eq_abs, g'0_eq_mul, norm_mul, mul_comm, ← one_mul (1 : ℝ)]
    refine mul_lt_mul g'0_lt_1 ?_ (norm_pos_iff.mpr e1) zero_le_one
    simp at e2 e3 ⊢
    norm_cast
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    { linarith }
    { linarith }

-- lemma step_2 (hz₀ : z₀ ∈ U) (f : embedding U 𝔻) (hf : f '' U ⊂ 𝔻) :
--   ∃ h : embedding U 𝔻, ‖deriv f z₀‖ < ‖deriv h z₀‖ :=
-- begin
--   obtain ⟨u, u_in_𝔻, u_not_in_f_U⟩ := set.exists_of_ssubset hf,
--   let φᵤ : embedding 𝔻 𝔻 := φ u_in_𝔻,
--   let φᵤf : embedding U 𝔻 := φᵤ.comp f,
--   have φᵤf_ne_zero : ∀ z ∈ U, φᵤf z ≠ 0 := λ z z_in_U hz, by { refine u_not_in_f_U ⟨z, z_in_U, _⟩,
--     apply φᵤ.is_inj (f.maps_to z_in_U) u_in_𝔻,
--     convert hz,
--     simp only [φᵤ, φ, div_eq_zero_iff, sub_self, eq_self_iff_true, true_or] },
--   obtain ⟨g, hg⟩ := φᵤf.sqrt' φᵤf_ne_zero,
--   let v : ℂ := g z₀,
--   have v_in_𝔻 : v ∈ 𝔻 := g.maps_to hz₀,
--   let h : embedding U 𝔻 := (φ v_in_𝔻).comp g,
--   have h_z₀_eq_0 : h z₀ = 0 := by simp [h, φ],
--   let σ : ℂ → ℂ := λ z, z ^ 2,
--   let ψ : ℂ → ℂ := φ (neg_in_𝔻 u_in_𝔻) ∘ σ ∘ φ (neg_in_𝔻 v_in_𝔻),
--   have f_eq_ψ_h : EqOn f (ψ ∘ h) U := λ z hz, by {
--     symmetry,
--     calc ψ (h z) = φ _ (φ _ (φ _ (g z)) ^ 2) : rfl
--              ... = φ _ (g z ^ 2) : by rw [(φ_inv v_in_𝔻 (g.maps_to hz) : φ _ (φ _ (g z)) = g z)]
--              ... = φ _ (φᵤf z) : by simp [hg hz]
--              ... = f z : φ_inv u_in_𝔻 (f.maps_to hz) },
--   have ψ_is_diff : differentiableOn ℂ ψ 𝔻 := by {
--     refine (φ (neg_in_𝔻 u_in_𝔻)).is_diff.comp _ _,
--     { apply differentiableOn.comp,
--       { apply differentiableOn.pow,
--         have := differentiable_id.differentiableOn,
--         exact this },
--       { convert (φ (neg_in_𝔻 v_in_𝔻)).is_diff },
--       { exact (φ (neg_in_𝔻 v_in_𝔻)).maps_to } },
--     { refine set.maps_to.comp _ (φ (neg_in_𝔻 v_in_𝔻)).maps_to,
--       intros z hz,
--       simpa [𝔻] using hz } },
--   have deriv_eq_mul : deriv f z₀ = deriv ψ 0 * deriv h z₀ := by {
--     have e1 : U ∈ 𝓝 z₀ := good_domain.is_open.mem_nhds hz₀,
--     have e2 : 𝔻 ∈ 𝓝 (0 : ℂ) := ball_mem_nhds _ zero_lt_one,
--     have e3 : deriv f z₀ = deriv (ψ ∘ h) z₀ := (filter.eventually_eq_of_mem e1 f_eq_ψ_h).deriv_eq,
--     rw [e3, ← h_z₀_eq_0],
--     refine deriv.comp z₀ _ (h.is_diff.differentiableAt e1),
--     simpa [h_z₀_eq_0] using ψ_is_diff.differentiableAt e2 },
--   rw [deriv_eq_mul, norm_mul],
--   refine ⟨h, mul_lt_of_lt_one_left _ _⟩,
--   { exact norm_pos_iff.2 (embedding.deriv_ne_zero good_domain.is_open hz₀) },
--   { apply non_injective_schwarz ψ_is_diff,
--     { refine λ z hz, (φ (neg_in_𝔻 u_in_𝔻)).maps_to (mem_𝔻_iff.mpr _),
--       simp only [𝔻, complex.abs_pow, sq_lt_one_iff_abs_lt_one, complex.abs_abs, mem_ball_zero_iff],
--       exact mem_𝔻_iff.mp ((φ (neg_in_𝔻 v_in_𝔻)).maps_to hz) },
--     { simp only [InjOn, not_forall, exists_prop],
--       have e1 : (2⁻¹ : ℂ) ∈ 𝔻 := by { simp [𝔻], norm_num },
--       have e2 : (-2⁻¹ : ℂ) ∈ 𝔻 := by { simp [𝔻], norm_num },
--       refine ⟨φ v_in_𝔻 2⁻¹, (φ v_in_𝔻).maps_to e1, φ v_in_𝔻 (-2⁻¹), (φ v_in_𝔻).maps_to e2, _, _⟩,
--       { simp only [ψ, σ, function.comp_app, φ_inv v_in_𝔻 e1, φ_inv v_in_𝔻 e2, neg_sq] },
--       { intro h,
--         have := (φ v_in_𝔻).is_inj e1 e2 h,
--         norm_num at this } } }
-- end

end RMT