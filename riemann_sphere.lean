-- import analysis.complex.basic
-- import geometry.manifold.charted_space
-- import geometry.manifold.smooth_manifold_with_corners
-- import linear_algebra.projective_space.basic
-- import topology.constructions

-- noncomputable theory

-- open_locale manifold

-- variables (K V : Type*) [field K] [add_comm_group V] [module K V]

-- namespace projectivization

-- /- General lemmas about projectivization (for mathlib) -/

-- instance [topological_space V] : topological_space (ℙ K V) := quotient.topological_space

-- @[simp] lemma quotient_mk_eq_mk (z : V) (h : z ≠ 0) :
--   @quotient.mk _ (projectivization_setoid _ _) ⟨z, h⟩ = mk K z h := rfl

-- def lift_on {K V α : Type*} [field K] [add_comm_group V] [module K V]
--   (z : ℙ K V) (f : {w : V // w ≠ 0} → α)
--   (hf : ∀ (x y : V) (hx : x ≠ 0) (hy : y ≠ 0), mk K x hx = mk K y hy → f ⟨x,hx⟩ = f ⟨y,hy⟩) : α :=
-- quotient.lift_on' z f (λ ⟨x, hx⟩ ⟨y, hy⟩ h, hf x y hx hy (quotient.eq'.mpr h))

-- @[simp] lemma lift_on_mk {α : Type*} {z : V} (h : z ≠ 0) (f : {w : V // w ≠ 0} → α) (hf) :
--   lift_on (mk K z h) f hf = f ⟨z, h⟩ := rfl

-- @[simp] lemma lift_on_mk' {α : Type*} {z : V} (h : z ≠ 0) (f : {w : V // w ≠ 0} → α) (hf) :
--   quotient.lift_on' (mk K z h) f hf = f ⟨z, h⟩ := rfl

-- /- Specific case of the projective line -/

-- local notation `[`x`:`y`, `h`]` := (mk _ (x,y) h)
-- local notation `[`x`:`y`]` := [x:y, by simp]

-- lemma mk_eq_mk_iff_mul_eq_mul ⦃x y : K × K⦄ (hx : x ≠ 0) (hy : y ≠ 0) :
--   mk K x hx = mk K y hy ↔ x.1 * y.2 = x.2 * y.1 :=
-- begin
--   rw [mk_eq_mk_iff],
--   split,
--   { rintro ⟨a, rfl⟩,
--     simp [units.smul_def, mul_assoc, mul_comm y.1 _] },
--   { intro hxy,
--     rcases x with ⟨x1, x2⟩,
--     rcases y with ⟨y1, y2⟩,
--     rcases eq_or_ne y1 0 with (rfl | h),
--     { simp only [ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hy,
--       simp only [hy, mul_zero, mul_eq_zero, or_false] at hxy,
--       simp only [hxy, ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hx,
--       use units.mk0 (x2/y2) (div_ne_zero hx hy),
--       simp [units.smul_def, hy, hxy] },
--     { rcases eq_or_ne x1 0 with (rfl | h'),
--       { simp only [ne.def, prod.mk_eq_zero, eq_self_iff_true, true_and] at hx,
--         simp only [hx, h, zero_mul, zero_eq_mul, false_or] at hxy,
--         contradiction },
--       { use units.mk0 (x1/y1) (div_ne_zero h' h),
--         simp [div_mul_cancel, h, div_mul_eq_mul_div, div_eq_iff, hxy] } } }
-- end

-- def lift_of_div {α K : Type*} [field K] (f : K → α) (z : ℙ K (K × K)) : α :=
-- lift_on z (λ w, f (w.val.1 / w.val.2))
-- begin
--   intros x y hx hy hxy,
--   obtain ⟨a, rfl⟩ := (mk_eq_mk_iff _ _ _ _ _).mp hxy,
--   exact congr_arg f (mul_div_mul_left y.1 y.2 a.ne_zero)
-- end

-- instance [topological_space K] [t1_space K] [has_continuous_sub K] [has_continuous_mul K] :
--   t1_space (ℙ K (K × K)) :=
-- begin
--   refine ⟨λ x, _⟩,
--   induction x using projectivization.ind with x hx,
--   have hc : continuous (λ z : {w : K × K // w ≠ 0}, z.val.1 * x.2 - z.val.2 * x.1) :=
--     ((continuous_fst.comp continuous_induced_dom).mul continuous_const).sub
--     ((continuous_snd.comp continuous_induced_dom).mul continuous_const),
--   apply is_open_compl_iff.mp,
--   change is_open {z | ¬ mk' K z = mk K x hx},
--   simp_rw [mk'_eq_mk, mk_eq_mk_iff_mul_eq_mul],
--   convert ← is_open_compl_singleton.preimage hc,
--   ext,
--   exact sub_ne_zero
-- end

-- @[continuity] lemma continuous_lift_of_div {K α : Type*} [field K]
--   [topological_space K] [t1_space K] [has_continuous_inv₀ K] [has_continuous_mul K]
--   [topological_space α] {f : K → α} (hf : continuous f) :
--   continuous_on (lift_of_div f) {[1:0]}ᶜ :=
-- begin
--   rw continuous_on_iff,
--   intros z hz t ht hzt,
--   refine ⟨lift_of_div f ⁻¹' t ∩ {[1:0]}ᶜ, _, ⟨hzt, hz⟩, by simp [set.inter_assoc, set.inter_subset_left]⟩,
--   refine ⟨{z | z.2 ≠ 0 ∧ f (z.1 / z.2) ∈ t}, _, _⟩,
--   { suffices : continuous_on (λ z : K × K, f (z.1 / z.2)) {z | z.2 ≠ 0},
--       exact this.preimage_open_of_open (is_open_compl_singleton.preimage continuous_snd) ht,
--     refine continuous.comp_continuous_on hf _,
--     exact continuous_fst.continuous_on.div continuous_snd.continuous_on (λ _, id) },
--   { ext ⟨x, hx⟩,
--     simp [lift_of_div, mk_eq_mk_iff_mul_eq_mul, and_comm, eq_comm] }
-- end

-- /- Specific sub-case of the Riemann sphere -/

-- abbreviation C'2 := {z : ℂ × ℂ // z ≠ 0}
-- abbreviation CP1 := ℙ ℂ (ℂ × ℂ)

-- /- Chart constructions -/

-- def main_chart [topological_space K] [t1_space K] [has_continuous_sub K] [has_continuous_mul K]
--   [has_continuous_inv₀ K] :
--   local_homeomorph (ℙ K (K × K)) K :=
-- {
--   to_fun := lift_of_div id,
--   inv_fun := λ z, mk K (z,1) (by simp),
--   source := {mk K (1,0) (by simp)}ᶜ,
--   target := set.univ,

--   map_source' := λ _ _, set.mem_univ _,
--   map_target' := by simp [mk_eq_mk_iff_mul_eq_mul],
--   left_inv' := λ z hz, by {
--     induction z using projectivization.ind with z h,
--     simp [mk_eq_mk_iff_mul_eq_mul, ← ne.def] at hz,
--     simp [lift_of_div, mk_eq_mk_iff_mul_eq_mul, hz.symm] },
--   right_inv' := by simp [lift_of_div],
--   open_source := is_open_compl_singleton,
--   open_target := is_open_univ,
--   continuous_to_fun := continuous_lift_of_div continuous_id,
--   continuous_inv_fun :=
--     (continuous_quotient_mk.comp ((continuous.prod.mk_left 1).subtype_mk _)).continuous_on
-- }

-- lemma _root_.prod.swap_eq_iff_eq_swap {α : Type*} {z z' : α × α} : z.swap = z' ↔ z = z'.swap :=
-- ⟨λ h, prod.swap_swap z ▸ congr_arg prod.swap h, λ h, prod.swap_swap z' ▸ congr_arg prod.swap h⟩

-- def antipode [topological_space K] : ℙ K (K × K) ≃ₜ ℙ K (K × K) :=
-- let antip : ℙ K (K × K) → ℙ K (K × K) := λ z, lift_on z
--   (λ w, mk K w.val.swap (by simp [w.prop, prod.swap_eq_iff_eq_swap]))
--   (by simp [mk_eq_mk_iff_mul_eq_mul, eq_comm]) in
-- have inv : function.involutive antip := λ z, by {
--   induction z using projectivization.ind with z h,
--   simp [antip] },
-- have cts : continuous antip := (continuous_quotient_mk.comp ((continuous_swap.comp
--   continuous_subtype_val).subtype_mk _)).quotient_lift_on' _,
-- {
--   to_fun := antip,
--   inv_fun := antip,
--   left_inv := inv,
--   right_inv := inv,
--   continuous_to_fun := cts,
--   continuous_inv_fun := cts
-- }

-- def other_chart [topological_space K] [t1_space K] [has_continuous_sub K] [has_continuous_mul K]
--   [has_continuous_inv₀ K] :
--   local_homeomorph (ℙ K (K × K)) K :=
-- (antipode K).to_local_homeomorph ≫ₕ main_chart K

-- /- The Riemann sphere -/

-- instance : charted_space ℂ CP1 :=
-- {
--   atlas := {φ | φ = main_chart ℂ ∨ φ = other_chart ℂ},
--   chart_at := λ z, by { by_cases z = [1:0], exact other_chart ℂ, exact main_chart ℂ },
--   mem_chart_source := λ z, by {
--     by_cases z = [1:0]; simp [h, antipode, mk_eq_mk_iff_mul_eq_mul, main_chart, other_chart] },
--   chart_mem_atlas := λ z, by { by_cases z = [1:0]; simp [h] }
-- }

-- /- Manifold instance -/

-- @[simp] lemma dom1 : (main_chart ℂ).target ∩ (main_chart ℂ).symm ⁻¹' (other_chart ℂ).source = {0}ᶜ :=
-- begin
--   ext,
--   simp [antipode, mk_eq_mk_iff_mul_eq_mul, eq_comm, main_chart, other_chart],
-- end

-- @[simp] lemma dom2 : (other_chart ℂ).target ∩ (other_chart ℂ).symm ⁻¹' (main_chart ℂ).source = {0}ᶜ :=
-- begin
--   ext,
--   simp [antipode, mk_eq_mk_iff_mul_eq_mul, eq_comm, main_chart, other_chart],
-- end

-- instance : smooth_manifold_with_corners 𝓘(ℂ) CP1 :=
-- smooth_manifold_with_corners_of_cont_diff_on 𝓘(ℂ) CP1
-- begin
--   simp,
--   rintro e e' (rfl|rfl) (rfl|rfl),
--   { simp [cont_diff_on_id.congr, lift_of_div, main_chart, other_chart] },
--   { exact dom1.symm ▸ (cont_diff_on_inv ℂ).congr (by simp [antipode, lift_of_div, main_chart, other_chart]) },
--   { exact dom2.symm ▸ (cont_diff_on_inv ℂ).congr (by simp [antipode, lift_of_div, main_chart, other_chart]) },
--   { simp [cont_diff_on_id.congr, lift_of_div, main_chart, other_chart] }
-- end

-- end projectivization
