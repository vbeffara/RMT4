import RMT4.cindex

open Set Complex Metric Topology

-- open complex set filter metric
-- open_locale topological_space filter

-- variables {U : set ℂ} {x y z₀ : ℂ} {f g : ℂ → ℂ}

def has_sqrt (U : Set ℂ) : Prop :=
  ∀ (f : ℂ → ℂ), (∀ z ∈ U, f z ≠ 0) → DifferentiableOn ℂ f U →
  ∃ g, DifferentiableOn ℂ g U ∧ EqOn f (g ^ 2) U

def has_primitives (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ EqOn (deriv g) f U

def has_logs (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
  ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ EqOn f (exp ∘ g) U

lemma EqOn_zero_of_deriv_eq_zero (hU : IsOpen U) (hU' : IsPreconnected U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hf' : EqOn (deriv f) 0 U) (hz₀ : z₀ ∈ U) (hfz₀ : f z₀ = 0) :
    EqOn f 0 U := by
  apply (hf.analyticOn hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hU' hz₀
  obtain ⟨r, hr, hrU⟩ := nhds_basis_ball.mem_iff.1 (hU.mem_nhds hz₀)
  refine eventually_nhds_iff.2 ⟨r, hr, λ z hz => ?_⟩
  rw [Pi.zero_apply, ← hfz₀]
  suffices h : ∀ z ∈ ball z₀ r, fderivWithin ℂ f (ball z₀ r) z = 0
  { exact (convex_ball z₀ r).is_const_of_fderivWithin_eq_zero (hf.mono hrU) h hz (mem_ball_self hr) }
  rintro w hw
  have : UniqueDiffWithinAt ℂ (ball z₀ r) w := isOpen_ball.uniqueDiffWithinAt hw
  rw [fderivWithin_eq_fderiv this (hf.differentiableAt (hU.mem_nhds (hrU hw)))]
  ext1
  simpa [fderiv_deriv] using hf' (hrU hw)

lemma EqOn_of_deriv_eq_zero (hU : IsOpen U) (hU' : IsPreconnected U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hf' : EqOn (deriv f) 0 U) (hz₀ : z₀ ∈ U) :
    EqOn f (λ _ => f z₀) U := by
  set g := λ z => f z - f z₀
  have h2 : EqOn (deriv g) 0 U := λ z hz => by simp [deriv_sub_const, hf' hz]
  have h3 : g z₀ = 0 := by simp
  have := EqOn_zero_of_deriv_eq_zero hU hU' (hf.sub_const _) h2 hz₀ h3
  exact λ z hz => sub_eq_zero.1 (this hz)

lemma EqOn_of_EqOn_deriv {f g : ℂ → ℂ} (hU : IsOpen U) (hU' : IsPreconnected U) (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) (hfg : EqOn (deriv f) (deriv g) U) (hz₀ : z₀ ∈ U) (hfgz₀ : f z₀ = g z₀) :
    EqOn f g U := by
  refine λ z hz => sub_eq_zero.1 ?_
  have h2 : EqOn (deriv (λ y => f y - g y)) 0 U := by
    rintro z hz
    have e1 : U ∈ 𝓝 z := hU.mem_nhds hz
    rw [deriv_sub (hf.differentiableAt e1) (hg.differentiableAt e1), hfg hz, sub_self]
    rfl
  exact EqOn_zero_of_deriv_eq_zero hU hU' (hf.sub hg) h2 hz₀ (by simp [hfgz₀]) hz

lemma has_logs.has_sqrt (h : has_logs U) : has_sqrt U := by
  rintro f hfz hf
  obtain ⟨l, hl, hlf⟩ := h f hf hfz
  refine ⟨λ z => exp (l z / 2), differentiable_exp.comp_differentiableOn (hl.div_const _), λ z hz => ?_⟩
  simpa [pow_two, ← exp_add] using hlf hz

lemma has_primitives.has_logs (hp : has_primitives U) (hU : IsOpen U) (hU' : IsPreconnected U) :
    has_logs U := by
  by_cases U = ∅
  case pos => exact λ f => by simp [h, DifferentiableOn]
  case neg =>
    obtain ⟨z₀, hz₀⟩ := nonempty_iff_ne_empty.2 h
    rintro f hf hfz
    obtain ⟨lf, hlf1, hlf2⟩ := hp (deriv f / f) ((hf.deriv hU).div hf hfz)
    let g : ℂ → ℂ := λ z => lf z + (log (f z₀) - lf z₀)
    set h : ℂ → ℂ := f / (exp ∘ g)
    have h3 : DifferentiableOn ℂ g U := hlf1.add (differentiableOn_const _)
    have e4 : DifferentiableOn ℂ (exp ∘ g) U := differentiable_exp.comp_differentiableOn h3
    have e1 : DifferentiableOn ℂ h U := hf.div e4 (λ z _ => exp_ne_zero _)
    refine ⟨g, h3, ?_⟩
    suffices : EqOn h (λ _ => 1) U
    { exact λ z hz => eq_of_div_eq_one (this hz) }
    have : 1 = h z₀ := by simp [exp_log, hfz z₀ hz₀]
    rw [this]
    refine EqOn_of_deriv_eq_zero hU hU' e1 (λ z hz => ?_) hz₀
    have f0 : U ∈ 𝓝 z := hU.mem_nhds hz
    dsimp
    rw [Pi.div_def, deriv_div (hf.differentiableAt f0) (e4.differentiableAt f0) (exp_ne_zero _)]
    rw [deriv.scomp z differentiableAt_exp (h3.differentiableAt f0)]
    have e5 : deriv g z = deriv lf z := by simp
    field_simp [exp_ne_zero, hlf2 hz, hfz z hz, e5]
    ring