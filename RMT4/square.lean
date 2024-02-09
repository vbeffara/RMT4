import Mathlib

set_option autoImplicit false

open Complex

variable {t x₁ x₂ y a b : ℝ} {w z : ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ}

def φ (t : ℝ) : ℝ := 3 * t^2 - 2 * t^3
def φ' (t : ℝ) : ℝ := 6 * t - 6 * t^2

noncomputable
def cint (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℂ := ∫ t in a..b, deriv γ t • f (γ t)

@[simp] theorem φ_zero : φ 0 = 0 := by norm_num [φ]
@[simp] theorem φ_one : φ 1 = 1 := by norm_num [φ]

theorem φ_hasderiv : HasDerivAt φ (φ' t) t := by
  refine HasDerivAt.sub ?_ ?_
  · have : HasDerivAt (fun x => x ^ 2) (2 * t) t := by
      convert hasDerivAt_pow 2 t ; ring
    convert HasDerivAt.const_mul 3 this using 1 ; ring
  · have : HasDerivAt (fun x => x ^ 3) (3 * t ^ 2) t := by
      convert hasDerivAt_pow 3 t
    convert HasDerivAt.const_mul 2 this using 1 ; ring

theorem φ_deriv : deriv φ t = φ' t := φ_hasderiv.deriv
-- theorem φ_deriv0 : HasDerivAt φ 0 0 := by convert φ_hasderiv ; norm_num
-- theorem φ_deriv1 : HasDerivAt φ 0 1 := by convert φ_hasderiv ; norm_num

theorem φ'_continuous : Continuous φ' := by sorry

def Φ (w z : ℂ) (t : ℝ) : ℂ := w + φ t • (z - w)
theorem Φ_deriv : deriv (Φ w z) t = φ' t • (z - w) := sorry

theorem lineint_eq_cint {f : ℂ → ℂ} (hf : Continuous f):
    (∫ x : ℝ in x₁..x₂, f (x + y * I)) = cint f (Φ (x₁ + y * I) (x₂ + y * I)) 0 1 := by
  simp only [cint]
  have := @intervalIntegral.integral_comp_smul_deriv ℂ _ _ 0 1 φ φ' (fun u => f (w + u • (z - w)))
    (fun t _ => φ_hasderiv) (φ'_continuous.continuousOn) (by continuity)

  let ψ (t : ℝ) : ℝ := x₁ + φ t • (x₂ - x₁)
  let ψ' (t : ℝ) : ℝ := φ' t • (x₂ - x₁)
  have h1 : ∀ x ∈ Set.uIcc 0 1, HasDerivAt ψ (ψ' x) x := sorry
  have h2 : ContinuousOn ψ' (Set.uIcc 0 1) := sorry
  have h3 : Continuous fun (x : ℝ) => f (x + ↑y * I) := sorry
  have h4 : ψ 0 = x₁ := by simp
  have h5 : ψ 1 = x₂ := by simp

  have := @intervalIntegral.integral_comp_smul_deriv ℂ _ _ 0 1 ψ ψ' (λ x => f (x + y * I)) h1 h2 h3
  rw [h4, h5] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro t ht
  simp [Φ, Φ_deriv]; left; ring_nf
