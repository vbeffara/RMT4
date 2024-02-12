import Mathlib
import RMT4.Primitive

set_option autoImplicit false

local notation "𝕀" => unitInterval

variable {f : ℂ → ℂ} {w z z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : ℂ} {x x₁ x₂ y y₁ y₂ : ℝ}

open Complex Set

noncomputable def SegmentIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    (w - z) • ∫ t in (0:ℝ)..1, f (z + t • (w - z))

theorem SegmentIntegral.symm : SegmentIntegral f w z = - SegmentIntegral f z w := by
  simp [SegmentIntegral]
  have := @intervalIntegral.integral_comp_sub_left ℂ _ _ 0 1 (λ t => f (w + (1 - t) * (z - w))) 1
  simp at this ; rw [this]
  ring_nf ; congr <;> ext <;> ring_nf

theorem shim : SegmentIntegral = primitive := by
  ext f z w
  simp [SegmentIntegral, primitive]
  left
  apply intervalIntegral.integral_congr
  intro t _
  simp ; ring_nf

theorem cheat (hf : Differentiable ℂ f) : HasDerivAt (SegmentIntegral f z) (f w) w := by
  have h1 : StarConvex ℝ z (univ : Set ℂ) := starConvex_univ z
  rw [shim]
  exact @DifferentiableOn.exists_primitive f z w univ hf.differentiableOn h1 isOpen_univ (mem_univ _)

theorem cheat' (hf : Differentiable ℂ f) : HasDerivAt (λ z => SegmentIntegral f z w) (- f z) z := by
  have : (λ z => SegmentIntegral f z w) = (λ z => - SegmentIntegral f w z) := by
    ext ; exact SegmentIntegral.symm
  rw [this]
  exact (cheat hf).neg

noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable def QuadIntegral (f : ℂ → ℂ) (w₁ w₂ w₃ w₄ : ℂ) : ℂ := SegmentIntegral f w₁ w₂ +
    SegmentIntegral f w₂ w₃ + SegmentIntegral f w₃ w₄ + SegmentIntegral f w₄ w₁

theorem QuadIntegral_rotate : QuadIntegral f w₂ w₃ w₄ w₁ = QuadIntegral f w₁ w₂ w₃ w₄ := by
  simp [QuadIntegral] ; abel

theorem SideIntegral_eq_LineIntegral {f : ℂ → ℂ} :
    ∫ x : ℝ in x₁..x₂, f (x + y * I) = SegmentIntegral f (x₁ + y * I) (x₂ + y * I) := by
  have := @intervalIntegral.smul_integral_comp_mul_add ℂ _ _ _ 0 1 (fun z => f (z + y * I)) (x₂ - x₁) x₁
  simp at this
  rw [← this]
  simp [SegmentIntegral]
  left
  congr ; ext ; ring_nf

theorem SideIntegral_eq_LineIntegral' {f : ℂ → ℂ} :
    I • ∫ y : ℝ in y₁..y₂, f (x + y * I) = SegmentIntegral f (x + y₁ * I) (x + y₂ * I) := by
  have := @intervalIntegral.smul_integral_comp_mul_add ℂ _ _ _ 0 1 (fun z => f (x + z * I)) (y₂ - y₁) y₁
  simp at this
  rw [← this]
  simp [SegmentIntegral]
  simp_rw [← mul_assoc, mul_sub, mul_comm]
  congr ; ext ; ring_nf

def zw (z w : ℂ) : ℂ := w.re + z.im * I

theorem rect_eq_quad : RectangleIntegral f z w = QuadIntegral f z (zw z w) w (zw w z) := by
  simp_rw [RectangleIntegral, QuadIntegral, sub_eq_add_neg, ← smul_neg]
  simp_rw [← intervalIntegral.integral_symm]
  simp_rw [SideIntegral_eq_LineIntegral, SideIntegral_eq_LineIntegral']
  simp [zw] ; ring

theorem loc_constant_4 {hf : Differentiable ℂ f} : HasDerivAt (QuadIntegral f z₁ z₂ z₃) 0 z := by
  have : HasDerivAt (fun _ => SegmentIntegral f z₁ z₂ + SegmentIntegral f z₂ z₃) 0 z :=
    hasDerivAt_const z _
  have : HasDerivAt (fun w₄ => SegmentIntegral f z₁ z₂ + SegmentIntegral f z₂ z₃ +
      SegmentIntegral f z₃ w₄) (f z) z := by
    simpa using @HasDerivAt.add _ _ _ _ _ _ (SegmentIntegral f z₃) 0 (f z) z this (cheat hf)
  simpa using HasDerivAt.add (f' := f z) (g' := -f z) (x := z) this (cheat' hf)
