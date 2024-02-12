import Mathlib
import RMT4.Primitive

set_option autoImplicit false

variable {f : ℂ → ℂ} {w z z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ : ℂ} {x x₁ x₂ y y₁ y₂ : ℝ} {U : Set ℂ}

open Complex Set Metric

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

theorem convex_neighborhood (hU : IsOpen U) (hzw : segment ℝ z w ⊆ U) :
    ∃ V : Set ℂ, IsOpen V ∧ segment ℝ z w ⊆ V ∧ V ⊆ U ∧ Convex ℝ V := by
  obtain ⟨δ, hδ, hδU⟩ := isCompact_segment.exists_thickening_subset_open hU hzw
  exact ⟨_, isOpen_thickening, self_subset_thickening hδ _, hδU, (convex_segment z w).thickening _⟩

theorem nocheat (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hzw : segment ℝ z w ⊆ U) :
    HasDerivAt (SegmentIntegral f z) (f w) w := by
  rw [shim]
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := convex_neighborhood hU hzw
  have h1 : DifferentiableOn ℂ f V := hf.mono hV3
  have h2 : w ∈ V := hV2 (right_mem_segment ℝ z w)
  have h3 : StarConvex ℝ z V :=hV4.starConvex <| hV2 (left_mem_segment ℝ z w)
  apply DifferentiableOn.exists_primitive h1 h3 hV1 h2

theorem nocheat' (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hzw : segment ℝ z w ⊆ U) :
    HasDerivAt (λ z => SegmentIntegral f z w) (- f z) z := by
  have : (λ z => SegmentIntegral f z w) = (λ z => - SegmentIntegral f w z) := by
    ext ; exact SegmentIntegral.symm
  rw [this]
  exact (nocheat hU hf (segment_symm ℝ w z ▸ hzw)).neg

noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable def QuadIntegral (f : ℂ → ℂ) (w₁ w₂ w₃ w₄ : ℂ) : ℂ := SegmentIntegral f w₁ w₂ +
    SegmentIntegral f w₂ w₃ + SegmentIntegral f w₃ w₄ + SegmentIntegral f w₄ w₁

def QuadSupport (w₁ w₂ w₃ w₄ : ℂ) : Set ℂ := segment ℝ w₁ w₂ ∪ segment ℝ w₂ w₃ ∪ segment ℝ w₃ w₄ ∪
    segment ℝ w₄ w₁

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

theorem loc_constant_4 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (h : QuadSupport z₁ z₂ z₃ z₄ ⊆ U) : HasDerivAt (QuadIntegral f z₁ z₂ z₃) 0 z₄ := by
  have l3 : HasDerivAt (λ z => SegmentIntegral f z₃ z) (f z₄) z₄ := by
    refine nocheat hU hf <| Subset.trans ?_ h
    refine Subset.trans ?_ (subset_union_left _ _)
    exact subset_union_right _ _
  have l1 : HasDerivAt (λ z => SegmentIntegral f z₁ z₂ + SegmentIntegral f z₂ z₃ +
      SegmentIntegral f z₃ z) (f z₄) z₄ := by
    simpa using (hasDerivAt_const z₄ _).add l3
  have l2 : HasDerivAt (λ z => SegmentIntegral f z z₁) (- f z₄) z₄ := by
    apply nocheat' hU hf <| Subset.trans (by simp [QuadSupport]) h
  simpa using l1.add l2
