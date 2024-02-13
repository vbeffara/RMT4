import Mathlib
import RMT4.Primitive

set_option autoImplicit false

variable {f f' F : ℂ → ℂ} {w z z₁ z₂ z₃ z₄ w₁ w₂ w₃ w₄ p : ℂ} {W : Fin 4 -> ℂ}
  {t x x₁ x₂ y y₁ y₂ : ℝ} {U : Set ℂ} {γ₁ γ₂ : ℝ → ℂ}

open Complex Set Metric Topology Interval

local notation "𝕀" => Icc (0 : ℝ) 1

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
  have h3 : StarConvex ℝ z V := hV4.starConvex <| hV2 (left_mem_segment ℝ z w)
  apply DifferentiableOn.exists_primitive h1 h3 hV1 h2

theorem nocheat' (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hzw : segment ℝ z w ⊆ U) :
    HasDerivAt (λ z => SegmentIntegral f z w) (- f z) z := by
  have : (λ z => SegmentIntegral f z w) = (λ z => - SegmentIntegral f w z) := by
    ext ; exact SegmentIntegral.symm
  rw [this]
  exact (nocheat hU hf (segment_symm ℝ w z ▸ hzw)).neg

theorem SegmentIntegral_deriv (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hzw : segment ℝ z w ⊆ U) : SegmentIntegral (deriv f) z w = f w - f z := by
  have l0 : MapsTo (fun t => z + t • (w - z)) (Icc (0 : ℝ) 1) U := by
    intro t ht ; apply hzw ; convert mem_segment ht using 1 ; simp ; ring
  have l1 : ContinuousOn (fun t => deriv f (z + t • (w - z))) (Icc 0 1 : Set ℝ) := by
    refine (hf.deriv hU).continuousOn.comp ?_ l0
    apply Continuous.continuousOn
    continuity
  have l2 : ∀ t ∈ (Icc 0 1 : Set ℝ), HasDerivAt f (deriv f (z + t • (w - z))) (z + t • (w - z)) := by
    intro t ht
    refine hasDerivAt_deriv_iff.mpr ?_
    refine hf.differentiableAt ?_
    apply hU.mem_nhds
    exact l0 ht
  simpa using intervalIntegral.integral_unitInterval_deriv_eq_sub l1 l2

lemma mapsto_segment (h : segment ℝ z w ⊆ U) : MapsTo (fun t => z + t • (w - z)) 𝕀 U := by
  intro t ht ; apply h ; convert mem_segment ht using 1 ; simp ; ring

theorem SegmentIntegral_deriv' (hf : ContinuousOn f U) (hzw : segment ℝ z w ⊆ U)
    (h'2 : ∀ z ∈ U, HasDerivAt F (f z) z) : SegmentIntegral f z w = F w - F z := by
  have l1 : ContinuousOn (fun t => f (z + t • (w - z))) 𝕀 := by
    refine hf.comp ?_ <| mapsto_segment hzw
    apply Continuous.continuousOn ; continuity
  have l2 (t : ℝ) (ht : t ∈ 𝕀) : HasDerivAt F (f (z + t • (w - z))) (z + t • (w - z)) :=
    h'2 _ <| mapsto_segment hzw ht
  simpa using intervalIntegral.integral_unitInterval_deriv_eq_sub l1 l2

theorem LineIntegral_diff (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hγ₁ : Differentiable ℝ γ₁)
    (hγ₂ : Differentiable ℝ γ₂) (h : segment ℝ (γ₁ t) (γ₂ t) ⊆ U) :
    HasDerivAt (λ t => SegmentIntegral f (γ₁ t) (γ₂ t))
    (f (γ₂ t) * deriv γ₂ t - f (γ₁ t) * deriv γ₁ t) t := by
  obtain ⟨V, hV1, hV2, hV3, hV4⟩ := convex_neighborhood hU h
  have e5 : γ₁ t ∈ V := hV2 <| left_mem_segment ℝ (γ₁ t) (γ₂ t)
  have e4 : γ₂ t ∈ V := hV2 <| right_mem_segment ℝ (γ₁ t) (γ₂ t)
  have (z : ℂ) (hz : z ∈ V) : HasDerivAt (primitive f (γ₁ t)) (f z) z :=
    (hf.mono hV3).exists_primitive (hV4.starConvex e5) hV1 hz
  have e1 : ∀ᶠ s in 𝓝 t, γ₁ s ∈ V := hγ₁.continuous.continuousAt <| hV1.mem_nhds e5
  have e2 : ∀ᶠ s in 𝓝 t, γ₂ s ∈ V := hγ₂.continuous.continuousAt <| hV1.mem_nhds e4
  have e3 : DifferentiableOn ℂ (primitive f (γ₁ t)) V := by
    intro z hz ; exact (this z hz).differentiableAt.differentiableWithinAt
  have l1 : ∀ᶠ s in 𝓝 t, SegmentIntegral f (γ₁ s) (γ₂ s) =
      primitive f (γ₁ t) (γ₂ s) - primitive f (γ₁ t) (γ₁ s) := by
    filter_upwards [e1, e2] with s hs1 hs2
    have e4 : segment ℝ (γ₁ s) (γ₂ s) ⊆ V := hV4.segment_subset hs1 hs2
    rw [← SegmentIntegral_deriv hV1 e3 e4]
    simp [SegmentIntegral] ; left
    apply intervalIntegral.integral_congr
    intro t ht
    simp
    have e5 := hV4.add_smul_mem (y := γ₂ s - γ₁ s) hs1 (by simpa using hs2) (by simpa using ht)
    exact (this (γ₁ s + t * (γ₂ s - γ₁ s)) (by simpa using e5)).deriv.symm
  refine HasDerivAt.congr_of_eventuallyEq (HasDerivAt.sub ?_ ?_) l1
  · exact this (γ₂ t) e4 |>.comp _ (hγ₂ t).hasDerivAt
  · exact this (γ₁ t) e5 |>.comp _ (hγ₁ t).hasDerivAt

noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

noncomputable def QuadIntegral (f : ℂ → ℂ) (w₁ w₂ w₃ w₄ : ℂ) : ℂ := SegmentIntegral f w₁ w₂ +
    SegmentIntegral f w₂ w₃ + SegmentIntegral f w₃ w₄ + SegmentIntegral f w₄ w₁

noncomputable def QuadIntegral' (f : ℂ → ℂ) (w : Fin 4 -> ℂ) : ℂ :=
    QuadIntegral f (w 0) (w 1) (w 2) (w 3)

def QuadSupport (w₁ w₂ w₃ w₄ : ℂ) : Set ℂ := segment ℝ w₁ w₂ ∪ segment ℝ w₂ w₃ ∪ segment ℝ w₃ w₄ ∪
    segment ℝ w₄ w₁

def QuadSupport' (w : Fin 4 -> ℂ) : Set ℂ := QuadSupport (w 0) (w 1) (w 2) (w 3)

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

theorem loc_constant_1 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (h : QuadSupport z₁ z₂ z₃ z₄ ⊆ U) : HasDerivAt (λ z => QuadIntegral f z z₂ z₃ z₄) 0 z₁ := by
  simp only [QuadSupport, union_subset_iff] at h
  simpa using (nocheat' hU hf (by tauto)) |>.add (hasDerivAt_const _ _)
    |>.add (hasDerivAt_const _ _) |>.add (nocheat hU hf (by tauto))

theorem loc_constant_2 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (h : QuadSupport z₁ z₂ z₃ z₄ ⊆ U) : HasDerivAt (λ z => QuadIntegral f z₁ z z₃ z₄) 0 z₂ := by
  simp only [QuadSupport, union_subset_iff] at h
  simpa using (nocheat hU hf (by tauto)) |>.add (nocheat' hU hf (by tauto))
    |>.add (hasDerivAt_const _ _) |>.add (hasDerivAt_const _ _)

theorem loc_constant_3 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (h : QuadSupport z₁ z₂ z₃ z₄ ⊆ U) : HasDerivAt (λ z => QuadIntegral f z₁ z₂ z z₄) 0 z₃ := by
  simp only [QuadSupport, union_subset_iff] at h
  simpa using (hasDerivAt_const _ _) |>.add (nocheat hU hf (by tauto))
    |>.add (nocheat' hU hf (by tauto)) |>.add (hasDerivAt_const _ _)

theorem loc_constant_4 (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (h : QuadSupport z₁ z₂ z₃ z₄ ⊆ U) : HasDerivAt (λ z => QuadIntegral f z₁ z₂ z₃ z) 0 z₄ := by
  simp only [QuadSupport, union_subset_iff] at h
  simpa using hasDerivAt_const _ _ |>.add (nocheat hU hf (by tauto))
    |>.add (nocheat' hU hf (by tauto))

example {hf : Differentiable ℂ f} {γ : ℝ → ℂ} {hγ : Differentiable ℝ γ} {t : ℝ} :
    HasDerivAt (f ∘ γ) (deriv f (γ t) * deriv γ t) t := by
  refine @HasDerivAt.comp ℝ _ t ℂ _ _ γ f (deriv γ t) (deriv f (γ t)) ?_ ?_
  exact hasDerivAt_deriv_iff.mpr (hf (γ t))
  exact hasDerivAt_deriv_iff.mpr (hγ t)

abbrev HolomorphicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) (s : Set ℂ) :
    Prop := DifferentiableOn ℂ f s

def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

theorem QuadIntegral_cancel (hf : ContinuousOn f U) (hQ : QuadSupport w₁ w₂ w₃ w₄ ⊆ U)
    (h' : ∃ F : ℂ → ℂ, ∀ z ∈ U, HasDerivAt F (f z) z) : QuadIntegral f w₁ w₂ w₃ w₄ = 0 := by
  simp [QuadSupport] at hQ ; obtain ⟨⟨⟨l2, l3⟩, l4⟩, l5⟩ := hQ
  obtain ⟨F, hF2⟩ := h'
  simp [QuadIntegral, SegmentIntegral_deriv' hf l2 hF2, SegmentIntegral_deriv' hf l3 hF2,
    SegmentIntegral_deriv' hf l4 hF2, SegmentIntegral_deriv' hf l5 hF2]

-- example {a b c d : ℝ} (h1 : a = b) (h2 : c = d) : a + c = b + d := by
--   exact Mathlib.Tactic.LinearCombination.add_pf h1 h2

lemma mine (h1 : z.re < 0) (h2 : 0 < w.re) (h3 : z.im < 0) (h4 : 0 < w.im) (hU : IsOpen U)
    (hf : HolomorphicOn f (U \ {0})) (h : Rectangle z w ⊆ U) : ∀ᶠ c : ℝ in 𝓝[>] 0,
    RectangleIntegral f z w = RectangleIntegral f (- c - c * I) (c + c * I) := by
  have h1 : ∀ᶠ c : ℝ in 𝓝[>] 0, z.re < - c := sorry
  have h2 : ∀ᶠ c : ℝ in 𝓝[>] 0, c < w.re := sorry
  have h3 : ∀ᶠ c : ℝ in 𝓝[>] 0, z.im < - c := sorry
  have h4 : ∀ᶠ c : ℝ in 𝓝[>] 0, c < w.im := sorry
  filter_upwards [h1, h2, h3, h4] with c c1 c2 c3 c4
  let w₁ := - c - c * I
  let w₂ := c - c * I
  let w₃ := c + c * I
  let w₄ := - c + c * I

  rw [rect_eq_quad, rect_eq_quad, ← sub_eq_zero]

  have la1 : ContinuousOn f (Rectangle z (zw w₁ w)) := sorry
  have la2 : QuadSupport z (zw z w) w₂ w₁ ⊆ Rectangle z (zw w₁ w) := sorry
  have la3 : (∃ F, ∀ z_1 ∈ Rectangle z (zw w₁ w), HasDerivAt F (f z_1) z_1) := sorry
  have la := QuadIntegral_cancel la1 la2 la3 ; clear la1 la2 la3

  have lb1 : ContinuousOn f (Rectangle (zw z w₂) w) := sorry
  have lb2 : QuadSupport (zw z w) w w₃ w₂ ⊆ Rectangle (zw z w₂) w := sorry
  have lb3 : (∃ F, ∀ z_1 ∈ Rectangle (zw z w₂) w, HasDerivAt F (f z_1) z_1) := sorry
  have lb := QuadIntegral_cancel lb1 lb2 lb3 ; clear lb1 lb2 lb3

  have lc1 : ContinuousOn f (Rectangle (zw w₄ z) w) := sorry
  have lc2 : QuadSupport w (zw w z) w₄ w₃ ⊆ Rectangle (zw w₄ z) w := sorry
  have lc3 : (∃ F, ∀ z_1 ∈ Rectangle (zw w₄ z) w, HasDerivAt F (f z_1) z_1) := sorry
  have lc := QuadIntegral_cancel lc1 lc2 lc3 ; clear lc1 lc2 lc3

  have ld1 : ContinuousOn f (Rectangle z (zw w w₄)) := sorry
  have ld2 : QuadSupport (zw w z) z w₁ w₄ ⊆ Rectangle z (zw w w₄) := sorry
  have ld3 : (∃ F, ∀ z_1 ∈ Rectangle z (zw w w₄), HasDerivAt F (f z_1) z_1) := sorry
  have ld := QuadIntegral_cancel ld1 ld2 ld3 ; clear ld1 ld2 ld3

  have le := Mathlib.Tactic.LinearCombination.add_pf la lb
  have lf := Mathlib.Tactic.LinearCombination.add_pf lc ld
  have lg := Mathlib.Tactic.LinearCombination.add_pf le lf
  simp [QuadIntegral] at lg ⊢
  convert lg using 1 ; clear lg
  rw [← sub_eq_zero]
  ring_nf
  simp only [SegmentIntegral.symm (z := zw z w)] ; ring_nf
  simp only [SegmentIntegral.symm (z := zw w z)] ; ring_nf
  simp only [SegmentIntegral.symm (z := z)] ; ring_nf
  simp only [SegmentIntegral.symm (z := w)] ; ring_nf
  simp [zw] ; ring_nf
  simp only [SegmentIntegral.symm (z := ↑c + ↑c * I)] ; ring_nf
  simp only [SegmentIntegral.symm (z := -↑c - ↑c * I)] ; ring_nf

lemma RectanglePullToNhdOfPole {f : ℂ → ℂ} {z w p : ℂ} (zRe_lt_wRe : z.re < w.re)
    (zIm_lt_wIm : z.im < w.im) (pInRectInterior : Rectangle z w ∈ nhds p)
    (fHolo : HolomorphicOn f (Rectangle z w \ {p})) :
    ∀ᶠ (c : ℝ) in 𝓝[>]0, RectangleIntegral f z w =
      RectangleIntegral f (-c - I * c + p) (c + I * c + p) := by
  sorry
