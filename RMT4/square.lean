import Mathlib

set_option autoImplicit false

local notation "𝕀" => unitInterval

open Complex

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {w z : V}
  {t x x₁ x₂ y y₁ y₂ a b : ℝ} {f : ℂ → ℂ} {γ : ℝ → ℂ}

noncomputable def RectangleIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
    ((∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I))
     + I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) - I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I))

structure C1Path where
  toFun : ℝ → ℂ
  contDiffOn : ContDiffOn ℝ 1 toFun 𝕀

noncomputable def concat (Γ₁ Γ₂ : C1Path) (h0 : Γ₁.toFun 1 = Γ₂.toFun 0)
    (h1 : derivWithin Γ₁.toFun 𝕀 1 = derivWithin Γ₂.toFun 𝕀 0) : C1Path where
  toFun t := if t ≤ 0.5 then Γ₁.toFun (2 * t) else Γ₂.toFun (2 * t - 1)
  contDiffOn := by
    refine (contDiffOn_succ_iff_derivWithin uniqueDiffOn_Icc_zero_one).mpr ⟨?_, ?_⟩
    · sorry
    · sorry

noncomputable def cint (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℂ := ∫ t in a..b, deriv γ t • f (γ t)

noncomputable def C1Int (f : ℂ → ℂ) (Γ : C1Path) : ℂ := cint f Γ.toFun 0 1

abbrev φ : ℝ → ℝ := fun t => 3 * t ^ 2 - 2 * t ^ 3
abbrev φ' : ℝ → ℝ := fun t => 6 * t - 6 * t ^ 2

@[simp] theorem φ_zero : φ 0 = 0 := by norm_num
@[simp] theorem φ_one : φ 1 = 1 := by norm_num
@[simp] theorem φ'_zero : φ' 0 = 0 := by norm_num
@[simp] theorem φ'_one : φ' 1 = 0 := by norm_num

theorem φ_hasderiv : HasDerivAt φ (φ' t) t := by
  have h1 : HasDerivAt (fun x => x ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have h2 : HasDerivAt (fun x => x ^ 3) (3 * t ^ 2) t := hasDerivAt_pow 3 t
  have h3 : HasDerivAt (fun x => 3 * x ^ 2) (6 * t) t := by
    convert h1.const_mul 3 using 1 ; ring
  have h4 : HasDerivAt (fun x => 2 * x ^ 3) (6 * t ^ 2) t := by
    convert h2.const_mul 2 using 1 ; ring
  exact h3.sub h4

@[simp] theorem φ_deriv : deriv φ t = φ' t := φ_hasderiv.deriv

theorem φ'_continuous : Continuous φ' := by continuity

noncomputable abbrev Φ (w z : V) (t : ℝ) : V := w + φ t • (z - w)
noncomputable abbrev Φ' (w z : V) (t : ℝ) : V := φ' t • (z - w)

theorem Φ_hasderiv : HasDerivAt (Φ w z) (Φ' w z t) t := (φ_hasderiv.smul_const _).const_add _

@[simp] theorem Φ_deriv : deriv (Φ w z) = Φ' w z := by ext1 t; exact Φ_hasderiv.deriv
@[simp] theorem Φ_zero : Φ w z 0 = w := by simp
@[simp] theorem Φ_one : Φ w z 1 = z := by simp [Φ]
@[simp] theorem Φ'_zero : Φ' w z 0 = 0 := by simp
@[simp] theorem Φ'_one : Φ' w z 1 = 0 := by simp

theorem Φ'_continuous : Continuous (Φ' w z) := φ'_continuous.smul continuous_const

noncomputable def Ψ (w z : ℂ) : C1Path where
  toFun := Φ w z
  contDiffOn := by
    apply ContDiff.contDiffOn
    apply contDiff_succ_iff_deriv.mpr
    constructor
    · exact fun t => Φ_hasderiv.differentiableAt
    · simpa only [Nat.zero_eq, CharP.cast_eq_zero, contDiff_zero, Φ_deriv] using Φ'_continuous

noncomputable def LineIntegral (f : ℂ → ℂ) (z w : ℂ) : ℂ := C1Int f (Ψ z w)

theorem SideIntegral_eq_LineIntegral {f : ℂ → ℂ} (hf : Continuous f) :
    ∫ x : ℝ in x₁..x₂, f (x + y * I) = LineIntegral f (x₁ + y * I) (x₂ + y * I) := by
  have := @intervalIntegral.integral_comp_smul_deriv ℂ _ _ 0 1 (Φ x₁ x₂) (Φ' x₁ x₂)
    (λ x => f (x + y * I)) (fun _ _ => Φ_hasderiv) Φ'_continuous.continuousOn (by continuity)
  rw [Φ_zero, Φ_one] at this
  rw [← this]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Ψ, Φ, Φ_deriv, Φ', φ']
  simp; left; ring_nf

theorem SideIntegral_eq_LineIntegral' {f : ℂ → ℂ} (hf : Continuous f) :
    I * ∫ y : ℝ in y₁..y₂, f (x + y * I) = LineIntegral f (x + y₁ * I) (x + y₂ * I) := by
  have := @intervalIntegral.integral_comp_smul_deriv ℂ _ _ 0 1 (Φ y₁ y₂) (Φ' y₁ y₂)
    (λ y => f (x + y * I)) (fun _ _ => Φ_hasderiv) Φ'_continuous.continuousOn (by continuity)
  rw [Φ_zero, Φ_one] at this
  rw [← this]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Φ, Φ_deriv, Φ', φ', Ψ]
  simp ; ring_nf

def zw (z w : ℂ) : ℂ := w.re + z.im * I

theorem RectangleIntegral_of_LineIntegral {z w : ℂ} (hf : Continuous f) : RectangleIntegral f z w =
    LineIntegral f z (zw z w) + LineIntegral f (zw z w) w + LineIntegral f w (zw w z) +
    LineIntegral f (zw w z) z := by
  simp_rw [RectangleIntegral, smul_eq_mul, sub_eq_add_neg, ← mul_neg]
  simp_rw [← intervalIntegral.integral_symm]
  simp_rw [SideIntegral_eq_LineIntegral hf, SideIntegral_eq_LineIntegral' hf]
  simp [zw]; abel

noncomputable abbrev RC (z w : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 then Φ z (zw z w) t else
  if t ≤ 2 then Φ (zw z w) w (t - 1) else
  if t ≤ 3 then Φ w (zw w z) (t - 2) else
  Φ (zw w z) z (t - 3)

noncomputable def RRCC (z w : ℂ) : C1Path := by
  let p1 := concat (Ψ z (zw z w)) (Ψ (zw z w) w) (by simp [Ψ]) sorry
  let p2 := concat (Ψ w (zw w z)) (Ψ (zw w z) z) (by simp [Ψ]) sorry
  exact concat p1 p2 sorry sorry

theorem RC_1 {z w : ℂ} (ht : t ∈ Set.uIcc 0 1) : RC z w t = Φ z (zw z w) t := sorry
theorem RC_2 {z w : ℂ} (ht : t ∈ Set.uIcc 1 2) : RC z w t = Φ (zw z w) w (t - 1) := sorry
theorem RC_3 {z w : ℂ} (ht : t ∈ Set.uIcc 2 3) : RC z w t = Φ w (zw w z) (t - 2) := sorry
theorem RC_4 {z w : ℂ} (ht : t ∈ Set.uIcc 3 4) : RC z w t = Φ (zw w z) z (t - 3) := sorry

noncomputable abbrev RC' (z w : ℂ) (t : ℝ) : ℂ :=
  if t ≤ 1 then Φ' z (zw z w) t else
  if t ≤ 2 then Φ' (zw z w) w (t - 1) else
  if t ≤ 3 then Φ' w (zw w z) (t - 2) else
  Φ' (zw w z) z (t - 3)

theorem RC'_1 {z w : ℂ} (ht : t ∈ Set.uIcc 0 1) : RC' z w t = Φ' z (zw z w) t := sorry
theorem RC'_2 {z w : ℂ} (ht : t ∈ Set.uIcc 1 2) : RC' z w t = Φ' (zw z w) w (t - 1) := sorry
theorem RC'_3 {z w : ℂ} (ht : t ∈ Set.uIcc 2 3) : RC' z w t = Φ' w (zw w z) (t - 2) := sorry
theorem RC'_4 {z w : ℂ} (ht : t ∈ Set.uIcc 3 4) : RC' z w t = Φ' (zw w z) z (t - 3) := sorry

theorem RC_hasderiv {z w : ℂ} {t : ℝ} : HasDerivAt (RC z w) (RC' z w t) t := by sorry
@[simp] theorem RC_deriv {z w : ℂ} {t : ℝ} : deriv (RC z w) t = RC' z w t := RC_hasderiv.deriv

theorem side_1 {z w : ℂ} :
    ∫ x in (0 : ℝ)..1, RC' z w x • f (RC z w x) = LineIntegral f z (zw z w) := by
  apply intervalIntegral.integral_congr
  intro t ht
  simp [RC_1, RC'_1, ht, Φ_deriv]

theorem side_2 {z w : ℂ} :
    ∫ x in (1 : ℝ)..2, RC' z w x • f (RC z w x) = LineIntegral f (zw z w) w := by
  have e1 : (1 : ℝ) = 0 + 1 := by norm_num
  have e2 : (2 : ℝ) = 1 + 1 := by norm_num
  rw [e1, e2, ← intervalIntegral.integral_comp_add_right]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t + 1 ∈ Set.uIcc 1 2 := sorry
  simp [RC_2, RC'_2, ht', Φ_deriv]

theorem side_3 {z w : ℂ} :
    ∫ x in (2 : ℝ)..3, RC' z w x • f (RC z w x) = LineIntegral f w (zw w z) := by
  have e1 : (2 : ℝ) = 0 + 2 := by norm_num
  have e2 : (3 : ℝ) = 1 + 2 := by norm_num
  rw [e1, e2, ← intervalIntegral.integral_comp_add_right]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t + 1 ∈ Set.uIcc 1 2 := sorry
  simp [RC_2, RC'_2, ht', Φ_deriv]

theorem side_4 {z w : ℂ} :
  ∫ x in (3 : ℝ)..4, RC' z w x • f (RC z w x) = LineIntegral f (zw w z) z := by sorry

theorem main_result {z w : ℂ} (hf : Continuous f) :
    RectangleIntegral f z w = cint f (RC z w) 0 4 := by
  rw [RectangleIntegral_of_LineIntegral hf, cint]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 0) (b := 1)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 1) (b := 2)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := 2) (b := 3)]
  simp_rw [RC_deriv, side_1, side_2, side_3, side_4] ; abel
  sorry
