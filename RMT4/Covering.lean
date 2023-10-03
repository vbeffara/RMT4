import Mathlib
import RMT4.pintegral

open Topology Filter Metric

lemma prekey {f : ℂ → ℂ} {z : ℂ} (h : ∀ᶠ w in 𝓝 z, HasDerivAt f 0 w) : ∀ᶠ w in 𝓝 z, f w = f z := by
  rw [eventually_nhds_iff_ball] at h ⊢
  obtain ⟨r, hr, hf⟩ := h
  refine ⟨r, hr, λ w hw => ?_⟩
  refine (convex_ball z r).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ) ?_ ?_ hw (mem_ball_self hr)
  · exact λ w hw => (hf w hw).differentiableAt.differentiableWithinAt
  · intro w hw
    have l1 : UniqueDiffWithinAt ℂ (ball z r) w := isOpen_ball.uniqueDiffWithinAt hw
    convert (hf w hw).hasFDerivAt.hasFDerivWithinAt.fderivWithin l1
    ext1 ; simp

lemma key {F1 F2 f : ℂ → ℂ}
    (h1 : ∀ᶠ w in 𝓝 z, HasDerivAt F1 (f w) w)
    (h2 : ∀ᶠ w in 𝓝 z, HasDerivAt F2 (f w) w) :
    ∀ᶠ w in 𝓝 z, F2 w - F2 z = F1 w - F1 z := by
  have : ∀ᶠ w in 𝓝 z, HasDerivAt (F2 - F1) 0 w := by
    filter_upwards [h1, h2] with w h1 h2 ; simpa using h2.sub h1
  filter_upwards [prekey this] with w h ; simpa [sub_eq_sub_iff_sub_eq_sub] using h

def holo_covering (_ : ℂ → ℂ) (U : Set ℂ) := U × ℂ

namespace holo_covering

variable {f : ℂ → ℂ} {U : Set ℂ} [T : Fact (HasLocalPrimitiveOn U f)] [T' : Fact (IsOpen U)]

def is_nhd_of (z : holo_covering f U) (s : Set (holo_covering f U)) : Prop :=
  ∃ F : ℂ → ℂ, ∀ᶠ w in 𝓝 z.1, HasDerivAt F (f w) w ∧
    ∀ hw : w ∈ U, (⟨w, hw⟩, z.2 + (F w - F z.1)) ∈ s

def nhd (z : holo_covering f U) : Filter (holo_covering f U) where
  sets := { s | is_nhd_of z s }
  univ_sets := by
    obtain ⟨F, hF⟩ := HasLocalPrimitiveOn.iff.1 T.out z.1 z.1.prop
    use F
    filter_upwards [hF] with w h using ⟨h, by simp⟩
  sets_of_superset {s1 s2} h1 h2 := by
    obtain ⟨F, hF⟩ := h1
    use F
    filter_upwards [hF] with w ⟨hw1, hw2⟩ using ⟨hw1, λ hw => h2 (hw2 hw)⟩
  inter_sets {s1 s2} h1 h2 := by
    obtain ⟨F1, hF1⟩ := h1
    obtain ⟨F2, hF2⟩ := h2
    have l3 := key (eventually_and.1 hF1).1 (eventually_and.1 hF2).1
    use F1
    filter_upwards [hF1, hF2, l3] with w ⟨e1, e2⟩ ⟨_, e4⟩ e5 using ⟨e1, λ hw => ⟨e2 hw, e5 ▸ e4 hw⟩⟩

instance : TopologicalSpace (holo_covering f U) := TopologicalSpace.mkOfNhds nhd

def p : holo_covering f U → U := λ z => z.1

theorem main : IsCoveringMap (p : holo_covering f U → U) := sorry

end holo_covering