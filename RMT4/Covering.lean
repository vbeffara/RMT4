import Mathlib
import RMT4.pintegral

open Topology Filter Metric TopologicalSpace

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

def holo_covering (_ : HasLocalPrimitiveOn U f) := U × ℂ

namespace holo_covering

def is_nhd_of (h : HasLocalPrimitiveOn U f) (z : holo_covering h) (s : Set (holo_covering h)) : Prop :=
  ∃ F : ℂ → ℂ, ∀ᶠ w in 𝓝 z.1, HasDerivAt F (f w) w ∧
    ∀ hw : w ∈ U, (⟨w, hw⟩, z.2 + (F w - F z.1)) ∈ s

def basic_nhd (h : HasLocalPrimitiveOn U f) (Λ : LocalPrimitiveOn U f) (z : U) (u : ℂ) :
    Set (holo_covering h) := (λ (w : U) => (w, u + (Λ.F z w - Λ.F z z))) '' U.restrict (Λ.S z)

lemma is_nhd (h : HasLocalPrimitiveOn U f) (Λ : LocalPrimitiveOn U f) (z : holo_covering h) :
  is_nhd_of h z (basic_nhd h Λ z.1 z.2) := sorry

def nhd (h : HasLocalPrimitiveOn U f) (z : holo_covering h) :
    Filter (holo_covering h) where
  sets := { s | is_nhd_of h z s }
  univ_sets := by
    obtain ⟨F, hF⟩ := HasLocalPrimitiveOn.iff.1 h z.1 z.1.prop
    use F
    filter_upwards [hF] with w h using ⟨h, by simp⟩
  sets_of_superset := by
    rintro s1 s2 ⟨F, hF⟩ h2
    use F
    filter_upwards [hF] with w ⟨hw1, hw2⟩ using ⟨hw1, λ hw => h2 (hw2 hw)⟩
  inter_sets := by
    rintro s1 s2 ⟨F1, hF1⟩ ⟨F2, hF2⟩
    use F1
    filter_upwards [hF1, hF2, key (eventually_and.1 hF1).1 (eventually_and.1 hF2).1]
      with w ⟨e1, e2⟩ ⟨_, e4⟩ e5 using ⟨e1, λ hw => ⟨e2 hw, e5 ▸ e4 hw⟩⟩

lemma pure_le_nhd (h : HasLocalPrimitiveOn U f) : pure ≤ nhd h := by
  intro a
  rw [Filter.pure_le_iff]
  intro s hs
  simp [nhd, is_nhd_of] at hs
  obtain ⟨F, _, h2⟩ := hs
  simpa using h2.self_of_nhds a.1.prop

lemma nhd_of_nhd (h : HasLocalPrimitiveOn U f) (a : holo_covering h) :
    ∀ s ∈ nhd h a, ∃ t ∈ nhd h a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ nhd h a' := sorry

instance : TopologicalSpace (holo_covering h) := TopologicalSpace.mkOfNhds (nhd h)

def p (h : HasLocalPrimitiveOn U f) : holo_covering h → U := λ z => z.1

lemma mem_nhds (h : HasLocalPrimitiveOn U f) (z : holo_covering h) (s : Set (holo_covering h)) :
    s ∈ 𝓝 z ↔ is_nhd_of h z s := by
  rw [nhds_mkOfNhds (nhd h) z (pure_le_nhd h) (nhd_of_nhd h)] ; rfl

lemma discreteTopology {U : Set ℂ} {f : ℂ → ℂ} (h : HasLocalPrimitiveOn U f) (z : U) :
    DiscreteTopology ↑(p h ⁻¹' {z}) := by
  simp only [discreteTopology_iff_singleton_mem_nhds]
  intro ⟨⟨x₁, x₂⟩, hx⟩
  simp [p] at hx ; subst hx
  simp [nhds_induced, mem_nhds h]
  obtain ⟨Λ⟩ := id h
  refine ⟨basic_nhd h Λ x₁ x₂, is_nhd h Λ _, ?_⟩
  rintro ⟨w₁, w₂⟩ rfl hb
  simp [basic_nhd] at hb
  rcases hb with ⟨a, ha, _, h2⟩
  refine Prod.ext rfl ?_
  rw [← h2]
  rw [Prod.ext_iff] at h2
  simp [p] at h2
  simp [p, ← h2.1]

theorem main (h : HasLocalPrimitiveOn U f) : IsCoveringMap (p h) := by
  intro z
  refine ⟨discreteTopology h z, ?_⟩
  sorry

end holo_covering