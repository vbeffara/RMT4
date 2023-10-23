import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyConstant.Basic
import RMT4.Glue

set_option autoImplicit false
set_option pp.proofs.withType false

open Set Topology Metric unitInterval

section misc

instance : Top I := ⟨1⟩
instance : OrderTop I := by refine ⟨λ _ => le_one'⟩

lemma isClopen_iff_nhds {α : Type*} [TopologicalSpace α] {s : Set α} :
    IsClopen s ↔ ∀ a, ∀ᶠ b in 𝓝 a, b ∈ s ↔ a ∈ s where
  mp h a := by
    by_cases h3 : a ∈ s
    · simpa [h3] using h.1.mem_nhds h3
    · simpa only [h3, iff_false] using h.2.isOpen_compl.mem_nhds h3
  mpr h := by
    constructor
    · simpa [isOpen_iff_mem_nhds] using λ a ha => by simpa [ha] using h a
    · exact ⟨by simpa [isOpen_iff_mem_nhds] using λ a ha => by simpa only [ha, iff_false] using h a⟩

end misc

section helpers

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : C(I, X)} {A : E}
  {t t₁ t₂ : I}

abbrev II (t : I) : Set ℝ := Icc 0 t
@[simp] lemma II_zero : II 0 = {0} := by simp [II]
lemma mem_II_zero {t : ℝ} : t ∈ II 0 ↔ t = 0 := by simp [II]
@[simp] lemma II_one : II 1 = I := rfl
lemma self_mem_II : ↑t ∈ II t := by simp [II, t.prop.1]
instance : Zero (II t) := by exact ⟨0, le_rfl, t.prop.1⟩
instance : CoeOut (II t) I := ⟨λ s => ⟨↑s, s.prop.1, s.prop.2.trans t.prop.2⟩⟩

def reachable (f : E → X) (γ : C(I, X)) (A : E) (t : I) : Prop :=
  ∃ Γ : C(II t, E), Γ 0 = A ∧ ∀ s, f (Γ s) = γ s

lemma reachable_zero (hγ : γ 0 = f A) : reachable f γ A 0 :=
  ⟨⟨λ _ => A, continuous_const⟩, rfl, λ ⟨s, hs⟩ => by simp [mem_II_zero.1 hs, hγ]⟩

lemma reachable_extend {T : Trivialization (f ⁻¹' {γ t}) f} (h : MapsTo γ (uIcc t₁ t₂) T.baseSet) :
    reachable f γ A t₁ → reachable f γ A t₂ := by
  rintro ⟨Γ, h1, h2⟩
  let ι (u : uIcc (t₁:ℝ) (t₂:ℝ)) : uIcc t₁ t₂ :=
    ⟨⟨u, (le_inf t₁.2.1 t₂.2.1).trans u.2.1, u.2.2.trans (sup_le t₁.2.2 t₂.2.2)⟩, u.2⟩
  set tt₁ : II t₁ := ⟨t₁, self_mem_II⟩
  let δ : C(uIcc (t₁ : ℝ) (t₂ : ℝ), E) := by
    refine ⟨λ s => T.invFun ⟨γ (ι s).1, (T (Γ tt₁)).2⟩, ?_⟩
    refine T.continuous_invFun.comp_continuous (by continuity) (λ s => ?_)
    simpa only [T.target_eq, mem_prod, mem_univ, and_true] using h (ι s).2
  have l1 : f (Γ tt₁) = γ t₁ := h2 tt₁
  have k1 : Γ tt₁ ∈ T.source := by simpa [T.source_eq, h2 tt₁] using h left_mem_uIcc
  have k2 : Γ tt₁ = δ ⟨t₁, left_mem_uIcc⟩ := by
    simpa [← l1, ← T.proj_toFun _ k1] using (T.left_inv' k1).symm
  refine ⟨Γ.trans' t₁.prop.1 δ k2, ?_, λ s => ?_⟩
  · simpa only [← h1] using ContinuousMap.trans'_left t₁.2.1 t₂.2.1 _
  · by_cases hh : (s : ℝ) ≤ t₁
    · simp [ContinuousMap.trans', glue_uIcc, hh, h2 ⟨s, s.2.1, hh⟩]
    · simp only [ContinuousMap.trans', glue_uIcc, ContinuousMap.coe_mk, hh, dite_false]
      set ss : I := ⟨s, _⟩
      have : γ ss ∈ T.baseSet := h ⟨inf_le_left.trans (not_le.1 hh).le, s.2.2.trans le_sup_right⟩
      refine (T.proj_toFun _ (T.map_target' <| by simpa [T.target_eq] using this)).symm.trans ?_
      exact congr_arg Prod.fst (T.right_inv' <| by simpa [T.target_eq] using this)

lemma reachable_nhds_iff (hf : IsCoveringMap f) :
    ∀ᶠ t' in 𝓝 t, reachable f γ A t' ↔ reachable f γ A t := by
  obtain ⟨_, T, h4⟩ := hf (γ t)
  have l2 : γ ⁻¹' T.baseSet ∈ 𝓝 t :=
    γ.continuous_toFun.continuousAt.preimage_mem_nhds <| T.open_baseSet.mem_nhds h4
  simp only [Filter.Eventually, Metric.mem_nhds_iff] at l2 ⊢
  obtain ⟨ε, hε, l3⟩ := l2
  refine ⟨ε, hε, λ u hu => ?_⟩
  have l4 : uIcc t u ⊆ ball t ε := by
    suffices uIcc t.1 u.1 ⊆ ball t.1 ε by intro v ; apply this
    simpa only [segment_eq_uIcc] using (convex_ball t.1 ε).segment_subset (mem_ball_self hε) hu
  have l5 : MapsTo γ (uIcc t u) T.baseSet := λ v hv => l3 (l4 hv)
  exact ⟨reachable_extend <| uIcc_comm t u ▸ l5, reachable_extend l5⟩

end helpers

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : C(I, X)} {A : E}

theorem lift' (hf : IsCoveringMap f) (hγ : γ 0 = f A) : ∃ Γ : C(I, E), Γ 0 = A ∧ f ∘ Γ = γ := by
  have l1 : Set.Nonempty {t | reachable f γ A t} := ⟨0, reachable_zero hγ⟩
  have l2 : IsClopen {t | reachable f γ A t} := isClopen_iff_nhds.2 <| λ t => reachable_nhds_iff hf
  let ⟨Γ, h1, h2⟩ := ((isClopen_iff.1 l2).resolve_left <| Nonempty.ne_empty l1).symm ▸ mem_univ 1
  exact ⟨Γ, h1, funext h2⟩
