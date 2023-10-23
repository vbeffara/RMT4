import Mathlib.Analysis.Convex.Normed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Topology.Covering
import Mathlib.Topology.LocallyConstant.Basic

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
  {s t t₁ t₂ : I}

abbrev II (t : I) : Set ℝ := Icc 0 t
@[simp] lemma II_zero : II 0 = {0} := by simp [II]
lemma mem_II_zero {t : ℝ} : t ∈ II 0 ↔ t = 0 := by simp [II]
@[simp] lemma II_one : II 1 = I := rfl
instance : Zero (II t) := by exact ⟨0, le_rfl, t.prop.1⟩
instance : CoeOut (II t) I := ⟨λ s => ⟨↑s, s.prop.1, s.prop.2.trans t.prop.2⟩⟩

def good (f : E → X) (γ : C(I, X)) (A : E) (t : I) : Prop :=
  ∃ Γ : I → E, ContinuousOn Γ (Iic t) ∧ Γ 0 = A ∧ ∀ s ≤ t, f (Γ s) = γ s

def good' (f : E → X) (γ : C(I, X)) (A : E) (t : I) : Prop :=
  ∃ Γ : C(II t, E), Γ 0 = A ∧ ∀ s, f (Γ s) = γ s

lemma good_zero (hγ : γ 0 = f A) : good f γ A 0 := by
  refine ⟨λ _ => A, continuousOn_const, rfl, ?_⟩
  rintro ⟨s, h1, _⟩ (h3 : s ≤ 0)
  simp [le_antisymm h3 h1, hγ]

lemma good'_zero (hγ : γ 0 = f A) : good' f γ A 0 :=
  ⟨⟨λ _ => A, continuous_const⟩, rfl, λ ⟨s, hs⟩ => by simp [mem_II_zero.1 hs, hγ]⟩

lemma good_mono (h2 : good f γ A t₂) (h12 : t₁ ≤ t₂) : good f γ A t₁ := by
  obtain ⟨Γ, h1, h2, h3⟩ := h2
  exact ⟨Γ, ContinuousOn.mono h1 <| Iic_subset_Iic.mpr h12, h2, λ s' hs' => h3 s' (hs'.trans h12)⟩

lemma good_extend {T : Trivialization (f ⁻¹' {γ t}) f} (h : MapsTo γ (uIcc t₁ t₂) T.baseSet) :
    good f γ A t₁ → good f γ A t₂ := by
  rintro ⟨Γ, h1, h2, h3⟩
  let δ (s : I) : E := T.invFun (γ s, (T (Γ t₁)).2)
  let Δ (s : I) : E := if s ≤ t₁ then Γ s else δ s
  refine ⟨Δ, ?_, by simp [show 0 ≤ t₁ from t₁.2.1, h2], ?_⟩
  · apply ContinuousOn.if
    · have l2 : T.baseSet ∈ 𝓝 (γ t₁) := T.open_baseSet.mem_nhds <| h ⟨inf_le_left, le_sup_left⟩
      have l3 : γ ⁻¹' T.baseSet ∈ 𝓝 t₁ := γ.continuous_toFun.continuousAt.preimage_mem_nhds l2
      have k1 : Γ t₁ ∈ T.source := by simpa [T.source_eq, h3 t₁ le_rfl] using mem_of_mem_nhds l3
      have k2 : (T (Γ t₁)).1 = f (Γ t₁) := T.proj_toFun _ k1
      have k3 : T.invFun (T (Γ t₁)) = Γ t₁ := T.left_inv' k1
      rintro a ⟨_, h'a⟩
      have k4 : a = t₁ := by simpa using (frontier_le_subset_eq continuous_id continuous_const) h'a
      simp_rw [k4, ← h3 t₁ le_rfl, ← k2, Prod.eta, k3]
    · refine h1.mono <| (inter_subset_right _ _).trans (?_ : closure (Iic t₁) ⊆ Iic t₁)
      simpa only [closure_Iic] using subset_rfl
    · have : ContinuousOn δ (γ ⁻¹' T.baseSet) := by
        refine T.continuous_invFun.comp ?_ <| λ u hu => by simpa [T.target_eq] using hu
        apply Continuous.continuousOn
        simpa only [continuous_prod_mk, continuous_const, and_true] using γ.continuous_toFun
      refine this.mono <| subset_trans (λ v ⟨hv1, hv2⟩ => ?_) h
      simp only [not_le] at hv2
      have : v ∈ Ici t₁ := closure_lt_subset_le continuous_const continuous_id hv2
      exact Icc_subset_uIcc <| by simpa only [← Ici_inter_Iic] using mem_inter this hv1
  · intro v hv
    by_cases l6 : v ≤ t₁
    · simp only [LocalEquiv.invFun_as_coe, LocalHomeomorph.coe_coe_symm, l6, ite_true, h3]
    · simp only [l6, ite_false]
      have : γ v ∈ T.baseSet := h ⟨inf_le_left.trans <| not_le.1 l6 |>.le, hv.trans le_sup_right⟩
      have l7 : T.invFun (γ v, (T (Γ t₁)).snd) ∈ T.source :=
        T.map_target' <| by simp only [T.target_eq, mem_prod, this, mem_univ, and_self]
      rw [← T.proj_toFun _ l7]
      have : T (T.invFun (γ v, (T (Γ t₁)).snd)) = (γ v, (T (Γ t₁)).snd) :=
        T.right_inv' <| by simp only [T.target_eq, mem_prod, this, mem_univ, and_self]
      simp_all only [Trivialization.coe_coe]

lemma good'_extend {T : Trivialization (f ⁻¹' {γ t}) f} (h : MapsTo γ (uIcc t₁ t₂) T.baseSet) :
    good' f γ A t₁ → good' f γ A t₂ := by sorry

lemma good_nhds_iff (hf : IsCoveringMap f) : ∀ᶠ t' in 𝓝 t, good f γ A t' ↔ good f γ A t := by
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
  exact ⟨good_extend <| uIcc_comm t u ▸ l5, good_extend l5⟩

lemma good'_nhds_iff (hf : IsCoveringMap f) : ∀ᶠ t' in 𝓝 t, good' f γ A t' ↔ good' f γ A t := by
  sorry

end helpers

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {f : E → X} {γ : C(I, X)} {A : E}

theorem lift (hf : IsCoveringMap f) (hγ : γ 0 = f A) : ∃ Γ : C(I, E), Γ 0 = A ∧ f ∘ Γ = γ := by
  suffices {t | good f γ A t} = univ by
    obtain ⟨Γ, h1, h2, h3⟩ := this.symm ▸ mem_univ ⊤
    refine ⟨⟨Γ, ?_⟩, h2, funext <| λ s => h3 s s.2.2⟩
    simpa [continuous_iff_continuousOn_univ] using h1
  have l1 : Set.Nonempty {t | good f γ A t} := ⟨0, good_zero hγ⟩
  have l2 : IsClopen {t | good f γ A t} := isClopen_iff_nhds.2 <| λ t => good_nhds_iff hf
  exact (isClopen_iff.1 l2).resolve_left <| Nonempty.ne_empty l1

theorem lift' (hf : IsCoveringMap f) (hγ : γ 0 = f A) : ∃ Γ : C(I, E), Γ 0 = A ∧ f ∘ Γ = γ := by
  have l1 : Set.Nonempty {t | good' f γ A t} := ⟨0, good'_zero hγ⟩
  have l2 : IsClopen {t | good' f γ A t} := isClopen_iff_nhds.2 <| λ t => good'_nhds_iff hf
  let ⟨Γ, h1, h2⟩ := ((isClopen_iff.1 l2).resolve_left <| Nonempty.ne_empty l1).symm ▸ mem_univ 1
  exact ⟨Γ, h1, funext h2⟩
