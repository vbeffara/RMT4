import RMT4.Lift

open Set Topology Metric unitInterval Filter ContinuousMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
  {f : E → X} {γ : C(I, X)} {x : X} {A : E} {t t₁ t₂ : I} {Γ Γ₁ Γ₂ : C(I, E)}

lemma prekey {T : Trivialization (f ⁻¹' {x}) f} [DiscreteTopology (f ⁻¹' {x})] {z : E}
    (h : z ∈ T.source) : ∀ᶠ w in 𝓝 z, T w = (f w, (T z).2) := by
  have l1 : {(T z).2} ∈ 𝓝 (T z).2 := by simp only [nhds_discrete, mem_pure, mem_singleton_iff]
  have l2 : ∀ᶠ w in 𝓝 z, (T w).2 = (T z).2 := continuousAt_snd.comp (T.continuousAt h) l1
  filter_upwards [T.open_source.mem_nhds h, l2] with s hs r2 using Prod.ext (T.coe_fst hs) r2

lemma key {T : Trivialization (f ⁻¹' {x}) f} [DiscreteTopology (f ⁻¹' {x})] (h : Γ t ∈ T.source) :
    ∀ᶠ s in 𝓝 t, T (Γ s) = (f (Γ s), (T (Γ t)).2) := Γ.continuousAt _ (prekey h)

lemma key2 {T : Trivialization (f ⁻¹' {x}) f} [DiscreteTopology (f ⁻¹' {x})] (h : Γ t ∈ T.source) :
    ∀ᶠ s in 𝓝 t, Γ s = T.invFun (f (Γ s), (T (Γ t)).2) := by
  filter_upwards [key h, Γ.continuousAt _ <| T.open_source.mem_nhds h] with s r1 r2
  simpa only [← r1] using (T.left_inv r2).symm

lemma locally_eq (hf : IsCoveringMap f) (h1 : Γ₁ t = Γ₂ t) (h2 : f ∘ Γ₁ =ᶠ[𝓝 t] f ∘ Γ₂) :
    Γ₁ =ᶠ[𝓝 t] Γ₂ := by
  obtain ⟨l1, T, l2⟩ := hf (f (Γ₁ t))
  rw [← T.mem_source] at l2
  filter_upwards [key2 l2, key2 (Γ := Γ₂) (T := T) (h1 ▸ l2), h2] with s r2 r3 (r4 : f _ = f _)
  rw [r2, r3] ; congr

lemma locally_eq_iff (hf : IsCoveringMap f) (h2 : f ∘ Γ₁ =ᶠ[𝓝 t] f ∘ Γ₂) :
    ∀ᶠ s in 𝓝 t, Γ₁ s = Γ₂ s ↔ Γ₁ t = Γ₂ t := by
  obtain ⟨l1, T, l2⟩ := hf (f (Γ₁ t))
  have : f _ = f _ := h2.self_of_nhds
  have l3 : f (Γ₂ t) ∈ T.baseSet := by simp [← show f (Γ₁ t) = f (Γ₂ t) from this, l2]
  rw [← T.mem_source] at l2 l3
  filter_upwards [key2 l2, key2 l3, key l2, key l3, h2] with s r2 r3 r4 r5 (r6 : f _ = f _)
  refine ⟨λ h => ?_, λ h => by { rw [r2, r3] ; congr }⟩
  suffices T (Γ₁ t) = T (Γ₂ t) by rw [← T.left_inv' l2, ← T.left_inv' l3] ; congr 1
  apply Prod.ext (by simpa [T.coe_fst, l2, l3])
  simpa using congr_arg Prod.snd (show (_, _) = (_, _) from (h ▸ r4).symm.trans r5)
