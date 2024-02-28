/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/

import Mathlib.Topology.UniformSpace.Equicontinuity

open Set Filter Uniformity Function UniformConvergence

variable {X ι α : Type*} [TopologicalSpace X] [UniformSpace α] {F : ι → X → α}

lemma theorem1 [CompactSpace X] (hF : Equicontinuous F) :
    (UniformFun.uniformSpace X α).comap F = (Pi.uniformSpace (λ _ => α)).comap F := by
  refine le_antisymm (UniformSpace.comap_mono (le_iff_uniformContinuous_id.mpr UniformFun.uniformContinuous_toFun)) ?_
  change comap _ _ ≤ comap _ _
  simp_rw [Pi.uniformity, Filter.comap_iInf, Filter.comap_comap, Function.comp]
  refine ((UniformFun.hasBasis_uniformity X α).comap (Prod.map F F)).ge_iff.mpr ?_
  intro U hU
  rcases comp_comp_symm_mem_uniformity_sets hU with ⟨V, hV, Vsymm, hVU⟩
  let Ω : X → Set X := λ x => {y | ∀ i, (F i x, F i y) ∈ V}
  rcases CompactSpace.elim_nhds_subcover Ω (λ x => hF x V hV) with ⟨S, Scover⟩
  have : (⋂ s ∈ S, {ij : ι × ι | (F ij.1 s, F ij.2 s) ∈ V}) ⊆ (Prod.map F F) ⁻¹' UniformFun.gen X α U := by
    rintro ⟨i, j⟩ hij x
    rw [mem_iInter₂] at hij
    rcases mem_iUnion₂.mp (Scover.symm.subset $ mem_univ x) with ⟨s, hs, hsx⟩
    exact hVU (prod_mk_mem_compRel (prod_mk_mem_compRel (Vsymm.mk_mem_comm.mp (hsx i)) (hij s hs)) (hsx j))
  exact mem_of_superset (S.iInter_mem_sets.mpr $ λ x _ => mem_iInf_of_mem x $ preimage_mem_comap hV) this

-- TODO: this is too long
lemma theorem1' {𝔖 : Set (Set X)} (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F =
      (⨅ K ∈ 𝔖, ⨅ x ∈ K, ‹UniformSpace α›.comap (eval x)).comap F := by
  rw [UniformOnFun.uniformSpace]
  sorry
  -- simp_rw [UniformSpace.comap_iInf, ← UniformSpace.comap_comap]
  -- refine iInf_congr (λ K => iInf_congr $ λ hK => ?_)
  -- haveI : CompactSpace K := isCompact_iff_compactSpace.mp (h𝔖 K hK)
  -- simp_rw [theorem1 (hF K hK), UniformSpace.comap_comap,
  --           Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, UniformSpace.comap_iInf, iInf_subtype]
  -- refine iInf_congr (λ x => iInf_congr $ λ hx => congr_arg _ ?_)
  -- rw [← UniformSpace.comap_comap]
  -- exact congr_fun (congr_arg _ rfl) _

lemma theorem1'' {𝔖 : Set (Set X)} (hcover : ⋃₀ 𝔖 = univ) (h𝔖 : ∀ K ∈ 𝔖, IsCompact K)
    (hF : ∀ K ∈ 𝔖, Equicontinuous ((K.restrict : (X → α) → (K → α)) ∘ F)) :
    (UniformOnFun.uniformSpace X α 𝔖).comap F = (Pi.uniformSpace (λ _ => α)).comap F := by
  simp [theorem1' h𝔖 hF, Pi.uniformSpace, UniformSpace.ofCoreEq_toCore, ← iInf_sUnion, hcover]

lemma ascoli₀ {𝔖 : Set (Set X)} {F : ι → X →ᵤ[𝔖] α} {l : Filter ι} [NeBot l]
    (h1 : ∀ A ∈ 𝔖, IsCompact A)
    (h2 : ∀ A ∈ 𝔖, Equicontinuous (λ i => Set.restrict A (F i)))
    (h3 : ∀ x ∈ ⋃₀ 𝔖, Cauchy (map (eval x ∘ F) l)) :
    Cauchy (map F l) := by
  have e1 : @Cauchy _ (⨅ K ∈ 𝔖, ⨅ x ∈ K, ‹UniformSpace _›.comap (eval x)) (map F l) := by
    simp_rw [cauchy_iInf_uniformSpace', cauchy_comap_uniformSpace, ← forall_sUnion]
    exact h3
  rcases e1 with ⟨e2, e3⟩
  refine ⟨e2, ?_⟩
  rw [prod_map_map_eq, map_le_iff_le_comap] at e3 ⊢
  exact e3.trans (theorem1' h1 h2).ge

lemma ascoli {𝔖 : Set (Set X)} {F : ι → X →ᵤ[𝔖] α}
    (h1 : ∀ A ∈ 𝔖, IsCompact A)
    (h2 : ∀ A ∈ 𝔖, Equicontinuous (λ i => Set.restrict A (F i)))
    (h3 : ∀ x ∈ ⋃₀ 𝔖, TotallyBounded (range (λ i => F i x))) :
    TotallyBounded (range F) := by
  simp_rw [totallyBounded_iff_ultrafilter] at h3 ⊢
  intro f hf
  have : F '' univ ∈ f := by rwa [image_univ, ← Ultrafilter.mem_coe, ← le_principal_iff]
  rw [← Ultrafilter.ofComapInfPrincipal_eq_of_map this]
  set g := Ultrafilter.ofComapInfPrincipal this
  apply ascoli₀ h1 h2
  intro x hx
  apply h3 x hx (g.map (eval x ∘ F))
  exact (le_principal_iff.mpr range_mem_map)
