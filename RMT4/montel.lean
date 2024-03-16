import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.UniformSpace.Ascoli
import RMT4.Basic
import RMT4.defs
import RMT4.hurwitz

open Set Function Metric UniformConvergence Complex

variable {ι : Type*} {U K : Set ℂ} {z : ℂ} {F : ι → ℂ →ᵤ[compacts U] ℂ}

@[simp] lemma union_compacts : ⋃₀ compacts U = U :=
  subset_antisymm (λ _ ⟨_, hK, hz⟩ => hK.1 hz)
    (λ z hz => ⟨{z}, ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩, mem_singleton z⟩)

def UniformlyBoundedOn (F : ι → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ∈ compacts U, ∃ M > 0, ∀ z ∈ K, range (eval z ∘ F) ⊆ closedBall 0 M

lemma UniformlyBoundedOn.totally_bounded_at (h1 : UniformlyBoundedOn F U) (hz : z ∈ U) :
    TotallyBounded (range (λ (i : ι) => F i z)) := by
  obtain ⟨M, _, hM⟩ := h1 {z} ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩
  have := hM z (mem_singleton z)
  exact totallyBounded_subset this (isCompact_closedBall 0 M).totallyBounded

lemma UniformlyBoundedOn.deriv (h1 : UniformlyBoundedOn F U) (hU : IsOpen U)
    (h2 : ∀ i, DifferentiableOn ℂ (F i) U) :
    UniformlyBoundedOn (deriv ∘ F) U := by
  rintro K ⟨hK1, hK2⟩
  obtain ⟨δ, hδ, h⟩ := hK2.exists_cthickening_subset_open hU hK1
  have e1 : cthickening δ K ∈ compacts U :=
    ⟨h, isCompact_of_isClosed_isBounded isClosed_cthickening hK2.isBounded.cthickening⟩
  obtain ⟨M, hMp, hM⟩ := h1 _ e1
  refine ⟨M / δ, div_pos hMp hδ, ?_⟩
  rintro z₀ hz₀ w ⟨i, rfl⟩
  simp only [mem_closedBall_zero_iff]
  refine norm_deriv_le_aux hδ ?_ ?_
  · exact (h2 i).diffContOnCl_ball ((closedBall_subset_cthickening hz₀ δ).trans h)
  · rintro z hz
    have : z ∈ cthickening δ K :=
      sphere_subset_closedBall.trans (closedBall_subset_cthickening hz₀ δ) hz
    simpa using hM z this ⟨i, rfl⟩

lemma UniformlyBoundedOn.equicontinuous_on
    (h1 : UniformlyBoundedOn F U)
    (hU : IsOpen U)
    (h2 : ∀ (i : ι), DifferentiableOn ℂ (F i) U)
    (hK : K ∈ compacts U) :
    EquicontinuousOn F K := by
  apply (equicontinuous_restrict_iff _).mp
  have key := h1.deriv hU h2
  rintro ⟨z, hz⟩
  obtain ⟨δ, hδ, h⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hK.1 hz))
  obtain ⟨M, hMp, hM⟩ := key (closedBall z δ) ⟨h, isCompact_closedBall _ _⟩
  rw [equicontinuousAt_iff]
  rintro ε hε
  refine ⟨δ ⊓ ε / M, gt_iff_lt.2 (lt_inf_iff.2 ⟨hδ, div_pos hε hMp⟩), λ w hw i => ?_⟩
  simp
  have e1 : ∀ x ∈ closedBall z δ, DifferentiableAt ℂ (F i) x :=
    λ x hx => (h2 i).differentiableAt (hU.mem_nhds (h hx))
  have e2 : ∀ x ∈ closedBall z δ, ‖_root_.deriv (F i) x‖ ≤ M :=
    λ x hx => by simpa using hM x hx ⟨i, rfl⟩
  have e3 : z ∈ closedBall z δ := mem_closedBall_self hδ.le
  have e4 : w.1 ∈ closedBall z δ := by simpa using (lt_inf_iff.1 hw).1.le
  rw [dist_eq_norm]
  refine ((convex_closedBall _ _).norm_image_sub_le_of_norm_deriv_le e1 e2 e4 e3).trans_lt ?_
  have : ‖z - w.val‖ < ε / M := by
    have := (lt_inf_iff.1 hw).2
    rwa [dist_comm, Subtype.dist_eq, dist_eq_norm] at this
  convert mul_lt_mul' le_rfl this (norm_nonneg _) hMp
  field_simp [hMp.lt.ne.symm, mul_comm]

def 𝓕K (U : Set ℂ) (Q : Set ℂ → Set ℂ) : Set (ℂ →ᵤ[compacts U] ℂ) :=
  {f | DifferentiableOn ℂ f U ∧ ∀ K ∈ compacts U, MapsTo f K (Q K)}

theorem isClosed_𝓕K (hU : IsOpen U) {Q : Set ℂ → Set ℂ} (hQ : ∀ K ∈ compacts U, IsCompact (Q K)) :
    IsClosed (𝓕K U Q) := by
  rw [𝓕K, setOf_and] ; apply (isClosed_𝓗 hU).inter
  simp only [setOf_forall, MapsTo]
  apply isClosed_biInter ; intro K hK
  apply isClosed_biInter ; intro z hz
  apply (hQ K hK).isClosed.preimage
  exact ((UniformOnFun.uniformContinuous_eval_of_mem ℂ (compacts U)
    (mem_singleton z) ⟨singleton_subset_iff.2 (hK.1 hz), isCompact_singleton⟩).continuous)

theorem isCompact_𝓕K (hU : IsOpen U) {Q : Set ℂ → Set ℂ} (hQ : ∀ K ∈ compacts U, IsCompact (Q K)) :
    IsCompact (𝓕K U Q) := by

  rw [isCompact_iff_compactSpace]
  apply @ArzelaAscoli.compactSpace_of_closedEmbedding (𝓕K U Q) ℂ ℂ _ _ Subtype.val _
    (compacts U) (fun K hK => hK.2)
  · constructor
    · constructor
      · tauto
      · exact fun f g => Subtype.ext
    · simpa [range, UniformOnFun.ofFun] using isClosed_𝓕K hU hQ
  · intro K hK
    refine UniformlyBoundedOn.equicontinuous_on ?_ hU (fun f => f.2.1) hK
    intro K' hK'
    have := (hQ K' hK').isBounded
    have := (isBounded_iff_subset_closedBall 0).mp this
    obtain ⟨M, hM⟩ := this
    refine ⟨M ⊔ 1, by simp, fun z hz y hy => ?_⟩
    obtain ⟨f, rfl⟩ := mem_range.mp hy
    have := hM (f.2.2 K' hK' hz)
    simp at this
    simp [this]
  · intro K hK z hz
    refine ⟨Q K, hQ K hK, fun f => f.2.2 K hK hz⟩

theorem montel (hU : IsOpen U) (h1 : UniformlyBoundedOn F U) (h2 : ∀ i, DifferentiableOn ℂ (F i) U) :
    TotallyBounded (range F) := by

  choose! M hM using h1
  let Q (K : Set ℂ) : Set ℂ := closedBall 0 (M K)
  let S := 𝓕K U Q

  have l1 : range F ⊆ S := by
    rintro f ⟨i, rfl⟩
    refine ⟨h2 i, fun K hK z hz => ?_⟩
    apply (hM K hK).2 z hz
    simp
  apply totallyBounded_subset l1
  apply IsCompact.totallyBounded
  apply isCompact_𝓕K hU
  intro K _
  exact isCompact_closedBall _ _
