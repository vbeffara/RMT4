import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.UniformSpace.Ascoli
import RMT4.Basic
import RMT4.defs
import RMT4.hurwitz

open Set Function Metric UniformConvergence Complex

variable {ι : Type*} {U K : Set ℂ} {z : ℂ} {F : ι → ℂ →ᵤ[compacts U] ℂ} {Q : Set ℂ → Set ℂ}

@[simp] lemma union_compacts : ⋃₀ compacts U = U :=
  subset_antisymm (λ _ ⟨_, hK, hz⟩ => hK.1 hz)
    (λ z hz => ⟨{z}, ⟨singleton_subset_iff.2 hz, isCompact_singleton⟩, mem_singleton z⟩)

def UniformlyBoundedOn (F : ι → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ∈ compacts U, ∃ Q, IsCompact Q ∧ ∀ i, MapsTo (F i) K Q

@[deprecated] def UniformlyBoundedOn'' (F : ι → ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K ∈ compacts U, ∃ M > 0, ∀ z ∈ K, range (eval z ∘ F) ⊆ closedBall 0 M

lemma uniformlyBoundedOn''_iff_uniformlyBoundedOn (F : ι → ℂ → ℂ) (U : Set ℂ) :
    UniformlyBoundedOn'' F U ↔ UniformlyBoundedOn F U := by
  constructor <;> intro h K hK
  · obtain ⟨M, -, hM2⟩ := h K hK
    refine ⟨closedBall 0 M, isCompact_closedBall _ _, fun i z hz => ?_⟩
    exact hM2 z hz <| mem_range.mpr ⟨i, rfl⟩
  · obtain ⟨Q, hQ1, hQ2⟩ := h K hK
    obtain ⟨M, hM⟩ := hQ1.isBounded.subset_closedBall 0
    refine ⟨M ⊔ 1, by simp, fun z hz y => ?_⟩
    rintro ⟨i, rfl⟩
    have := hM (hQ2 i hz)
    simp at this
    simp [this]

lemma UniformlyBoundedOn.deriv (h1 : UniformlyBoundedOn F U) (hU : IsOpen U)
    (h2 : ∀ i, DifferentiableOn ℂ (F i) U) :
    UniformlyBoundedOn (deriv ∘ F) U := by
  rintro K ⟨hK1, hK2⟩
  obtain ⟨δ, hδ, h⟩ := hK2.exists_cthickening_subset_open hU hK1
  have e1 : cthickening δ K ∈ compacts U :=
    ⟨h, isCompact_of_isClosed_isBounded isClosed_cthickening hK2.isBounded.cthickening⟩
  obtain ⟨Q, hQ1, hQ2⟩ := h1 _ e1
  obtain ⟨M, hM⟩ := hQ1.isBounded.subset_closedBall 0
  refine ⟨closedBall 0 (M / δ), isCompact_closedBall _ _, ?_⟩
  intro i x hx
  simp only [mem_closedBall_zero_iff]
  refine norm_deriv_le_aux hδ ?_ ?_
  · exact (h2 i).diffContOnCl_ball ((closedBall_subset_cthickening hx δ).trans h)
  · rintro z hz
    have : z ∈ cthickening δ K :=
      sphere_subset_closedBall.trans (closedBall_subset_cthickening hx δ) hz
    simpa using hM (hQ2 i this)

lemma UniformlyBoundedOn.equicontinuousOn
    (h1 : UniformlyBoundedOn F U)
    (hU : IsOpen U)
    (h2 : ∀ (i : ι), DifferentiableOn ℂ (F i) U)
    (hK : K ∈ compacts U) :
    EquicontinuousOn F K := by
  apply (equicontinuous_restrict_iff _).mp
  have key := h1.deriv hU h2
  rintro ⟨z, hz⟩
  obtain ⟨δ, hδ, h⟩ := nhds_basis_closedBall.mem_iff.1 (hU.mem_nhds (hK.1 hz))
  have : ∃ M > 0, ∀ x ∈ closedBall z δ, ∀ i, _root_.deriv (F i) x ∈ closedBall 0 M := by
    rw [← uniformlyBoundedOn''_iff_uniformlyBoundedOn] at key
    obtain ⟨m, hm, h⟩ := key (closedBall z δ) ⟨h, isCompact_closedBall _ _⟩
    exact ⟨m, hm, fun x hx i => h x hx ⟨i, rfl⟩⟩
  obtain ⟨M, hMp, hM⟩ := this
  rw [equicontinuousAt_iff]
  rintro ε hε
  refine ⟨δ ⊓ ε / M, gt_iff_lt.2 (lt_inf_iff.2 ⟨hδ, div_pos hε hMp⟩), λ w hw i => ?_⟩
  simp
  have e1 : ∀ x ∈ closedBall z δ, DifferentiableAt ℂ (F i) x :=
    λ x hx => (h2 i).differentiableAt (hU.mem_nhds (h hx))
  have e2 : ∀ x ∈ closedBall z δ, ‖_root_.deriv (F i) x‖ ≤ M :=
    λ x hx => by simpa using hM x hx i
  have e3 : z ∈ closedBall z δ := mem_closedBall_self hδ.le
  have e4 : w.1 ∈ closedBall z δ := by simpa using (lt_inf_iff.1 hw).1.le
  rw [dist_eq_norm]
  refine ((convex_closedBall _ _).norm_image_sub_le_of_norm_deriv_le e1 e2 e4 e3).trans_lt ?_
  have : ‖z - w.val‖ < ε / M := by
    have := (lt_inf_iff.1 hw).2
    rwa [dist_comm, Subtype.dist_eq, dist_eq_norm] at this
  convert mul_lt_mul' le_rfl this (norm_nonneg _) hMp
  field_simp [hMp.lt.ne.symm, mul_comm]

def 𝓑 (U : Set ℂ) (Q : Set ℂ → Set ℂ) : Set (ℂ →ᵤ[compacts U] ℂ) :=
    {f ∈ 𝓗 U | ∀ K ∈ compacts U, MapsTo f K (Q K)}

lemma 𝓑_const {Q : Set ℂ} : 𝓑 U (fun _ => Q) = {f ∈ 𝓗 U | MapsTo f U Q} := by
  simp [𝓑, ← mapsTo_sUnion]

theorem isClosed_𝓑 (hU : IsOpen U) (hQ : ∀ K ∈ compacts U, IsCompact (Q K)) :
    IsClosed (𝓑 U Q) := by
  rw [𝓑, setOf_and] ; apply (isClosed_𝓗 hU).inter
  simp only [setOf_forall, MapsTo]
  apply isClosed_biInter ; intro K hK
  apply isClosed_biInter ; intro z hz
  apply (hQ K hK).isClosed.preimage
  exact ((UniformOnFun.uniformContinuous_eval_of_mem ℂ (compacts U)
    (mem_singleton z) ⟨singleton_subset_iff.2 (hK.1 hz), isCompact_singleton⟩).continuous)

theorem uniformlyBoundedOn_𝓑 (hQ : ∀ K ∈ compacts U, IsCompact (Q K)) :
    UniformlyBoundedOn ((↑) : 𝓑 U Q → ℂ →ᵤ[compacts U] ℂ) U := by
  exact fun K hK => ⟨Q K, hQ K hK, fun f => f.2.2 K hK⟩

theorem isCompact_𝓑 (hU : IsOpen U) (hQ : ∀ K ∈ compacts U, IsCompact (Q K)) :
    IsCompact (𝓑 U Q) := by
  have l1 (K) (hK : K ∈ compacts U) : EquicontinuousOn ((↑) : 𝓑 U Q → ℂ →ᵤ[compacts U] ℂ) K :=
    (uniformlyBoundedOn_𝓑 hQ).equicontinuousOn hU (fun f => f.2.1) hK
  have l2 (K) (hK : K ∈ compacts U) (x) (hx : x ∈ K) : ∃ L, IsCompact L ∧ ∀ i : 𝓑 U Q, i.1 x ∈ L :=
    ⟨Q K, hQ K hK, fun f => f.2.2 K hK hx⟩
  rw [isCompact_iff_compactSpace]
  refine ArzelaAscoli.compactSpace_of_closedEmbedding (fun K hK => hK.2) ?_ l1 l2
  refine ⟨⟨by tauto, fun f g => Subtype.ext⟩, ?_⟩
  simpa [range, UniformOnFun.ofFun] using isClosed_𝓑 hU hQ

theorem montel (hU : IsOpen U) (h1 : UniformlyBoundedOn F U) (h2 : ∀ i, DifferentiableOn ℂ (F i) U) :
    TotallyBounded (range F) := by
  choose! Q hQ1 hQ2 using h1
  have l1 : range F ⊆ 𝓑 U Q := by rintro f ⟨i, rfl⟩ ; exact ⟨h2 i, fun K hK => hQ2 K hK i⟩
  exact totallyBounded_subset l1 <| (isCompact_𝓑 hU hQ1).totallyBounded

#print axioms montel
