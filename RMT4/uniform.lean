import Mathlib.Topology.UniformSpace.UniformConvergence

open Set Filter UniformSpace Function Uniformity Topology

lemma symmetricRel_of (hx : ∀ {a b : α}, (a, b) ∈ x → (b, a) ∈ x) : SymmetricRel x :=
  ext (λ _ => ⟨(hx ·), (hx ·)⟩)

namespace UniformSpace -- uniform thickening

def thickening (U : Set (α × α)) (S : Set α) : Set α := ⋃ x ∈ S, ball x U

lemma mem_thickening : a ∈ thickening u s ↔ ∃ x ∈ s, (x, a) ∈ u := by
  simp only [thickening, ball, mem_iUnion, mem_preimage, exists_prop]

@[simp] lemma thickening_singleton : thickening u {a} = ball a u := by
  simp only [thickening, mem_singleton_iff, iUnion_iUnion_eq_left]

@[simp] lemma monotone_thickening : Monotone (thickening · s) := by
  intro u v huv
  apply iUnion₂_mono
  simp only [ball, le_eq_subset] at huv ⊢
  exact λ _ _ => preimage_mono huv

lemma thickening_mono : Monotone (thickening u) :=
  λ _ _ h => iUnion₂_mono' (λ a ha => ⟨a, h ha, subset_rfl⟩)

@[simp] lemma thickening_comp : thickening v (thickening u s) = thickening (u ○ v) s := by
  ext; simp [thickening, ball]

lemma disjoint_ball_iff : Disjoint (ball a u) t ↔ ∀ b ∈ t, (a, b) ∉ u := by
  rw [← compl_compl (ball a u), disjoint_compl_left_iff_subset]
  rfl

lemma thickening_inter_eq_empty : thickening u s ∩ t = ∅ ↔ ∀ a ∈ s, ∀ b ∈ t, (a, b) ∉ u := by
  simp [thickening, ← disjoint_iff_inter_eq_empty, disjoint_ball_iff]

lemma thickening_inter_eq_empty_comm (hu : SymmetricRel u) :
    thickening u s ∩ t = ∅ ↔ s ∩ thickening u t = ∅ := by
  simp [thickening_inter_eq_empty, inter_comm s]
  apply Iff.intro; repeat exact λ h a ha b hb hab => h b hb a ha (hu.mk_mem_comm.mp hab)

lemma thickening_inter_thickening_eq_empty_of_comp (hv : SymmetricRel v) (hvu : v ○ v ⊆ u)
    (hST : thickening u s ∩ t = ∅) :
    thickening v s ∩ thickening v t = ∅ := by
  simp only [←thickening_inter_eq_empty_comm hv, thickening_comp]
  exact subset_eq_empty (inter_subset_inter_left _ (monotone_thickening hvu)) hST

end UniformSpace

-----------------------------------------------------------------------------

def uniform_nhds_set [UniformSpace α] (s : Set α) : Filter α :=
  Filter.lift' (𝓤 α) (UniformSpace.thickening · s)

scoped[Uniformity] notation "𝓝ᵘ" => uniform_nhds_set

namespace UniformSpace -- uniform_nhds_set

variable [UniformSpace α]

lemma thickening_mem_uniform_nhds_set (hu : u ∈ 𝓤 α) : thickening u s ∈ 𝓝ᵘ s :=
  (mem_lift'_sets monotone_thickening).mpr ⟨u, hu, subset_rfl⟩

lemma uniform_nhds_set_mono {s t : Set α} (h : s ⊆ t) : 𝓝ᵘ s ≤ 𝓝ᵘ t :=
  lift'_mono le_rfl (λ _ => thickening_mono h)

lemma uniform_nhds_set_singleton {a : α} : 𝓝ᵘ {a} = 𝓝 a := by
  simp only [uniform_nhds_set, thickening_singleton, nhds_eq_uniformity]

lemma mem_uniform_nhds_set_iff : s ∈ 𝓝ᵘ t ↔ ∃ u ∈ 𝓤 α, thickening u t ⊆ s := by
  simp [uniform_nhds_set, mem_lift'_sets]

lemma nhds_le_uniform_nhds_set {s : Set α} (ha : a ∈ s) : 𝓝 a ≤ 𝓝ᵘ s := by
  simpa [← uniform_nhds_set_singleton] using uniform_nhds_set_mono (singleton_subset_iff.mpr ha)

lemma nhds_set_le_uniform_nhds_set {s : Set α} : 𝓝ˢ s ≤ 𝓝ᵘ s := by
  simpa [nhdsSet] using λ _ => nhds_le_uniform_nhds_set

lemma uniform_nhds_inf_uniform_nhds_eq_bot {s t : Set α} (h : 𝓝ᵘ s ⊓ 𝓟 t = ⊥) : 𝓝ᵘ s ⊓ 𝓝ᵘ t = ⊥ := by
  simp_rw [inf_principal_eq_bot, inf_eq_bot_iff, mem_uniform_nhds_set_iff] at h ⊢
  obtain ⟨u, hu, hsu⟩ := h
  obtain ⟨v, hv, hvs, hvu⟩ := comp_symm_of_uniformity hu
  refine ⟨_, ⟨v, hv, subset_rfl⟩, _, ⟨v, hv, subset_rfl⟩, ?h⟩
  apply thickening_inter_thickening_eq_empty_of_comp (symmetricRel_of hvs) hvu
  exact (subset_compl_iff_disjoint_right.mp hsu).inter_eq

lemma nhds_inf_uniform_nhds_eq_bot {s : Set α} (hf : 𝓝 a ⊓ 𝓟 s = ⊥) : 𝓝 a ⊓ 𝓝ᵘ s = ⊥ := by
  rw [← uniform_nhds_set_singleton] at hf ⊢
  exact uniform_nhds_inf_uniform_nhds_eq_bot hf

lemma is_compact.nhds_set_eq_uniform_nhds_set {s : Set α} (hs : IsCompact s) : 𝓝ˢ s = 𝓝ᵘ s :=
  (hs.nhdsSet_basis_uniformity (basis_sets _)).eq_of_same_basis ⟨λ _ => mem_uniform_nhds_set_iff⟩

end UniformSpace

-----------------------------------------------------------------------------

open UniformSpace

lemma lemma0 [UniformSpace α] : Tendsto Prod.snd (𝓤 α ⊓ comap Prod.fst (𝓟 s)) (𝓝ᵘ s) := by
  simp_rw [comap_principal, uniform_nhds_set, tendsto_lift', eventually_inf_principal]
  exact λ U hU => mem_of_superset hU (λ ⟨x, y⟩ hxy hx => mem_biUnion hx hxy)

lemma lemma2 {p : Filter ι} {f : α →β} {s : Set α} : Tendsto (f ∘ Prod.snd) (p ×ˢ (𝓟 s)) (𝓟 (f '' s)) :=
  (tendsto_principal_principal.mpr $ λ _ => mem_image_of_mem f).comp tendsto_snd

lemma lemma1 {F : ι → α → β} {f : α → β} [UniformSpace β] (hF : TendstoUniformlyOn F f p s) :
    Tendsto (λ (q : ι × α) => (f q.2, F q.1 q.2)) (p ×ˢ 𝓟 s) ((𝓟 (f '' s)) ×ˢ (𝓝ᵘ (f '' s))) := by
  rw [tendstoUniformlyOn_iff_tendsto] at hF
  refine tendsto_prod_iff'.mpr ⟨lemma2, ?h⟩
  exact lemma0.comp (tendsto_inf.mpr ⟨hF, tendsto_comap_iff.mpr lemma2⟩)

lemma lemma13 {f : α → β} [UniformSpace β] (hF : TendstoUniformlyOn F f p s) :
    Tendsto (uncurry F) (p ×ˢ 𝓟 s) (𝓝ᵘ (f '' s)) :=
  (tendsto_prod_iff'.mp (lemma1 hF)).2
