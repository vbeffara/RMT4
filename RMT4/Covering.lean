import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant
import RMT4.to_mathlib

open Topology Filter Metric TopologicalSpace Set

variable {U : Set ℂ} {f : ℂ → ℂ} {Λ : LocalPrimitiveOn U f}

def holo_covering (_ : LocalPrimitiveOn U f) := U × ℂ

namespace LocalPrimitiveOn

def map₀ (Λ : LocalPrimitiveOn U f) (z : U) (v : ℂ) : ℂ → ℂ :=
  λ w => v + (Λ.F z w - Λ.F z z)

@[simp] lemma map₀_self {z : U} {v : ℂ} : Λ.map₀ z v z.1 = v := by
  simp [map₀]

@[simp] lemma map₀_self' {z v : ℂ} {hz : z ∈ U} : Λ.map₀ ⟨z, hz⟩ v z = v := by
  simp [map₀]

lemma der₀ (Λ : LocalPrimitiveOn U f) {z : U} {v w : ℂ} (hw : w ∈ Λ.S z) :
    HasDerivAt (Λ.map₀ z v) (f w) w := by
  convert hasDerivAt_const _ _ |>.add (Λ.der z w hw |>.sub<| hasDerivAt_const _ _) using 1 ; simp

def map (Λ : LocalPrimitiveOn U f) (z : U) (v : ℂ) : U → holo_covering Λ :=
  λ w => (w, Λ.map₀ z v w)

@[simp] lemma map_self (a : holo_covering Λ) : Λ.map a.1 a.2 a.1 = a := by simp [map]

end LocalPrimitiveOn

namespace holo_covering

def nhd (z : holo_covering Λ) : Filter (holo_covering Λ) :=
  Filter.map (Λ.map z.1 z.2) (𝓝 z.1)

instance : TopologicalSpace (holo_covering Λ) := TopologicalSpace.mkOfNhds nhd

lemma mem_nhd (z : holo_covering Λ) (s : Set (holo_covering Λ)) :
    s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, Λ.map z.1 z.2 '' t ⊆ s := by
  rw [nhd, mem_map_iff_exists_image]

lemma mem_nhd' {z : holo_covering Λ} {s : Set (holo_covering Λ)} (h : s ∈ nhd z) :
    ∃ t ∈ 𝓝 z.1, (Subtype.val '' t ⊆ Λ.S z.1) ∧ Λ.map z.1 z.2 '' t ⊆ s := by
  obtain ⟨t, l1, l2⟩ := (mem_nhd z s).1 h
  refine ⟨t ∩ Subtype.val ⁻¹' (Λ.S z.1), ?_, ?_, ?_⟩
  · exact Filter.inter_mem l1 <| IsOpen.mem_nhds (isOpen_induced (Λ.opn z.1)) <| Λ.mem z.1
  · exact image_inter_subset _ _ _ |>.trans<| inter_subset_right _ _ |>.trans<|
      image_preimage_subset _ _
  · exact image_subset (Λ.map z.1 z.2) (inter_subset_left _ _) |>.trans l2

lemma pure_le_nhd : pure ≤ nhd (Λ := Λ) := by
  intro a
  simp only [nhd, le_map_iff, mem_pure]
  exact λ s hs => (mem_image _ _ _).2 ⟨a.1, mem_of_mem_nhds hs, Λ.map_self _⟩

lemma mem_map_iff (s : Set U) (x y : holo_covering Λ) :
    y ∈ Λ.map x.1 x.2 '' s ↔ y.1 ∈ s ∧ y.2 = Λ.map₀ x.1 x.2 y.1 where
  mp h := by
    obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).1 h
    simp [LocalPrimitiveOn.map, hz]
  mpr h := by
    refine (mem_image _ _ _).2 ⟨y.1, h.1, ?_⟩
    apply Prod.ext <;> simp [LocalPrimitiveOn.map, h.2]

lemma image_eq_of_mem_map {s : Set U} {x y : holo_covering Λ} (h : y ∈ Λ.map x.1 x.2 '' s) :
    y.2 = Λ.map₀ x.1 x.2 y.1 :=
  ((mem_map_iff _ _ _).1 h).2

lemma eqOn_map₀ {s : Set ℂ} (hs : IsPreconnected s) (hs2 : IsOpen s) {x y : holo_covering Λ}
    (hxy : y.2 = Λ.map₀ x.1 x.2 y.1) (hy : y.1.1 ∈ s) (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) :
    EqOn (Λ.map₀ x.1 x.2) (Λ.map₀ y.1 y.2) s := by
  apply hs.apply_eq_of_hasDeriv_eq hs2 hy (λ z hz => Λ.der₀ (hsx hz)) (λ z hz => Λ.der₀ (hsy hz))
  simp [LocalPrimitiveOn.map₀, hxy]

lemma eqOn_map (hU : IsOpen U) {s : Set U} (hs : IsPreconnected s) (hs2 : IsOpen s)
    {x y : holo_covering Λ} (hy : y ∈ Λ.map x.1 x.2 '' s) (hs3 : Subtype.val '' s ⊆ Λ.S x.1)
    (hs4 : Subtype.val '' s ⊆ Λ.S y.1) : EqOn (Λ.map x.1 x.2) (Λ.map y.1 y.2) s := by
  let s₀ : Set ℂ := Subtype.val '' s
  have hs₀ : IsPreconnected s₀ := hs.image _ continuous_subtype_val.continuousOn
  have hs2₀ : IsOpen s₀ := hU.isOpenMap_subtype_val s hs2
  have key : EqOn (Λ.map₀ x.1 x.2) (Λ.map₀ y.1 y.2) s₀ := by
    obtain ⟨hy1, hy2⟩ := (mem_map_iff _ _ _).1 hy
    exact eqOn_map₀ hs₀ hs2₀ hy2 (mem_image_of_mem Subtype.val hy1) hs3 hs4
  intro z hz
  simp [LocalPrimitiveOn.map, key (mem_image_of_mem Subtype.val hz)]

lemma nhd_is_nhd (hU : IsOpen U) (z : holo_covering Λ) :
    ∀ S ∈ nhd z, ∃ T ∈ nhd z, T ⊆ S ∧ ∀ a ∈ T, S ∈ nhd a := by
  have C := hU.locallyConnectedSpace
  intro S hS
  obtain ⟨s, hs1, hs3, hs2⟩ := mem_nhd' hS
  obtain ⟨t, ht1, ht2, ht3, _⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C z.1 s hs1
  refine ⟨Λ.map z.1 z.2 '' t, image_mem_map (ht2.mem_nhds ht3), (image_subset _ ht1).trans hs2, ?_⟩
  intro a ha
  have l1 : t ∩ Subtype.val ⁻¹' (Λ.S a.1) ∈ 𝓝 a.1 := by
    apply Filter.inter_mem
    · exact ht2.mem_nhds <| ((mem_map_iff _ _ _).1 ha).1
    · exact isOpen_induced (Λ.opn a.1) |>.mem_nhds (Λ.mem a.1)
  obtain ⟨t₀, l2, l3, l4, l5⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C a.1 _ l1
  refine (mem_nhd _ _).2 ⟨t₀, l3.mem_nhds l4, ?_⟩
  intro u hu
  obtain ⟨w, hw, rfl⟩ := (mem_image _ _ _).1 hu
  have key : Λ.map z.1 z.2 w = Λ.map a.1 a.2 w := by
    refine eqOn_map hU l5.isPreconnected l3 ?_ ?_ ?_ hw
    · simp only [mem_map_iff, l4, image_eq_of_mem_map ha, and_self]
    · exact image_subset _ (l2.trans (inter_subset_left _ _ |>.trans ht1)) |>.trans hs3
    · simpa only [image_subset_iff] using λ _ hx => (inter_subset_right _ _ (l2 hx))
  exact hs2 <| key ▸ mem_image_of_mem _ (ht1 (l2 hw).1)

def p (Λ : LocalPrimitiveOn U f) : holo_covering Λ → U := λ z => z.1

lemma discreteTopology (hU : IsOpen U) (z : U) : DiscreteTopology ↑(p Λ ⁻¹' {z}) := by
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_mkOfNhds, nhds_induced, p]
  rintro ⟨z, u⟩ rfl
  rw [nhds_mkOfNhds _ _ pure_le_nhd (nhd_is_nhd hU)]
  refine ⟨Λ.map z u '' (Subtype.val ⁻¹' (Λ.S z)), ?_, ?_⟩
  · apply image_mem_map
    simpa only [nhds_induced] using ⟨_, Λ.nhd z, by rfl⟩
  · rintro ⟨⟨a₁, ha₁⟩, a₂⟩ rfl
    simp only [LocalPrimitiveOn.map, mem_image, Subtype.exists, forall_exists_index, and_imp]
    rintro z _ _ h2
    congr
    obtain ⟨h3, h4⟩ := Prod.ext_iff.1 h2
    simp only [Subtype.mk.injEq] at h3 ; subst h3
    simpa using h4.symm

def T (Λ : LocalPrimitiveOn U f) (z : U) : Trivialization (↑(p Λ ⁻¹' {z})) (p Λ) := sorry

theorem isCoveringMap (hU : IsOpen U) : IsCoveringMap (p Λ) := by
  intro z
  refine ⟨discreteTopology hU z, ?_⟩
  sorry

end holo_covering