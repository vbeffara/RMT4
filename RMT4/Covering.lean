import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant
import RMT4.to_mathlib

open Topology Filter Metric TopologicalSpace Set

variable {U : Set ℂ} {f : ℂ → ℂ} {Λ : LocalPrimitiveOn U f}

def holo_covering (_ : HasLocalPrimitiveOn U f) := U × ℂ

def LocalPrimitiveOn.map₀ (Λ : LocalPrimitiveOn U f) (z : U) (v : ℂ) : ℂ → ℂ :=
  λ w => v + (Λ.F z w - Λ.F z z)

lemma LocalPrimitiveOn.der₀ (Λ : LocalPrimitiveOn U f) {z : U} {v w : ℂ} (hw : w ∈ Λ.S z) :
    HasDerivAt (Λ.map₀ z v) (f w) w := by
  simp [map₀]
  have l1 : HasDerivAt (λ _ => v) 0 w := hasDerivAt_const _ _
  have l2 : HasDerivAt (λ w => Λ.F z w) (f w) w := Λ.der z w hw
  have l3 : HasDerivAt (λ _ => Λ.F z z) 0 w := hasDerivAt_const _ _
  convert HasDerivAt.add l1 (l2.sub l3) using 1 ; simp

def LocalPrimitiveOn.map (Λ : LocalPrimitiveOn U f) (z : U) (v : ℂ) : U → holo_covering ⟨Λ⟩ :=
  λ w => (w, Λ.map₀ z v w)

namespace holo_covering

def nhd (Λ : LocalPrimitiveOn U f) (z : holo_covering ⟨Λ⟩) : Filter (holo_covering ⟨Λ⟩) :=
  Filter.map (Λ.map z.1 z.2) (𝓝 z.1)

instance : TopologicalSpace (holo_covering h) := TopologicalSpace.mkOfNhds (nhd h.some)

lemma mem_nhd (z : holo_covering ⟨Λ⟩) (s : Set (holo_covering ⟨Λ⟩)) :
    s ∈ nhd Λ z ↔ ∃ t ∈ 𝓝 z.1, Λ.map z.1 z.2 '' t ⊆ s := by
  rw [nhd, mem_map_iff_exists_image]

lemma mem_nhd' {z : holo_covering ⟨Λ⟩} {s : Set (holo_covering ⟨Λ⟩)} (h : s ∈ nhd Λ z) :
    ∃ t ∈ 𝓝 z.1, (Subtype.val '' t ⊆ Λ.S z.1) ∧ Λ.map z.1 z.2 '' t ⊆ s := by
  obtain ⟨t, l1, l2⟩ := (mem_nhd z s).1 h
  refine ⟨t ∩ U.restrict (Λ.S z.1), ?_, ?_, ?_⟩
  · apply Filter.inter_mem l1
    apply IsOpen.mem_nhds
    · exact isOpen_induced (Λ.opn z.1)
    · exact Λ.mem z.1
  · refine (Set.image_inter_subset _ _ _).trans ?_
    refine (Set.inter_subset_right _ _).trans ?_
    simp
    rintro ⟨x, hx⟩ hx'
    exact hx'
  · exact (Set.image_subset (Λ.map z.1 z.2) (inter_subset_left _ _)).trans l2

lemma pure_le_nhd : pure ≤ nhd Λ := by
  intro a
  simp only [nhd, le_map_iff, mem_pure]
  intro s hs
  apply (mem_image _ _ _).2 ⟨a.1, mem_of_mem_nhds hs,
    by simp [LocalPrimitiveOn.map, LocalPrimitiveOn.map₀]⟩

lemma mem_map_iff (s : Set U) (x y : holo_covering ⟨Λ⟩) :
    y ∈ Λ.map x.1 x.2 '' s ↔ y.1 ∈ s ∧ y = Λ.map x.1 x.2 y.1 where
  mp h := by
    obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).1 h
    simp [LocalPrimitiveOn.map, hz]
  mpr h := (mem_image _ _ _).2 ⟨y.1, h.1, h.2.symm⟩

lemma image_eq_of_mem_map {s : Set U} {x y : holo_covering ⟨Λ⟩}
    (h : y ∈ Λ.map x.1 x.2 '' s) : y.2 = Λ.map₀ x.1 x.2 y.1 := by
  rw [((mem_map_iff _ _ _).1 h).2] ; rfl

lemma premain {s : Set ℂ} (hs : IsPreconnected s) (hs2 : IsOpen s) {x y : holo_covering ⟨Λ⟩}
    (hxy : y.2 = Λ.map₀ x.1 x.2 y.1) (hy : y.1.1 ∈ s) (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) :
    EqOn (Λ.map₀ x.1 x.2) (Λ.map₀ y.1 y.2) s := by
  have l1 (z) (hz : z ∈ s) : HasDerivAt (Λ.map₀ x.1 x.2) (f z) z := Λ.der₀ (hsx hz)
  have l2 (z) (hz : z ∈ s) : HasDerivAt (Λ.map₀ y.1 y.2) (f z) z := Λ.der₀ (hsy hz)
  apply hs.apply_eq_of_hasDeriv_eq hs2 hy l1 l2
  simp [LocalPrimitiveOn.map₀, hxy]

lemma main (hU : IsOpen U) (s : Set U) (hs : IsPreconnected s) (hs2 : IsOpen s)
    {x y : holo_covering ⟨Λ⟩} (hy : y ∈ Λ.map x.1 x.2 '' s) (hs3 : Subtype.val '' s ⊆ Λ.S x.fst)
    (hs4 : Subtype.val '' s ⊆ Λ.S y.fst) : EqOn (Λ.map x.1 x.2) (Λ.map y.1 y.2) s := by
  let s₀ : Set ℂ := Subtype.val '' s
  have hs₀ : IsPreconnected s₀ := hs.image _ continuous_subtype_val.continuousOn
  have hs2₀ : IsOpen s₀ := hU.isOpenMap_subtype_val s hs2
  have key : EqOn (LocalPrimitiveOn.map₀ Λ x.fst x.snd) (LocalPrimitiveOn.map₀ Λ y.fst y.snd) s₀ := by
    obtain ⟨hy1, hy2⟩ := (mem_map_iff _ _ _).1 hy
    rw [Prod.ext_iff] at hy2
    refine premain hs₀ hs2₀ hy2.2 ?_ hs3 hs4
    exact mem_image_of_mem Subtype.val hy1
  intro z hz
  simp [LocalPrimitiveOn.map, key (mem_image_of_mem Subtype.val hz)]

lemma nhd_is_nhd (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : holo_covering ⟨Λ⟩) :
    ∀ S ∈ nhd Λ z, ∃ T ∈ nhd Λ z, T ⊆ S ∧ ∀ a ∈ T, S ∈ nhd Λ a := by
  have C := hU.locallyConnectedSpace
  intro S hS
  obtain ⟨s, hs1, hs3, hs2⟩ := mem_nhd' hS
  obtain ⟨t, ht1, ht2, ht3, _⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C z.1 s hs1
  refine ⟨Λ.map z.1 z.2 '' t, image_mem_map (ht2.mem_nhds ht3), (image_subset _ ht1).trans hs2, ?_⟩
  intro a ha

  let t' := t ∩ U.restrict (Λ.S a.1)
  have l1 : t' ∈ 𝓝 a.1 := by
    apply Filter.inter_mem
    · apply ht2.mem_nhds
      rw [mem_map_iff] at ha
      exact ha.1
    · apply IsOpen.mem_nhds
      · exact isOpen_induced (Λ.opn a.1)
      · exact Λ.mem a.1
  obtain ⟨t₀, l2, l3, l4, l5⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C a.1 t' l1

  refine (mem_nhd _ _).2 ⟨t₀, l3.mem_nhds l4, ?_⟩
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := (mem_image _ _ _).1 hu
    apply hs2

    have l6 : a ∈ LocalPrimitiveOn.map Λ z.fst z.snd '' t₀ := by
      rw [mem_map_iff, Prod.ext_iff, LocalPrimitiveOn.map]
      simp [image_eq_of_mem_map ha, l4]
    have l7 : Subtype.val '' t₀ ⊆ LocalPrimitiveOn.S Λ z.fst := by
      apply (image_subset _ (l2.trans ((inter_subset_left _ _).trans ht1))).trans hs3
    have l8 : Subtype.val '' t₀ ⊆ LocalPrimitiveOn.S Λ a.fst := by
      simp only [image_subset_iff]
      exact λ _ hx => (inter_subset_right _ _ (l2 hx))
    rw [← main hU t₀ l5.isPreconnected l3 l6 l7 l8 hw]
    exact mem_image_of_mem _ (ht1 (l2 hw).1)

def p (h : HasLocalPrimitiveOn U f) : holo_covering h → U := λ z => z.1

lemma discreteTopology (hU : IsOpen U) (h : HasLocalPrimitiveOn U f) (z : U) :
    DiscreteTopology ↑(p h ⁻¹' {z}) := by
  let Λ := h.some
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_mkOfNhds, nhds_induced, p]
  rintro ⟨z, u⟩ rfl
  rw [nhds_mkOfNhds _ _ pure_le_nhd (nhd_is_nhd _ hU)]
  refine ⟨Λ.map z u '' U.restrict (Λ.S z), ?_, ?_⟩
  · apply image_mem_map
    simp only [nhds_induced]
    exact ⟨_, Λ.nhd z, by rfl⟩
  · rintro ⟨⟨a₁, ha₁⟩, a₂⟩ rfl
    simp [LocalPrimitiveOn.map]
    rintro z hz _ h2
    obtain ⟨h3, h4⟩ := Prod.ext_iff.1 h2
    simp at h3 h4
    simp [LocalPrimitiveOn.map, LocalPrimitiveOn.map₀, h3] at h4
    rw [← h4]

-- theorem isCoveringMap [LocallyConnectedSpace U] (hU : IsOpen U) (h : HasLocalPrimitiveOn U f) :
--     IsCoveringMap (p h) := by
--   intro z
--   refine ⟨discreteTopology hU h z, ?_⟩
--   sorry

end holo_covering