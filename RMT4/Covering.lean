import Mathlib
import RMT4.pintegral
import RMT4.LocallyConstant
import RMT4.to_mathlib
import RMT4.Bunch

open Topology Filter Metric TopologicalSpace Set Subtype

variable {U : Set ℂ} {f : ℂ → ℂ} {Λ Λ' : LocalPrimitiveOn U f}

namespace LocalPrimitiveOn

/-- The shift of `Λ.F z` going through a -/
def FF (Λ : LocalPrimitiveOn U f) (z : U) (a : U × ℂ) (w : ℂ) : ℂ := Λ.F z w + (a.2 - Λ.F z a.1)

@[simp] lemma FF_self : LocalPrimitiveOn.FF Λ z (w, u) w = u := by simp [FF]

@[simp] lemma FF_self' : LocalPrimitiveOn.FF Λ z w w.1 = w.2 := FF_self

lemma FF_deriv (hw : w ∈ Λ.S z) : HasDerivAt (Λ.FF z a) (f w) w := Λ.der z w hw |>.add_const _

theorem isOpen_FF_eq (Λ : LocalPrimitiveOn U f) (i j : U × ℂ) :
    IsOpen { z : U | z ∈ val ⁻¹' S Λ i.1 ∩ val ⁻¹' S Λ j.1 ∧ Λ.FF i.1 i ↑z = Λ.FF j.1 j ↑z } := by
  simp only [isOpen_iff_nhds, mem_setOf_eq, nhds_induced, le_principal_iff, mem_comap,
    preimage_subset_iff, Subtype.forall, and_imp]
  rintro z _ ⟨h1, h2⟩ h3
  have l1 : ∀ᶠ w in 𝓝 z, HasDerivAt (FF Λ i.1 i) (f w) w :=
    eventually_of_mem (Λ.opn i.1 |>.mem_nhds h1) (λ w => FF_deriv)
  have l2 : ∀ᶠ w in 𝓝 z, HasDerivAt (FF Λ j.1 j) (f w) w :=
    eventually_of_mem (Λ.opn j.1 |>.mem_nhds h2) (λ w => FF_deriv)
  have l4 := @eventuallyEq_of_hasDeriv ℂ _ f z (Λ.FF i.1 i) (Λ.FF j.1 j) l1 l2 h3
  have l5 := inter_mem (inter_mem l4 (Λ.opn i.1 |>.mem_nhds h1)) (Λ.opn j.1 |>.mem_nhds h2)
  exact ⟨_, l5, λ w _ h => ⟨⟨h.1.2, h.2⟩, h.1.1.symm⟩⟩

def toBunch (Λ : LocalPrimitiveOn U f) : Bunch (U × ℂ) U ℂ where
  S i := val ⁻¹' Λ.S i.1
  F i w := Λ.FF i.1 i w
  cmp := Λ.isOpen_FF_eq

def _root_.holo_covering (Λ : LocalPrimitiveOn U f) := Λ.toBunch.space

abbrev _root_.p (Λ : LocalPrimitiveOn U f) : holo_covering Λ → U := Prod.fst

def map (Λ : LocalPrimitiveOn U f) (z : U) (w : U × ℂ) : holo_covering Λ := (w.1, Λ.FF z (z, w.2) w.1)

/-- The shear transformation. `Φ z` maps a point `(u, v)` to `(u, w)` where `w` is the value above
  `z` of the translate of `F z` that goes through `(u, v)`, and `(Φ z).symm` maps `(u, w)` to
  `(u, v)` where `v` is the value above `u` of the translate of `F` that goes through `(z, v)`. -/

def Φ (Λ : LocalPrimitiveOn U f) (z : U) : holo_covering Λ ≃ U × ℂ where
  toFun w := (w.1, Λ.FF z w z)
  invFun w := (w.1, Λ.FF z (z, w.2) w.1)
  left_inv _ := by simp [FF]
  right_inv _ := by simp [FF]

def π (Λ : LocalPrimitiveOn U f) (z : U) : ℂ ≃ p Λ ⁻¹' {z} where
  toFun w := ⟨⟨z, w⟩, rfl⟩
  invFun w := w.val.2
  left_inv _ := rfl
  right_inv := by rintro ⟨w, rfl⟩ ; simp

def ψ (Λ : LocalPrimitiveOn U f) (z : U) : U × ℂ ≃ U × p Λ ⁻¹' {z} :=
  (Equiv.refl _).prodCongr (π Λ z)

def Ψ (Λ : LocalPrimitiveOn U f) (z : U) : holo_covering Λ ≃ U × p Λ ⁻¹' {z} :=
  (Φ Λ z).trans (ψ Λ z)

def L (Λ : LocalPrimitiveOn U f) (z : U) : LocalEquiv (holo_covering Λ) (U × p Λ ⁻¹' {z}) :=
  (Ψ Λ z).toLocalEquiv

lemma L_image : (L Λ z).IsImage ((val ⁻¹' Λ.S z) ×ˢ univ) ((val ⁻¹' Λ.S z) ×ˢ univ) := by
  intro ⟨z₁, z₂⟩ ; rw [mem_prod, mem_prod] ; simp [L, Ψ, ψ, Φ]

def _root_.holo_covering.T_LocalEquiv (Λ : LocalPrimitiveOn U f) (z : U) :
    LocalEquiv (holo_covering Λ) (U × p Λ ⁻¹' {z}) := L_image.restr

end LocalPrimitiveOn

namespace holo_covering

@[simp] lemma T_fst : (T_LocalEquiv Λ z w).1 = w.1 := rfl

def nhd (z : holo_covering Λ) : Filter (holo_covering Λ) :=
  Filter.map (λ w => (w, Λ.FF z.1 z w)) (𝓝 z.1)

-- example (s : Set (holo_covering Λ)): s ∈ nhd z ↔ s ∈ 𝓝 z := by
--   simp [nhd, mem_map, Bunch.nhds_eq_nhd, Bunch.mem_nhd, Bunch.tile, LocalPrimitiveOn.toBunch,
--     Bunch.idx]
--   rw [← exists_mem_subset_iff]
--   constructor
--   · rintro ⟨t, h1, h2⟩
--     refine ⟨z.1, z.1.2, z.2, ⟨Λ.mem z.1, by simp⟩, t, h1, h2⟩
--   · rintro ⟨a, ha, b, ⟨h1, h2⟩, t, h3, hhh⟩
--     simp [LocalPrimitiveOn.FF] at h2 hhh ⊢
--     refine ⟨t, h3, ?_⟩
--     sorry

def nhd_from (x : U) (z : holo_covering Λ) : Filter (holo_covering Λ) :=
  Filter.map (λ w => (w, Λ.FF x z w)) (𝓝 z.1)

instance : TopologicalSpace (holo_covering Λ) := TopologicalSpace.mkOfNhds nhd

lemma mem_nhd_1 {z : holo_covering Λ} : s ∈ nhd z ↔ ∀ᶠ u in 𝓝 z.1, ⟨u, Λ.FF z.1 z u⟩ ∈ s :=
  by rfl

lemma mem_nhd_from {z : holo_covering Λ} : s ∈ nhd_from x z ↔ ∀ᶠ u in 𝓝 z.1, ⟨u, Λ.FF x z u⟩ ∈ s :=
  by rfl

lemma mem_nhd {z : holo_covering Λ} :
    s ∈ nhd z ↔ ∃ t ∈ 𝓝 z.1, (λ w => ⟨w, Λ.FF z.1 z w⟩) '' t ⊆ s := by
  simpa [mem_nhd_1] using eventually_iff_exists_mem

theorem toto6 : ∀ᶠ x in 𝓝 ↑z, x ∈ Λ.S z := isOpen_iff_eventually.1 (Λ.opn z) ↑z (Λ.mem z)

lemma toto7 : val ⁻¹' Λ.S z ∈ 𝓝 z := by simpa only [nhds_induced] using ⟨_, Λ.nhd z, by rfl⟩

lemma mem_nhd' (h : s ∈ nhd z) : ∃ t ∈ 𝓝 z.1, val '' t ⊆ Λ.S z.1 ∧ (Λ.map z.1 ⟨·, z.2⟩) '' t ⊆ s := by
  -- change ∀ᶠ w in 𝓝 z.1, ↑w ∈ Λ.S z.1 ∧ (Λ.map z.1 ⟨w, z.2⟩) ∈ s
  obtain ⟨t, l1, l2⟩ := mem_nhd.1 h
  refine ⟨t ∩ val ⁻¹' Λ.S z.1, ?_, ?_, ?_⟩
  · exact Filter.inter_mem l1 <| IsOpen.mem_nhds (isOpen_induced (Λ.opn z.1)) <| Λ.mem z.1
  · exact image_inter_subset _ _ _ |>.trans<| inter_subset_right _ _ |>.trans<|
      image_preimage_subset _ _
  · exact image_subset (Λ.map z.1 ⟨·, z.2⟩) (inter_subset_left _ _) |>.trans l2

lemma pure_le_nhd : pure ≤ nhd (Λ := Λ) := by
  intro a
  simp only [nhd, le_map_iff, mem_pure]
  refine λ s hs => (mem_image _ _ _).2 ⟨a.1, mem_of_mem_nhds hs, ?_⟩
  simp [LocalPrimitiveOn.map]

lemma mem_map_iff {y : holo_covering Λ} :
    y ∈ (Λ.map u ⟨·, v⟩) '' s ↔ y.1 ∈ s ∧ y.2 = Λ.FF u ⟨u, v⟩ y.1 where
  mp h := by
    obtain ⟨z, hz, rfl⟩ := (mem_image _ _ _).1 h
    simp [LocalPrimitiveOn.map, hz, LocalPrimitiveOn.FF]
  mpr h := by
    refine (mem_image _ _ _).2 ⟨y.1, h.1, ?_⟩
    simp [LocalPrimitiveOn.map, LocalPrimitiveOn.FF, ← h.2]
    apply Prod.ext <;> simp [LocalPrimitiveOn.map, h.2] ; ring_nf
    simp [LocalPrimitiveOn.FF]

lemma image_eq_of_mem_map {s : Set U} {x y : holo_covering Λ} (h : y ∈ (Λ.map x.1 ⟨·, x.2⟩) '' s) :
    y.2 = Λ.FF x.1 x y.1 :=
  (mem_map_iff.1 h).2

lemma eqOn_F {x y : holo_covering Λ} {s : Set ℂ} (hs : IsOpen s) (hs' : IsPreconnected s)
    (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) (hys : y.1.1 ∈ s) :
    EqOn (Λ.F x.1 · + (y.2 - Λ.F x.1 y.1)) (Λ.F y.1 · + (y.2 - Λ.F y.1 y.1)) s := by
  have l1 (w) (hw : w ∈ s) : HasDerivAt (Λ.F x.1 · + (y.2 - Λ.F x.1 ↑y.1)) (f w) w :=
    Λ.der x.1 w (hsx hw) |>.add_const _
  have l2 (w) (hw : w ∈ s) : HasDerivAt (Λ.F y.1 · + (y.2 - Λ.F y.1 ↑y.1)) (f w) w :=
    Λ.der y.1 w (hsy hw) |>.add_const _
  exact @IsPreconnected.apply_eq_of_hasDeriv_eq ℂ _ f (Λ.F x.1 · + (y.2 - Λ.F x.1 y.1))
    (Λ.F y.1 · + (y.2 - Λ.F y.1 y.1)) y.1 s hs' hs hys l1 l2 (by ring)

lemma eqOn_FF {x y : holo_covering Λ} {s : Set ℂ} (hs' : IsPreconnected s)
    (hs : IsOpen s) (hsx : s ⊆ Λ.S x.1) (hsy : s ⊆ Λ.S y.1) (hys : y.1.1 ∈ s) :
    EqOn (Λ.FF x.1 y) (Λ.FF y.1 y) s :=
  λ _ hws => eqOn_F hs hs' hsx hsy hys hws

lemma titi1 (ha : z.1 ∈ Λ.S a) (hb : z.1 ∈ Λ'.S b) : ∀ᶠ u in 𝓝 z.1, Λ.FF a z u = Λ'.FF b z u := by
  let s := Λ.S a ∩ Λ'.S b
  have l1 : IsOpen s := (Λ.opn a).inter (Λ'.opn b)
  have l2 : s ∈ 𝓝 z.1.1 := l1.mem_nhds ⟨ha, hb⟩
  have l3 : LocallyConnectedSpace ℂ := by infer_instance
  obtain ⟨t, ht1, ht2, ht3, ht4⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 l3 z.1 s l2
  apply eventually_of_mem (ht2.mem_nhds ht3)
  have l5 : ∀ x ∈ t, HasDerivAt (Λ.FF a z) (f x) x := λ x hx => Λ.FF_deriv (ht1 hx).1
  have l6 : ∀ x ∈ t, HasDerivAt (Λ'.FF b z) (f x) x := λ x hx => Λ'.FF_deriv (ht1 hx).2
  apply ht4.isPreconnected.apply_eq_of_hasDeriv_eq ht2 ht3 l5 l6 (by simp)

lemma nhd_from_eq_nhd {z : holo_covering Λ} (h : ↑z.1 ∈ Λ.S x) : nhd_from x z = nhd z := by
  rw [nhd, nhd_from, nhds_induced]
  apply Filter.map_congr
  simp [EventuallyEq]
  filter_upwards [titi1 h (Λ.mem z.1)] with w h1 w' h2 h3
  simp [h3, h1]

lemma eqOn_map (hU : IsOpen U) {s : Set U} (hs : IsPreconnected s) (hs2 : IsOpen s)
    {x y : holo_covering Λ} (hy : y ∈ (Λ.map x.1 ⟨·, x.2⟩) '' s) (hs3 : val '' s ⊆ Λ.S x.1)
    (hs4 : val '' s ⊆ Λ.S y.1) : EqOn (Λ.map x.1 ⟨·, x.2⟩) (Λ.map y.1 ⟨·, y.2⟩) s := by
  let s₀ : Set ℂ := val '' s
  have hs₀ : IsPreconnected s₀ := hs.image _ continuous_subtype_val.continuousOn
  have hs2₀ : IsOpen s₀ := hU.isOpenMap_subtype_val s hs2
  intro z hz
  simp [LocalPrimitiveOn.map]
  obtain ⟨hy1, hy2⟩ := mem_map_iff.1 hy
  have l2 : z.1 ∈ s₀ := by simp [hz]
  rw [Prod.ext_iff] ; simp
  have := eqOn_FF hs₀ hs2₀ hs3 hs4 (mem_image_of_mem val hy1) l2
  rw [← this] ; simp [LocalPrimitiveOn.FF, hy2]

lemma nhd_is_nhd (hU : IsOpen U) (z : holo_covering Λ) :
    ∀ S ∈ nhd z, ∃ T ∈ nhd z, T ⊆ S ∧ ∀ a ∈ T, S ∈ nhd a := by
  have C := hU.locallyConnectedSpace
  intro S hS
  obtain ⟨s, hs1, hs3, hs2⟩ := mem_nhd' hS
  obtain ⟨t, ht1, ht2, ht3, _⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C z.1 s hs1
  refine ⟨(λ w => (w, Λ.FF z.1 z w)) '' t, image_mem_map (ht2.mem_nhds ht3), (image_subset _ ht1).trans hs2, ?_⟩
  intro a ha
  have l1 : t ∩ val ⁻¹' Λ.S a.1 ∈ 𝓝 a.1 := by
    apply Filter.inter_mem
    · exact ht2.mem_nhds <| (mem_map_iff.1 ha).1
    · exact isOpen_induced (Λ.opn a.1) |>.mem_nhds (Λ.mem a.1)
  obtain ⟨t₀, l2, l3, l4, l5⟩ := locallyConnectedSpace_iff_open_connected_subsets.1 C a.1 _ l1
  refine mem_nhd.2 ⟨t₀, l3.mem_nhds l4, ?_⟩
  intro u hu
  obtain ⟨w, hw, rfl⟩ := (mem_image _ _ _).1 hu
  have key : Λ.map z.1 (w, z.2) = Λ.map a.1 (w, a.2) := by
    refine eqOn_map hU l5.isPreconnected l3 ?_ ?_ ?_ hw
    · simp [mem_map_iff, l4, image_eq_of_mem_map ha, and_self, LocalPrimitiveOn.map]
      simp [LocalPrimitiveOn.FF]
      aesop
    · exact image_subset _ (l2.trans (inter_subset_left _ _ |>.trans ht1)) |>.trans hs3
    · simpa only [image_subset_iff] using λ _ hx => (inter_subset_right _ _ (l2 hx))
  apply hs2
  simp
  exact ⟨w, w.2, ht1 (l2 hw).1, key⟩

lemma nhds_eq_nhd (hU : IsOpen U) (z : holo_covering Λ) : 𝓝 z = nhd z :=
  nhds_mkOfNhds nhd z pure_le_nhd (nhd_is_nhd hU)

lemma discreteTopology (hU : IsOpen U) : DiscreteTopology (p Λ ⁻¹' {z}) := by
  simp [discreteTopology_iff_singleton_mem_nhds, nhds_induced]
  rintro ⟨z, u⟩ rfl
  rw [nhds_eq_nhd hU]
  refine ⟨(Λ.map z ⟨·, u⟩) '' (val ⁻¹' (Λ.S z)), image_mem_map toto7, ?_⟩
  simp only [mem_map_iff]
  rintro ⟨a₁, a₂⟩ rfl ⟨_, h2⟩
  simp at h2
  simp [h2]

theorem isOpen_source (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : ↑U) :
    IsOpen (T_LocalEquiv Λ z).source := by
  simp only [isOpen_iff_eventually, T_LocalEquiv, eventually_mem_set]
  intro ⟨a₁, a₂⟩ ha
  simp [LocalPrimitiveOn.L] at ha
  rw [mem_prod] at ha ; simp at ha
  simp only [nhds_eq_nhd hU, nhd, nhds_induced, mem_map, mem_comap]
  refine ⟨Λ.S z, (Λ.opn z) |>.mem_nhds ha, ?_⟩
  exact λ x hx => by
    simp at hx
    simp [LocalPrimitiveOn.L]
    rw [mem_prod]
    simp [hx, LocalPrimitiveOn.map]

theorem isOpen_target : IsOpen (T_LocalEquiv Λ z).target := by
  simp [T_LocalEquiv, LocalPrimitiveOn.L]
  exact IsOpen.prod (isOpen_induced (Λ.opn z)) isOpen_univ

lemma toto10 (l : Filter α) (b : β) : s ∈ l ×ˢ pure b ↔ ∃ t ∈ l, t ×ˢ {b} ⊆ s := by
  simpa using exists_mem_subset_iff.symm

lemma toto11 {s : Set (α × β)}: t ×ˢ {b} ⊆ s ↔ ∀ y ∈ t, (y, b) ∈ s where
  mp h y hy := h ⟨hy, rfl⟩
  mpr h := by rintro ⟨y, b'⟩ ⟨hy, rfl⟩ ; exact h y hy

lemma toto12 [TopologicalSpace α] [TopologicalSpace β] [DiscreteTopology β] {s : Set (α × β)}
  {w : α × β} : s ∈ 𝓝 w ↔ ∀ᶠ x in 𝓝 w.1, (x, w.2) ∈ s := by
  rw [nhds_prod_eq, nhds_discrete β, toto10, eventually_iff_exists_mem]
  simp only [toto11]

lemma toto13 (hU : IsOpen U) {w : U × p Λ ⁻¹' {z}} : s ∈ 𝓝 w ↔ ∀ᶠ x in 𝓝 w.1, (x, w.2) ∈ s := by
  have l1 : DiscreteTopology (p Λ ⁻¹' {z}) := discreteTopology hU
  exact toto12

theorem toto9 (hU : IsOpen U) (h : ↑w.1 ∈ Λ.S z) : ContinuousAt (T_LocalEquiv Λ z) w := by
  rw [ContinuousAt, Tendsto]
  intro s hs
  rw [toto13 hU] at hs
  rw [nhds_eq_nhd hU, ← nhd_from_eq_nhd h]
  simp [T_LocalEquiv, LocalPrimitiveOn.L, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π,
    LocalPrimitiveOn.Φ, mem_nhd_from] at hs ⊢
  filter_upwards [hs] with x hx
  simp [LocalPrimitiveOn.FF] at hx ⊢
  exact hx

theorem toto9' (hU : IsOpen U) (h : ↑w.1 ∈ Λ.S z) : ContinuousAt (T_LocalEquiv Λ z).symm w := by
  rw [ContinuousAt, Tendsto]
  intro s hs
  simp
  rw [toto13 hU]
  rw [nhds_eq_nhd hU, ← nhd_from_eq_nhd h] at hs
  simp [T_LocalEquiv, LocalPrimitiveOn.L, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π,
    LocalPrimitiveOn.Φ, mem_nhd_from] at hs ⊢
  filter_upwards [hs] with x hx
  simp [LocalPrimitiveOn.FF] at hx ⊢
  exact hx

theorem toto8 (hU : IsOpen U) : ContinuousOn (T_LocalEquiv Λ z) (T_LocalEquiv Λ z).source := by
  rintro w h
  rw [continuousWithinAt_iff_continuousAt <| isOpen_source Λ hU z |>.mem_nhds h]
  simp [T_LocalEquiv, LocalPrimitiveOn.L, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π,
    LocalPrimitiveOn.Φ] at h
  rw [mem_prod] at h
  simp at h
  apply toto9 hU h

theorem toto8' (hU : IsOpen U) : ContinuousOn (T_LocalEquiv Λ z).symm (T_LocalEquiv Λ z).target := by
  rintro w h
  rw [continuousWithinAt_iff_continuousAt <| isOpen_target |>.mem_nhds h]
  simp [T_LocalEquiv, LocalPrimitiveOn.L, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π,
    LocalPrimitiveOn.Φ] at h
  apply toto9' hU h

def T_LocalHomeomorph (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : U) :
    LocalHomeomorph (holo_covering Λ) (U × p Λ ⁻¹' {z}) where
  toLocalEquiv := T_LocalEquiv Λ z
  open_source := isOpen_source Λ hU z
  open_target := isOpen_target
  continuous_toFun := toto8 hU
  continuous_invFun := toto8' hU

def T (Λ : LocalPrimitiveOn U f) (hU : IsOpen U) (z : U) : Trivialization (p Λ ⁻¹' {z}) (p Λ) where
  toLocalHomeomorph := T_LocalHomeomorph Λ hU z
  baseSet := val ⁻¹' Λ.S z
  open_baseSet := isOpen_induced (Λ.opn z)
  source_eq := by simp [T_LocalHomeomorph, T_LocalEquiv, LocalPrimitiveOn.L] ; ext ; simp
  target_eq := by simp [T_LocalHomeomorph, T_LocalEquiv, LocalPrimitiveOn.L]
  proj_toFun x _:= rfl

theorem isCoveringMap (hU : IsOpen U) : IsCoveringMap (p Λ) :=
  λ z => ⟨discreteTopology hU, T Λ hU z, Λ.mem z⟩

end holo_covering
