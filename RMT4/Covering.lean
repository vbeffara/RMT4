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

abbrev _root_.holo_covering (Λ : LocalPrimitiveOn U f) := Λ.toBunch.space

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

set_option pp.proofs.withType false

def nhd_from (x : U) (z : holo_covering Λ) : Filter (holo_covering Λ) :=
  Filter.map (λ w => (w, Λ.FF x z w)) (𝓝 z.1)

lemma mem_nhd_from {z : holo_covering Λ} : s ∈ nhd_from x z ↔ ∀ᶠ u in 𝓝 z.1, ⟨u, Λ.FF x z u⟩ ∈ s :=
  by rfl

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

lemma nhd_eq_toBunch_nhd : nhd = Λ.toBunch.nhd := by
  ext ⟨a, b⟩ s
  have : Nonempty ↑(Bunch.idx (LocalPrimitiveOn.toBunch Λ) (a, b)) := by
    simp [LocalPrimitiveOn.toBunch, Bunch.idx, LocalPrimitiveOn.FF]
    refine ⟨a.1, a.prop, Λ.mem a, b, by ring⟩
  constructor
  · intro h
    simp only [nhd, Bunch.nhd, this, dite_true, mem_map, Filter.IsBasis.mem_filter_iff]
    simp only [Bunch.reaches, Bunch.idx]
    simp only [LocalPrimitiveOn.toBunch]
    refine ⟨⟨(a, b), _⟩, ⟨?_, h⟩, ?_⟩
    · simpa using Λ.mem a
    · simpa [Bunch.tile] using subset_rfl
  · simp only [Bunch.nhd, this, dite_true, mem_map, Filter.IsBasis.mem_filter_iff]
    simp only [Bunch.reaches, Bunch.idx]
    simp only at *
    rintro ⟨⟨z, t⟩, ⟨⟨h1, h2⟩, h3⟩, h4⟩
    have : nhd_from (Λ := Λ) z.1 (a, b) = nhd (a, b) := by
      apply nhd_from_eq_nhd
      simpa [LocalPrimitiveOn.toBunch] using h1
    simp only [← this, nhd_from, mem_map]
    simp only [LocalPrimitiveOn.toBunch, Bunch.tile] at *
    simp at h4
    apply mem_of_superset h3
    simp [LocalPrimitiveOn.FF] at h2
    simp [LocalPrimitiveOn.FF, ← h2] at h4 ⊢
    exact h4

lemma nhds_eq_nhd (z : holo_covering Λ) : 𝓝 z = nhd z := by
  rw [nhd_eq_toBunch_nhd, Bunch.nhds_eq_nhd]

lemma discreteTopology : DiscreteTopology (p Λ ⁻¹' {z}) := Bunch.discreteTopology

theorem isOpen_source (Λ : LocalPrimitiveOn U f) (z : ↑U) :
    IsOpen (T_LocalEquiv Λ z).source := by
  simp only [isOpen_iff_eventually, T_LocalEquiv, eventually_mem_set]
  intro ⟨a₁, a₂⟩ ha
  simp [LocalPrimitiveOn.L] at ha
  rw [mem_prod] at ha ; simp at ha
  simp only [nhds_eq_nhd, nhd, nhds_induced, mem_map, mem_comap]
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
  have l1 : DiscreteTopology (p Λ ⁻¹' {z}) := discreteTopology
  exact toto12

theorem toto9 (hU : IsOpen U) (h : ↑w.1 ∈ Λ.S z) : ContinuousAt (T_LocalEquiv Λ z) w := by
  rw [ContinuousAt, Tendsto]
  intro s hs
  rw [toto13 hU] at hs
  rw [nhds_eq_nhd, ← nhd_from_eq_nhd h]
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
  rw [nhds_eq_nhd, ← nhd_from_eq_nhd h] at hs
  simp [T_LocalEquiv, LocalPrimitiveOn.L, LocalPrimitiveOn.Ψ, LocalPrimitiveOn.ψ, LocalPrimitiveOn.π,
    LocalPrimitiveOn.Φ, mem_nhd_from] at hs ⊢
  filter_upwards [hs] with x hx
  simp [LocalPrimitiveOn.FF] at hx ⊢
  exact hx

theorem toto8 (hU : IsOpen U) : ContinuousOn (T_LocalEquiv Λ z) (T_LocalEquiv Λ z).source := by
  rintro w h
  rw [continuousWithinAt_iff_continuousAt <| isOpen_source Λ z |>.mem_nhds h]
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
  open_source := isOpen_source Λ z
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
  λ z => ⟨discreteTopology, T Λ hU z, Λ.mem z⟩

end holo_covering
