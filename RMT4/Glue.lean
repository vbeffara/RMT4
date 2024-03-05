import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric
import Mathlib.Topology.Algebra.Order.ProjIcc

open Set Interval

variable {a b c t : ℝ} {E : Type*} [TopologicalSpace E]

section real

variable {f g : ℝ → E}

noncomputable def glue_at (b : ℝ) (f g : ℝ → E) := λ t => if t ≤ b then f t else g t

lemma continuous_glue (hf : Continuous f) (hg : Continuous g) (h : f b = g b) :
    Continuous (glue_at b f g) :=
  hf.if_le hg continuous_id continuous_const (λ _ hx => hx.symm ▸ h)

end real

section Icc

variable {F : Icc a b → E} {G : Icc b c → E}

noncomputable def glue_Icc (F : Icc a b → E) (G : Icc b c → E) (t : Icc a c) : E :=
  if h : t ≤ b then F ⟨t, t.2.1, h⟩ else G ⟨t, not_le.1 h |>.le, t.2.2⟩

lemma glue_Icc_eq (hab : a ≤ b) (hbc : b ≤ c) :
    glue_Icc F G = λ t : Icc a c => if t ≤ b then IccExtend hab F t else IccExtend hbc G t := by
  ext t ; simp [glue_Icc] ; split_ifs <;> symm <;> apply IccExtend_of_mem

lemma continuous_glue_Icc (hF : Continuous F) (hG : Continuous G) (hab : a ≤ b) (hbc : b ≤ c)
    (h : F ⟨b, right_mem_Icc.2 hab⟩ = G ⟨b, left_mem_Icc.2 hbc⟩) :
    Continuous (glue_Icc F G) := by
  rw [glue_Icc_eq hab hbc]
  exact continuous_glue hF.Icc_extend' hG.Icc_extend' (by simpa) |>.comp continuous_subtype_val

noncomputable def ContinuousMap.trans (hab : a ≤ b) (hbc : b ≤ c) (F : C(Icc a b, E))
    (G : C(Icc b c, E)) (h : F ⟨b, right_mem_Icc.2 hab⟩ = G ⟨b, left_mem_Icc.2 hbc⟩) :
    C(Icc a c, E) where
  toFun := glue_Icc F G
  continuous_toFun := continuous_glue_Icc F.continuous G.continuous hab hbc h

end Icc

section uIcc

variable {F : Icc a b → E} {G : uIcc b c → E}

noncomputable def glue_uIcc (F : Icc a b → E) (G : uIcc b c → E) (t : Icc a c) : E :=
  if h : t ≤ b then F ⟨t, t.2.1, h⟩ else
    G ⟨t, inf_le_left.trans <| not_le.1 h |>.le, t.2.2.trans le_sup_right⟩

@[simp] lemma glue_uIcc_left (hab : a ≤ b) (hac : a ≤ c) :
    glue_uIcc F G ⟨a, left_mem_Icc.2 hac⟩ = F ⟨a, left_mem_Icc.2 hab⟩ := by
  simp [glue_uIcc, hab]

lemma glue_uIcc_eq (hab : a ≤ b) : glue_uIcc F G = λ t : Icc a c =>
    if t ≤ b then IccExtend hab F t else IccExtend inf_le_sup G t := by
  ext t ; simp [glue_uIcc] ; split_ifs <;> symm <;> apply IccExtend_of_mem

lemma continuous_glue_uIcc (hF : Continuous F) (hG : Continuous G) (hab : a ≤ b)
    (h : F ⟨b, right_mem_Icc.2 hab⟩ = G ⟨b, left_mem_uIcc⟩) : Continuous (glue_uIcc F G) := by
  rw [glue_uIcc_eq hab]
  suffices Continuous fun t => if t ≤ b then IccExtend hab F t else IccExtend inf_le_sup G t from
    this.comp continuous_subtype_val
  refine hF.Icc_extend'.if_le hG.Icc_extend' continuous_id continuous_const (λ x hx => ?_)
  simpa [IccExtend_of_mem, hx] using h

noncomputable def ContinuousMap.trans' (hab : a ≤ b) (F : C(Icc a b, E)) (G : C(uIcc b c, E))
    (h : F ⟨b, right_mem_Icc.2 hab⟩ = G ⟨b, left_mem_uIcc⟩) : C(Icc a c, E) where
  toFun := glue_uIcc F G
  continuous_toFun := continuous_glue_uIcc F.continuous G.continuous hab h

@[simp] lemma ContinuousMap.trans'_left (hab : a ≤ b) (hac : a ≤ c) {F : C(Icc a b, E)}
    {G : C(uIcc b c, E)} (h : F ⟨b, right_mem_Icc.2 hab⟩ = G ⟨b, left_mem_uIcc⟩) :
    F.trans' hab G h ⟨a, left_mem_Icc.2 hac⟩ = F ⟨a, left_mem_Icc.2 hab⟩ := by
  simp [ContinuousMap.trans', hab, hac]

end uIcc

section Iic

variable
  {T E : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T][OrderClosedTopology T] {a b : T}
  {E : Type*} [TopologicalSpace E] {f : Iic a → E} {g : uIcc a b → E}

def glue_Iic (f : Iic a → E) (g : uIcc a b → E) (t : Iic b) : E :=
  if h : t ≤ a then f ⟨t, h⟩ else g ⟨t, inf_le_left.trans (not_le.1 h).le, t.2.trans le_sup_right⟩

lemma glue_Iic_eq : glue_Iic f g = λ t : Iic b =>
    if t ≤ a then IicExtend f t else IccExtend inf_le_sup g t := by
  ext t ; simp [glue_Iic] ; split_ifs <;> symm
  · apply IicExtend_of_mem
  · apply IccExtend_of_mem

lemma continuous_projIic : Continuous (Set.projIic a) :=
  (continuous_const.min continuous_id).subtype_mk _

lemma Continuous.Iic_extend' (hf : Continuous f) : Continuous (IicExtend f) :=
  hf.comp continuous_projIic

lemma continuous_glue_Iic (hf : Continuous f) (hg : Continuous g)
    (h : f ⟨a, le_rfl⟩ = g ⟨a, ⟨inf_le_left, le_sup_left⟩⟩) : Continuous (glue_Iic f g) := by
  rw [glue_Iic_eq]
  suffices h : Continuous fun t => if t ≤ a then IicExtend f t else IccExtend inf_le_sup g t
    by exact h.comp continuous_subtype_val
  refine hf.Iic_extend'.if_le hg.Icc_extend' continuous_id continuous_const ?_
  rintro x rfl ; simpa [IccExtend_of_mem] using h

def ContinuousMap.trans_Iic (F : C(Iic a, E)) (G : C(uIcc a b, E))
    (h : F ⟨a, le_rfl⟩ = G ⟨a, ⟨inf_le_left, le_sup_left⟩⟩) : C(Iic b, E) :=
  ⟨glue_Iic F G, continuous_glue_Iic F.continuous G.continuous h⟩

@[simp] lemma ContinuousMap.trans_Iic_of_le {F : C(Iic a, E)} {G : C(uIcc a b, E)}
    {h : F ⟨a, le_rfl⟩ = G ⟨a, ⟨inf_le_left, le_sup_left⟩⟩} {u : Iic b} (hu : u ≤ a) :
    F.trans_Iic G h u = F ⟨u, hu⟩ := by
  simp [trans_Iic, glue_Iic, hu]

end Iic
