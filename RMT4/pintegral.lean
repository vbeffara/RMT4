import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ContDiffDef
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Calculus.MeanValue
import RMT4.Subdivision

open BigOperators Metric Set Subdivision Topology Filter Nat

structure LocalPrimitiveOn (U : Set ℂ) (f : ℂ → ℂ) :=
  F : U → ℂ → ℂ
  S : U → Set ℂ
  mem (z : U) : z.1 ∈ S z
  opn (z : U) : IsOpen (S z)
  dif (z : U) : DifferentiableOn ℂ (F z) (S z)
  eqd (z : U) : (S z).EqOn (deriv (F z)) f

lemma LocalPrimitiveOn.nhd (h : LocalPrimitiveOn U f) (z : U) : h.S z ∈ 𝓝 z.1 :=
  (h.opn z).mem_nhds (h.mem z)

noncomputable def LocalPrimitiveOn_deriv (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) :
    LocalPrimitiveOn U (deriv F) where
  F _ := F
  S _ := U
  mem z := z.2
  opn _ := hU
  eqd _ := eqOn_refl (deriv F) U
  dif _ := hF

def HasLocalPrimitiveOn (U : Set ℂ) (f : ℂ → ℂ) : Prop := Nonempty (LocalPrimitiveOn U f)

noncomputable def pintegral_aux (hab : a < b) (f : ℂ → ℂ) (γ : ℝ → ℂ) (h2 : MapsTo γ (Icc a b) U)
    (hγ : ContinuousOn γ (Icc a b)) (hf : LocalPrimitiveOn U f) : ℂ :=
  have h1 (t : Icc a b) : ∃ i, hf.S i ∈ 𝓝 (γ t) :=
    let u : U := ⟨γ t, h2 t.2⟩
    ⟨u, hf.nhd u⟩
  let RW := exists_reladapted hab hγ h1
  RW.σ.sumSubAlong (hf.F ∘ RW.I) γ

noncomputable def pintegral (a b : ℝ) (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ := by
  by_cases h : a < b ∧ ContinuousOn γ (Icc a b) ∧ ∃ U : Set ℂ, MapsTo γ (Icc a b) U ∧
    HasLocalPrimitiveOn U f
  · choose hab hγ U h2 hf using h
    exact pintegral_aux hab f γ h2 hγ hf.some
  · exact 0

lemma isLocallyConstant_of_deriv_eq_zero (hU : IsOpen U) {f : ℂ → ℂ} (h : DifferentiableOn ℂ f U)
    (hf : U.EqOn (deriv f) 0) :
    IsLocallyConstant (U.restrict f) := by
  refine (IsLocallyConstant.iff_exists_open _).2 (λ ⟨z, hz⟩ => ?_)
  obtain ⟨ε, L1, L2⟩ := isOpen_iff.1 hU z hz
  refine ⟨ball ⟨z, hz⟩ ε, isOpen_ball, mem_ball_self L1, λ ⟨z', _⟩ hz' => ?_⟩
  refine (convex_ball z ε).is_const_of_fderivWithin_eq_zero (h.mono L2) ?_ hz' (mem_ball_self L1)
  intro x hx
  rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hx)]
  · exact ContinuousLinearMap.ext_ring (hf (L2 hx))
  · exact h.differentiableAt (hU.mem_nhds (L2 hx))

lemma apply_eq_of_path (hab : a ≤ b) {f : ℂ → ℂ} (hf : IsLocallyConstant (U.restrict f))
    {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc a b)) (h : MapsTo γ (Icc a b) U) :
    f (γ b) = f (γ a) := by
  haveI : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.1 isPreconnected_Icc
  have h2 := hf.comp_continuous (hγ.restrict_mapsTo h)
  exact @IsLocallyConstant.apply_eq_of_isPreconnected _ _ _ _ (h2) _ isPreconnected_univ
    ⟨b, hab, le_rfl⟩ ⟨a, le_rfl, hab⟩ (mem_univ _) (mem_univ _)

lemma sumSubAlong_eq_zero (hab : a < b) {DW : LocalPrimitiveOn U 0}
  {RW : reladapted a b DW.S γ} (hγ : ContinuousOn γ (Icc a b)) :
    RW.σ.sumSubAlong (DW.F ∘ RW.I) γ = 0 := by
  refine Subdivision.sum_eq_zero (λ k => (sub_eq_zero.2 ?_))
  apply apply_eq_of_path (RW.σ.mono' hab).le
  · apply isLocallyConstant_of_deriv_eq_zero (DW.opn _) (DW.dif _)
    exact λ _ hz => DW.eqd (RW.I k) hz
  · exact hγ.mono (RW.σ.piece_subset hab.le)
  · exact mapsTo'.2 (RW.sub k)

@[simp] lemma pintegral_zero (hab : a < b) (hγ : ContinuousOn γ (Icc a b)) :
    pintegral a b 0 γ = 0 := by
  have h : ∃ U, MapsTo γ (Icc a b) U ∧ HasLocalPrimitiveOn U 0 := by
    refine ⟨univ, mapsTo_univ _ _, ?_⟩
    refine ⟨λ _ => 0, λ _ => univ, λ _ => mem_univ _, λ _ => isOpen_univ,
        ?_, ?_⟩
    · intro z
      apply differentiableOn_const
    · intro z u _
      change deriv (λ _ => 0) u = 0
      simp only [deriv_const]
  simp [pintegral, hab, hγ, h, pintegral_aux, sumSubAlong_eq_zero]

lemma sub_eq_sub_of_deriv_eq_deriv (hab : a ≤ b) (hU : IsOpen U)
    {γ : ℝ → ℂ} (hγ₁ : ContinuousOn γ (Icc a b)) (hγ₂ : MapsTo γ (Icc a b) U)
    {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hfg : ∀ z ∈ U, deriv f z = deriv g z) :
    f (γ b) - f (γ a) = g (γ b) - g (γ a) := by
  rw [sub_eq_sub_iff_sub_eq_sub]
  change (f - g) (γ b) = (f - g) (γ a)
  refine apply_eq_of_path (U := U) hab ?_ hγ₁ hγ₂
  refine isLocallyConstant_of_deriv_eq_zero hU (hf.sub hg) (λ z hz => ?_)
  have h1 : DifferentiableAt ℂ f z := hf.differentiableAt (hU.mem_nhds hz)
  have h2 : DifferentiableAt ℂ g z := hg.differentiableAt (hU.mem_nhds hz)
  have h3 : deriv (f - g) z = deriv f z - deriv g z := deriv_sub h1 h2
  simp [hfg z hz, h3]

lemma sumSubAlong_eq_of_sigma (hab : a < b) {hf : LocalPrimitiveOn U f} {RW₁ RW₂ : reladapted a b hf.S γ}
    (h : RW₁.σ = RW₂.σ) (hγ : ContinuousOn γ (Icc a b)) :
    RW₁.σ.sumSubAlong (hf.F ∘ RW₁.I) γ = RW₂.σ.sumSubAlong (hf.F ∘ RW₂.I) γ := by
  rcases hf with ⟨F, S, _, Sopn, Sdif, Seqd⟩
  rcases RW₁ with ⟨σ, I₁, hI₁⟩
  rcases RW₂ with ⟨σ', I₂, hI₂⟩
  subst h
  refine Subdivision.sum_congr (λ k => ?_)
  apply sub_eq_sub_of_deriv_eq_deriv (σ.mono' hab).le ((Sopn _).inter (Sopn _))
  · exact (hγ.mono (σ.piece_subset hab.le))
  · simpa only [mapsTo'] using subset_inter (hI₁ k) (hI₂ k)
  · exact (Sdif _).mono (inter_subset_left _ _)
  · exact (Sdif _).mono (inter_subset_right _ _)
  · exact λ z hz => (Seqd _ hz.1).trans (Seqd _ hz.2).symm

lemma telescopic (f : Fin (n + 1) → ℂ) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (Fin.last n) - f 0 := by
  have l1 : ∑ i : Fin n, f (i.succ) = ∑ i : Fin (n + 1), f i - f 0 := by
    simp [Fin.sum_univ_succ f]
  have l2 : ∑ i : Fin n, f (i.castSucc) = ∑ i : Fin (n + 1), f i - f (Fin.last n) := by
    simp [Fin.sum_univ_castSucc f]
  simp [l1, l2]

-- missing : DifferentiableOn.inter
lemma sumSubAlong_eq_sub (hab : a < b) (hF : DifferentiableOn ℂ F U) (hf : LocalPrimitiveOn U (deriv F))
    (hγ : ContinuousOn γ (Icc a b)) (RW : reladapted a b hf.S γ) (hU : IsOpen U)
    (hh : MapsTo γ (Icc a b) U):
    RW.σ.sumSubAlong (hf.F ∘ RW.I) γ = F (γ b) - F (γ a) := by
  have key (i : Fin (RW.σ.size + 1)) :
      ((hf.F ∘ RW.I) i ∘ γ) (RW.σ.y i) - ((hf.F ∘ RW.I) i ∘ γ) (RW.σ.x i) =
      F (γ (RW.σ.y i)) - F (γ (RW.σ.x i)) := by
    apply sub_eq_sub_of_deriv_eq_deriv (U := hf.S (RW.I i) ∩ U)
    · exact (RW.σ.mono' hab).le
    · exact (hf.opn (RW.I i)).inter hU
    · exact hγ.mono (RW.σ.piece_subset hab.le)
    · have e1 := Set.mapsTo'.2 (RW.sub i)
      have e2 := RW.σ.piece_subset (i := i) hab.le
      have e3 := hh.mono_left e2
      exact e1.inter e3
    · have := (hf.dif (RW.I i))
      intro z hz
      apply (differentiableWithinAt_inter ?_).2 (this z hz.1)
      exact hU.mem_nhds hz.2
    · apply DifferentiableOn.mono hF
      exact inter_subset_right _ _
    · exact λ z hz => hf.eqd (RW.I i) hz.1
  simp only [sumSubAlong, sumSub, sum, key]
  convert telescopic (F ∘ γ ∘ RW.σ)
  simp

-- lemma pintegral_deriv (hab : a < b) (hU : IsOpen U) (hγ : ContinuousOn γ (Icc a b))
--     (h2 : MapsTo γ (Icc a b) U) (hF : DifferentiableOn ℂ F U) :
--     pintegral_aux hab (deriv F) γ h2 hγ (LocalPrimitiveOn_deriv hU hF) = F (γ b) - F (γ a) :=
--   sumSubAlong_eq_sub hab hF _ hγ _
