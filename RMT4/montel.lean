import Mathlib.Analysis.Complex.Liouville
-- import topology.continuous_function.bounded
-- import topology.uniform_space.uniform_convergence_topology
import RMT4.defs
import RMT4.hurwitz
import RMT4.ascoli

open Set Function Metric UniformConvergence Complex

-- open complex set metric filter RMT bounded_continuous_function function
-- open_locale bounded_continuous_function uniform_convergence topological_space uniformity filter

def compacts (U : Set ℂ) : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}

variable {F : ι → ℂ →ᵤ[compacts U] ℂ}
-- variables {ι : Type*} {U K : set ℂ}  {z : ℂ}

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
    ⟨h, isCompact_of_isClosed_bounded isClosed_cthickening hK2.bounded.cthickening⟩
  obtain ⟨M, hMp, hM⟩ := h1 _ e1
  refine ⟨M / δ, div_pos hMp hδ, ?_⟩
  rintro z₀ hz₀ w ⟨i, rfl⟩
  simp only [mem_closedBall_zero_iff]
  refine norm_deriv_le_aux hδ ?_ ?_
  { exact (h2 i).diffContOnCl_ball ((closedBall_subset_cthickening hz₀ δ).trans h) }
  { rintro z hz
    have : z ∈ cthickening δ K :=
      sphere_subset_closedBall.trans (closedBall_subset_cthickening hz₀ δ) hz
    simpa using hM z this ⟨i, rfl⟩ }

-- lemma UniformlyBoundedOn.equicontinuous_on
--   (h1 : UniformlyBoundedOn F U)
--   (hU : IsOpen U)
--   (h2 : ∀ (i : ι), DifferentiableOn ℂ (F i) U)
--   (hK : K ∈ compacts U) :
--   equicontinuous (λ i, K.restrict (F i)) :=
-- begin
--   have key := h1.deriv hU h2,
--   rintro ⟨z, hz⟩,
--   obtain ⟨δ, hδ, h⟩ := nhds_basis_closed_ball.mem_iff.1 (hU.mem_nhds (hK.1 hz)),
--   obtain ⟨M, hMp, hM⟩ := key (closed_ball z δ) ⟨h, is_compact_closed_ball _ _⟩,
--   rw [equicontinuous_at_iff],
--   rintro ε hε,
--   refine ⟨δ ⊓ ε / M, gt_iff_lt.2 (lt_inf_iff.2 ⟨hδ, div_pos hε hMp⟩), λ w hw i, _⟩,
--   simp,
--   have e1 : ∀ x ∈ closed_ball z δ, differentiable_at ℂ (F i) x,
--     from λ x hx, (h2 i).differentiable_at (hU.mem_nhds (h hx)),
--   have e2 : ∀ x ∈ closed_ball z δ, ‖deriv (F i) x‖ ≤ M,
--     from λ x hx, by simpa using hM x hx ⟨i, rfl⟩,
--   have e3 : z ∈ closed_ball z δ := mem_closed_ball_self hδ.le,
--   have e4 : w.1 ∈ closed_ball z δ := by simpa using (lt_inf_iff.1 hw).1.le,
--   rw [dist_eq_norm],
--   refine ((convex_closed_ball _ _).norm_image_sub_le_of_norm_deriv_le e1 e2 e4 e3).trans_lt _,
--   have : ‖z - w.val‖ < ε / M,
--   { have := (lt_inf_iff.1 hw).2,
--     rwa [dist_comm, subtype.dist_eq, dist_eq_norm] at this },
--   convert mul_lt_mul' le_rfl this (norm_nonneg _) hMp,
--   field_simp [hMp.lt.ne.symm, mul_comm]
-- end

-- theorem montel (hU : IsOpen U) (h1 : UniformlyBoundedOn F U)
--   (h2 : ∀ i, DifferentiableOn ℂ (F i) U) :
--   totally_bounded (range F) :=
-- begin
--   refine ascoli (λ K hK, hK.2) _ (by simpa using λ z, h1.totally_bounded_at),
--   exact λ K hK, h1.equicontinuous_on hU h2 hK
-- end

-- lemma bound_on_deriv {f : ℂ → ℂ} {r : ℝ} {z₀ : ℂ} (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
--   (hfr : maps_to f (ball z₀ r) 𝔻) (hrU : closed_ball z₀ r ⊆ U) :
--   ‖deriv f z₀‖ ≤ 1 / r :=
-- begin
--   have e1 : DifferentiableOn ℂ f (closure (ball z₀ r)),
--   from hf.mono ((closure_ball z₀ hr.ne.symm).symm ▸hrU),
--   have e4 : maps_to f (closed_ball z₀ r) (closed_ball 0 1),
--   { simp only [← closure_ball z₀ hr.ne.symm, ← closure_ball (0 : ℂ) one_ne_zero] at hrU ⊢,
--     exact hfr.closure_of_continuous_on e1.continuous_on },
--   refine norm_deriv_le_aux hr e1.diff_cont_on_cl (λ z hz, _),
--   simpa using e4 (sphere_subset_closed_ball hz)
-- end
