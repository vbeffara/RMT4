import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Topology Filter Set Function UniformConvergence

variable {ι : Type*} {l : Filter ι} {U : Set ℂ}

def compacts (U : Set ℂ) : Set (Set ℂ) := {K ⊆ U | IsCompact K}

abbrev 𝓒 (U : Set ℂ) := ℂ →ᵤ[compacts U] ℂ

noncomputable def uderiv (f : 𝓒 U) : 𝓒 U := deriv f

def 𝓗 (U : Set ℂ) := {f : 𝓒 U | DifferentiableOn ℂ f U}

lemma tendsto_iff (hU : IsOpen U) {F : ι → 𝓒 U} {f : 𝓒 U} :
    Tendsto F l (𝓝 f) ↔ TendstoLocallyUniformlyOn F f l U := by
  simp [UniformOnFun.tendsto_iff_tendstoUniformlyOn, _root_.compacts]
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).symm

lemma isClosed_𝓗 (hU : IsOpen U) : IsClosed (𝓗 U) := by
  refine isClosed_iff_clusterPt.2 (λ f hf => ?_)
  refine @TendstoLocallyUniformlyOn.differentiableOn _ _ _ _ _ _ _ id f hf ?_ ?_ hU
  · simp [← tendsto_iff hU, Tendsto]
  · simp [eventually_inf_principal, 𝓗]; exact eventually_of_forall (λ g => id)

lemma ContinuousOn_uderiv (hU : IsOpen U) : ContinuousOn uderiv (𝓗 U) := by
  rintro f -
  refine (tendsto_iff hU).2 ?_
  refine TendstoLocallyUniformlyOn.deriv ?_ eventually_mem_nhdsWithin hU
  apply (tendsto_iff hU).1
  exact nhdsWithin_le_nhds
