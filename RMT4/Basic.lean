import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.LocallyUniformLimit

open Topology Filter Set Function UniformConvergence

variable {ι : Type*} {l : Filter ι} {U : Set ℂ}

def compacts (U : Set ℂ) : Set (Set ℂ) := {K | K ⊆ U ∧ IsCompact K}

def 𝓗 (U : Set ℂ) := {f : ℂ →ᵤ[compacts U] ℂ | DifferentiableOn ℂ f U}

lemma tendsto_iff (hU : IsOpen U) {F : ι → ℂ →ᵤ[compacts U] ℂ} {f : ℂ →ᵤ[compacts U] ℂ} :
    Tendsto F l (𝓝 f) ↔ TendstoLocallyUniformlyOn F f l U := by
  simp [UniformOnFun.tendsto_iff_tendstoUniformlyOn, _root_.compacts]
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).symm

lemma isClosed_𝓗 (hU : IsOpen U) : IsClosed (𝓗 U) := by
  refine isClosed_iff_clusterPt.2 (λ f hf => ?_)
  refine @TendstoLocallyUniformlyOn.differentiableOn _ _ _ _ _ _ _ id f hf ?_ ?_ hU
  · simp [← tendsto_iff hU, Tendsto]
  · simp [eventually_inf_principal, 𝓗]; exact eventually_of_forall (λ g => id)
