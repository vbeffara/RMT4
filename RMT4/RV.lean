import Mathlib

open Prod Function

variable {Ω Ω' α α₁ α₂ : Type*}

@[ext] structure RV (Ω : Type*) := (toFun : Ω → ℝ)

instance : CoeFun (RV Ω) (fun _ => Ω → ℝ) := ⟨RV.toFun⟩
instance : Add (RV Ω) := ⟨(⟨· + ·⟩)⟩

class compatible (α₁ α₂ : Type*) :=
  (α : Type*)
  (proj₁ : α → α₁)
  (proj₂ : α → α₂)

instance : compatible Ω Ω := ⟨Ω, id, id⟩
instance : compatible Ω (Ω × Ω') := ⟨Ω × Ω', fst, id⟩
instance : compatible (Ω × Ω') Ω := ⟨Ω × Ω', id, fst⟩

instance [T : compatible α₁ α₂] : Coe (RV α₁) (RV T.α) := ⟨λ X => ⟨X ∘ T.proj₁⟩⟩
instance [T : compatible α₁ α₂] : Coe (RV α₂) (RV T.α) := ⟨λ X => ⟨X ∘ T.proj₂⟩⟩

instance [T : compatible α₁ α₂] : HAdd (RV α₁) (RV α₂) (RV T.α) := ⟨(· + ·)⟩

def copy (X : RV Ω) : RV (Ω × Ω) := ⟨X ∘ snd⟩

def double₁ (X : RV Ω) := X + copy X
def double₂ (X : RV Ω) := copy X + X

example (X : RV Ω) : double₁ X = double₂ X := by ext ω ; apply add_comm
