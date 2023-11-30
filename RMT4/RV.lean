import Mathlib

def Copy (Ω : Type*) := Ω -- to prevent typeclass from mixing up components?

structure RV (Ω : Type*) := (toFun : Ω → ℝ)

variable {Ω Ω' : Type*}

instance : CoeFun (RV Ω) (fun _ => Ω → ℝ) := ⟨RV.toFun⟩

instance : Coe (RV Ω) (RV (Ω × Ω')) := ⟨λ X => ⟨λ ω => X ω.1⟩⟩

def add (X Y : RV Ω) : RV Ω := ⟨λ ω => X ω + Y ω⟩

def copy (X : RV Ω) : RV (Ω × Copy Ω) := ⟨λ ω => X ω.2⟩

def double (X : RV Ω) := add (copy X) X

def double' (X : RV Ω) := @add (Ω × Copy Ω) X (copy X) -- wrong
