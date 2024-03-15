import Lake
open Lake DSL

package «rMT4» where
  leanOptions := #[
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "2190b95"

-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.2"

@[default_target] lean_lib RMT4 {
  -- add any library configuration options here
  -- moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
}

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
