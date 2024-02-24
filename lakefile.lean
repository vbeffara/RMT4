import Lake
open Lake DSL

package «rMT4» {
  -- add any package configuration options here
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.2"

@[default_target]
lean_lib RMT4 {
  -- add any library configuration options here
  -- moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
}

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
