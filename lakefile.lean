import Lake
open Lake DSL

package jsp572four where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "f61f3ed7633ff99ecaae4a086395b501652a76ee"

@[default_target]
lean_lib JSP572Four
