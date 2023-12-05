import Lake
open Lake DSL

package «fos» {
  -- add package configuration options here
  moreLinkArgs := #["-L./.lake/packages/LeanInfer/.lake/build/lib", "-lonnxruntime", "-lctranslate2"]
}

require LeanInfer from git "https://github.com/lean-dojo/LeanInfer.git" @ "v0.1.0"

lean_lib «Fos» {
  -- add library configuration options here
}
