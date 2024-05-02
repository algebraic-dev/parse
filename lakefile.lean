import Lake
open Lake DSL

package «Parse» where
  -- add package configuration options here

module_data alloy.c.o : BuildJob FilePath

lean_lib «Parse» where
  precompileModules := true
  nativeFacets := #[Module.oFacet, `alloy.c.o]

@[default_target]
lean_exe Exe where
  root := `Main

require alloy from git "https://github.com/tydeu/lean4-alloy.git"
