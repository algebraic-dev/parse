import Lake
open Lake DSL

package «Parse» where
  -- add package configuration options here

module_data alloy.c.o.export : BuildJob FilePath
module_data alloy.c.o.noexport : BuildJob FilePath

lean_lib «Parse» where
  precompileModules := true
  nativeFacets := fun shouldExport =>
    if shouldExport then
      #[Module.oExportFacet, `alloy.c.o.export]
    else
      #[Module.oNoExportFacet, `alloy.c.o.noexport]

require alloy from git "https://github.com/tydeu/lean4-alloy.git"
