import Lake
open Lake DSL

package «Parse» where

lean_lib «Parse» where
  precompileModules := true

require alloy from git "https://github.com/tydeu/lean4-alloy.git"
