import Lake
open Lake DSL

package «Parse» where
  -- add package configuration options here

lean_lib «Parse» where
  -- add library configuration options here

@[default_target]
lean_exe «http» where
  root := `Main
