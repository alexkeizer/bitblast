import Lake
open Lake DSL

package «bitblast» where
  -- add package configuration options here

lean_lib «Bitblast» where
  -- add library configuration options here

@[default_target]
lean_exe «bitblast» where
  root := `Main
