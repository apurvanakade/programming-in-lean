import Lake
open Lake DSL

package «programming-in-lean» {
  -- add package configuration options here
}

lean_lib ProgrammingInLean {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe «programming-in-lean» {
  root := `Main
}
