import KissingCheck
open KissingCheck

/-- Write the rays built in Lean, one per line, so they can be compared
with the witness files. -/
def dump (path : String) (v : Array (Array Int)) : IO Unit := do
  let lines := v.toList.map fun x => " ".intercalate (x.toList.map toString)
  IO.FS.writeFile path ("\n".intercalate lines ++ "\n")

def main : IO Unit := do
  dump "out/lean_rays_d19.txt" D19.rays
  dump "out/lean_rays_d21.txt" D21.rays
  IO.println s!"d19 {D19.rays.size} (base {D19.base.size}, additions {D19.additions.size}, octads {D19.octads.size})"
  IO.println s!"d21 {D21.rays.size} (base {D21.base.size}, new {D21.newPoints.size}, octads {D21.octads.size})"
