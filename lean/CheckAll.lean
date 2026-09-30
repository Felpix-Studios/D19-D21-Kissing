import KissingCheck
open KissingCheck

/-- Run the Boolean checks that the proofs evaluate: `checkall 19` or `checkall 21`. -/
def main (args : List String) : IO Unit := do
  for a in args do
    let (n, v) := if a == "19" then (19, D19.rays) else (21, D21.rays)
    IO.println s!"D{n}: size {v.size}, wellFormed {wellFormed n v}, allPairs {allPairs n v}"
