import Solution.Secp256k1ScalarMul.Main
open Lean

-- Emit, for every Solution module, the source ranges of all declarations (ALL) and of the
-- declarations reached by the constant closure of the exported theorems (KEEP).
run_meta do
  let env ← getEnv
  let roots : List Name := [``Solution.Secp256k1ScalarMul.soundness, ``Solution.Secp256k1ScalarMul.completeness,
    ``Solution.Secp256k1ScalarMul.mainCost, ``Solution.Secp256k1ScalarMul.isR1CS,
    ``Solution.Secp256k1ScalarMul.computableWitness]
  let mut seen : NameSet := {}
  let mut stack : List Name := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet do
        if !seen.contains d then stack := d :: stack
  let mut out : Array String := #[]
  for m in env.header.moduleNames, idx in [0:env.header.moduleNames.size] do
    if !(`Solution).isPrefixOf m then continue
    let names := env.header.moduleData[idx]!.constNames
    let mut allR : Std.HashSet (Nat × Nat) := {}
    let mut keepR : Std.HashSet (Nat × Nat) := {}
    let mut noRange : Array Name := #[]
    for c in names do
      -- find a range for c or one of its prefixes, provided that name lives in this module
      let mut cand := c
      let mut found : Option DeclarationRanges := none
      while cand != .anonymous do
        if (env.getModuleIdxFor? cand).map (·.toNat) == some idx then
          if let some r ← findDeclarationRanges? cand then
            found := some r
            break
        cand := cand.getPrefix
      match found with
      | some r =>
        let key := (r.range.pos.line, r.range.endPos.line)
        allR := allR.insert key
        if seen.contains c then keepR := keepR.insert key
      | none =>
        if seen.contains c then noRange := noRange.push c
    for (s, e) in allR.toList do
      out := out.push s!"ALL {m} {s} {e}"
    for (s, e) in keepR.toList do
      out := out.push s!"KEEP {m} {s} {e}"
    for c in noRange do
      out := out.push s!"NORANGE {m} {c}"
    out := out.push s!"SUMMARY {m} all={allR.size} keep={keepR.size} consts={names.size}"
  let h ← IO.FS.Handle.mk "/tmp/claude-0/-home-user-skills/4fcfa319-a98c-5fdf-89f7-44b7afe6a05b/scratchpad/dce_ranges.txt" .write
  for l in out do h.putStrLn l
  logInfo m!"closure {seen.size}; wrote {out.size} lines"
