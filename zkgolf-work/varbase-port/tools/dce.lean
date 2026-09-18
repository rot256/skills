import Solution.Secp256k1ScalarMul.Main
open Lean

/-!
Declaration-granularity closure of the exported theorems.

Every constant of a Solution module is attributed to a source declaration range
(its own, or that of the nearest prefix name living in the same module).  When a
constant is reached, the whole declaration is kept and all constants attributed to
that declaration are explored as well, so auxiliary proofs, match auxiliaries and
structure fields never leave dangling references.
-/

run_meta do
  let env ← getEnv
  let roots : List Name := [``Solution.Secp256k1ScalarMul.soundness, ``Solution.Secp256k1ScalarMul.completeness,
    ``Solution.Secp256k1ScalarMul.mainCost, ``Solution.Secp256k1ScalarMul.isR1CS,
    ``Solution.Secp256k1ScalarMul.computableWitness]
  -- attribute constants to ranges
  let mut rangeOf : Std.HashMap Name (Name × Nat × Nat) := {}
  let mut members : Std.HashMap (Name × Nat × Nat) (Array Name) := {}
  let mut allRanges : Std.HashMap Name (Std.HashSet (Nat × Nat)) := {}
  let mut noRange : Array (Name × Name) := #[]
  for m in env.header.moduleNames, idx in [0:env.header.moduleNames.size] do
    if !(`Solution).isPrefixOf m then continue
    for c in env.header.moduleData[idx]!.constNames do
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
        let key := (m, r.range.pos.line, r.range.endPos.line)
        rangeOf := rangeOf.insert c key
        members := members.insert key ((members.getD key #[]).push c)
        allRanges := allRanges.insert m ((allRanges.getD m {}).insert (key.2.1, key.2.2))
      | none => noRange := noRange.push (m, c)
  -- closure
  let mut seen : NameSet := {}
  let mut keptKeys : Std.HashSet (Name × Nat × Nat) := {}
  let mut stack : List Name := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some key := rangeOf[n]? then
      if !keptKeys.contains key then
        keptKeys := keptKeys.insert key
        for c in members.getD key #[] do
          if !seen.contains c then stack := c :: stack
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet do
        if !seen.contains d then stack := d :: stack
  let mut out : Array String := #[]
  for (m, rs) in allRanges.toList do
    let mut keep := 0
    for (s, e) in rs.toList do
      out := out.push s!"ALL {m} {s} {e}"
      let mem := (members.getD (m, s, e) #[]).toList.map (fun n => n.toString) |>.take 40
      out := out.push s!"NAMES {m} {s} {e} {String.intercalate " " mem}"
      if keptKeys.contains (m, s, e) then
        out := out.push s!"KEEP {m} {s} {e}"
        keep := keep + 1
    out := out.push s!"SUMMARY {m} all={rs.size} keep={keep}"
  for m in env.header.moduleNames do
    if (`Solution).isPrefixOf m && !allRanges.contains m then
      out := out.push s!"SUMMARY {m} all=0 keep=0"
  for (m, c) in noRange do
    if seen.contains c then out := out.push s!"NORANGE {m} {c}"
  let h ← IO.FS.Handle.mk "dce_ranges.txt" .write
  for l in out do h.putStrLn l
  logInfo m!"closure {seen.size} constants, {keptKeys.size} declarations; wrote {out.size} lines to dce_ranges.txt"
