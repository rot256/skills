import Solution.Secp256k1ScalarMul.Main
open Lean

/- Print why a constant is in the declaration-granularity closure: the chain of
constants/declarations from an exported theorem down to it.  Names are read from
`WHY_NAMES` (comma separated). -/
run_meta do
  let env ← getEnv
  let targets := ((← IO.getEnv "WHY_NAMES").getD "").splitOn "," |>.map String.toName
  let roots : List Name := [``Solution.Secp256k1ScalarMul.soundness, ``Solution.Secp256k1ScalarMul.completeness,
    ``Solution.Secp256k1ScalarMul.mainCost, ``Solution.Secp256k1ScalarMul.isR1CS,
    ``Solution.Secp256k1ScalarMul.computableWitness]
  let mut rangeOf : Std.HashMap Name (Name × Nat × Nat) := {}
  let mut members : Std.HashMap (Name × Nat × Nat) (Array Name) := {}
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
      if let some r := found then
        let key := (m, r.range.pos.line, r.range.endPos.line)
        rangeOf := rangeOf.insert c key
        members := members.insert key ((members.getD key #[]).push c)
  let mut seen : NameSet := {}
  let mut parent : Std.HashMap Name (Name × String) := {}
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
          if !seen.contains c then
            stack := c :: stack
            if !parent.contains c then parent := parent.insert c (n, "same-decl")
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet do
        if !seen.contains d then
          stack := d :: stack
          if !parent.contains d then parent := parent.insert d (n, "uses")
  for t in targets do
    if !seen.contains t then
      logInfo m!"{t}: NOT in closure"
      continue
    let mut cur := t
    let mut chain : Array String := #[]
    let mut steps := 0
    while steps < 60 do
      steps := steps + 1
      match parent[cur]? with
      | some (p, how) =>
        chain := chain.push s!"  <-{how}- {p}"
        cur := p
      | none => break
    logInfo m!"{t}\n{String.intercalate "\n" chain.toList}"
