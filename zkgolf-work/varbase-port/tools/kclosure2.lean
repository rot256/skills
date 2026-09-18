import Solution.Secp256k1ScalarMul.Main
open Lean

-- For selected modules: which of their constants are in the closure of the exported theorems,
-- and one constant (outside the module) that uses each.
run_meta do
  let env ← getEnv
  let roots : List Name := [``Solution.Secp256k1ScalarMul.soundness, ``Solution.Secp256k1ScalarMul.completeness,
    ``Solution.Secp256k1ScalarMul.mainCost, ``Solution.Secp256k1ScalarMul.isR1CS,
    ``Solution.Secp256k1ScalarMul.computableWitness]
  let mut seen : NameSet := {}
  let mut parent : Std.HashMap Name Name := {}
  let mut stack : List Name := roots
  while !stack.isEmpty do
    let n := stack.head!
    stack := stack.tail!
    if seen.contains n then continue
    seen := seen.insert n
    if let some ci := env.find? n then
      for d in ci.getUsedConstantsAsSet do
        if !seen.contains d then
          stack := d :: stack
          if !parent.contains d then parent := parent.insert d n
  let modOf (n : Name) : Option Name := do
    let idx ← env.getModuleIdxFor? n
    pure env.header.moduleNames[idx.toNat]!
  let interesting : List String := ["MulModTargetW", "MulModVariants", "MulModTheorems", "MulModFold32N",
    "MulModTargetW2", "InterpMul14", "ValidPBytes", "PointValid", "DivOrZeroS32", "MulModFold32T",
    "MulModFoldT", "ValidP", "MulMod", "DivOrZeroF3", "VarLookup", "GLVScalarRelation", "InterpMul",
    "MulModFold32NInv", "MulModVariantsCost", "Lazy_Donor0", "Lazy_Donor1", "Lazy_Donor2", "Lazy_Donor3",
    "Lazy_Donor5", "Lazy_Donor6", "Lazy_Donor7", "GLVBuildTableCostCW", "GLVBuildTable", "CompleteAdd",
    "MulModSub2W32N", "MulModSub2F32", "GroupedEqXV", "GroupedEqV", "EqViaCarries", "BaselinePrelude"]
  let mut perMod : Std.HashMap Name (Array Name) := {}
  let mut total : Std.HashMap Name Nat := {}
  for n in seen do
    if let some m := modOf n then
      perMod := perMod.insert m ((perMod.getD m #[]).push n)
  for m in env.header.moduleNames do
    if (`Solution).isPrefixOf m then
      let cnt := env.header.moduleData[(env.getModuleIdx? m).get!.toNat]!.constNames.size
      total := total.insert m cnt
  for s in interesting do
    let m := `Solution.Secp256k1ScalarMul ++ s.toName
    let touched := perMod.getD m #[]
    logInfo m!"MODULE {s}: touched {touched.size} / {total.getD m 0}"
    -- show up to 12 touched constants with an external user
    let mut shown := 0
    for n in touched do
      if shown ≥ 12 then break
      let p := parent.getD n .anonymous
      if modOf p != some m then
        logInfo m!"   {n}  <- used by {p}"
        shown := shown + 1
