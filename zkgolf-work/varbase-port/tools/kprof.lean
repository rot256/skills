import Lean
open Lean

/-- Replay each constant of a module one at a time (in dependency order) into the
environment of its imports, printing the kernel time of each. -/
unsafe def main (args : List String) : IO Unit := do
  let modName := args[0]!.toName
  let threshold : Float := (Float.ofNat ((args[1]?.bind String.toNat?).getD 200)) / 1000.0
  initSearchPath (← findSysroot)
  let mFile ← findOLean modName
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  if h : parts.size = 0 then throw <| IO.userError "failed to read module data" else
  let (mod, _) := parts[0]
  let (_, s) ← importModulesCore mod.imports |>.run
  let mut env ← finalizeImport s mod.imports {} 0 false false (isModule := true)
  let last := parts[parts.size-1].1
  let mut todo : Array ConstantInfo := #[]
  for ci in last.constants do
    if !ci.isUnsafe && !ci.isPartial then todo := todo.push ci
  let mut total : Float := 0
  let mut rounds := 0
  while todo.size > 0 && rounds < 10000 do
    rounds := rounds + 1
    let mut next : Array ConstantInfo := #[]
    let mut progressed := false
    for ci in todo do
      let deps := ci.getUsedConstantsAsSet
      let ready := deps.all fun n => env.contains n || n == ci.name
      if ready then
        let t0 ← IO.monoNanosNow
        let m : Std.HashMap Name ConstantInfo := ({} : Std.HashMap Name ConstantInfo).insert ci.name ci
        env ← env.replay m
        let dt := (Float.ofNat ((← IO.monoNanosNow) - t0)) / 1.0e9
        total := total + dt
        if dt > threshold then IO.println s!"{dt} {ci.name}"
        progressed := true
      else
        next := next.push ci
    todo := next
    if !progressed then
      IO.println s!"stuck with {todo.size} constants: {todo.map (·.name) |>.toList.take 5}"
      break
  IO.println s!"TOTAL {total} s over module {modName}"
