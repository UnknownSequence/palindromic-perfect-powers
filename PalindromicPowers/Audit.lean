import PalindromicPowers.MainTheorem

/-!
# Trust audit

Run, after `lake build`, with

    lake env lean PalindromicPowers/Audit.lean

It prints

1. `#print axioms` for the main theorems: expected `propext`, `Classical.choice`,
   `Quot.sound` only (no `sorryAx`, no project axiom);
2. `#hff_status`: for every HFF block, its Lean declarations (those whose docstring starts with
   `**[HFF n]**`) and their status:
   * `definition` — the block is a definition;
   * `proved` — the block's own proof (including its private auxiliary lemmas) has no `sorry`;
   * `complete` — moreover every block it depends on is `complete`, down to `KnownResults`;
   * `sorry` — the block's own proof still contains a `sorry`.
   It also writes `hff/lean_status.json` (block number ↦ status), read by the HFF map builder;
3. `#used_known_results`: the fields of `KnownResults` that the proof of a declaration uses.
-/

open Lean Elab Command

namespace PalindromicPowers.Audit

/-- A declaration of this project (including private and compiler-generated auxiliary ones). -/
def isProjectName (n : Name) : Bool :=
  n.components.any (· == `PalindromicPowers)

/-- The block number `n` of a docstring starting with `**[HFF n]`. -/
def hffBlock? (doc : String) : Option Nat :=
  match doc.splitOn "**[HFF " with
  | pre :: rest :: _ =>
    if pre.toList.all Char.isWhitespace then
      (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat?
    else none
  | _ => none

/-- Project constants reachable from `root` through types and values, not expanding the
constants for which `stop` holds (other than `root` itself). -/
partial def reach (env : Environment) (root : Name) (stop : Name → Bool) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : List Name := [root]
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if n != root && stop n then continue
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if isProjectName d && !seen.contains d then stack := d :: stack
          else if d == ``sorryAx then seen := seen.insert d
  return seen

/-- The HFF-tagged declarations of the project: `(block, name, isTheorem)`. -/
def hffDecls : CommandElabM (Array (Nat × Name × Bool)) := do
  let env ← getEnv
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    if !isProjectName n then continue
    let some doc ← liftIO (findDocString? env n) | continue
    let some b := hffBlock? doc | continue
    let isThm := match ci with | .thmInfo _ => true | _ => false
    out := out.push (b, n, isThm)
  return out.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.1.toString < b.2.1.toString))

elab "#hff_status" : command => do
  let env ← getEnv
  let decls ← hffDecls
  let tagged : NameSet := decls.foldl (fun s d => if d.2.2 then s.insert d.2.1 else s) {}
  let blocks := (decls.map (·.1)).toList.eraseDups
  let mut lines : Array String := #[]
  let mut json : Array String := #[]
  let mut nSorry : Nat := 0
  for b in blocks do
    let ds := decls.filter (·.1 == b)
    let thms := ds.filter (·.2.2)
    let names := ", ".intercalate (ds.map (fun d => d.2.1.componentsRev.head!.toString)).toList
    let status ←
      if thms.isEmpty then pure "definition"
      else
        let localSorry := thms.any fun d =>
          (reach env d.2.1 (fun n => tagged.contains n)).contains ``sorryAx
        let anySorry := thms.any fun d => (reach env d.2.1 (fun _ => false)).contains ``sorryAx
        pure (if localSorry then "sorry" else if anySorry then "proved" else "complete")
    if status == "sorry" then nSorry := nSorry + 1
    lines := lines.push s!"[HFF {b}] {status}: {names}"
    let st := if status == "complete" then "proved" else status
    json := json.push s!"  \"{b}\": \"{st}\""
  liftIO <| IO.FS.writeFile "hff/lean_status.json" ("{\n" ++ ",\n".intercalate json.toList ++ "\n}\n")
  logInfo m!"{"\n".intercalate lines.toList}\n\nblocks with a `sorry` in their own proof: {nSorry}\n(wrote hff/lean_status.json)"

elab "#used_known_results " id:ident : command => do
  let env ← getEnv
  let s := reach env id.getId (fun _ => false)
  let fields := s.toList.filter fun n => n.getPrefix == ``PalindromicPowers.KnownResults && n != ``PalindromicPowers.KnownResults.mk
  logInfo m!"{(fields.map (·.componentsRev.head!.toString)).mergeSort (· ≤ ·)}"

/-- For each field of `KnownResults`, the HFF blocks whose own proof (including private
auxiliary lemmas, but not other blocks) uses it. -/
elab "#known_results_usage" : command => do
  let env ← getEnv
  let decls ← hffDecls
  let tagged : NameSet := decls.foldl (fun s d => if d.2.2 then s.insert d.2.1 else s) {}
  let mut usage : Std.HashMap String (List Nat) := {}
  for d in decls do
    if !d.2.2 then continue
    let s := reach env d.2.1 (fun n => tagged.contains n)
    for n in s.toList do
      if n.getPrefix == ``PalindromicPowers.KnownResults && n != ``PalindromicPowers.KnownResults.mk then
        let f := n.componentsRev.head!.toString
        usage := usage.insert f ((usage.getD f []) ++ [d.1]).eraseDups
  let lines := usage.toList.map (fun (f, bs) => s!"{f}: blocks {bs.mergeSort (· ≤ ·)}")
  logInfo m!"{"\n".intercalate (lines.mergeSort (· ≤ ·))}"

end PalindromicPowers.Audit

#print axioms PalindromicPowers.main_theorem_unconditional
#print axioms PalindromicPowers.main_theorem_digits

#used_known_results PalindromicPowers.main_theorem

#known_results_usage

#hff_status
