import Lean

open Lean

/- Run via Lake so imports and syntax extensions come from the checkout being measured. -/
unsafe def main (args : List String) : IO Unit := do
  let [file, setupPath, output] := args
    | throw (IO.userError "Expected a source file, its Lake setup, and an output path")
  let stdin ← IO.getStdin
  let names ← IO.ofExcept (Json.parse (← stdin.getLine) >>= fromJson? (α := Array String))
  let input := Parser.mkInputContext (← IO.FS.readFile file) file
  let (header, parserState, messages) ← Parser.parseHeader input
  let setup ← ModuleSetup.load setupPath
  let opts := setup.options.toOptions
  enableInitializersExecution
  setup.dynlibs.forM loadDynlib
  let (env, messages) ← Elab.processHeaderCore (Elab.HeaderSyntax.startPos header)
    (setup.imports?.getD (Elab.HeaderSyntax.imports header))
    (setup.isModule || Elab.HeaderSyntax.isModule header) opts messages input
    (plugins := setup.plugins) (mainModule := setup.name) (package? := setup.package?)
    (arts := setup.importArts) (headerStx? := header)
  let results ← Elab.IO.processCommands input parserState (Elab.Command.mkState env messages opts)
  if results.commandState.messages.hasErrors then
    for msg in results.commandState.messages.toList do
      if msg.severity == .error then IO.eprintln (← msg.toString)
    throw (IO.userError s!"Could not process {file}")
  let mut commands := #[]
  for stx in results.commands do
    let some range := stx.getRange? | continue
    if range.start < range.stop then
      commands := commands.push (range, input.fileMap.utf8RangeToLspRange range)
  let env := results.commandState.env
  let mut rows := #[]
  for name in names do
    let some declRange := declRangeExt.find? (level := .exported) env name.toName <|>
      declRangeExt.find? (level := .server) env name.toName | continue
    let pos : Lsp.Position := ⟨declRange.selectionRange.pos.line - 1,
      declRange.selectionRange.charUtf16⟩
    let some (range, loc) := commands.find? (fun (_, loc) =>
      compare loc.start pos != .gt && compare pos loc.end == .lt) | continue
    rows := rows.push (Json.mkObj [
      ("id", toJson name), ("start", toJson range.start.byteIdx), ("end", toJson range.stop.byteIdx),
      ("line", toJson loc.start.line), ("character", toJson loc.start.character)])
  IO.FS.writeFile output (toJson rows).compress
