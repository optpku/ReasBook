/-
Authors: Zichen Wang, Wanli Ma
Released under Apache 2.0 license as described in the file LICENSE.
Generated website runtime; adapted from ReasBookSite/LiterateModule.lean.
Mathematical source authors are credited separately.
-/

import VersoBlog
import SubVerso.Module

open Lean Verso Doc Elab ArgParse
open SubVerso.Highlighting

namespace ReasBook.StatementCode

/-- Source selections use Unicode-codepoint offsets, not UTF-8 byte offsets. -/
structure Selection where
  module : String
  source_path : String
  source_sha256 : String
  ranges : Array (Nat × Nat)
deriving FromJson

/-- Slice the original checked tree, retaining metadata only on complete tokens.
In particular, never use `Highlighted.take`, which may retain an entire proof
span after crossing its boundary. Diagnostics and proof states are not previews.
-/
partial def slice (hl : Highlighted) (start stop : Nat) : Highlighted := Id.run do
  if stop ≤ start then return .empty
  match hl with
  | .seq xs =>
    let mut offset := 0
    let mut out := #[]
    for x in xs do
      let size := x.toString.length
      if start < offset + size && offset < stop then
        out := out.push (slice x (start - offset) (min size (stop - offset)))
      offset := offset + size
      if offset ≥ stop then break
    return .seq out
  | .span _ x | .tactics _ _ _ x => return slice x start stop
  | .point .. => return .empty
  | .text s | .unparsed s =>
    return .text (SubVerso.Compat.String.take (SubVerso.Compat.String.drop s start) (stop - start))
  | .token tok =>
    if start == 0 && stop ≥ tok.content.length then return .token tok
    return .text (SubVerso.Compat.String.take (SubVerso.Compat.String.drop tok.content start) (stop - start))

/-- Normalize line endings just as Python's source reader does, preserving tokens. -/
partial def normalize (hl : Highlighted) : Highlighted :=
  match hl with
  | .seq xs => .seq (xs.map normalize)
  | .text s => .text (s.replace "\r\n" "\n")
  | .unparsed s => .unparsed (s.replace "\r\n" "\n")
  | .token tok => .token {tok with content := tok.content.replace "\r\n" "\n"}
  | .span info x => .span info (normalize x)
  | .tactics info a b x => .tactics info a b (normalize x)
  | .point .. => hl

def decode (json : Json) : Except String Highlighted := do
  -- Use SubVerso's own decoder for its compact export format. Older ReasBook
  -- extractors emit a plain array with a native Highlighted value per command.
  match fromJson? (α := SubVerso.Module.Module) json with
  | .ok mod => return .seq (mod.items.map (·.code))
  | .error _ =>
    let items ← json.getArr?
    let code ← items.mapM fun item => item.getObjVal? "code" >>= fromJson? (α := Highlighted)
    return .seq code

-- Keep only the most recent module: whole chapter caches can otherwise retain
-- hundreds of complete proof trees while rendering statement-only excerpts.
initialize lastModule : IO.Ref (Option (String × Highlighted)) ← IO.mkRef none

def load (selection : Selection) : IO Highlighted := do
  let moduleParts := selection.module.splitOn "."
  if moduleParts.any (fun s => s.isEmpty || s.contains '/' || s.contains '\\') then
    throw <| IO.userError "Invalid statement module name"
  let key := selection.module ++ ":" ++ selection.source_sha256
  if let some (old, code) ← lastModule.get then
    if old == key then return code
  let mapText ← IO.FS.readFile ".literate-sources.json"
  let mapping ← IO.ofExcept (Json.parse mapText)
  let source ← IO.ofExcept (mapping.getObjValAs? String selection.module)
  if source != selection.source_path || (source.splitOn "/").any (fun s => s == ".." || s.isEmpty)
      || source.contains '\\' then
    throw <| IO.userError "Statement source does not match generated module inventory"
  let sourceText ← IO.FS.readFile (System.FilePath.mk "../ReasBook" / source)
  let jsonPath := System.FilePath.mk "../ReasBook/.lake/build/literate" /
    ("/".intercalate moduleParts ++ ".json")
  if !(← jsonPath.pathExists) then
    throw <| IO.userError s!"Missing statement semantic data: {jsonPath}. Build .literate-modules.json with verso-literate first."
  let json ← IO.FS.readFile jsonPath
  let code ← IO.ofExcept (Json.parse json >>= decode)
  let code := normalize code
  if code.toString != sourceText.replace "\r\n" "\n" then
    throw <| IO.userError s!"Stale statement semantic data: {selection.module}"
  lastModule.set (some (key, code))
  return code

def fromExport (text : String) : Highlighted :=
  match Json.parse text >>= ExportCode.fromJson? >>= ExportCode.toHighlighted with
  | .ok code => code
  | .error err => panic! s!"Invalid checked statement export: {err}"

def codeOptions (name : Name) : Verso.Genre.Blog.CodeOpts :=
  {contextName := name, showProofStates := false}

structure Args where
  selection : String

instance : FromArgs Args DocElabM where
  fromArgs := Args.mk <$> .positional `selection .string

end ReasBook.StatementCode

open ReasBook.StatementCode in
@[code_block]
def reasbookStatement : CodeBlockExpanderOf Args
  | args, text => do
    let selection ← IO.ofExcept (Json.parse args.selection >>= fromJson? (α := Selection))
    let code ← load selection
    let sourceLength := code.toString.length
    let mut parts : Array Highlighted := #[]
    for (start, stop) in selection.ranges do
      if start ≥ stop || stop > sourceLength then
        throwError "Invalid statement source range: {start}–{stop}"
      if !parts.isEmpty then parts := parts.push (.text "\n")
      parts := parts.push (slice code start stop)
    let excerpt := Highlighted.seq parts
    if excerpt.toString != SubVerso.Compat.String.trim text.getString then
      throwError "Statement text does not match its checked source ranges: {selection.module}"
    let exported := excerpt.exportCode.toJson.compress
    let context := selection.module.toName
    ``(Verso.Doc.Block.other
        (Verso.Genre.Blog.BlockExt.highlightedCode
          (ReasBook.StatementCode.codeOptions $(quote context))
          (ReasBook.StatementCode.fromExport $(quote exported))) #[])
