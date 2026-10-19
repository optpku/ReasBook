/-
Copyright (c) 2023-2024 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Compat
import SubVerso.Examples.Env
import SubVerso.Module
import MD4Lean

open Lean Elab Frontend
open Lean.Elab.Command hiding Context
open SubVerso Examples Module
open SubVerso.Highlighting (Highlighted highlight)

def helpText : String :=
"Extract a module's highlighted representation as JSON

Usage: subverso-extract-mod [OPTS] MOD [OUT]

MOD is the name of a Lean module, and OUT is the destination of the JSON.
If OUT is not specified, the JSON is emitted to standard output.

OPTS may be:
  --suppress-namespace NS
    Suppress the showing of namespace NS in metadata

  --suppress-namespaces FILE
    Suppress the showing of the whitespace-delimited list of namespaces in FILE

Each command in the module is represented as a JSON object with the following
fields:

 * \"kind\": the syntax kind of the command, as emitted by the Lean parser

 * \"range\": the start and end source positions of the command. Line and column
   numbers are one-based, so the start of the file is {\"line\": 1, \"column\": 1},
   and columns are in terms of Unicode code points.

 * \"defines\": the names defined in the command, as an array of strings.

 * \"terms\": terms that occur as literals in documentation comments in the command,
   as an object that maps the occurring strings to their highlighted representations.

 * \"code\": the JSON serialization of SubVerso's highlighted code datatype. The
   specifics of this representation are an implementation detail, and it should
   be deserialized using the same version of SubVerso.
"

partial def allCode (md : String) : StateM (Array String) Unit := do
  MD4Lean.parse md |>.forM fun ⟨blocks⟩ => blocks.forM blockCode

where
  blockCode : MD4Lean.Block → StateM (Array String) Unit
    | .p txts => txts.forM textCode
    | .table xs ys => xs.forM (·.forM textCode) *> ys.forM (·.forM (·.forM textCode))
    | .blockquote bs => bs.forM blockCode
    | .code _ _ _ xs => modify (·.push <| "\n".intercalate xs.toList)
    | .ul _ _ items | .ol _ _ _ items =>
      items.forM fun i => i.contents.forM blockCode
    | .header _ txt => txt.forM textCode
    | .html .. | .hr => pure ()
  textCode : MD4Lean.Text → StateM (Array String) Unit
    | .code s => modify (·.push <| "\n".intercalate s.toList)
    | .a _ _ _ xs | .wikiLink _ xs | .del xs | .u xs | .em xs | .strong xs | .img _ _ xs => xs.forM textCode
    | .normal .. | .latexMathDisplay .. | .latexMath .. | .entity .. | .br .. | .softbr .. | .nullchar => pure ()


open Lean.Parser.Command in
def allTerms (stx : Syntax) : Array String := go stx |>.run #[] |>.snd
where
  go (stx : Syntax) : StateM (Array String) Unit :=
    discard <| stx.replaceM fun s => do
      if s.getKind == ``docComment || s.getKind == ``moduleDoc then
        s[1].getAtomVal |> allCode
        pure none
      else
        pure none

/--
Extends the last token's trailing whitespace to include the rest of the file.
-/
partial def wholeFile (contents : String) (stx : Syntax) : Syntax :=
  wholeFile' stx |>.getD stx
where
  wholeFile' : Syntax → Option Syntax
  | Syntax.atom info val => pure <| Syntax.atom (wholeFileInfo info) val
  | Syntax.ident info rawVal val pre => pure <| Syntax.ident (wholeFileInfo info) rawVal val pre
  | Syntax.node info k args => do
    for i in [0:args.size - 1] do
      let j := args.size - (i + 1)
      if let some s := wholeFile' args[j]! then
        let args := args.set! j s
        return Syntax.node info k args
    none
  | .missing => none

  wholeFileInfo : SourceInfo → SourceInfo
    | .original l l' t _ => .original l l' t contents.rawEndPos
    | i => i

def spansOverlap (x y : Syntax.Range) : Bool :=
  !(x.stop <= y.start || y.stop <= x.start)

def toPersistentArray (xs : Array α) : PersistentArray α :=
  xs.foldl (init := {}) fun acc x => acc.push x

partial def filterInfoTreeBySpan (span : Syntax.Range) : InfoTree → Option InfoTree
  | .context ctx t => do
      let t' ← filterInfoTreeBySpan span t
      pure (.context ctx t')
  | .node info children =>
      let children' := toPersistentArray <| children.toArray.filterMap (filterInfoTreeBySpan span)
      let overlaps := info.range?.any (spansOverlap · span)
      if overlaps || !children'.isEmpty then
        pure (.node info children')
      else
        none
  | .hole _ => none

def rootRange? : InfoTree → Option Syntax.Range
  | .context _ t => rootRange? t
  | .node info _ => info.range?
  | .hole _ => none

def rootOverlapsSpan (span : Syntax.Range) (t : InfoTree) : Bool :=
  -- Fast pre-filter: if a root range is available and disjoint, avoid walking this tree.
  match rootRange? t with
  | some rootSpan => spansOverlap rootSpan span
  | none => true

def infoTreesForCommand (cmdSpan : Syntax.Range) (trees : Array InfoTree) : Array InfoTree :=
  -- Preserve previous semantics while reducing work on obviously unrelated trees.
  trees.filterMap fun t =>
    if rootOverlapsSpan cmdSpan t then
      filterInfoTreeBySpan cmdSpan t
    else
      none

def mergedTreesForCommand (cmdStx : Syntax) (treeFrags : Array InfoTree) : PersistentArray InfoTree :=
  if h : treeFrags.isEmpty then
    {}
  else if h' : treeFrags.size = 1 then
    let merged := treeFrags[0]
    ({ } : PersistentArray InfoTree).push merged
  else
    let mergedRoot : InfoTree :=
      .node (.ofCommandInfo { elaborator := `ReasBook.LiterateExtract.mergedInfoTree, stx := cmdStx }) (toPersistentArray treeFrags)
    ({ } : PersistentArray InfoTree).push mergedRoot

def cmdSpan? (stx : Syntax) : Option Syntax.Range :=
  stx.getRange? (canonicalOnly := true) <|> stx.getRange?

def infoTreeOverlapsAny (spans : Array Syntax.Range) (tree : InfoTree) : Bool :=
  spans.any fun span => filterInfoTreeBySpan span tree |>.isSome

def spanToString (fm : FileMap) (span : Syntax.Range) : String :=
  let s := fm.toPosition span.start
  let e := fm.toPosition span.stop
  s!"{s.line}:{s.column}-{e.line}:{e.column}"

def commandPreview (stx : Syntax) : String :=
  let txt := toString stx
  if txt.length > 120 then
    txt.take 120 ++ "..."
  else
    txt

structure ModuleItem' extends ModuleItem where
  terms : Array (String × Highlighted)

instance : ToJson ModuleItem' where
  toJson v := toJson v.toModuleItem |>.setObjVal! "terms" (mkJson v.terms)
where
  mkJson xs := Json.mkObj <| xs.toList.map fun (txt, tm) => (txt, toJson tm)

unsafe def go (suppressedNamespaces : Array Name) (debugMatching : Bool) (mod : String) (out : IO.FS.Stream) : IO UInt32 := do
  try
    initSearchPath (← findSysroot)
    let modName := mod.toName

    let sp ← Compat.initSrcSearchPath
    let sp : SearchPath := (sp : List System.FilePath) ++ [("." : System.FilePath)]
    let fname ← do
      if let some fname ← sp.findModuleWithExt "lean" modName then
        pure fname
      else
        throw <| IO.userError s!"Failed to load {modName} from {sp}"
    let contents ← IO.FS.readFile fname
    let fm := FileMap.ofString contents
    let ictx := Parser.mkInputContext contents fname.toString
    let (headerStx, parserState, msgs) ← Parser.parseHeader ictx
    let imports := headerToImports headerStx
    enableInitializersExecution
    let env ← Compat.importModules imports {}
    let pctx : Context := {inputCtx := ictx}

    let commandState : Command.State := { env, maxRecDepth := defaultMaxRecDepth, messages := msgs }
    let scopes :=
      let sc := commandState.scopes[0]!
      { sc with opts := (maxHeartbeats.set sc.opts 10000000).setBool `pp.tagAppFns true } ::
        commandState.scopes.tail!
    let commandState := { commandState with scopes }
    let cmdPos := parserState.pos
    let cmdSt ← IO.mkRef {commandState, parserState, cmdPos}

    let res ← Compat.Frontend.processCommands headerStx pctx cmdSt

    let infos := (← cmdSt.get).commandState.infoState.trees
    let msgs := Array.flatten (res.items.map (Compat.messageLogArray ·.messages))
    let res := res.updateLeading contents
    let cmds := res.syntax

    if debugMatching then
      IO.eprintln s!"[literate-extract] module={modName} commands={cmds.size} trees={infos.size}"
      for cmd in cmds do
        match cmdSpan? cmd with
        | some span =>
          let matched := infoTreesForCommand span infos.toArray
          IO.eprintln s!"[literate-extract] command kind={cmd.getKind} span={spanToString fm span} matchedTrees={matched.size} text={commandPreview cmd}"
        | none =>
          IO.eprintln s!"[literate-extract] command kind={cmd.getKind} span=<none> matchedTrees=0 text={commandPreview cmd}"
      let commandSpans := cmds.filterMap cmdSpan?
      let unmatched := infos.toArray.foldl (init := 0) fun acc t =>
        if infoTreeOverlapsAny commandSpans t then acc else acc + 1
      IO.eprintln s!"[literate-extract] unmatchedTrees={unmatched}/{infos.size}"

    let hls ←
      (Frontend.runCommandElabM <| liftTermElabM <|
        SubVerso.Highlighting.highlightFrontendResult res (suppressNamespaces := suppressedNamespaces.toList)) pctx cmdSt

    let env := (← cmdSt.get).commandState.env
    let getTerms := cmds.mapM fun (stx : Syntax) => show FrontendM _ from do
      -- Commands were already elaborated by `processCommands`; avoid a second expensive pass.
      let tms := allTerms stx
      tms.mapM fun tm => show FrontendM _ from do
        let .ok e := Parser.runParserCategory env `term tm
          | pure (tm, Highlighted.empty)
        let hl ← runCommandElabM <| withoutModifyingEnv <| Compat.commandWithoutAsync do
          let infoState ← getInfoState
          let messageLog ← modifyGet fun x => (x.messages, {x with messages := {}})
          try
            setInfoState {}
            withEnableInfoTree true do
              let cmd ← `(#check $(⟨e⟩))
              try
                elabCommand cmd
              catch
                | e =>
                  dbg_trace (← e.toMessageData.toString)
                  pure ()
              let trees := (← get).infoState.trees
              let msgs := (← get).messages
              liftTermElabM <| do
                highlight e msgs.toArray trees
          finally
            setInfoState infoState
            modify fun x => {x with messages := messageLog}
        pure (tm, hl)
    let terms ← getTerms pctx cmdSt
    let items : Array ModuleItem' := hls.zip (cmds |>.zip terms) |>.map fun (hl, stx, terms) => {
      defines := hl.definedNames.toArray,
      kind := stx.getKind,
      range := stx.getRange?.map fun ⟨s, e⟩ => (fm.toPosition s, fm.toPosition e),
      code := hl,
      terms := terms
    }

    out.putStrLn (toString (Json.arr (items.map toJson)))

    return (0 : UInt32)

  catch e =>
    IO.eprintln s!"error finding highlighted code: {toString e}"
    return 2

structure Config where
  suppressedNamespaces : Array Name := #[]
  debugMatching : Bool := false
  mod : String
  outFile : Option String := none

def Config.fromArgs (args : List String) : IO Config := go #[] (debugMatching := false) args
where
  go (nss : Array Name) (debugMatching : Bool := false) : List String → IO Config
    | "--debug-matching" :: more =>
      go nss (debugMatching := true) more
    | "--suppress-namespace" :: more =>
      if let ns :: more := more then
        go (nss.push ns.toName) (debugMatching := debugMatching) more
      else
        throw <| .userError "No namespace given after --suppress-namespace"
    | "--suppress-namespaces" :: more => do
      if let file :: more := more then
        let contents ← IO.FS.readFile file
        let nss' := contents.splitToList (·.isWhitespace) |>.filter (!·.isEmpty) |>.map (·.toName)
        go (nss ++ nss'.toArray) (debugMatching := debugMatching) more
      else
        throw <| .userError "No namespace file given after --suppress-namespaces"
    | [mod] => pure {suppressedNamespaces := nss, debugMatching, mod}
    | [mod, outFile] => pure {suppressedNamespaces := nss, debugMatching, mod, outFile := some outFile}
    | other => throw <| .userError s!"Didn't understand remaining arguments: {other}"

unsafe def main (args : List String) : IO UInt32 := do
  try
    let {suppressedNamespaces, debugMatching, mod, outFile} ← Config.fromArgs args
    match outFile with
    | none =>
      go suppressedNamespaces debugMatching mod (← IO.getStdout)
    | some outFile =>
      if let some p := (outFile : System.FilePath).parent then
        IO.FS.createDirAll p
      IO.FS.withFile outFile .write fun h =>
        go suppressedNamespaces debugMatching mod (.ofHandle h)
  catch e =>
    IO.eprintln e
    IO.println helpText
    pure 1
