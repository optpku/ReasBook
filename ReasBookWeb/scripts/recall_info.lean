/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Reader extraction support; mathematical source authors are credited separately.
-/

open scoped SubVerso.Compat

/-- A token spelling normalized by the parser/highlighter, at its original
source position. Semantic metadata still comes exclusively from elaboration. -/
private structure ReasbookSourceSpelling where
  start : Nat
  canonical : String
  original : String

private def reasbookSourceSpelling (source : String) (stx : Syntax)
    (canonical : String) : Array ReasbookSourceSpelling := Id.run do
  unless stx.getHeadInfo matches .original .. do return #[]
  let (some start, some stop) := (stx.getPos?, stx.getTailPos?) | return #[]
  let original := Compat.String.Pos.extract source start stop
  if original == canonical then return #[]
  return #[⟨(Compat.String.Pos.extract source 0 start).length, canonical, original⟩]

/-- Keep parser positions before updateLeading extends any token to EOF.
For field notation, include the same component spans used by SubVerso. -/
private partial def reasbookSourceSpellings (source : String) : Syntax → Array ReasbookSourceSpelling
  | stx@(.atom _ value) => reasbookSourceSpelling source stx value
  | stx@(.ident _ _ name _) => Id.run do
    let mut result := reasbookSourceSpelling source stx name.toString
    if let [receiver, field] := stx.identComponents (nFields? := some 1) then
      for component in [receiver, field] do
        if component.getId != name then
          result := result ++ reasbookSourceSpellings source component
    return result
  | .node _ _ children => children.foldl (fun acc child => acc ++ reasbookSourceSpellings source child) #[]
  | .missing => #[]

/-- Restore only a parser-proven token spelling at its exact source offset.
Do not rewrite hover types, diagnostics, tactic states, or mathematical source.
This handles escaped identifiers (`«cone»`) and normalized numerals (`!₂[...]`).
-/
private partial def reasbookRestoreSpelling (edits : Array ReasbookSourceSpelling)
    (offset : Nat) (code : Highlighted) : Highlighted × Nat := Id.run do
  match code with
  | .seq children =>
    let mut pos := offset
    let mut result := #[]
    for child in children do
      let (child, next) := reasbookRestoreSpelling edits pos child
      result := result.push child
      pos := next
    return (.seq result, pos)
  | .span info child =>
    let (child, next) := reasbookRestoreSpelling edits offset child
    return (.span info child, next)
  | .tactics info a b child =>
    let (child, next) := reasbookRestoreSpelling edits offset child
    return (.tactics info a b child, next)
  | .token token =>
    let token := match edits.find? (fun e => e.start == offset && e.canonical == token.content) with
      | some e => {token with content := e.original}
      | none => token
    return (.token token, offset + token.content.length)
  | .point .. => return (code, offset)
  | .text text | .unparsed text => return (code, offset + text.length)

/-- Find the actual elaboration context, including namespace and open names. -/
private partial def reasbookCommandContext? : InfoTree → Option CommandContextInfo
  | .context (.commandCtx ctx) _ => some ctx
  | .context _ child => reasbookCommandContext? child
  | .node _ children => children.toArray.findSome? reasbookCommandContext?
  | .hole _ => none

/-- A bare #check can shadow a global with a section variable. Only use the
constant that Lean actually elaborated at this exact identifier range. -/
private partial def reasbookCheckedConstant? (id : Syntax) : InfoTree → Option Name
  | .context _ child => reasbookCheckedConstant? id child
  | .node (.ofTermInfo info) children =>
    if info.stx.getPos? == id.getPos? && info.stx.getTailPos? == id.getTailPos? then
      -- A parser identifier such as `b.dense_span` can elaborate to an
      -- application. Its receiver and projection already have separate native
      -- tokens; do not replace both with the unapplied head constant's type.
      match info.expr.consumeMData with
      | .const name _ => some name
      | _ => none
    else children.toArray.findSome? (reasbookCheckedConstant? id)
  | .node _ children => children.toArray.findSome? (reasbookCheckedConstant? id)
  | .hole _ => none

/-- Replace only the parser-identified identifier span, retaining its text. -/
private partial def reasbookRecallToken (code : Highlighted) (offset start stop : Nat)
    (kind : SubVerso.Highlighting.Token.Kind) : Highlighted × Nat := Id.run do
  let text := code.toString
  if offset == start && offset + text.length == stop then
    return (.token ⟨kind, text⟩, 1)
  if offset ≥ stop || offset + text.length ≤ start then return (code, 0)
  match code with
  | .seq children =>
    let mut pos := offset
    let mut found := 0
    let mut result := #[]
    for child in children do
      let (newChild, count) := reasbookRecallToken child pos start stop kind
      pos := pos + child.toString.length
      found := found + count
      result := result.push newChild
    return (.seq result, found)
  | .span info child =>
    let (child, found) := reasbookRecallToken child offset start stop kind
    return (.span info child, found)
  | _ => return (code, 0)

/-- Recover only an unknown leaf token, not a compound expression or an already
typed identifier. Macro-expanded notation such as `ℕ` can have term info at the
original source range even when SubVerso leaves the surface token unknown. -/
private partial def reasbookCheckToken (code : Highlighted) (offset start stop : Nat)
    (kind : SubVerso.Highlighting.Token.Kind) : Highlighted := Id.run do
  if offset ≥ stop || offset + code.toString.length ≤ start then return code
  match code with
  | .token tok =>
    if tok.kind == .unknown && offset == start && offset + tok.content.length == stop then
      return .token {tok with kind := kind}
    return code
  | .seq children =>
    let mut pos := offset
    let mut result := #[]
    for child in children do
      result := result.push (reasbookCheckToken child pos start stop kind)
      pos := pos + child.toString.length
    return .seq result
  | .span info child => return .span info (reasbookCheckToken child offset start stop kind)
  | _ => return code

/-- Use each term's own elaboration context and instantiated expression. Never
resolve an operator by spelling or substitute an application's head constant. -/
private def reasbookCheckTokens (source : String) (codeStart : Nat)
    (trees : Array InfoTree) (code : Highlighted) : IO Highlighted := do
  let mut code := code
  for tree in trees do
    code ← tree.foldInfoM (init := code) fun ctx node current => do
      let .ofTermInfo term := node | return current
      let (some start, some stop) := (term.stx.getPos?, term.stx.getTailPos?)
        | return current
      let start := (Compat.String.Pos.extract source 0 start).length
      let stop := (Compat.String.Pos.extract source 0 stop).length
      -- Avoid pretty-printing terms that do not correspond to an unknown leaf.
      if reasbookCheckToken current codeStart start stop (.withType "") == current then
        return current
      let kind ← term.runMetaM ctx do
        let expr ← Lean.instantiateMVars term.expr
        let type ← Meta.inferType expr >>= Lean.instantiateMVars >>= Meta.ppExpr
        match expr.consumeMData with
        | .const name _ =>
          let docs ← findDocString? (← getEnv) name
          let signature := s!"{name} : {type}"
          return (%first_succeeding [
            SubVerso.Highlighting.Token.Kind.const name signature docs false none,
            SubVerso.Highlighting.Token.Kind.const name signature docs false])
        | .fvar id => return (%first_succeeding [
            SubVerso.Highlighting.Token.Kind.var id (toString type) none,
            SubVerso.Highlighting.Token.Kind.var id (toString type)])
        | _ => return .withType (toString type)
      return reasbookCheckToken current codeStart start stop kind
  return code

/-- Some Mathlib/SubVerso combinations discard a recalled identifier's info,
or a bare global identifier in a final `#check` command.
Resolve that exact parser span in its recorded Lean environment and attach a
native constant token with Lean's own pretty-printed type. This also works with
SubVerso versions that ignore extra standalone term-info roots. No spelling-
based lookup, scope guessing, source rewriting, or proof re-elaboration occurs.
-/
def reasbookRecallCodes (result : Compat.Frontend.FrontendResult) (source : String)
    (codes : Array Highlighted) : IO (Array Highlighted) := do
  if codes.size != result.items.size + 1 then
    throw <| IO.userError "Recall metadata: highlighted command inventory mismatch"
  let edits := result.syntax.foldl (fun acc stx => acc ++ reasbookSourceSpellings source stx) #[]
  let mut codes := codes
  let mut sourceOffset := 0
  for i in [:codes.size] do
    let (restored, next) := reasbookRestoreSpelling edits sourceOffset codes[i]!
    codes := codes.set! i restored
    sourceOffset := next
  if String.join (codes.toList.map (·.toString)) != source then
    throw <| IO.userError "Native highlight spelling does not match the complete original source"
  let mut offset := codes[0]!.toString.length
  for i in [:result.items.size] do
    let item := result.items[i]!
    let mut code := codes[i + 1]!
    let codeStart := offset
    offset := offset + code.toString.length
    let isRecall := item.commandSyntax.getKind == `Mathlib.Tactic.Recall.recall
    let isCheck := item.commandSyntax.getKind == `Lean.Parser.Command.check
    if isCheck then
      code ← reasbookCheckTokens source codeStart item.info.toArray code
      codes := codes.set! (i + 1) code
    if isRecall || isCheck then
      let some id := item.commandSyntax.getArgs.find? (·.isIdent)
        | if isRecall then throw <| IO.userError "Recall command has no identifier" else continue
      let (some start, some stop) := (id.getPos?, id.getTailPos?)
        | throw <| IO.userError "Recall identifier has no source range"
      let some ctx := item.info.toArray.findSome? reasbookCommandContext?
        | throw <| IO.userError "Recall command has no elaboration context"
      let info : ContextInfo := { toCommandContextInfo := ctx }
      let kind? ← info.runMetaM {} do
        -- A #check may name a section-local variable. Leave its native term
        -- metadata alone rather than pretending it is a global constant.
        let name? ← if isRecall then some <$> realizeGlobalConstNoOverload id else
          pure (item.info.toArray.findSome? (reasbookCheckedConstant? id))
        let some name := name? | return none
        let constant ← getConstInfo name
        let type ← Meta.ppExpr constant.type
        let docs ← findDocString? (← getEnv) name
        let signature := s!"{name} : {type}"
        return some (%first_succeeding [
          SubVerso.Highlighting.Token.Kind.const name signature docs false none,
          SubVerso.Highlighting.Token.Kind.const name signature docs false])
      let some kind := kind? | continue
      let start := (Compat.String.Pos.extract source 0 start).length
      let stop := (Compat.String.Pos.extract source 0 stop).length
      let (patched, count) := reasbookRecallToken code codeStart start stop kind
      if count != 1 || patched.toString != code.toString then
        throw <| IO.userError s!"Statement identifier does not match one exact source token: {id.getId} (offset={codeStart}, start={start}, stop={stop}, matches={count}, textUnchanged={patched.toString == code.toString})"
      codes := codes.set! (i + 1) patched
  return codes
