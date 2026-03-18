/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Moritz Roos
-/
module

public meta import Lean.Meta.Instances
public meta import Batteries.Tactic.Lint.Basic
public meta import Lean.Elab.Command
public meta import Lean.Linter.Basic
public meta import Lean.Server.InfoUtils
public meta import Batteries.Data.List.Basic

public meta section

section environmentLinters

namespace Batteries.Tactic.Lint
open Lean Meta

/--
Lints for instances with arguments that cannot be filled in, like
```
instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
```
-/
@[env_linter] def impossibleInstance : Linter where
  noErrorsFound := "No instance has arguments that are impossible to infer"
  errorsFound := "SOME INSTANCES HAVE ARGUMENTS THAT ARE IMPOSSIBLE TO INFER
These are arguments that are not instance-implicit and do not appear in
another instance-implicit argument or the return type."
  test declName := do
    unless ← isInstance declName do return none
    forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName)) fun args ty => do
    let argTys ← args.mapM inferType
    let impossibleArgs ← args.zipIdx.filterMapM fun (arg, i) => do
      let fv := arg.fvarId!
      if (← fv.getDecl).binderInfo.isInstImplicit then return none
      if ty.containsFVar fv then return none
      if argTys[i+1:].any (·.containsFVar fv) then return none
      return some m!"argument {i+1} {arg} : {← inferType arg}"
    if impossibleArgs.isEmpty then return none
    addMessageContextFull <| .joinSep impossibleArgs.toList ", "

/--
A linter for checking if any declaration whose type is not a class is marked as an instance.
-/
@[env_linter] def nonClassInstance : Linter where
  noErrorsFound := "No instances of non-classes"
  errorsFound := "INSTANCES OF NON-CLASSES"
  test declName := do
    if !(← isInstance declName) then return none
    let info ← getConstInfo declName
    if !(← isClass? info.type).isSome then return "should not be an instance"
    return none

end Batteries.Tactic.Lint
end environmentLinters



section StandardLinters

/-- `getTopLevelDeclsByBody tree` returns the top level names of declarations
    (along with their syntax) which have been logged in the infotree `tree`.

    Specifically, this function collects the contained names and syntax for all nodes
    with a `BodyInfo` value.
    Since we return a `NameMap Syntax`, each name is only returned once.-/
partial def Lean.Elab.InfoTree.getTopLevelDeclsByBody : InfoTree → NameMap Syntax :=
  go none {}
where
  go (ctx? : Option ContextInfo) (acc : NameMap Syntax) : InfoTree → NameMap Syntax
    | context ctx t => go (ctx.mergeIntoOuter? ctx?) acc t
    | node i ts => Id.run do
      if let .ofCustomInfo i := i then
        if i.value.typeName == ``Lean.Elab.Term.BodyInfo then
          if let some decl := ctx?.bind (·.parentDecl?) then
            return acc.insertIfNew decl i.stx -- don't descend into `ts`
      ts.foldl (init := acc) (go ctx?)
    | hole _ => acc

/-- `getInfoTreesDecls` returns the top-level names and syntax declarations made by
    the current command, based on `BodyInfo` nodes in the infotree data.

    This function filters out declarations appearing in the infotree that do not appear
    in the environment.
    Since we return a `NameMap Syntax`, each name is only returned once.
-/
partial def Lean.Elab.getInfoTreesDecls : Command.CommandElabM (NameMap Syntax) := do
  let mut names : NameMap Syntax := {}
  for t in (← getInfoTrees) do
    names := Std.TreeMap.mergeWith (fun _ s _ => s) names t.getTopLevelDeclsByBody
  /- the `getTopLevelDeclsByBody` function picks up some internal names from `examples` that it
     probably shouldn't. We filter these here. -/
  let env ← getEnv
  return names.filter (fun name _ => env.contains name)



open Lean Meta in
/-- Returns the pretty-printed form of a free variable with its type,
    using the appropriate brackets for its `BinderInfo`.
    Example output: `{α : Type}`. -/
def ppFVar (fv : FVarId) : MetaM MessageData := do
  let decl ← fv.getDecl
  let (lBracket, rBracket) : String × String := match decl.binderInfo with
    | .implicit       => ("{", "}")
    | .strictImplicit => ("⦃", "⦄")
    | .instImplicit   => ("[", "]")
    | .default        => ("(", ")")
  return s!"`{lBracket}{decl.userName} : {← inferType (mkFVar fv)}{rBracket}`"


namespace Batteries.Linter
open Lean Elab Command Linter Std Meta

/-- Option for turning the `impossibleInstance` linter on and off. -/
register_option linter.impossibleInstance : Bool := {
  defValue := true
  descr := "Warn when an instance is found that can never be synthesized by typeclass synthesis."
}


/--
Lints for instances with arguments that cannot be filled in, like
```
instance impossible {α β : Type} [Inhabited α] : Nonempty α := ⟨default⟩
```
This is a syntax linter, i.e. it runs on your declarations as you write them.
-/
def syntax.impossibleInstance : Linter where run cmdSyntax := do
  unless Linter.getLinterValue linter.impossibleInstance (← Linter.getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  /- todo use `withSetOptionIn` after `https://github.com/leanprover/lean4/pull/11313` has
     been resolved, to allow disabling this linter with
     `set_option linter.syntax.impossibleInstance false in`. -/
  let errorsFound1 := m!"This instance has at least one argument that cannot be \
    inferred using typeclass synthesis. Specifically\n"
  let errorsFound2 := m!"\nThese are arguments that are not instance-implicit and \
    appear neither in another instance-implicit argument nor the return type, so they cannot \
    be inferred using typeclass synthesis."
  let test (declName : Name) : MetaM (Option MessageData) := do
    unless ← isInstance declName do return none
    forallTelescopeReducing (← inferType (← mkConstWithLevelParams declName)) fun args ty => do
    let argTys ← args.mapM inferType
    let impossibleArgs ← args.zipIdx.filterMapM fun (arg, i) => do
      let fv := arg.fvarId!
      if (← fv.getDecl).binderInfo.isInstImplicit then return none
      if ty.containsFVar fv then return none
      if argTys[i+1:].any (·.containsFVar fv) then return none
      return some (m!"    argument {i+1}: " ++ (← ppFVar fv))
    if impossibleArgs.isEmpty then return none
    return errorsFound1 ++ (Lean.MessageData.joinSep impossibleArgs.toList ", ") ++ errorsFound2
  /- We do the check for each (different) top level instance name we can get from the infotrees.
     Mostly this will only be one name, but for `mutual` blocks this will be more. -/
  let names ← Lean.Elab.getInfoTreesDecls
  for (name, stx) in names do
    /- If the return type is not class valued (but an instance), the `nonClassInstance'`
       linter will already put a message on this declaration, so we skip it here in that case.
       If the declaration is not an instance it is skipped in `test`.  -/
    let constInfo ← (Lean.getConstInfo name)
    if not (← liftTermElabM (isClass? constInfo.type)).isSome then continue
    /- Now the actual linting check: -/
    let some lintmessage ← liftTermElabM (test name) | continue
    /- Use the range that actually corresponds to the `name` not to the whole mutual block: -/
    Linter.logLint linter.impossibleInstance stx lintmessage
  return
initialize addLinter syntax.impossibleInstance

/-- Option for turning the `nonClassInstance` linter on and off. -/
register_option linter.nonClassInstance : Bool := {
  defValue := true
  descr := "Warn when a declaration is found whose type is not a class but is marked as instance. "
}

/--
A linter for checking if any declaration whose type is not a class is marked as an instance.
-/
def syntax.nonClassInstance : Linter where run cmdSyntax := do
  unless Linter.getLinterValue linter.nonClassInstance (← Linter.getLinterOptions) do
    return
  if (← get).messages.hasErrors then
    return
  /- todo use `withSetOptionIn` after `https://github.com/leanprover/lean4/pull/11313` has
     been resolved, to allow disabling this linter with
     `set_option linter.syntax.nonClassInstance false in`.
     Also add an `in` to the test in `BatteriesTest.lintTC.lean`. -/
  let test (declName : Name) : TermElabM (Option MessageData) := do
    if !(← isInstance declName) then return none
    let info ← getConstInfo declName
    if !(← isClass? info.type).isSome then
      return "This declaration should not be an instance as it is not class-valued."
    return none
  /- We do the check for each (different) top level instance name we can get from the infotrees.
     Mostly this will only be one name, but for `mutual` blocks this will be more. -/
  let names ← Lean.Elab.getInfoTreesDecls
  for (name, stx) in names do
    let some lintmessage ← liftTermElabM (test name) | continue
    Linter.logLint linter.nonClassInstance stx lintmessage
  return

initialize addLinter syntax.nonClassInstance

end Batteries.Linter
end StandardLinters
