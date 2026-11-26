/-
Copyright (c) 2026 The mmp authors. All rights reserved.
Released under the Apache 2.0 licence as described in the file LICENSE.
-/
import Lean4Lean.Replay

/-!
# lean4lean on all the modules of a package in one environment

The command `lean4lean <prefix>` loads a new environment for each module that has the prefix, and it loads these environments in parallel. For a package with more than a thousand modules on top of Mathlib, this takes too much memory and too much time.

This program loads the environment of the external imports one time. These are the imports of the modules of the package that are not modules of the package. Then it gives all the declarations of the package to the replay of lean4lean, which sends each declaration to the lean4lean kernel after the declarations that it uses. Thus each declaration of the package is checked again, and the declarations of Mathlib and of the other dependencies are taken as correct, as with `lean4lean <prefix>`.

The CI copies this file into a clone of lean4lean and builds it as the executable `l4lpackage`.

Usage: `lake env l4lpackage MinimalModel`.
-/

open Lean hiding Environment Exception
open Kernel Lean4Lean.Replay

/-- Read the data of the module `m` at the private level, as `replayFromImports` of lean4lean does. -/
unsafe def readModule (m : Name) : IO (ModuleData × Array CompactedRegion) := do
  let mFile ← findOLean m
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {m} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (mod, _) := parts[parts.size - 1]? | unreachable!
  pure (mod, parts.map (·.2))

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let [pkg] := args | throw <| IO.userError "usage: l4lpackage <module prefix>"
  let root := pkg.toName
  let sp ← searchPathRef.get
  let mut modSet : NameSet := {}
  for path in (← SearchPath.findAllWithExt sp "olean") do
    if let some m := (← searchModuleNameOfFileName path sp) then
      if root.isPrefixOf m then
        modSet := modSet.insert m
  if modSet.isEmpty then
    throw <| IO.userError s!"no oleans for the prefix {root}"
  let mut ext : Array Import := #[]
  let mut extSet : NameSet := {}
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  for m in modSet do
    let (mod, _) ← readModule m
    for i in mod.imports do
      unless modSet.contains i.module || extSet.contains i.module do
        ext := ext.push i
        extSet := extSet.insert i.module
    for name in mod.constNames, ci in mod.constants do
      newConstants := newConstants.insert name ci
  IO.println s!"{modSet.size} modules, {newConstants.size} constants, {ext.size} external imports"
  let start ← IO.monoMsNow
  let (_, s) ← (importModulesCore ext).run
  let env ← match Kernel.Environment.finalizeImport s ext `L4LPackage 0 with
    | .ok env => pure env
    | .error e => throw <| .userError <| ← (e.toMessageData {}).toString
  IO.println s!"the external imports took {(← IO.monoMsNow) - start} ms"
  -- Lean makes some auxiliary declarations, for example the `congr_simp` lemmas, when a module needs them. A module of the package and a module of Mathlib can make the same declaration. Such a declaration is already in the external environment. It is taken as correct if it has the same type and value, and else it is an error.
  let mut shared := 0
  for (name, ci) in newConstants.toList do
    if let some ci' := env.find? name then
      unless ci'.type == ci.type && ci'.value? == ci.value? do
        throw <| IO.userError s!"{name} is in the package and in the external imports, with a different type or value"
      newConstants := newConstants.erase name
      shared := shared + 1
  IO.println s!"{shared} constants of the package are also in the external imports"
  let start ← IO.monoMsNow
  let (n, _) ← replay { newConstants } env
  IO.println s!"the replay took {(← IO.monoMsNow) - start} ms"
  IO.println s!"checked {n} declarations"
  return 0
