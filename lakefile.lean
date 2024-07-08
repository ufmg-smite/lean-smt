import Lake

open Lake DSL

require cvc5 from
  git "https://github.com/abdoo8080/lean-cvc5.git" @ "main"

require mathlib from
  git "https://github.com/leanprover-community/mathlib4.git" @ "v4.9.0"

def libcpp : String :=
  if System.Platform.isWindows then "libstdc++-6.dll"
  else if System.Platform.isOSX then "libc++.dylib"
  else "libstdc++.so.6"

package smt where
  precompileModules := true
  moreLeanArgs := #[s!"--load-dynlib={libcpp}"]
  moreGlobalServerArgs := #[s!"--load-dynlib={libcpp}"]

@[default_target]
lean_lib Smt

open Std
open System

partial def readAllFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut files := #[]
  for entry in (← FilePath.readDir dir) do
    if ← entry.path.isDir then
      files := (← readAllFiles entry.path) ++ files
    else
      files := files.push entry.path
  return files

/--
Run tests.

USAGE:
  lake script run test

Run tests.
-/
script test do
  let files ← readAllFiles (FilePath.mk "Test")
  let mut tests : Array FilePath := #[]
  let mut expected : Array FilePath := #[]
  for file in files do
    if file.components.contains "Playground" then
      continue
    if file.components.contains "Reconstruction" then
      continue
    if file.components.contains "Examples" then
      continue
    if file.extension = some "lean" then
      tests := tests.push file
    else if file.extension = some "expected" then
      expected := expected.push file
  let mut tasks := []
  for t in tests do
    let e := t.withExtension "expected"
    if expected.contains e then
      tasks := (← IO.asTask (runTest t e (← readThe Lake.Context))) :: tasks
    else
      IO.println s!"Error: Could not find {e}"
      return 1
  for task in tasks do
    let code ← IO.ofExcept task.get
    if code ≠ 0 then
      return code
  return 0
where
  runTest (test : FilePath) (expected : FilePath) : ScriptM UInt32 := do
    IO.println s!"Start : {test}"
    let imports ← Lean.parseImports' (← IO.FS.readFile test) test.fileName.get!
    let modules ← imports.filterMapM (findModule? ·.module)
    let out ← IO.Process.output {
      cmd := (← getLean).toString
      args := #[s!"--load-dynlib={libcpp}"] ++ modules.map (s!"--load-dynlib={·.dynlibFile}") ++ #[test.toString]
      env := ← getAugmentedEnv
    }
    let expected ← IO.FS.readFile expected
    -- TODO: renable disjunct once cvc5 proofs become are more stable.
    if /- ¬out.stderr.isEmpty ∨ -/ out.stdout ≠ expected then
      IO.println s!"Failed: {test}"
      IO.println s!"Stderr:\n{out.stderr}"
      IO.println s!"Stdout:\n{out.stdout}"
      IO.println s!"Expect:\n{expected}"
      return 3
    IO.println s!"Passed: {test}"
    return 0

/--
Run update.

USAGE:
  lake script run update

Update expected output of tests.
-/
script update do
  let files ← readAllFiles (FilePath.mk "Test")
  let mut tests : Array FilePath := #[]
  for file in files do
    if file.components.contains "Playground" then
      continue
    if file.extension = some "lean" then
      tests := tests.push file
  let mut tasks := []
  for t in tests do
    tasks := (← IO.asTask (updateTest t (← readThe Lake.Context))) :: tasks
  for task in tasks do
    _ ← IO.ofExcept task.get
  return 0
where
  updateTest (test : FilePath) : ScriptM UInt32 := do
    let expected := test.withExtension "expected"
    IO.println s!"Start : {test}"
    let imports ← Lean.parseImports' (← IO.FS.readFile test) test.fileName.get!
    let modules ← imports.filterMapM (findModule? ·.module)
    let out ← IO.Process.output {
      cmd := (← getLean).toString
      args := #[s!"--load-dynlib={libcpp}"] ++ modules.map (s!"--load-dynlib={·.dynlibFile}") ++ #[test.toString]
      env := ← getAugmentedEnv
    }
    IO.FS.writeFile expected out.stdout
    return 0
