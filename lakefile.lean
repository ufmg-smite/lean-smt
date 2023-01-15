import Lake

open Lake DSL

package smt where
  precompileModules := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib Smt

lean_lib Certifying {
  srcDir := "./Smt/Reconstruction/"
}

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
  let lean ← getLean
  let files ← readAllFiles (FilePath.mk "Test")
  let mut tests : Array FilePath := #[]
  let mut expected : Array FilePath := #[]
  for file in files do
    if file.components.contains "Playground" then
      continue
    if file.extension = some "lean" then
      tests := tests.push file
    else if file.extension = some "expected" then
      expected := expected.push file
  let mut tasks := []
  for t in tests do
    let e := t.withExtension "expected"
    if (expected.contains e) then
      tasks := (← IO.asTask (runTest lean t e (← readThe Lake.Context))) :: tasks
    else
      IO.println s!"Error: Could not find {e}"
      return 1
  for task in tasks do
    let code ← IO.ofExcept task.get
    if code ≠ 0 then
      return code
  return 0
where
  runTest (lean : FilePath) (test : FilePath) (expected : FilePath) : ScriptM UInt32 := do
    IO.println s!"Start : {test}"
    let leanPath ← getAugmentedLeanPath
    -- Note: this only works on Unix since it needs the shared library `libSmt`
    -- to also loads its transitive dependencies.
    let dynlib := match (← findModule? `Smt) with
                  | some m => m.dynlibFile
                  | none   => panic "could not find module"
    let out ← IO.Process.output {
      cmd := lean.toString
      args := #[s!"--load-dynlib={dynlib}", test.toString],
      env := #[("LEAN_PATH", leanPath.toString)]
    }
    let expected ← IO.FS.readFile expected
    -- TODO: renable disjunct once cvc5 proofs become are more stable.
    if /- ¬out.stderr.isEmpty ∨ -/ out.stdout ≠ expected then
      IO.println s!"Failed: {test}"
      IO.println s!"Stderr:\n{out.stderr}"
      IO.println s!"Stdout:\n{out.stdout}"
      IO.println s!"Expect:\n{expected}"
      return 2
    IO.println s!"Passed: {test}"
    return 0

/--
Run update.

USAGE:
  lake script run update

Update expected output of tests.
-/
script update do
  let lean ← getLean
  let files ← readAllFiles (FilePath.mk "Test")
  let mut tests : Array FilePath := #[]
  for file in files do
    if file.components.contains "Playground" then
      continue
    if file.extension = some "lean" then
      tests := tests.push file
  let mut tasks := []
  for t in tests do
    tasks := (← IO.asTask (runTest lean t (← readThe Lake.Context))) :: tasks
  for task in tasks do
    _ ← IO.ofExcept task.get
  return 0
where
  runTest (lean : FilePath) (test : FilePath) : ScriptM UInt32 := do
    let expected := test.withExtension "expected"
    IO.println s!"Start : {test}"
    let leanPath ← getAugmentedLeanPath
    let dynlib := match (← findModule? `Smt) with
                  | some m => m.dynlibFile
                  | none   => panic "could not find module"
    let out ← IO.Process.output {
      cmd := lean.toString
      args := #[s!"--load-dynlib={dynlib}", test.toString],
      env := #[("LEAN_PATH", leanPath.toString)]
    }
    IO.FS.writeFile expected out.stdout
    return 0
