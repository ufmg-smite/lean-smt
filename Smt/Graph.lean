/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Lean.Data.HashMap
import Lean.Data.HashSet

open Std

def Graph (α) (β) [BEq α] [Hashable α] := HashMap α (HashMap α β)

namespace Graph

variable {α} {β} [BEq α] [Hashable α] (g : Graph α β) (v u : α) (e : β)

def empty : Graph α β := HashMap.empty

def vertices : List α := g.fold (fun a v _ => v :: a) []

def neighbors? : Option (List α) :=
  g.find? v >>= fun es => some (es.fold (fun a v _ => v :: a) [])

def neighbors! : List α := match (g.neighbors? v) with
  | some ns => ns
  | none    => panic! "vertex is not in the graph"

def addVertex : Graph α β := g.insert v HashMap.empty

def addEdge : Graph α β := g.insert v ((g.find! v).insert u e)

def weight? : Option β := g.find? v >>= fun es => es.find? u

partial def dfs [Monad m] (f : α → m Unit) : m Unit :=
  StateT.run' (s := HashSet.empty) do
    for v in g.vertices do
      visitVertex v
where
  visitVertex (v : α) : StateT (HashSet α) m Unit := do
    let vs ← get
    if vs.contains v then
      return
    set (vs.insert v)
    for u in g.neighbors! v do
      visitVertex u
    f v

open Format in
protected def format [ToFormat α] [ToFormat β] : Format :=
  bracket "{" (joinSep (g.vertices.map formatVertex) ("," ++ line)) "}"
where
  formatVertex (v : α) : Format :=
    format v ++ " ↦ " ++ bracket "{" (joinSep (g.neighbors! v) ("," ++ line)) "}"

instance [ToFormat α] [ToFormat β] : ToFormat (Graph α β) where
  format g := Graph.format g

end Graph
