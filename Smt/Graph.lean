import Std

section

open Std

def Graph (α) (β) [BEq α] [Hashable α] := HashMap α (HashMap α β)

namespace Graph

variable {α} {β} [BEq α] [Hashable α] (g : Graph α β) (v u : α) (e : β)

def empty : Graph α β := HashMap.empty

def vertices : List α := g.fold (λ a v _ => v :: a) []

def neighbors : Option (List α) :=
  (g.find? v).bind λ es => some (es.fold (λ a v _ => v :: a) [])

def addVertex : Graph α β := g.insert v HashMap.empty

def addEdge : Graph α β := g.insert v ((g.find! v).insert u e)

def weight : Option β := (g.find? v).bind λ es => es.find? u

partial def dfs [Monad m] (f : α → m Unit) : m Unit := do
  let mut vs : HashSet α := HashSet.empty
  for v in g.vertices do
    let mut u : m Unit := return
    (u, vs) := StateT.run (dfs' v) vs
    _ ← u
  where
    dfs' (v : α) : StateM (HashSet α) (m Unit) := do
      let vs ← get
      if vs.contains v then
        return
      set (vs.insert v)
      match g.neighbors v with
      | none    => return (f v)
      | some ns =>
        let mut us := []
        for u in ns do
          us := (← dfs' u) :: us
        us := f v :: us
        return us.foldrM (λ u _ => u) ()

def formatGraph [ToFormat α] [ToFormat β] : Format :=
  Format.text "{" ++ Format.joinSep (g.vertices.map format') ","
                  ++ Format.text "}"
  where
    format' (v : α) : Format :=
     Format.text "(" ++ format v ++ Format.text ":"
                     ++ format'' (g.neighbors v) ++ Format.text ")"
    format'' : Option (List α) → Format
      | none    => Format.nil
      | some es => Format.joinSep es ","

instance [ToFormat α] [ToFormat β] : ToFormat (Graph α β) where
  format (g) := Graph.formatGraph g

end Graph

end
