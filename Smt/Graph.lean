import Std
import Lean.Message

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

partial def dfs [Monad m] (f : α → m Unit) : m Unit :=
  StateT.run' (s := HashSet.empty) do
    for v in g.vertices do
      visitVertex v
  where
    visitVertex (v : α) : StateT (HashSet α) m Unit := do
      let vs ← get
      if vs.contains v then
        return ()
      set (vs.insert v)
      match g.neighbors v with
      | none    => f v
      | some ns =>
        for u in ns do
          visitVertex u
        f v

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

open Lean in
def toMessageData [ToMessageData α] [ToMessageData β] : MessageData :=
  m!"\{{MessageData.group <| .node <| g.vertices.toArray.map formatVertex}}"
where
  formatVertex (v : α) : MessageData :=
    m!"({v}:{formatNeighbors <| g.neighbors v})"
  formatNeighbors : Option (List α) → MessageData
    | none    => .nil
    | some es => .group <| .node <| es.toArray.map ToMessageData.toMessageData

open Lean in
instance [ToMessageData α] [ToMessageData β] : ToMessageData (Graph α β) where
  toMessageData g := toMessageData g

end Graph

end
