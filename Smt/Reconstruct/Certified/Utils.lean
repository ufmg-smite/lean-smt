module

@[expose] public section

@[simp] def isSome : Option α → Prop
| none => False
| some _ => True
