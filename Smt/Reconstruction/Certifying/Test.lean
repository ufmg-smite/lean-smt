import Smt.Reconstruction.Certifying.Boolean
import Smt.Reconstruction.Certifying.TimedBoolean

set_option trace.smt.profile true

#check timed

#check congrArg

variable (a b : Prop)
variable (h : a = b)
variable (f : Prop → Prop)
variable (hh : ¬ (a → b))

open Smt.Reconstruction.Certifying

example : True := by
  have h' := by timed flipCongrArg h [f]
  have h'' := by timed notImplies1 hh
  admit
