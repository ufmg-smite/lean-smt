import Lean

instance [DecidableEq α] : DecidableEq (OptionT Id α) :=
  instDecidableEqOption

instance [ToString α] : ToString (OptionT Id α) :=
  instToStringOption

instance [Lean.Eval α] [ToString α] : Lean.Eval (OptionT Id α) :=
  Lean.instEval

instance [Lean.MetaEval α] [ToString α] : Lean.MetaEval (OptionT Id α) :=
  Lean.instMetaEval


namespace proof

/- dep is the sort for terms that have polymorphic sorts such as
   equality and ITE. These sorts are handled in a special way in the
   type checker.

   Additionally, we have atomic sorts, parameterized by a Nat, arrow
   for functional sorts, and bitvector sorts parameterized by their
   length -/
inductive sort : Type where
| dep : sort
-- id
| atom : Nat → sort
-- domain sort, range sort
| arrow : sort → sort → sort
-- size
| bv : Nat → sort
-- index sort, element sort
| array : sort → sort → sort
-- placeholder if not using Option
| undef : sort
deriving DecidableEq

namespace sort

/- Each predefined function is also parameterized by a
   Nat, an application of terms is parametrized
   by all the Nats involved in the application,
   thus giving unique sets of Nats to unique terms -/
def botNum     : Nat := 0
def notNum     : Nat := botNum + 1
def orNum      : Nat := notNum + 1
def andNum     : Nat := orNum + 1
def impliesNum : Nat := andNum + 1
def xorNum     : Nat := impliesNum + 1
def bIteNum   : Nat := xorNum + 1
def fIteNum   : Nat := bIteNum + 1
def eqNum      : Nat := fIteNum + 1
def distinctNum : Nat := eqNum + 1
def forallNum  : Nat := eqNum + 1
def bvBitOfNum : Nat := forallNum + 1
def bvBbTNum : Nat := bvBitOfNum + 1
def bvNotNum : Nat := bvBbTNum + 1
def bvAndNum : Nat := bvNotNum + 1
def bvOrNum : Nat := bvAndNum + 1
def bvXorNum : Nat := bvOrNum + 1
def bvNandNum : Nat := bvXorNum + 1
def bvNorNum : Nat := bvNandNum + 1
def bvXnorNum : Nat := bvNorNum + 1
def bvCompNum : Nat := bvXnorNum + 1
def bvUltNum : Nat := bvCompNum + 1
def bvUleNum : Nat := bvUltNum + 1
def bvUgtNum : Nat := bvUleNum + 1
def bvUgeNum : Nat := bvUgtNum + 1
def bvSltNum : Nat := bvUgeNum + 1
def bvSleNum : Nat := bvSltNum + 1
def bvSgtNum : Nat := bvSleNum + 1
def bvSgeNum : Nat := bvSgtNum + 1
def bvAddNum : Nat := bvSgeNum + 1
def bvNegNum : Nat := bvAddNum + 1
def bvSubNum : Nat := bvNegNum + 1
def bvMulNum : Nat := bvSubNum + 1
def bvUDivNum : Nat := bvMulNum + 1
def bvURemNum : Nat := bvUDivNum + 1
def bvShlNum : Nat := bvURemNum + 1
def bvLShrNum : Nat := bvShlNum + 1
def bvAShrNum : Nat := bvLShrNum + 1
def bvExtractNum : Nat := bvAShrNum + 1
def bvConcatNum : Nat := bvExtractNum + 1
def bvZeroExtNum : Nat := bvConcatNum + 1
def bvSignExtNum : Nat := bvZeroExtNum + 1
def bvRepeatNum : Nat := bvSignExtNum + 1

def plusNum : Nat := bvRepeatNum + 1
def minusNum : Nat := plusNum + 1
def multNum : Nat := minusNum + 1
def gtNum : Nat := multNum + 1
def gteNum : Nat := gtNum + 1
def ltNum : Nat := gteNum + 1
def lteNum : Nat := ltNum + 1

def selectNum : Nat := ltNum + 1
def storeNum : Nat := selectNum + 1

def emptyStrNum : Nat := storeNum + 1
def strPlusNum : Nat := emptyStrNum + 1
def strLengthNum : Nat := strPlusNum + 1
def inReNum : Nat := strLengthNum + 1
def REInterNum : Nat := inReNum + 1

-- sorts
def boolNum : Nat := 1
def intNum : Nat := boolNum + 1
def strNum : Nat := intNum + 1
def RENum : Nat := strNum + 1


def sortToString : sort → String
| undef => "undef"
| dep => "blah"
| atom n => toString n
| bv n => "bv " ++ toString n
| arrow s1 s2 => "(" ++ sortToString s1 ++ " → " ++ sortToString s2 ++ ")"
| array i e => "(array " ++ sortToString i ++ " " ++ sortToString e ++ ")"

instance : ToString sort where toString := sortToString

/- arrowN curries multi-argument types
   f : X₁ × X₂ × ... into
   f : X₁ → X₂ → ... -/
def arrowN : List sort → sort
| [s] => s
| s₁::s₂::t => arrow s₁ (arrowN (s₂::t))
| _ => undef

end sort

inductive value : Type where
| bool : Bool → value
| bitvec : List Bool → value
| char : Nat → value
| integer : Int → value
deriving DecidableEq

def bvToString : List Bool → String
| [] => ""
| h :: t => (if h then "1" else "0") ++ bvToString t

def valueToString : value → String
| value.bool true => "⊤"
| value.bool false => "⊥"
| value.bitvec l => bvToString l
| value.char c => toString $ Char.ofNat c
| value.integer i => toString i

instance: ToString value where toString := valueToString


/- terms are values (interpreted constants),
   constants of a sort, applications,
   or quantified formulas
   Quantified variables are also
   parameterized by a Nat -/

inductive term : Type where
| undef : term
| val : value → sort → term
| const : Nat → sort → term
| app : term → term → term
| choice : Nat → term → term
| qforall : Nat → term → term
| lambda : Nat → term → term

deriving DecidableEq

namespace term

infixl:20  " • " => app

open sort
open value

-- Sort definitions
@[match_pattern] def boolSort := atom boolNum
@[match_pattern] def intSort := atom intNum
@[match_pattern] def strSort := atom strNum
@[match_pattern] def RESort := atom RENum

-- Interpreted constants
@[match_pattern] def botConst := const botNum boolSort
@[match_pattern] def notConst := const notNum (arrow boolSort boolSort)
@[match_pattern] def orConst :=
  const orNum (arrow boolSort (arrow boolSort boolSort))
@[match_pattern] def andConst :=
  const andNum (arrow boolSort (arrow boolSort boolSort))
@[match_pattern] def impliesConst :=
  const impliesNum (arrow boolSort (arrow boolSort boolSort))
@[match_pattern] def xorConst :=
  const xorNum (arrow boolSort (arrow boolSort boolSort))
@[match_pattern] def bIteConst :=
  const bIteNum (arrow boolSort (arrow boolSort (arrow boolSort boolSort)))

@[match_pattern] def eqConst := const eqNum dep
@[match_pattern] def distinctConst := const distinctNum dep
@[match_pattern] def fIteConst := const fIteNum dep


@[match_pattern] def plusConst :=
  const plusNum (arrow intSort (arrow intSort intSort))
@[match_pattern] def minusConst :=
  const minusNum (arrow intSort (arrow intSort intSort))
@[match_pattern] def multConst :=
  const multNum (arrow intSort (arrow intSort intSort))
@[match_pattern] def gtConst :=
  const gtNum (arrow intSort (arrow intSort boolSort))
@[match_pattern] def gteConst :=
  const gteNum (arrow intSort (arrow intSort boolSort))
@[match_pattern] def ltConst :=
  const ltNum (arrow intSort (arrow intSort boolSort))
@[match_pattern] def lteConst :=
  const lteNum (arrow intSort (arrow intSort boolSort))

@[match_pattern] def selectConst := const selectNum dep
@[match_pattern] def storeConst := const storeNum dep

@[match_pattern] def bitOfConst :=
  const bvBitOfNum dep
@[match_pattern] def bbTConst :=
  const bvBbTNum dep
@[match_pattern] def bvNotConst := const bvNotNum dep
@[match_pattern] def bvAndConst :=
  const bvAndNum dep
@[match_pattern] def bvOrConst :=
  const bvOrNum dep
@[match_pattern] def bvXorConst :=
  const bvXorNum dep
@[match_pattern] def bvNandConst :=
  const bvNandNum dep
@[match_pattern] def bvNorConst :=
  const bvNorNum dep
@[match_pattern] def bvXnorConst :=
  const bvXnorNum dep
@[match_pattern] def bvCompConst :=
  const bvCompNum dep
@[match_pattern] def bvUltConst :=
  const bvUltNum dep
@[match_pattern] def bvUleConst :=
  const bvUleNum dep
@[match_pattern] def bvUgtConst :=
  const bvUgtNum dep
@[match_pattern] def bvUgeConst :=
  const bvUgeNum dep
@[match_pattern] def bvSltConst :=
  const bvSltNum dep
@[match_pattern] def bvSleConst :=
  const bvSleNum dep
@[match_pattern] def bvSgtConst :=
  const bvSgtNum dep
@[match_pattern] def bvSgeConst :=
  const bvSgeNum dep
@[match_pattern] def bvAddConst :=
  const bvAddNum dep
@[match_pattern] def bvNegConst :=
  const bvNegNum dep
@[match_pattern] def bvSubConst :=
  const bvSubNum dep
@[match_pattern] def bvMulConst :=
  const bvMulNum dep
@[match_pattern] def bvShlConst :=
  const bvShlNum dep
@[match_pattern] def bvLShrConst :=
  const bvLShrNum dep
@[match_pattern] def bvAShrConst :=
  const bvAShrNum dep
@[match_pattern] def bvExtractConst :=
  const bvExtractNum dep
@[match_pattern] def bvConcatConst :=
  const bvConcatNum dep
@[match_pattern] def bvZeroExtConst :=
  const bvZeroExtNum dep
@[match_pattern] def bvSignExtConst :=
  const bvSignExtNum dep
@[match_pattern] def bvRepeatConst :=
  const bvRepeatNum dep

/-
@[match_pattern] def bvNotConst (n : Nat) := const bvNotNum (arrow (bv n) (bv n))
@[match_pattern] def bvAndConst (n : Nat) :=
  const bvAndNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvOrConst (n : Nat) :=
  const bvOrNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvXorConst (n : Nat) :=
  const bvXorNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvNandConst (n : Nat) :=
  const bvNandNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvNorConst (n : Nat) :=
  const bvNorNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvXnorConst (n : Nat) :=
  const bvXnorNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvCompConst (n : Nat) :=
  const bvCompNum (arrow (bv n) (arrow (bv n) (bv 1)))
@[match_pattern] def bvUltConst (n : Nat) :=
  const bvUltNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvUleConst (n : Nat) :=
  const bvUleNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvUgtConst (n : Nat) :=
  const bvUgtNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvUgeConst (n : Nat) :=
  const bvUgeNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvSltConst (n : Nat) :=
  const bvSltNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvSleConst (n : Nat) :=
  const bvSleNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvSgtConst (n : Nat) :=
  const bvSgtNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvSgeConst (n : Nat) :=
  const bvSgeNum (arrow (bv n) (arrow (bv n) boolSort))
@[match_pattern] def bvAddConst (n : Nat) :=
  const bvAddNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvNegConst (n : Nat) :=
  const bvNegNum (arrow (bv n) (bv n))
@[match_pattern] def bvSubConst (n : Nat) :=
  const bvSubNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvMulConst (n : Nat) :=
  const bvMulNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvShlConst (n : Nat) :=
  const bvShlNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvLShrConst (n : Nat) :=
  const bvLShrNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvAShrConst (n : Nat) :=
  const bvAShrNum (arrow (bv n) (arrow (bv n) (bv n)))
@[match_pattern] def bvExtractConst (n i j : Nat) :=
  const bvExtractNum (arrow (bv n) (arrow intSort (arrow intSort (bv (i - j + 1)))))
@[match_pattern] def bvConcatConst (m n : Nat) :=
  const bvConcatNum (arrow (bv m) (arrow (bv n) (bv (m+n))))
@[match_pattern] def bvZeroExtConst (n i : Nat) :=
  const bvZeroExtNum (arrow (bv n) (arrow intSort (bv (n + i))))
@[match_pattern] def bvSignExtConst (n i : Nat) :=
  const bvSignExtNum (arrow (bv n) (arrow intSort (bv (n + i))))
@[match_pattern] def bvRepeatConst (n i : Nat) :=
  const bvRepeatNum (arrow intSort (arrow (bv n) (bv (n * i))))
-/

@[match_pattern] def emptyStrConst := const emptyStrNum strSort
@[match_pattern] def strPlusConst := const strPlusNum (arrow strSort (arrow strSort strSort))
@[match_pattern] def strLengthConst := const strLengthNum (arrow strSort intSort)
@[match_pattern] def inREConst := const strLengthNum (arrow RESort (arrow strSort boolSort))
@[match_pattern] def REInterConst := const REInterNum (arrow RESort (arrow RESort RESort))

instance : Inhabited term where
  default := botConst

deriving instance Inhabited for term

-- macros for creating terms with interpreted constants
@[match_pattern] def bot : term := val (bool false) boolSort
@[match_pattern] def top : term := val (bool true) boolSort
@[match_pattern] def not : term → term := λ t => notConst • t
@[match_pattern] def or : term → term → term := λ t₁ t₂ => orConst • t₁ • t₂
@[match_pattern] def and : term → term → term := λ t₁ t₂ => andConst • t₁ • t₂
@[match_pattern] def implies : term → term → term :=
  λ t₁ t₂ => impliesConst • t₁ • t₂
@[match_pattern] def iff : term → term → term :=
  λ t₁ t₂ => andConst • (impliesConst • t₁ • t₂) • (impliesConst • t₂ • t₁)
@[match_pattern] def xor : term → term → term := λ t₁ t₂ => xorConst • t₁ • t₂
@[match_pattern] def nand : term → term → term := λ t₁ t₂ => notConst • (andConst • t₁ • t₂)
@[match_pattern] def nor : term → term → term := λ t₁ t₂ => notConst • (orConst • t₁ • t₂)
@[match_pattern] def bIte : term → term → term → term :=
  λ c t₁ t₂ => bIteConst • c • t₁ • t₂

@[match_pattern] def plus : term → term → term := λ t₁ t₂ => plusConst • t₁ • t₂
@[match_pattern] def minus : term → term → term :=
  λ t₁ t₂ => minusConst • t₁ • t₂
@[match_pattern] def mult : term → term → term := λ t₁ t₂ => multConst • t₁ • t₂
@[match_pattern] def gt : term → term → term := λ t₁ t₂ => gtConst • t₁ • t₂
@[match_pattern] def gte : term → term → term := λ t₁ t₂ => gteConst • t₁ • t₂
@[match_pattern] def lt : term → term → term := λ t₁ t₂ => ltConst • t₁ • t₂
@[match_pattern] def lte : term → term → term := λ t₁ t₂ => lteConst • t₁ • t₂

@[match_pattern] def fIte : term → term → term → term :=
  λ t₁ t₂ t₃ => fIteConst • t₁ • t₂ • t₃
@[match_pattern] def eq : term → term → term := λ t₁ t₂ => eqConst • t₁ • t₂
@[match_pattern] def distinct : term → term → term :=
  λ t₁ t₂ => distinctConst • t₁ • t₂

@[match_pattern] def select : term → term → term :=
  λ t₁ t₂ => selectConst • t₁ • t₂

@[match_pattern] def store : term → term → term → term :=
  λ t₁ t₂ t₃ => storeConst • t₁ • t₂ • t₃

@[match_pattern] def bitOf : term → term → term :=
  λ t₁ t₂ => bitOfConst • t₁ • t₂
@[match_pattern] def bbT : term := bbTConst
@[match_pattern] def bvNot : term → term :=
  λ t => bvNotConst • t
@[match_pattern] def bvAnd : term → term → term :=
  λ t₁ t₂ => bvAndConst • t₁ • t₂
@[match_pattern] def bvOr : term → term → term :=
  λ t₁ t₂ => bvOrConst • t₁ • t₂
@[match_pattern] def bvXor : term → term → term :=
  λ t₁ t₂ => bvXorConst • t₁ • t₂
@[match_pattern] def bvNand : term → term → term :=
  λ t₁ t₂ => bvNandConst • t₁ • t₂
@[match_pattern] def bvNor : term → term → term :=
  λ t₁ t₂ => bvNorConst • t₁ • t₂
@[match_pattern] def bvXnor : term → term → term :=
  λ t₁ t₂ => bvXnorConst • t₁ • t₂
@[match_pattern] def bvComp : term → term → term :=
  λ t₁ t₂ => bvCompConst • t₁ • t₂
@[match_pattern] def bvUlt : term → term → term :=
  λ t₁ t₂ => bvUltConst • t₁ • t₂
@[match_pattern] def bvUle : term → term → term :=
  λ t₁ t₂ => bvUleConst • t₁ • t₂
@[match_pattern] def bvUgt : term → term → term :=
  λ t₁ t₂ => bvUgtConst • t₁ • t₂
@[match_pattern] def bvUge : term → term → term :=
  λ t₁ t₂ => bvUgeConst • t₁ • t₂
@[match_pattern] def bvSlt : term → term → term :=
  λ t₁ t₂ => bvSltConst • t₁ • t₂
@[match_pattern] def bvSle : term → term → term :=
  λ t₁ t₂ => bvSleConst • t₁ • t₂
@[match_pattern] def bvSgt : term → term → term :=
  λ t₁ t₂ => bvSgtConst • t₁ • t₂
@[match_pattern] def bvSge : term → term → term :=
  λ t₁ t₂ => bvSgeConst • t₁ • t₂
@[match_pattern] def bvAdd : term → term → term :=
  λ t₁ t₂ => bvAddConst • t₁ • t₂
@[match_pattern] def bvNeg : term → term :=
  λ t => bvNegConst • t
@[match_pattern] def bvSub : term → term → term :=
  λ t₁ t₂ => bvSubConst • t₁ • t₂
@[match_pattern] def bvMul : term → term → term :=
  λ t₁ t₂ => bvMulConst • t₁ • t₂
@[match_pattern] def bvShl : term → term → term :=
  λ t₁ t₂ => bvShlConst • t₁ • t₂
@[match_pattern] def bvLShr : term → term → term :=
  λ t₁ t₂ => bvLShrConst • t₁ • t₂
@[match_pattern] def bvAShr : term → term → term :=
  λ t₁ t₂ => bvAShrConst • t₁ • t₂
@[match_pattern] def bvExtract :
  term → term → term → term :=
  λ t₁ t₂ t₃ => bvExtractConst • t₁ • t₂ • t₃
@[match_pattern] def bvConcat : term → term → term :=
  λ t₁ t₂ => bvConcatConst • t₁ • t₂
@[match_pattern] def bvZeroExt : term → term → term :=
  λ t₁ t₂ => bvZeroExtConst • t₁ • t₂
@[match_pattern] def bvSignExt : term → term → term :=
  λ t₁ t₂ => bvSignExtConst • t₁ • t₂
@[match_pattern] def bvRepeat : term → term → term :=
  λ t₁ t₂ => bvRepeatConst • t₁ • t₂
@[match_pattern] def emptyStr : term := emptyStrConst
@[match_pattern] def strPlus : term → term → term :=
  λ t₁ t₂ => strPlusConst • t₁ • t₂
@[match_pattern] def strLength : term → term := λ t => strLengthConst • t
@[match_pattern] def inRE : term → term → term := λ t₁ t₂ => inREConst • t₁ • t₂
@[match_pattern] def REInter : term → term → term := λ t₁ t₂ => REInterConst • t₁ • t₂

def termToString : term → String
| undef => "undef"
| val v _ => valueToString v
| not t => "¬(" ++ termToString t ++ ")"
| or t₁ t₂ => "(" ++ termToString t₁ ++ " ∨ " ++ termToString t₂ ++ ")"
| and t₁ t₂ => "(" ++ termToString t₁ ++ " ∧ " ++ termToString t₂ ++ ")"
| xor t₁ t₂ => termToString t₁ ++ " ⊕ " ++ termToString t₂
| implies t₁ t₂ => termToString t₁ ++ " ⇒ " ++ termToString t₂
| bIte c t₁ t₂ =>
    termToString c ++ " ? " ++ termToString t₁ ++ " : " ++ termToString t₂
| eq t₁ t₂ => termToString t₁ ++ " ≃ " ++ termToString t₂
| fIte c t₁ t₂ =>
    termToString c ++ " ? " ++ termToString t₁ ++ " : " ++ termToString t₂
| plus t₁ t₂ => termToString t₁ ++ " + " ++ termToString t₂
| minus t₁ t₂ => termToString t₁ ++ " - " ++ termToString t₂
| mult t₁ t₂ => termToString t₁ ++ " * " ++ termToString t₂
| gt t₁ t₂ => termToString t₁ ++ " > " ++ termToString t₂
| gte t₁ t₂ => termToString t₁ ++ " ≥ " ++ termToString t₂
| lt t₁ t₂ => termToString t₁ ++ " < " ++ termToString t₂
| lte t₁ t₂ => termToString t₁ ++ " ≤ " ++ termToString t₂
| select t₁ t₂ => termToString t₁ ++ "[" ++ termToString t₂ ++ "]"
| store t₁ t₂ t₃ => "(" ++
    termToString t₁ ++ "[" ++ termToString t₂ ++ "] := " ++ termToString t₃
    ++ ")"
| bitOf t₁ t₂ => termToString t₁ ++ "[" ++ termToString t₂ ++ "]"
| bbT => "bbT"
| bvNot t => "¬_bv" ++ termToString t
| bvAnd t₁ t₂ => termToString t₁ ++ " ∧_bv " ++ termToString t₂
| bvOr t₁ t₂ => termToString t₁ ++ " ∨_bv " ++ termToString t₂
| bvXor t₁ t₂ => termToString t₁ ++ " ⊕_bv " ++ termToString t₂
| bvNand t₁ t₂ => "BVNand " ++ termToString t₁ ++ " " ++ termToString t₂
| bvNor t₁ t₂ => "BVNor " ++ termToString t₁ ++ " " ++ termToString t₂
| bvXnor t₁ t₂ => "BVXnor " ++ termToString t₁ ++ " " ++ termToString t₂
| bvComp t₁ t₂ => "BVComp " ++ termToString t₁ ++ " " ++ termToString t₂
| bvUlt t₁ t₂ => termToString t₁ ++ " <ᵤ " ++ termToString t₂
| bvUle t₁ t₂ => termToString t₁ ++ " ≤ᵤ " ++ termToString t₂
| bvUgt t₁ t₂ => termToString t₁ ++ " >ᵤ " ++ termToString t₂
| bvUge t₁ t₂ => termToString t₁ ++ " ≥ᵤ " ++ termToString t₂
| bvSlt t₁ t₂ => termToString t₁ ++ " <ₛ " ++ termToString t₂
| bvSle t₁ t₂ => termToString t₁ ++ " ≤ₛ " ++ termToString t₂
| bvSgt t₁ t₂ => termToString t₁ ++ " >ₛ " ++ termToString t₂
| bvSge t₁ t₂ => termToString t₁ ++ " ≥ₛ " ++ termToString t₂
| bvAdd t₁ t₂ => termToString t₁ ++ " +_bv " ++ termToString t₂
| bvNeg t => "-_bv " ++ termToString t
| bvSub t₁ t₂ => termToString t₁ ++ " -_bv " ++ termToString t₂
| bvMul t₁ t₂ => termToString t₁ ++ " *_bv " ++ termToString t₂
| bvShl t₁ t₂ => termToString t₁ ++ " << " ++ termToString t₂
| bvLShr t₁ t₂ => termToString t₁ ++ " >> " ++ termToString t₂
| bvAShr t₁ t₂ => termToString t₁ ++ " >>ₐ " ++ termToString t₂
| bvExtract t₁ t₂ t₃ => ((termToString t₁) ++ "[" ++ (termToString t₂) ++ ":" ++ (termToString t₃) ++ "]")
| bvConcat t₁ t₂ => termToString t₁ ++ " ++ " ++ termToString t₂
| bvZeroExt t₁ t₂ => "zeroExt " ++ termToString t₁ ++ " " ++ termToString t₂
| bvSignExt t₁ t₂ => "signExt " ++ termToString t₁ ++ " " ++ termToString t₂
| bvRepeat t₁ t₂ => "repeat " ++ termToString t₁ ++ " " ++ termToString t₂
| const id _ => toString id
| f • t =>  "(" ++ (termToString f) ++ " " ++ (termToString t) ++ ")"
| qforall v t => "(∀ " ++ toString v ++ " . " ++ termToString t ++ ")"
| choice v t => "(ε " ++ toString v ++ " . " ++ termToString t ++ ")"
| lambda v t => "(λ " ++ toString v ++ ". " ++ termToString t ++ ")"

instance : ToString term where toString := termToString

-- computing the sort of terms
def sortOf : term → sort
| undef => sort.undef
| val (value.bool _) _ => boolSort
| val (bitvec l) _ =>
    Id.run do let len ← List.length l if len = 0 then sort.undef else bv len
| val (value.char _) _ => strSort
| val (integer _) _ => intSort
| eq t₁ t₂ =>
    let s₁ := sortOf t₁
    let s₂ := sortOf t₂
    if s₁ = s₂ then boolSort else sort.undef
| select a i =>
    let sa := sortOf a
    let si := sortOf i
    match sa with
    | array indexSort elementSort =>
            if si = indexSort then elementSort else sort.undef
    | _ => sort.undef
| store a i e =>
    let sa := sortOf a
    let si := sortOf i
    let se := sortOf e
    match sa with
    | array indexSort elementSort =>
            if si = indexSort ∧ se = elementSort then sa else sort.undef
    | _ => sort.undef
| fIte c t₁ t₂ =>
    let s₁ := sortOf c
    let s₂ := sortOf t₁
    let s₃ := sortOf t₂
    if s₁ = boolSort ∧ s₂ = s₃ then s₂ else sort.undef
| eqConst • t =>
  sort.arrow (sortOf t) boolSort
| term.app f t =>
    let sf := sortOf f
    let _ := sortOf t
    match sf with
    | arrow _ s => s
    | _ => sort.undef
| qforall _ t =>
    let st := sortOf t
    if st = boolSort then st else sort.undef
| choice _ t => sortOf t
| lambda _ t => sortOf t
| const _ s => s

def appN (t : term) (l : List term) : term :=
  List.foldl term.app t l

-- if-then-else
--def mkIte (c t₁ t₂ : term) : term :=
--  let s₁ := sortOf t₁ if s₁ = boolSort then bIte c t₁ t₂ else fIte c t₁ t₂

-- negation
--def mkNot : term → term := not

-- Boolean ops
-- def mkOr : term → term → term :=
--   constructBinaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

-- def mkOrN : List (term) → term :=
--     constructNaryTerm or (λ s₁ s₂ => s₁ = boolSort ∧ s₂ = boolSort)

def termBinFoldr : (f : term → term → term) → List term → term
| f, a₁ :: a₂ :: [] => f a₁ a₂
| f, a :: as => f a (termBinFoldr f as)
| _, _ => bot

def orN : List term → term
| [] => bot
| t::[] => t
| s₁::s₂::t => or s₁ (orN (s₂::t))

def andN : List term → term
| [] => bot
| t::[] => t
| s₁::s₂::t => and s₁ (andN (s₂::t))

def mkForall (v : Nat) (body : term) : term :=
  qforall v body

/- Aux functions to create values -/
@[match_pattern] def mkValInt : Int → term :=
λ i => val (value.integer i) intSort

def mkValChar : Char → term := λ c =>
 val (value.char c.val.toNat) strSort

def mkValBV : List Bool → term :=
λ l => val (value.bitvec l) (bv (List.length l))

def mkBbTVal : term → List Bool → term
| acc, [] => acc
| acc, h::tl => mkBbTVal (acc • (if h then top else bot)) tl

-- #eval mkBbTVal bbT [true,false,false,false]

def mkBbTVar : Nat → Nat → term → term → term
| _, 0, acc, _ => acc
| n, i+1, acc, t => mkBbTVar n i (acc • (bitOf t $ mkValInt $ n - (i+1))) t

-- #eval mkBbTVar 4 4 bbT (const 10001 (bv 4))

def mkValChars : List Char → term :=
 List.foldl strPlus emptyStr ∘ List.map mkValChar

end term

end proof
