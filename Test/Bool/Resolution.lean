import Smt

theorem resolution (p q r : Bool) : p || q → !p || r → q || r := by
  smt
