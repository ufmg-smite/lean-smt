import Smt

opaque dvd : Int → Int → Prop

example
    (a b c d : Int)
    (dvdax : ∀ x y z, dvd x y → dvd x z → dvd x (y + z))
    (h1 : dvd a b)
    (h2 : dvd a c)
    (h3 : dvd a d)
  : dvd a (b + c + d) := by
    smt [dvdax, h1, h2, h3]
