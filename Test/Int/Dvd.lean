import Smt

opaque dvd : Int → Int → Bool

example
    (a b c d e : Int)
    (dvdax : ∀ x y z, dvd x y → dvd y z → dvd x z)
    (h1 : dvd a b)
    (h2 : dvd b c)
    (h3 : dvd c d)
    (h4 : dvd d e) :
  dvd a e := by
    have h5 : dvd a c := by
      smt [h1, h2, dvdax]
      exact dvdax _ _ _ h1 h2
    have h6 : dvd c e := by
      smt [h3, h4, dvdax]
      exact dvdax _ _ _ h3 h4
    smt [h5, h6, dvdax]
    exact dvdax _ _ _ h5 h6
