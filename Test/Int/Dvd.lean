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
      smt +mono [h1, h2, dvdax]
    have h6 : dvd c e := by
      smt +mono [h3, h4, dvdax]
    smt +mono [h5, h6, dvdax]
