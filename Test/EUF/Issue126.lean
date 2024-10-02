import Smt

theorem extracted_1 (n a r v : Type) (b : a → Prop)
  (nmm : a → n → Prop) (ne ngt nm : n → Prop)
  (nsih : ∀ (s1 s2 : n), ∃ a, nmm a s1 ∧ nmm a s2 ∧ ¬b a)
  (noh : ∀ (s : n), ngt s → ∃ a, nmm a s ∧ ¬b a)
  (nsg : ∀ (s : n), nm s → ngt s)
  (nne : ∀ (s : n), ngt s → ¬ne s)
  (sa : a → a → r → v → Prop)
  (sb sc : a → a → a → r → v → Prop) (sg : a → r → Prop)
  (sd se sf : a → a → r → v → Prop)
  (ha :
    (∀ (s d₁ d₂ : a) (r : r) (v₁ v₂ : v),
        ¬b d₁ ∧ ¬b d₂ ∧ sf d₁ s r v₁ ∧ sf d₂ s r v₂ → v₁ = v₂) ∧
      (∀ (s d : a) (r : r) (v : v),
          ¬b s ∧ ¬b d ∧ sf d s r v →
            sg s r ∧ ∀ (d : a), sa s d r v) ∧
        (∀ (s d : a) (r : r) (v : v),
            ¬b s ∧ ¬b d ∧ se d s r v →
              sg s r ∧ ∀ (d : a), sa s d r v) ∧
          (∀ (s o d₁ d₂ : a) (r : r) (v₁ v₂ : v),
              ¬b s → sc s d₁ o r v₁ ∧ sc s d₂ o r v₂ → v₁ = v₂) ∧
            (∀ (s o d₁ d₂ : a) (r : r) (v₁ v₂ : v),
                ¬b s → sb s d₁ o r v₁ ∧ sb s d₂ o r v₂ → v₁ = v₂) ∧
              (∀ (s d₁ d₂ : a) (r : r) (v₁ v₂ : v),
                  ¬b s → sa s d₁ r v₁ ∧ sa s d₂ r v₂ → v₁ = v₂) ∧
                (∀ (s d : a) (r : r) (v : v),
                    ¬b s → ((∀ (d : a), sa s d r v) ↔ sa s d r v)) ∧
                  (∀ (n o : a) (r : r) (v : v),
                      ¬b n →
                        sf n o r v →
                          ∃ q,
                            nm q ∧
                              ∀ (s : a), nmm s q → sc s n o r v) ∧
                    (∀ (n o : a) (r : r) (v : v),
                        ¬b n →
                          se n o r v →
                            (∃ q,
                                nm q ∧
                                  ∀ (s : a), nmm s q → sb s n o r v) ∨
                              ∃ q,
                                ngt q ∧
                                  ∀ (s : a), nmm s q → sc s n o r v) ∧
                      (∀ (n d o : a) (r : r) (v : v),
                          ¬b n → (se n o r v ↔ sc n d o r v)) ∧
                        (∀ (n o : a) (r : r) (v : v),
                            ¬b n → sd n o r v → sa o n r v) ∧
                          (∀ (n d o : a) (r : r) (v : v),
                              ¬b n → (sd n o r v ↔ sb n d o r v)) ∧
                            ∀ (s : a) (r : r),
                              ¬b s → (sg s r ↔ ∃ v, ∀ (d : a), sa s d r v))
  (ta : a → a → r → v → Prop)
  (tb tc : a → a → a → r → v → Prop) (tg : a → r → Prop)
  (td te tf : a → a → r → v → Prop)
  (hb :
    (∀ (s d : a) (r : r) (v : v),
        ¬b s ∧ (sa s d r v ↔ ta s d r v) ∨
          b s ∧ (sa s d r v → ta s d r v)) ∧
      (∀ (s d o : a) (r : r) (v : v),
          ¬b s ∧ (sb s d o r v ↔ tb s d o r v) ∨
            b s ∧ (sb s d o r v → tb s d o r v)) ∧
        (∀ (s d o : a) (r : r) (v : v),
            ¬b s ∧ (sc s d o r v ↔ tc s d o r v) ∨
              b s ∧ (sc s d o r v → tc s d o r v)) ∧
          (∀ (a_2 : a) (a_3 : r), sg a_2 a_3 = tg a_2 a_3) ∧
            (∀ (a_2 a_3 : a) (a_4 : r) (a_5 : v),
                sd a_2 a_3 a_4 a_5 = td a_2 a_3 a_4 a_5) ∧
              (∀ (a_2 a_3 : a) (a_4 : r) (a_5 : v),
                  se a_2 a_3 a_4 a_5 = te a_2 a_3 a_4 a_5) ∧
                ∀ (a_2 a_3 : a) (a_4 : r) (a_5 : v),
                  sf a_2 a_3 a_4 a_5 = tf a_2 a_3 a_4 a_5)
  (n o : a) (r : r) (v : v) :
  ¬b n →
    te n o r v →
      (∃ q, nm q ∧ ∀ (s : a), nmm s q → tb s n o r v) ∨
        ∃ q,
          ngt q ∧ ∀ (s : a), nmm s q → tc s n o r v := by
  smt_show [nsih, noh, nsg, nne, ha, hb]
