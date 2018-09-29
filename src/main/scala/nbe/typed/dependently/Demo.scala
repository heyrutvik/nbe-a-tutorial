package nbe.typed.dependently

object Demo extends App {

  import Tutorial._
  import Implicits._

  val l1 = Lam('x, Var('x))
  val l2 = Lam('y, Var('y))

  val p1 = Pi('j, Nat, Pi('k, Nat, U))

  assert(p1.notation == "(Π (j : Nat) -> (Π (k : Nat) -> U))")
  assert(isAlphaEquiv(l1, l2) == true)

  val the_id =
    The(Pi('x, U, Pi('y, Var('x), Var('x))), Lam('a, Lam('b, Var('b))))
  val let_id = Let('id, the_id)
  val app_typ = App(Var('id), Nat)
  val app_val = App(app_typ, Zero)

  val the_u_cons = The(U, Si('x, Nat, Nat))
  val the_cons = The(Si('x, Nat, Nat), Cons(Zero, Add1(Zero)))
  val let_cons = Let('p, the_cons)
  val the_car = The(Nat, Car(Var('p)))
  val the_cdr = The(Nat, Cdr(Var('p)))

  val the_atom = The(Atom, Quote("quoted"))
  val let_atom = Let('a, the_atom)
  val the_p1 = The(Si('x, Nat, Atom), Cons(Zero, Var('a)))

  val the_same = The(Eq(Nat, Add1(Zero), Add1(Zero)), Same)

  val rep1 =
    Replace(The(Eq(Nat, Add1(Zero), Add1(Zero)), Same), Lam('x, Atom), Var('a))

  val indn1 = IndNat(
    Add1(Add1(Add1(Zero))),
    Lam('x, Nat),
    Zero,
    Lam('x, Lam('n, Add1(Var('n))))
  )

  val the_NatEqConsequences = The(
    Pi('j, Nat, Pi('k, Nat, U)),
    Lam(
      'j,
      Lam(
        'k,
        IndNat(
          Var('j),
          Lam('_, U),
          IndNat(Var('k), Lam('_, U), Trivial, Lam('_, Lam('_, Absurd))),
          Lam('j1,
              Lam('_,
                  IndNat(
                    Var('k),
                    Lam('_, U),
                    Absurd,
                    Lam('k1, Lam('_, Eq(Nat, Var('j1), Var('k1))))
                  )))
        )
      )
    )
  )

  val let_NatEqConsequences = Let('natEqConsequences, the_NatEqConsequences)

  val the_NatEqConsequencesRefl = The(
    Pi('n, Nat, App(App(Var('natEqConsequences), Var('n)), Var('n))),
    Lam('n,
        IndNat(
          Var('n),
          Lam('k, App(App(Var('natEqConsequences), Var('k)), Var('k))),
          Sole,
          Lam('n1, Lam('_, Same))
        ))
  )

  val let_NatEqConsequencesRefl =
    Let('natEqConsequencesRefl, the_NatEqConsequencesRefl)

  val necr1 = App(Var('natEqConsequencesRefl), Zero)
  val necr2 = App(Var('natEqConsequencesRefl), Add1(Add1(Zero)))

  val the_thereAreConsequences = The(
    Pi('j,
       Nat,
       Pi('k,
          Nat,
          Pi('jk,
             Eq(Nat, Var('j), Var('k)),
             App(App(Var('natEqConsequences), Var('j)), Var('k))))),
    Lam('j,
        Lam('k,
            Lam('jk,
                Replace(
                  Var('jk),
                  Lam('n, App(App(Var('natEqConsequences), Var('j)), Var('n))),
                  App(Var('natEqConsequencesRefl), Var('j))
                ))))
  )
  val let_thereAreConsequences =
    Let('thereAreConsequences, the_thereAreConsequences)

  val tac1 = App(App(Var('thereAreConsequences), Zero), Zero)
  val tac2 = App(App(App(Var('thereAreConsequences), Zero), Zero), Same)
  val tac3 = App(App(Var('thereAreConsequences), Add1(Zero)), Add1(Zero))
  val tac4 =
    App(App(App(Var('thereAreConsequences), Add1(Zero)), Add1(Zero)), Same)
  val tac5 = App(App(Var('thereAreConsequences), Zero), Add1(Zero))
  val tac6 = App(App(Var('thereAreConsequences), Add1(Zero)), Zero)

  run(
    List(
      let_id,
      the_id,
      app_typ,
      app_val,
      the_u_cons,
      let_cons,
      the_cons,
      the_car,
      the_cdr,
      the_atom,
      let_atom,
      the_p1,
      the_same,
      rep1,
      indn1,
      the_NatEqConsequences,
      let_NatEqConsequences,
      the_NatEqConsequencesRefl,
      let_NatEqConsequencesRefl,
      the_thereAreConsequences,
      let_thereAreConsequences,
      necr1,
      necr2,
      tac1,
      tac2,
      tac3,
      tac4,
      tac5,
      tac6
    )
  )

  /**
  * Output:
  *
  * Type: (Π (x : U) -> (Π (y : x) -> x))
  * Normal Form: (λx.((λy.y)))
  *
  * Type: (Π (y : Nat) -> Nat)
  * Normal Form: (λy.y)
  *
  * Type: Nat
  * Normal Form: zero
  *
  * Type: U
  * Normal Form: (Σ (x : Nat) -> Nat)
  *
  * Type: (Σ (x : Nat) -> Nat)
  * Normal Form: (cons (zero) ((add1 (zero))))
  *
  * Type: Nat
  * Normal Form: zero
  *
  * Type: Nat
  * Normal Form: (add1 (zero))
  *
  * Type: Atom
  * Normal Form: 'quoted
  *
  * Type: (Σ (x : Nat) -> Atom)
  * Normal Form: (cons (zero) ('quoted))
  *
  * Type: (= (Nat) ((add1 (zero))) ((add1 (zero))))
  * Normal Form: same
  *
  * Type: Atom
  * Normal Form: 'quoted
  *
  * Type: Nat
  * Normal Form: (add1 ((add1 ((add1 (zero))))))
  *
  * Type: (Π (j : Nat) -> (Π (k : Nat) -> U))
  * Normal Form: (λj.((λk.((ind-Nat (j) ((λk*.(U))) ((ind-Nat (k) ((λk*.(U))) (Trivial) ((λn.((λih.(Absurd))))))) ((λn.((λih.((ind-Nat (k) ((λk*.(U))) (Absurd) ((λn*.((λih*.((= (Nat) (n) (n*))))))))))))))))))
  *
  * Type: (Π (n : Nat) -> ((natEqConsequences n) n))
  * Normal Form: (λn.((ind-Nat (n) ((λk.((ind-Nat (k) ((λk*.(U))) ((ind-Nat (k) ((λk*.(U))) (Trivial) ((λn*.((λih.(Absurd))))))) ((λn*.((λih.((ind-Nat (k) ((λk*.(U))) (Absurd) ((λn**.((λih*.((= (Nat) (n*) (n**))))))))))))))))) (sole) ((λn*.((λih.(same))))))))
  *
  * Type: (Π (j : Nat) -> (Π (k : Nat) -> (Π (jk : (= (Nat) (j) (k))) -> ((natEqConsequences j) k))))
  * Normal Form: (λj.((λk.((λjk.((replace (jk) ((λx.((ind-Nat (j) ((λk*.(U))) ((ind-Nat (x) ((λk*.(U))) (Trivial) ((λn.((λih.(Absurd))))))) ((λn.((λih.((ind-Nat (x) ((λk*.(U))) (Absurd) ((λn*.((λih*.((= (Nat) (n) (n*))))))))))))))))) ((ind-Nat (j) ((λk*.((ind-Nat (k*) ((λk**.(U))) ((ind-Nat (k*) ((λk**.(U))) (Trivial) ((λn.((λih.(Absurd))))))) ((λn.((λih.((ind-Nat (k*) ((λk**.(U))) (Absurd) ((λn*.((λih*.((= (Nat) (n) (n*))))))))))))))))) (sole) ((λn.((λih.(same))))))))))))))
  *
  * Type: Trivial
  * Normal Form: sole
  *
  * Type: (= (Nat) ((add1 (zero))) ((add1 (zero))))
  * Normal Form: same
  *
  * Type: (Π (jk : (= (Nat) (zero) (zero))) -> Trivial)
  * Normal Form: (λjk.(sole))
  *
  * Type: Trivial
  * Normal Form: sole
  *
  * Type: (Π (jk : (= (Nat) ((add1 (zero))) ((add1 (zero))))) -> (= (Nat) (zero) (zero)))
  * Normal Form: (λjk.((replace (jk) ((λx.((ind-Nat (x) ((λk.(U))) (Absurd) ((λn.((λih.((= (Nat) (zero) (n))))))))))) (same))))
  *
  * Type: (= (Nat) (zero) (zero))
  * Normal Form: same
  *
  * Type: (Π (jk : (= (Nat) (zero) ((add1 (zero))))) -> Absurd)
  * Normal Form: (λjk.((the Absurd (replace (jk) ((λx.((ind-Nat (x) ((λk.(U))) (Trivial) ((λn.((λih.(Absurd))))))))) (sole)))))
  *
  * Type: (Π (jk : (= (Nat) ((add1 (zero))) (zero))) -> Absurd)
  * Normal Form: (λjk.((the Absurd (replace (jk) ((λx.((ind-Nat (x) ((λk.(U))) (Absurd) ((λn.((λih.((= (Nat) (zero) (n))))))))))) (same)))))
  */
}
