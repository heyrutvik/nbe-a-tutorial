package nbe.typed.simply

object Demo extends App {

  import Implicits._
  import Tutorial._

  assert(typeEq(Nat, Nat))
  assert(typeEq(Nat -> (Nat -> Nat), Nat -> (Nat -> Nat)))

  assert(synthesis(List(('x, Nat)), Var('x)) == Right(Nat))
  assert(checking(Nil, Zero, Nat) == Right(true))
  assert(checking(Nil, Add1(Zero), Nat) == Right(true))
  assert(checking(Nil, Lam('x, Var('x)), Nat -> Nat) == Right(true))

  val three = Let('three, The(Nat, Add1(Add1(Add1(Zero)))))

  val plus = Let('+,
    The(
      Nat -> (Nat -> Nat),
      Lam('n,
        Lam('k,
          Rec(Nat, Var('n), Var('k), Lam('pred, Lam('almostsum, Add1(Var('almostsum))))))))
  )

  println("checkProgram: ")
  checkProgram(Nil,
               List(three,
                    plus,
                    App(Var('+), Var('three)),
                    App(App(Var('+), Var('three)), Var('three))))

  println("runProgram: ")
  runProgram(
    Nil,
    List(
      plus,
      Var('+),
      App(Var('+), Add1(Add1(Zero))),
      App(App(Var('+), Add1(Add1(Zero))), Add1(Zero))
    )
  )
}
