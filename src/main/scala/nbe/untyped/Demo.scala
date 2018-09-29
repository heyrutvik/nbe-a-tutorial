package nbe.untyped

object Demo extends App {

  import ChurchNumeral._
  import Tutorial._

  val e1 = App(
    Lam('a, Lam('b, App(Var('a), Var('b)))),
    Lam('c, Var('c))
  )

  runProgram(Nil, List(e1))

  runProgram(Nil, withNumerals(toChurch(0)))
  runProgram(Nil, withNumerals(toChurch(1)))
  runProgram(Nil, withNumerals(toChurch(4)))
}