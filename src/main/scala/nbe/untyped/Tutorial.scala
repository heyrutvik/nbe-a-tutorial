package nbe.untyped

/**
  * 1 Evaluating Untyped λ-Calculus
  * http://davidchristiansen.dk/tutorials/nbe/#%28part._untyped-eval%29
  *
  * 2 Generating Fresh Names
  * http://davidchristiansen.dk/tutorials/nbe/#%28part._.Generating_.Fresh_.Names%29
  *
  * 3 Normalizing Untyped λ-Calculus
  * http://davidchristiansen.dk/tutorials/nbe/#%28part._untyped-norm%29
  */

object Tutorial {

  import Implicits._
  import nbe.{lookup, extend, freshen}

  // environment
  type Rho = nbe.Env[Value]
  type Program = nbe.Program[Expr]

  // run-time value
  sealed trait Value
  case class CLOS(p: Rho, x: Symbol, b: Expr) extends Value
  sealed trait Neutral extends Value // represents neutral values
  case class NVar(x: Symbol) extends Neutral // neutral variable
  case class NAp(e1: Neutral, e2: Value) extends Neutral // neutral application

  // lambda expression
  sealed trait Expr
  case class Var(x: Symbol) extends Expr
  case class Lam(x: Symbol, b: Expr) extends Expr
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Let(x: Symbol, e: Expr) extends Expr // adding definitions

  // val
  def eval(p: Rho, e: Expr): Value = e match {
    case Var(x) =>
      lookup(p, x) match {
        case Some((x, v)) => v
        case _ => sys.error(s"eval: Unknown variable $x")
      }
    case Lam(x, b) =>
      CLOS(p, x, b)
    case App(e1, e2) =>
      apply(eval(p, e1), eval(p, e2))
    case Let(_, _) => sys.error("eval: doesn't deal with define")
  }

  // do-ap
  def apply(fun: Value, arg: Value): Value = fun match {
    case CLOS(p, x, b) => eval(extend(p, x, arg), b)
    case f: Neutral => NAp(f, arg)
    case _ => sys.error(s"can not apply to $fun")
  }

  // read-back: convert a value back into its representation as abstract syntax
  def readBack(usedName: List[Symbol], v: Value): Expr = v match {
    case NVar(x) => Var(x)
    case NAp(e1, e2) => App(readBack(usedName, e1), readBack(usedName, e2))
    case CLOS(p, x, b) =>
      val fx = freshen(usedName, x) // create fresh name using x
      val nfx = NVar(fx) // neutral value as newly created name
      Lam(fx, readBack(fx :: usedName, eval(extend(p, x, nfx), b)))
  }

  // normalize an expression
  def norm(p: Rho, e: Expr) = readBack(Nil, eval(p, e))

  // run-program
  def runProgram(p: Rho, exprs: Program): Unit = exprs match {
    case Nil => ()
    case Let(x, b) :: rest =>
      val v = eval(p, b)
      runProgram(extend(p, x, v), rest)
    case h :: rest =>
      println(norm(p, h).notation)
      runProgram(p, rest)
  }
}

object Implicits {

  import Tutorial._

  implicit class ExprOps(e: Expr) {
    def notation: String = e match {
      case Var(x) => x.name
      case Lam(x, Var(b)) => s"(λ${x.name}.${b.name})"
      case Lam(x, b) => s"(λ${x.name}.(${b.notation}))"
      case App(e1, e2) => s"(${e1.notation} ${e2.notation})"
      case Let(x, b) => s"(define ${x.name} (${b.notation})"
    }
  }

  implicit class ValueOps(v: Value) {
    def string: String = v match {
      case CLOS(p, v, b) =>
        s"Closure(${p.map{case (x, v) => s"${x.name} -> ${v.string}"}.mkString("[", ",", "]")}, " +
        s"${v.name}, " +
        s"${b.notation})"
    }
  }
}

object ChurchNumeral {

  import Tutorial._

  val ZERO = Symbol("church-zero")
  val ADD1 = Symbol("church-add1")

  // place expression e into a context where zero and add1 defined
  def withNumerals(e: Expr): Program = {
    List(
      Let(ZERO, Lam('f, Lam('x, Var('x)))),
      Let(ADD1, Lam('n, Lam('f, Lam('x, App(Var('f), App(App(Var('n), Var('f)), Var('x))))))),
      e
    )
  }

  // recursively apply add1 on zero till n hits zero
  def toChurch(n: Int): Expr = {
    if (n == 0) Var(ZERO)
    else if (n >= 0) {
      App(Var(ADD1), toChurch(n-1))
    } else sys.error(s"toChurch: $n negative number not allowed")
  }
}
