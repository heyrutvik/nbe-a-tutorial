package nbe.typed.simply

/**
  * 5 Bidirectional Type Checking
  * http://davidchristiansen.dk/tutorials/nbe/#%28part._.Bidirectional_.Type_.Checking%29
  *
  * 6 Typed Normalization by Evaluation
  * http://davidchristiansen.dk/tutorials/nbe/#%28part._typed-nbe%29
  */
object Tutorial {

  import Implicits._
  import nbe.{extend, freshen, lookup}

  type Ctx = nbe.Env[Type]
  type Rho = nbe.Env[Value]
  type Go[A] = Either[String, A]
  type Program = nbe.Program[Expr]

  // abstract syntax
  sealed trait Expr
  // introduction form
  case object Zero extends Expr
  case class Add1(e: Expr) extends Expr
  case class Lam(x: Symbol, b: Expr) extends Expr
  // elimination form
  case class App(e1: Expr, e2: Expr) extends Expr
  case class Rec(t: Type, target: Expr, base: Expr, step: Expr) extends Expr
  //
  case class Var(x: Symbol) extends Expr
  case class The(t: Type, e: Expr) extends Expr
  // adding definition
  case class Let(x: Symbol, e: Expr) extends Expr

  // types
  sealed trait Type
  case object Nat extends Type // natural number type
  case class ->(a: Type, r: Type) extends Type // function type

  // values for typed nbe
  sealed trait Value
  case object ZERO extends Value
  case class ADD1(v: Value) extends Value
  case class NEU(t: Type, v: Neutral) extends Value
  case class CLOS(p: Rho, x: Symbol, b: Expr) extends Value
  sealed trait Norm extends Value
  case class THE(t: Type, v: Value) extends Norm
  sealed trait Neutral extends Value
  case class NVar(x: Symbol) extends Neutral
  case class NAp(e1: Neutral, e2: Norm) extends Neutral
  case class NRec(t: Type, target: Neutral, base: Norm, step: Norm)
      extends Neutral

  // type=? structural type equality
  def typeEq(t1: Type, t2: Type): Boolean = (t1, t2) match {
    case (Nat, Nat) => true
    case (a1 -> r1, a2 -> r2) =>
      typeEq(a1, a2) && typeEq(r1, r2)
    case _ => false
  }

  // bidirectional type checking

  // synth
  def synthesis(ctx: Ctx, e: Expr): Go[Type] = e match {
    case The(t, expr) => for (_ <- checking(ctx, expr, t)) yield (t)
    case Rec(t, target, base, step) =>
      for {
        tt <- synthesis(ctx, target)
        _ <- if (typeEq(tt, Nat)) Right(t) else Left(s"Expected Nat, got $tt")
        _ <- checking(ctx, base, t)
        _ <- checking(ctx, step, Nat -> (t -> t))
      } yield (t)
    case Var(x) =>
      lookup(ctx, x) match {
        case Some((_, t)) => Right(t)
        case _            => Left(s"Variable ${x.name} not found")
      }
    case App(e1, e2) =>
      for {
        ft <- synthesis(ctx, e1)
        rt <- ft match {
          case at -> bt => checking(ctx, e2, at).map(_ => bt)
          case _        => Left(s"Not a function type ${ft.string}")
        }
      } yield (rt)
    case Let(_, _) => sys.error("synthesis: doesn't deal with define")
  }

  // check
  def checking(ctx: Ctx, e: Expr, t: Type): Go[Boolean] = e match {
    case Zero =>
      if (typeEq(t, Nat)) Right(true) else Left(s"Tried to use $t for zero")
    case Add1(n) =>
      if (typeEq(t, Nat)) for (_ <- checking(ctx, n, Nat)) yield (true)
      else Left(s"Tried to use ${t.string} for add1")
    case Lam(x, b) =>
      t match {
        case at -> bt =>
          for (_ <- checking(extend(ctx, x, at), b, bt)) yield (true)
        case aot =>
          Left(s"Instead of -> type, got ${aot.string}") // any other type `ot`; non arrow
      }
    case _ =>
      for {
        t2 <- synthesis(ctx, e)
        b <- {
          if (typeEq(t, t2)) Right(true)
          else
            Left(
              s"Synthesized type ${t2.string} where type ${t.string} was expected")
        }
      } yield (b)
    case Let(_, _) => sys.error("checking: doesn't deal with define")
  }

  // check-program
  def checkProgram(ctx: Ctx, program: Program): Go[Ctx] = program match {
    case Nil => Right(ctx)
    case Let(x, e) :: rest =>
      for {
        t <- synthesis(ctx, e)
        c <- checkProgram(extend(ctx, x, t), rest)
      } yield (c)
    case e :: rest =>
      for {
        t <- synthesis(ctx, e)
        _ = println(s"${e.notation} has type ${t.string}")
        c <- checkProgram(ctx, rest)
      } yield (c)
  }

  // val
  def eval(p: Rho, e: Expr): Value = e match {
    case The(t, e1) => eval(p, e1)
    case Zero       => ZERO
    case Add1(n)    => ADD1(eval(p, n))
    case Var(x) =>
      lookup(p, x) match {
        case Some((_, v)) => v
        case _            => sys.error(s"eval: Unknown variable $x")
      }
    case Lam(x, b) => CLOS(p, x, b)
    case Rec(t, target, base, step) =>
      rec(t, eval(p, target), eval(p, base), eval(p, step))
    case App(e1, e2) =>
      apply(eval(p, e1), eval(p, e2))
  }

  // do-ap
  def apply(fun: Value, arg: Value): Value = fun match {
    case CLOS(p, x, e)   => eval(extend(p, x, arg), e)
    case NEU(a -> b, ne) => NEU(b, NAp(ne, THE(a, arg)))
    case _               => sys.error("apply: ")
  }

  // do-rec
  def rec(t: Type, target: Value, base: Value, step: Value): Value =
    target match {
      case ZERO => base
      case ADD1(n) =>
        apply(apply(step, n), rec(t, n, base, step))
      case NEU(Nat, ne) =>
        NEU(t, NRec(t, ne, THE(t, base), THE(Nat -> (t -> t), step)))
    }

  // read-back
  def readBack(usedNames: List[Symbol], t: Type, v: Value): Expr = t match {
    case Nat =>
      v match {
        case ZERO       => Zero
        case ADD1(n)    => Add1(readBack(usedNames, Nat, n))
        case NEU(_, ne) => readBackNeutral(usedNames, ne)
      }
    case a -> b =>
      val x = freshen(usedNames, 'x)
      Lam(x, readBack(x :: usedNames, b, apply(v, NEU(a, NVar(x)))))
    case _ => sys.error("readBack: ")
  }

  // read-back-neutral
  def readBackNeutral(usedNames: List[Symbol], ne: Neutral): Expr = ne match {
    case NVar(x) => Var(x)
    case NAp(fun, THE(at, arg)) =>
      App(readBackNeutral(usedNames, fun), readBack(usedNames, at, arg))
    case NRec(t, target, THE(bt, base), THE(st, step)) =>
      Rec(
        t,
        readBackNeutral(usedNames, target),
        readBack(usedNames, bt, base),
        readBack(usedNames, st, step)
      )
    case _ => sys.error("readBackNeutral: ")
  }

  // definitions
  case class Def(t: Type, v: Value)
  type Delta = nbe.Env[Def]

  // defs->ctx
  def deltaToCtx(delta: Delta): Ctx = delta match {
    case Nil                    => Nil
    case (x, Def(t, _)) :: rest => extend(deltaToCtx(rest), x, t)
  }

  // defs->env
  def deltaToRho(delta: Delta): Rho = delta match {
    case Nil                    => Nil
    case (x, Def(_, v)) :: rest => extend(deltaToRho(rest), x, v)
  }

  // run-program
  def runProgram(delta: Delta, program: Program): Go[Delta] = program match {
    case Nil => Right(delta)
    case Let(x, e) :: rest =>
      for {
        t <- synthesis(deltaToCtx(delta), e)
        d <- runProgram(extend(delta, x, Def(t, eval(deltaToRho(delta), e))),
                        rest)
      } yield (d)
    case e :: rest =>
      val ctx = deltaToCtx(delta)
      val p = deltaToRho(delta)
      for {
        t <- synthesis(ctx, e)
        v = eval(p, e)
        e1 = readBack(ctx.map(_._1), t, v)
        _ = println(s"(the ${t.string} ${e1.notation})")
        d <- runProgram(delta, rest)
      } yield (d)
  }
}

object Implicits {

  import Tutorial.{-> => Fun, _}

  implicit class TypeOps(t1: Type) {
    def ->(t2: Type): Type = Fun(t1, t2)

    def string: String = t1 match {
      case Nat       => "Nat"
      case Fun(a, b) => s"(${a.string} -> ${b.string})"
    }
  }

  implicit class ExprOps(e: Expr) {
    def notation: String = e match {
      case Var(x)         => x.name
      case Lam(x, Var(b)) => s"(λ${x.name}.${b.name})"
      case Lam(x, b)      => s"(λ${x.name}.(${b.notation}))"
      case App(e1, e2)    => s"(${e1.notation} ${e2.notation})"
      case Let(x, b)      => s"(define ${x.name} (${b.notation})"
      case The(t, e)      => s"(the ${t.string} ${e.notation})"
      case Rec(t, target, base, step) =>
        s"(rec ${t.string} ${target.notation} ${base.notation} ${step.notation}"
      case Zero    => "zero"
      case Add1(e) => s"(add1 ${e.notation})"
    }
  }
}
