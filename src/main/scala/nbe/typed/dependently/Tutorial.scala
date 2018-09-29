package nbe.typed.dependently

/**
  * 7 A Tiny Piece of Pie (Tartlet)
  * http://davidchristiansen.dk/tutorials/nbe/#%28part._.A_.Tiny_.Piece_of_.Pie%29
  */
object Tutorial {

  import Implicits._
  import nbe.{lookup, extend, gensym, freshen}

  type Sym = nbe.Env[Symbol]
  type Rho = nbe.Env[Value]
  type Ctx = nbe.Env[Context]
  type Go[A] = Either[String, A]

  /**
    * dependently typed expression
    *
    * types are first-class constructs
    */
  sealed trait Expr

  case class Var(x: Symbol) extends Expr
  // (Π ((x pt)) rt)
  case class Pi(x: Symbol, pt: Expr, rt: Expr) extends Expr // Π-type constructor
  case class Lam(x: Symbol, b: Expr) extends Expr // constructor
  case class App(e1: Expr, e2: Expr) extends Expr // eliminator
  // (Σ ((x t1)) t2)
  case class Si(x: Symbol, t1: Expr, t2: Expr) extends Expr // Σ-type constructor
  case class Cons(fst: Expr, snd: Expr) extends Expr // constructor
  case class Car(p: Expr) extends Expr // eliminator
  case class Cdr(p: Expr) extends Expr // eliminator
  // natural number
  case object Nat extends Expr // type constructor
  case object Zero extends Expr // constructor
  case class Add1(n: Expr) extends Expr // constructor
  case class IndNat(target: Expr, motive: Expr, base: Expr, step: Expr)
      extends Expr // eliminator
  // equality type
  case class Eq(t: Expr, w1: Expr, w2: Expr) extends Expr // type constructor
  case object Same extends Expr
  case class Replace(target: Expr, motive: Expr, base: Expr) extends Expr
  // type with exactly one value
  case object Trivial extends Expr
  case object Sole extends Expr
  // type with no values
  case object Absurd extends Expr
  case class IndAbsurd(at: Expr, t1: Expr) extends Expr
  // symbols
  case object Atom extends Expr
  case class Quote(s: String) extends Expr
  // universe describes all types
  case object U extends Expr
  // asserts that `e` is a `t`
  case class The(t: Expr, e: Expr) extends Expr
  // adding definition
  case class Let(x: Symbol, e: Expr) extends Expr

  // values
  sealed trait Value
  // closure values
  sealed trait Closure extends Value
  case class CLOS(p: Rho, x: Symbol, b: Expr) extends Closure
  case class HOCLOS(x: Symbol, f: Value => Value) extends Closure
  // function value
  case class PI(pt: Value, ft: Closure) extends Value
  case class LAM(b: Closure) extends Value
  // pair value
  case class SI(t1: Value, t2: Closure) extends Value
  case class PAIR(car: Value, cdr: Value) extends Value
  // natural number value
  case object NAT extends Value
  case object ZERO extends Value
  case class ADD1(n: Value) extends Value
  // equality value
  case class EQ(t: Value, from: Value, to: Value) extends Value
  case object SAME extends Value
  // singleton value
  case object TRIVIAL extends Value
  case object SOLE extends Value
  // void value
  case object ABSURD extends Value
  // atom value
  case object ATOM extends Value
  case class QUOTE(s: String) extends Value
  // universal type value
  case object UNI extends Value
  // type and neutral value
  case class NEU(t: Value, n: Neutral) extends Value
  // neutral values
  sealed trait Neutral extends Value
  case class NVar(x: Symbol) extends Neutral
  case class NAp(fun: Neutral, arg: Norm) extends Neutral
  case class NCar(p: Neutral) extends Neutral
  case class NCdr(p: Neutral) extends Neutral
  case class NIndNat(target: Neutral, motive: Norm, base: Norm, step: Norm)
      extends Neutral
  case class NReplace(target: Neutral, motive: Norm, base: Norm) extends Neutral
  case class NIndAbsurd(target: Neutral, motive: Norm) extends Neutral
  // normal value
  sealed trait Norm extends Value
  case class THE(t: Value, v: Value) extends Norm

  // closure name
  def closureName(c: Closure): Symbol = c match {
    case CLOS(_, x, _)         => x
    case Tutorial.HOCLOS(x, _) => x
  }

  // context binder
  sealed trait Context
  case class Def(t: Value, v: Value) extends Context
  case class Bind(t: Value) extends Context // free-variable binding
  // lookup-type
  def lookupType(ctx: Ctx, x: Symbol): Value = lookup(ctx, x) match {
    case Some((_, Def(t, _))) => t
    case Some((_, Bind(t)))   => t
  }
  // ctx->env
  def ctxToRho(ctx: Ctx): Rho = ctx.map {
    case (name, context) =>
      context match {
        case Bind(t)       => (name, NEU(t, NVar(name)))
        case Def(_, value) => (name, value)
      }
  }
  // extend-ctx
  def extendCtx(ctx: Ctx, x: Symbol, t: Value): Ctx = extend(ctx, x, Bind(t))

  // α-equiv?
  def isAlphaEquiv(e1: Expr, e2: Expr): Boolean = {

    // α-equiv-aux
    def isAlphaEquivAux(e1: Expr, e2: Expr, s1: Sym, s2: Sym): Boolean =
      (e1, e2) match {
        case (Var(x), Var(y)) =>
          (lookup(s1, x), lookup(s2, y)) match {
            case (Some((_, x1)), Some((_, y1))) => x1 == y1
            case (None, None)                   => x == y
          }
        case (Lam(x, b1), Lam(y, b2)) =>
          val fx = gensym
          isAlphaEquivAux(b1, b2, extend(s1, x, fx), extend(s2, y, fx))
        case (Pi(x, e1, b1), Pi(y, e2, b2)) =>
          val fx = gensym
          isAlphaEquivAux(e1, e2, s1, s2) && isAlphaEquivAux(b1,
                                                             b2,
                                                             extend(s1, x, fx),
                                                             extend(s2, y, fx))
        case (Si(x, e1, b1), Si(y, e2, b2)) =>
          val fx = gensym
          isAlphaEquivAux(e1, e2, s1, s2) && isAlphaEquivAux(b1,
                                                             b2,
                                                             extend(s1, x, fx),
                                                             extend(s2, y, fx))
        case (Quote(x), Quote(y))             => x == y
        case (The(Absurd, _), The(Absurd, _)) => true
        case (Cons(fst1, snd1), Cons(fst2, snd2)) =>
          isAlphaEquivAux(fst1, fst2, s1, s2) && isAlphaEquivAux(snd1,
                                                                 snd2,
                                                                 s1,
                                                                 s2)
        case (x, y) if x == y => true // any expression which are same
        case _                => false
      }

    isAlphaEquivAux(e1, e2, Nil, Nil)
  }

  // val
  def eval(p: Rho, e: Expr): Value = e match {
    case The(t, e)      => eval(p, e)
    case U              => UNI
    case Pi(x, pt, rt)  => PI(eval(p, pt), CLOS(p, x, rt))
    case Lam(x, b)      => LAM(CLOS(p, x, b))
    case Si(x, t1, t2)  => SI(eval(p, t1), CLOS(p, x, t2))
    case Cons(fst, snd) => PAIR(eval(p, fst), eval(p, snd))
    case Car(pr)        => applyCar(eval(p, pr))
    case Cdr(pr)        => applyCdr(eval(p, pr))
    case Nat            => NAT
    case Zero           => ZERO
    case Add1(n)        => ADD1(eval(p, n))
    case IndNat(target, motive, base, step) =>
      applyIndNat(eval(p, target),
                  eval(p, motive),
                  eval(p, base),
                  eval(p, step))
    case Eq(t, w1, w2) =>
      EQ(eval(p, t), eval(p, w1), eval(p, w2))
    case Same => SAME
    case Replace(target, motive, base) =>
      applyReplace(eval(p, target), eval(p, motive), eval(p, base))
    case Trivial => TRIVIAL
    case Sole    => SOLE
    case Absurd  => ABSURD
    case IndAbsurd(target, motive) =>
      applyAbsurd(eval(p, target), eval(p, motive))
    case Atom        => ATOM
    case Quote(s)    => QUOTE(s)
    case App(e1, e2) => apply(eval(p, e1), eval(p, e2))
    case Var(x) =>
      lookup(p, x) match {
        case Some((_, v)) => v
        case _            => sys.error(s"eval: Unknown variable $x")
      }
  }

  // val-of-closure
  def evalClosure(c: Closure, arg: Value): Value = c match {
    case CLOS(p, x, b) => eval(extend(p, x, arg), b)
    case HOCLOS(_, f)  => f(arg)
  }

  // do-car
  def applyCar(v: Value): Value = v match {
    case PAIR(car, _)       => car
    case NEU(SI(t1, _), ne) => NEU(t1, NCar(ne))
  }

  // do-cdr
  def applyCdr(v: Value): Value = v match {
    case PAIR(_, cdr)       => cdr
    case NEU(SI(_, t2), ne) => NEU(evalClosure(t2, applyCar(v)), NCdr(ne))
  }

  // do-app
  def apply(fun: Value, arg: Value): Value = fun match {
    case LAM(c) => evalClosure(c, arg)
    case NEU(PI(pt, rt), ne) =>
      NEU(evalClosure(rt, arg), NAp(ne, THE(pt, arg)))
  }

  // do-ind-Absurd
  def applyAbsurd(target: Value, motive: Value): Value = target match {
    case NEU(ABSURD, ne) => NEU(motive, NIndAbsurd(ne, THE(UNI, motive)))
  }

  // do-replace
  def applyReplace(target: Value, motive: Value, base: Value): Value =
    target match {
      case SAME => base
      case NEU(EQ(t, from, to), ne) =>
        NEU(
          apply(motive, to),
          NReplace(
            ne,
            THE(PI(t, HOCLOS('x, _ => UNI)), motive),
            THE(apply(motive, from), base)
          )
        )
    }

  // ind-Nat-step-type
  def indNatStepType(motive: Value): Value = {
    PI(NAT,
       HOCLOS(
         'n,
         n => PI(apply(motive, n), HOCLOS('ih, ih => apply(motive, ADD1(n))))))
  }

  // do-ind-Nat
  def applyIndNat(target: Value,
                  motive: Value,
                  base: Value,
                  step: Value): Value = target match {
    case ZERO    => base
    case ADD1(n) => apply(apply(step, n), applyIndNat(n, motive, base, step))
    case NEU(NAT, ne) =>
      NEU(
        apply(motive, target),
        NIndNat(
          ne,
          THE(PI(NAT, HOCLOS('k, _ => UNI)), motive),
          THE(apply(motive, ZERO), base),
          THE(indNatStepType(motive), step)
        )
      )
  }

  // read-back-norm
  def readBackNorm(ctx: Ctx, norm: Norm): Expr = norm match {
    case THE(NAT, ZERO) => Zero
    case THE(NAT, ADD1(n)) =>
      Add1(readBackNorm(ctx, THE(NAT, n)))
    case THE(PI(pt, rt), f) =>
      val x = closureName(rt)
      val fx = freshen(ctx.map(_._1), x)
      val nfx = NEU(pt, NVar(fx))
      Lam(fx,
          readBackNorm(extendCtx(ctx, fx, pt),
                       THE(evalClosure(rt, nfx), apply(f, nfx))))
    case THE(SI(t1, t2), p) =>
      val theCar = THE(t1, applyCar(p))
      val theCdr = THE(evalClosure(t2, theCar), applyCdr(p))
      Cons(readBackNorm(ctx, theCar), readBackNorm(ctx, theCdr))
    case THE(TRIVIAL, _) => Sole
    case THE(ABSURD, NEU(ABSURD, ne)) =>
      The(Absurd, readBackNeutral(ctx, ne))
    case THE(EQ(_, _, _), SAME) => Same
    case THE(ATOM, QUOTE(s))    => Quote(s)
    case THE(UNI, NAT)          => Nat
    case THE(UNI, TRIVIAL)      => Trivial
    case THE(UNI, ABSURD)       => Absurd
    case THE(UNI, EQ(t, from, to)) =>
      Eq(
        readBackNorm(ctx, THE(UNI, t)),
        readBackNorm(ctx, THE(t, from)),
        readBackNorm(ctx, THE(t, to))
      )
    case THE(UNI, SI(t1, t2)) =>
      val x = closureName(t2)
      val fx = freshen(ctx.map(_._1), x)
      Si(fx,
         readBackNorm(ctx, THE(UNI, t1)),
         readBackNorm(extendCtx(ctx, fx, t1),
                      THE(UNI, evalClosure(t2, NEU(t1, NVar(fx))))))
    case THE(UNI, PI(pt, rt)) =>
      val x = closureName(rt)
      val fx = freshen(ctx.map(_._1), x)
      Pi(fx,
         readBackNorm(ctx, THE(UNI, pt)),
         readBackNorm(extendCtx(ctx, fx, pt),
                      THE(UNI, evalClosure(rt, NEU(pt, NVar(fx))))))
    case THE(UNI, UNI)      => U
    case THE(UNI, ATOM)     => Atom
    case THE(_, NEU(_, ne)) => readBackNeutral(ctx, ne)
  }

  // read-back-neutral
  def readBackNeutral(ctx: Ctx, neu: Neutral): Expr = neu match {
    case NVar(x)   => Var(x)
    case NAp(f, a) => App(readBackNeutral(ctx, f), readBackNorm(ctx, a))
    case NCar(ne)  => Car(readBackNeutral(ctx, ne))
    case NCdr(ne)  => Cdr(readBackNeutral(ctx, ne))
    case NIndNat(ne, motive, base, step) =>
      IndNat(
        readBackNeutral(ctx, ne),
        readBackNorm(ctx, motive),
        readBackNorm(ctx, base),
        readBackNorm(ctx, step),
      )
    case NReplace(ne, motive, base) =>
      Replace(
        readBackNeutral(ctx, ne),
        readBackNorm(ctx, motive),
        readBackNorm(ctx, base),
      )
    case NIndAbsurd(target, motive) =>
      IndAbsurd(The(Absurd, readBackNeutral(ctx, target)),
                readBackNorm(ctx, motive))
  }

  // synth
  def synthesis(ctx: Ctx, e: Expr): Go[The] = e match {
    case v @ Var(x) =>
      val t = lookupType(ctx, x)
      Right(The(readBackNorm(ctx, THE(UNI, t)), v))
    case U => Right(The(U, U))
    case Pi(x, pt, rt) =>
      for {
        ao <- checking(ctx, pt, UNI)
        bo <- checking(extendCtx(ctx, x, eval(ctxToRho(ctx), ao)), rt, UNI)
      } yield (The(U, Pi(x, ao, bo)))
    case App(e1, e2) =>
      synthesis(ctx, e1).flatMap {
        case The(e1t, e2o) =>
          eval(ctxToRho(ctx), e1t) match {
            case PI(pt, rt) =>
              checking(ctx, e2, pt).flatMap { ro =>
                Right(
                  The(readBackNorm(
                        ctx,
                        THE(UNI, evalClosure(rt, eval(ctxToRho(ctx), ro)))),
                      App(e2o, ro)))
              }
            case v =>
              val t = readBackNorm(ctx, THE(UNI, v))
              Left(s"Expected Π, got $t")
          }
      }
    case The(t, e1) =>
      for {
        to <- checking(ctx, t, UNI)
        e1o <- checking(ctx, e1, eval(ctxToRho(ctx), to))
      } yield (The(to, e1o))
    case Nat => Right(The(U, Nat))
    case Si(x, t1, t2) =>
      for {
        t1o <- checking(ctx, t1, UNI)
        t2o <- checking(extendCtx(ctx, x, eval(ctxToRho(ctx), t1o)), t2, UNI)
      } yield (The(U, Si(x, t1o, t2o)))
    case Car(p) =>
      synthesis(ctx, p).flatMap {
        case The(pt, po) =>
          eval(ctxToRho(ctx), pt) match {
            case SI(t1, t2) =>
              Right(The(readBackNorm(ctx, THE(UNI, t1)), Car(po)))
            case v =>
              val t = readBackNorm(ctx, THE(UNI, v))
              Left(s"Expected Σ, got $t")
          }
      }
    case Cdr(p) =>
      synthesis(ctx, p).flatMap {
        case The(pt, po) =>
          eval(ctxToRho(ctx), pt) match {
            case SI(t1, t2) =>
              val tc = applyCar(eval(ctxToRho(ctx), po))
              Right(
                The(readBackNorm(ctx, THE(UNI, evalClosure(t2, tc))), Cdr(po)))
            case v =>
              val t = readBackNorm(ctx, THE(UNI, v))
              Left(s"Expected Σ, got $t")
          }
      }
    case Atom    => Right(The(U, Atom))
    case Trivial => Right(The(U, Trivial))
    case Absurd  => Right(The(U, Absurd))
    case IndAbsurd(target, motive) =>
      for {
        ao <- checking(ctx, target, ABSURD)
        mo <- checking(ctx, motive, UNI)
      } yield (The(mo, IndAbsurd(ao, mo)))
    case Eq(t, w1, w2) =>
      for {
        ao <- checking(ctx, t, UNI)
        av = eval(ctxToRho(ctx), ao)
        w1o <- checking(ctx, w1, av)
        w2o <- checking(ctx, w2, av)
      } yield (The(U, Eq(ao, w1o, w2o)))
    case Replace(target, motive, base) =>
      synthesis(ctx, target).flatMap {
        case The(tt, to) =>
          eval(ctxToRho(ctx), tt) match {
            case EQ(t, w1, w2) =>
              for {
                mo <- checking(ctx, motive, PI(t, HOCLOS('x, _ => UNI)))
                mv = eval(ctxToRho(ctx), mo)
                bo <- checking(ctx, base, apply(mv, w1))
              } yield
                (The(readBackNorm(ctx, THE(UNI, apply(mv, w2))),
                     Replace(to, mo, bo)))
            case v =>
              val t = readBackNorm(ctx, THE(UNI, v))
              Left(s"Expected Eq, got $t")
          }
      }
    case IndNat(target, motive, base, step) =>
      for {
        to <- checking(ctx, target, NAT)
        mo <- checking(ctx, motive, PI(NAT, HOCLOS('n, _ => UNI)))
        mv = eval(ctxToRho(ctx), mo)
        bo <- checking(ctx, base, apply(mv, ZERO))
        so <- checking(ctx, step, indNatStepType(mv))
      } yield
        (The(readBackNorm(ctx, THE(UNI, apply(mv, eval(ctxToRho(ctx), to)))),
             IndNat(to, mo, bo, so)))
  }

  // check
  def checking(ctx: Ctx, e: Expr, t: Value): Go[Expr] = e match {
    case Lam(x, b) =>
      t match {
        case PI(pt, rt) =>
          val nx = NEU(pt, NVar(x))
          for (bo <- checking(extendCtx(ctx, x, pt), b, evalClosure(rt, nx)))
            yield {
              Lam(x, bo)
            }
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Π, got $t1")
      }
    case Zero =>
      t match {
        case NAT => Right(Zero)
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Nat, got $t1")
      }
    case Add1(n) =>
      t match {
        case NAT =>
          for (no <- checking(ctx, n, NAT)) yield (Add1(no))
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Nat, got $t1")
      }
    case Cons(fst, snd) =>
      t match {
        case SI(t1, t2) =>
          for {
            fo <- checking(ctx, fst, t1)
            so <- checking(ctx, snd, evalClosure(t2, eval(ctxToRho(ctx), fo)))
          } yield (Cons(fo, so))
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Σ, got $t1")
      }
    case Quote(s) =>
      t match {
        case ATOM => Right(Quote(s))
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Atom, got $t1")
      }
    case Sole =>
      t match {
        case TRIVIAL => Right(Sole)
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Trivial, got $t1")
      }
    case Same =>
      t match {
        case EQ(t, w1, w2) =>
          for (_ <- convert(ctx, t, w1, w2)) yield (Same)
        case v =>
          val t1 = readBackNorm(ctx, THE(UNI, v))
          Left(s"Expected Eq, got $t1")
      }
    case _ =>
      synthesis(ctx, e).flatMap {
        case The(to, eo) =>
          convert(ctx, UNI, t, eval(ctxToRho(ctx), to)).map { _ =>
            eo
          }
      }
  }

  // convert
  def convert(ctx: Ctx, t: Value, v1: Value, v2: Value): Go[Boolean] = {
    val e1 = readBackNorm(ctx, THE(t, v1))
    val e2 = readBackNorm(ctx, THE(t, v2))
    if (isAlphaEquiv(e1, e2)) Right(true)
    else {
      val t1 = readBackNorm(ctx, THE(UNI, t))
      Left(s"Expected to be the same $t1 but found $e1 and $e2")
    }
  }

  // interact
  def interact(ctx: Ctx, input: Expr): Go[Ctx] = input match {
    case Let(x, e) =>
      lookup(ctx, x) match {
        case Some(_) => Left("Already defined")
        case None =>
          synthesis(ctx, e).map {
            case The(t, e1) =>
              val p = ctxToRho(ctx)
              extend(ctx, x, Def(eval(p, t), eval(p, e1)))
          }
      }
    case e =>
      synthesis(ctx, e).map {
        case The(t, e1) =>
          val p = ctxToRho(ctx)
          val n = readBackNorm(ctx, THE(eval(p, t), eval(p, e1)))
          println(s"Type: ${t.notation} \nNormal Form: ${n.notation}\n")
          ctx
      }
  }

  // run-program
  def runProgram(ctx: Ctx, inputs: List[Expr]): Go[Ctx] = inputs match {
    case Nil       => Right(ctx)
    case d :: rest => interact(ctx, d).flatMap(nctx => runProgram(nctx, rest))
  }

  def run(inputs: List[Expr]): Unit = runProgram(Nil, inputs) match {
    case Left(e) => println(e)
    case _       => ()
  }
}

object Implicits {

  import Tutorial._

  implicit class ExprOps(e: Expr) {
    def notation: String = e match {
      case Var(x) => x.name
      case Pi(x, pt, rt) =>
        s"(Π (${x.name} : ${pt.notation}) -> ${rt.notation})"
      case Lam(x, Var(b)) => s"(λ${x.name}.${b.name})"
      case Lam(x, b)      => s"(λ${x.name}.(${b.notation}))"
      case App(fun, arg)  => s"(${fun.notation} ${arg.notation})"
      case Si(x, t1, t2) =>
        s"(Σ (${x.name} : ${t1.notation}) -> ${t2.notation})"
      case Cons(fst, snd) => s"(cons (${fst.notation}) (${snd.notation}))"
      case Car(p)         => s"(car ${p.notation})"
      case Cdr(p)         => s"(cdr ${p.notation})"
      case Nat            => "Nat"
      case Zero           => "zero"
      case Add1(n)        => s"(add1 (${n.notation}))"
      case IndNat(ta, mo, ba, st) =>
        s"(ind-Nat (${ta.notation}) (${mo.notation}) (${ba.notation}) (${st.notation}))"
      case Eq(t, w1, w2) =>
        s"(= (${t.notation}) (${w1.notation}) (${w2.notation}))"
      case Same => "same"
      case Replace(ta, mo, ba) =>
        s"(replace (${ta.notation}) (${mo.notation}) (${ba.notation}))"
      case Trivial => "Trivial"
      case Sole    => "sole"
      case Absurd  => "Absurd"
      case IndAbsurd(at, t1) =>
        s"(ind-Absurd (${at.notation}) (${t1.notation}))"
      case Atom        => "Atom"
      case Quote(s)    => s"'$s"
      case U           => "U"
      case The(e1, e2) => s"(the ${e1.notation} ${e2.notation})"
    }
  }
}
