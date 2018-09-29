import scala.util.Random.nextInt

package object nbe {

  // environment
  type Env[A] = List[(Symbol, A)]

  // expression with definition
  type Program[A] = List[A]

  // assv
  def lookup[A](env: Env[A], x: Symbol): Option[(Symbol, A)] =
    env.filter(_._1 == x).headOption

  // extend
  def extend[A](p: Env[A], x: Symbol, v: A): Env[A] = (x, v) :: p

  // generating fresh names
  // add-*
  private def addStar(s: Symbol): Symbol = Symbol(s"${s.name}*")

  // freshen
  def freshen(used: List[Symbol], x: Symbol): Symbol =
    if (used.contains(x)) freshen(x :: used, addStar(x))
    else x

  // gensym
  def gensym = {
    Symbol(f"${('A' to 'Z')(nextInt(26))}${nextInt(10000)}%04d")
  }
}
