import scala.language.experimental.macros
import scala.reflect.macros.blackbox.Context
import scala.reflect.interpreter._

object ctfe {
  def apply[T](x: T): T = macro impl
  def impl(c: Context)(x: c.Tree) = {
    import c.universe._
    // TODO: needs runtime code execution to support the general case
    interpret(c)(x) match {
      case x: Byte => q"$x"
      case x: Short => q"$x"
      case x: Char => q"$x"
      case x: Int => q"$x"
      case x: Long => q"$x"
      case x: Float => q"$x"
      case x: Double => q"$x"
      case x: Boolean => q"$x"
      case x: Unit => q"$x"
      case x: String => q"$x"
      case _ => c.abort(c.enclosingPosition, s"unsupported evaluation result: $x")
    }
  }
}