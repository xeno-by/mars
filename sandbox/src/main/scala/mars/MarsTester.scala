package mars
object MarsTester {
  def main(args: Array[String]) = test(42)

  def test(a: Int): Unit = runtimeMacro()

  def runtimeMacro(): Unit = ???
}

