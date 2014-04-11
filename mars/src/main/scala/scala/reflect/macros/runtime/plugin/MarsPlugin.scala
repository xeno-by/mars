package scala.reflect.macros.runtime.plugin

import scala.tools.nsc.{ Global, Phase }
import scala.tools.nsc.plugins.{ Plugin, PluginComponent }
import scala.tools.nsc.typechecker.Macros

object MarsPlugin {
  val expandNameOpt = "expandName"
}

class MarsPlugin(val global: Global) extends Plugin {
  import MarsPlugin._
  import global._
  
  val name = "marsplugin"
  val description = "runtime macro expansion plugin"
  var expandName = "test"
  val components = List[PluginComponent](MarsComponent)

  override def processOptions(options: List[String], error: String => Unit) {
    for (option <- options) {
      if (option.startsWith(expandNameOpt)) {
        expandName = option.substring(expandNameOpt.length)
      } else{
          error("Option not understood: "+option)
      }
    }
  }

  private object MarsComponent extends PluginComponent {
    val global = MarsPlugin.this.global
    import global._
    import scala.reflect.macros.runtime.internal.ContextFactory

    override val runsAfter = List("typer")

    val phaseName = "mars"

    override def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
      override def apply(compUnit: CompilationUnit) {
        try {
            println(sm"""
            |=================================================
            |=============== Context Creator =================  
            |=================================================
            |phase name: ${prev.name}
            |unit: $compUnit""")
            
            val contextFactory = new ContextFactory {
              val global: MarsComponent.this.global.type = MarsComponent.this.global
            } 
            
            import contextFactory.{global => compiler, _}
            import compiler.analyzer.Context
            
            val unitTree = compUnit.body
            val initialContext = analyzer.rootContext(compUnit, EmptyTree, false)
            
            ContextCreator(initialContext).contexted(unitTree)
            val contextInfo = applyContextInfo
            if (contextInfo.nonEmpty) {
              val (applyTree, resultedContext) = contextInfo.get
              val untypedInjectTree = q"""println("Hello: " + a)"""
              val typechecker = global.analyzer.newTyper(resultedContext)
              val typedInjectTree = typechecker.typed(untypedInjectTree)
              val transformedTree = RuntimeMacroInjector(unitTree, typedInjectTree).expandMacroTree
              
              println(sm"""
              |applyTree: ${showRaw(applyTree)}
              |
              |===> resulted context: $resultedContext
              |
              |===> resulted scope: ${resultedContext.scope}
              |
              |resultedTree: ${showRaw(typedInjectTree)}
              |
              |transformedTree: ${showRaw(transformedTree)}
              |
              |transformedShowCode: ${showCode(transformedTree)}
              |""")
              
              compUnit.body = transformedTree
            } else {
              println("\n===> tree is not found!!!\n")
            }
            println("=================================================")
          } catch {
            case e: Exception =>
              e.printStackTrace()
              throw e
          }
      }
    }
  }
}
