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

    val phaseName = "marsPhase"

    override def newPhase(prev: Phase): StdPhase = new StdPhase(prev) {
      override def apply(compUnit: CompilationUnit) {
        try {
          //process only .scala files
          val fileName = compUnit.source.file.name
          if (fileName.endsWith(".scala")) {
            println(sm"""
            |=================================================
            |=============== Context Creator =================  
            |=================================================
            |phase name: ${prev.name}
            |unit: $compUnit""")
            
            val contextFactory = new ContextFactory {
              val global = MarsComponent.this.global
            } 
            
            import contextFactory.{global => compiler, _}
            import compiler.analyzer.Context
            
            val tree = compUnit.body.asInstanceOf[compiler.Tree]
            val initialContext = analyzer.rootContext(compUnit, EmptyTree, false).asInstanceOf[Context]
            
            ContextCreator(initialContext).contexted(tree)
            val contextInfo = applyContextInfo
            if (contextInfo.nonEmpty) {
              val (applyTree, resultedContext) = contextInfo.get
              val untypedInjectTree = q"""println("Hello: " + a)"""
              val typechecker = global.analyzer.newTyper(resultedContext.asInstanceOf[global.analyzer.Context])
              val typedInjectTree = typechecker.typed(untypedInjectTree).asInstanceOf[compiler.Tree]
              val unitTree = compUnit.body.asInstanceOf[compiler.Tree]
              val transformedTree = RuntimeMacroInjector(unitTree, typedInjectTree).expandMacroTree.asInstanceOf[Tree]
              
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
            //mode we should get from typer
            //global.analyzer.macroExpand(null, null, c.contextMode , null)
            println("=================================================")
          } else
            println("File " + fileName + " is not processed")
          } catch {
            case e: Exception =>
              e.printStackTrace()
              throw e
          }
      }
    }
  }
}
