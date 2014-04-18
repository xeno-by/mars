package scala.reflect.macros.runtime.internal

import scala.tools.nsc.Global

trait ContextFactory {
  val global: Global
  import global._
  import global.analyzer.Context
  var applyContextInfo: Option[(Tree, Context)] = None

  def isRuntimeMacro(apply: Apply) = {
    val Apply(fun, args) = apply
    fun match {
      case Select(_, name) => name.toString() == "runtimeMacro"
      case _ => false
    }
  }

  object RuntimeMacroInjector {
    def apply(tree: Tree, macroTree: Tree) = new RuntimeMacroInjector(tree, macroTree)
  }

  class RuntimeMacroInjector(val body: Tree, val macroTree: Tree) extends Transformer {
    def expandMacroTree: Tree = transform(body)

    override def transform(tree: Tree) = {
      tree match {
        case apply: Apply if isRuntimeMacro(apply) => macroTree
        case _ => super.transform(tree)
      }
    }
  }

  object ContextCreator {
    def apply(context: Context) =
      new ContextCreator(context)
  }

  class ContextCreator(context0: Context) {
    var context = context0

    def contextedStats(stats: List[Tree], exprOwner: Symbol = NoSymbol): Unit = {
      val inBlock = exprOwner == context.owner
      def includesTargetPos(tree: Tree) =
        tree.pos.isRange && context.unit.exists && (tree.pos includes context.unit.targetPos)
      val localTarget = stats exists includesTargetPos
      def typedStat(stat: Tree): Unit = {
        stat match {
          case imp @ Import(_, _) =>
            context = context.make(imp)
          case _ =>
            if (localTarget && !includesTargetPos(stat)) {
              // skip typechecking of statements in a sequence where some other statement includes
              // the targetposition
            } else {
              val localContextCreator = if (inBlock || (stat.isDef && !stat.isInstanceOf[LabelDef])) {
                this
              } else ContextCreator(context.make(stat, exprOwner))

              localContextCreator.contexted(stat)
            }
        }
      }

      stats map typedStat
    }

    def contextedTemplate(templ: Template) = {
      val self = templ.self

      if (self.name != nme.WILDCARD)
        context.scope enter self.symbol

      contextedStats(templ.body, templ.symbol)
    }

    def contextedModuleDef(mdef: ModuleDef) = {
      val clazz = mdef.symbol.moduleClass

      ContextCreator(context.make(mdef.impl, clazz, newScope)).contextedTemplate(mdef.impl)
    }

    def contextedClassDef(cdef: ClassDef) = {
      val clazz = cdef.symbol
      reenterTypeParams(cdef.tparams)
      cdef.tparams map (contextedTypeDef)
      ContextCreator(context.make(cdef.impl, clazz, newScope)).contextedTemplate(cdef.impl)
    }

    def reenterTypeParams(tparams: List[TypeDef]): List[Symbol] =
      for (tparam <- tparams) yield {
        context.scope enter tparam.symbol
      }

    def reenterValueParams(vparamss: List[List[ValDef]]) {
      for (vparams <- vparamss)
        for (vparam <- vparams)
          context.scope enter vparam.symbol
    }

    def contextedTypeDef(tdef: TypeDef): Unit =
      if (tdef.tparams.nonEmpty)
        ContextCreator(context.makeNewScope(tdef, tdef.symbol)).contextedTypeDefImpl(tdef)
      else
        contextedTypeDefImpl(tdef)

    private def contextedTypeDefImpl(tdef: TypeDef) = {
      val tparams1 = tdef.tparams map contextedTypeDef
      contexted(tdef.rhs) // typedType ~ typed
    }

    def contextedValDef(vdef: ValDef) = {
      val sym = vdef.symbol
      val valDefContextCreator = {
        val maybeConstrCtx =
          if ((sym.isParameter || sym.isEarlyInitialized) && sym.owner.isConstructor) context.makeConstructorContext
          else context
        ContextCreator(maybeConstrCtx.makeNewScope(vdef, sym))
      }
      valDefContextCreator.contextedValDefImpl(vdef)
    }

    private def contextedValDefImpl(vdef: ValDef) =
      contexted(vdef.rhs)

    final def constrTyperIf(inConstr: Boolean) =
      if (inConstr) {
        ContextCreator(context.makeConstructorContext)
      } else this

    def defDefContextCreator(ddef: DefDef) = {
      val sym = ddef.symbol
      val isConstrDefaultGetter = ddef.mods.hasDefault && sym.owner.isModuleClass &&
        nme.defaultGetterToMethod(sym.name) == nme.CONSTRUCTOR
      ContextCreator(context.makeNewScope(ddef, sym)).constrTyperIf(isConstrDefaultGetter)
    }

    def contextedDefDef(ddef: DefDef) = {
      val meth = ddef.symbol

      reenterTypeParams(ddef.tparams)
      reenterValueParams(ddef.vparamss)

      ddef.tparams map contextedTypeDef
      ddef.vparamss map (_ map contextedValDef)

      contexted(ddef.rhs)
    }

    def contextedBlock(block0: Block) = {
      //for (stat <- block0.stats) enterLabelDef(stat)

      contextedStats(block0.stats, context.owner)
      contexted(block0.expr)
    }
    
    def contextedIf(if0: If) = {
      contexted(if0.thenp) // then part
      contexted(if0.elsep) // else part
    }
    
    def contextedTypeApply(tree: TypeApply) = {
      val TypeApply(fun, args) = tree

      contexted(fun)
      val tparams = fun.symbol.typeParams

      args foreach (contexted(_))
    }
    
    def functionContext(fun: Function) = {
      ContextCreator(context.makeNewScope(fun, fun.symbol)).contextedFunction(fun)
    }
    
    def contextedFunction(fun: Function) = {
      /* probably cases when fun.body is samViable or Match(sel, cases) is not necessary 
       * for processing, tree should be already transformed
       */
      // regular Function
      fun.vparams foreach { vparam =>
        // enterSym(context, vparam) - enter sym to namer
        if (context.retyping) context.scope enter vparam.symbol
      }
      fun.vparams mapConserve contextedValDef // process vparams
      contexted(fun.body) // process body
    }

    def contextedAssign(assign: Assign) = {
      val Assign(lhs, rhs) = assign
      contexted(lhs)
      contexted(rhs)
    }

    def contextedArrayValue(tree: ArrayValue) = {
      val ArrayValue(elemtpt, elems) = tree
      contexted(elemtpt)
      tree.elems mapConserve (contexted(_))
    }

    def labelContextCreator(ldef: LabelDef) = {
      val labelContext = if (ldef.symbol == NoSymbol) { // shouldn't be required for mars
        ContextCreator(context.makeNewScope(ldef, context.owner))
      } else this
      labelContext.contextedLabelDef(ldef)
    }

    def contextedLabelDef(ldef: LabelDef) = contexted(ldef.rhs)

    // return context resulted from tree processing
    def contexted(tree: Tree): Context = {
      printBeforeTree(tree)

      val sym: Symbol = tree.symbol
      tree match {
        case tree @ ModuleDef(_, _, impl) =>
          val moduleContext = context.makeNewScope(tree, sym)
          val newCreator = ContextCreator(moduleContext)
          newCreator.contextedModuleDef(tree)

        case pdef @ PackageDef(pid, stats) =>
          val sym = tree.symbol
          contexted(pid)
          val pdefCont = context.make(tree, sym.moduleClass, sym.info.decls)
          ContextCreator(pdefCont).contextedStats(pdef.stats, NoSymbol)

        case tree: ClassDef =>
          val classContext = context.makeNewScope(tree, sym)
          ContextCreator(classContext).contextedClassDef(tree)

        case tree: TypeDef => contextedTypeDef(tree)

        case tree: ValDef => contextedValDef(tree)

        case tree: DefDef => defDefContextCreator(tree).contextedDefDef(tree)
        
        case ifTree: If => contextedIf(ifTree)
        
        case typeApply: TypeApply => contextedTypeApply(typeApply)
        
        case fun: Function => functionContext(fun)
        
        case assign: Assign => contextedAssign(assign)
        
        case Annotated(fun, _) => contexted(fun) // should be sufficient for runtime macro expansion
        
        case tree: ArrayValue => contextedArrayValue(tree)
        
        case tree: ReferenceToBoxed => contexted(tree.ident)
        
        case ld: LabelDef => contextedLabelDef(ld)

        case tree: Block =>
          val blockContext = context.makeNewScope(tree, context.owner)
          ContextCreator(blockContext).contextedBlock(tree)

        case sup: Super => contexted(sup.qual)

        case select @ Select(qual, _) => contexted(qual)

        case apply @ Apply(fun, args) =>
          // TODO: fix tree in context
          contexted(fun) // fix for args
          // TODO: add args processing
          if (isRuntimeMacro(apply)) {
            applyContextInfo = Option(apply, context)
          }

        case typed: Typed => contexted(typed.expr)  

        case _: New | _: This | _: Literal | _: Ident => // context shouldn't be changed
 
        /* TODO: add processing for other trees (if required):
         * from typedInPatternMode (Alternative, Star) + Bind
         * from typedTypTree (subtrees of TypTree)
         */
        case _ =>
      }
      printScopeInfo(tree)
      context
    }

    def printScopeInfo(tree: Tree) = {
      println(sm"""
      |=============================
      |show(tree): ${show(tree)}
      |
      |showRaw(tree): ${showRaw(tree)}
      |
      |context: $context
      |
      |scope: ${context.scope}"
      |=============================""")
    }

    def printBeforeTree(tree: Tree) = println(s"---> before typed: ${show(tree)}")
  }
}