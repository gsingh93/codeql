private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis
private import fb.util.taint.TaintTracking
private import fb.util.taint.config.UserControlledRange
private import fb.util.Util

pragma[inline]
private predicate isAnyArgUserControlled(Call c) {
  any(UserControlledRangeFlow config).hasFlowTo(DataFlow::exprNode(c.getAnArgument()))
}

abstract class ParameterRangeAnalysisExpr extends SimpleRangeAnalysisExpr {
  Parameter p;

  Parameter getParameter() { result = p }
}

// For any access to a function parameter, attempt to compute the bounds
// by looking at the bounds of the arguments at the callsites
class FunctionParameterAccess extends ParameterRangeAnalysisExpr {
  FunctionParameterAccess() {
    this = p.getAnAccess() and
    hasIntegralOrReferenceIntegralType(p) and
    exists(Call c |
      c.getTarget() = p.getFunction() and
      // If any argument to the Call is tainted, we want to propagate all the arguments
      isAnyArgUserControlled(c)
    )
  }

  override float getLowerBounds() {
    // If an argument has the bound [-200, 200], but locally constrains the bound to
    // [0, 200], we want to take the maximum of the potential lower bounds
    exists(RangeSsaDefinition pDefn, float localBound, float argBound |
      this = pDefn.getAUse(p) and
      localBound = getDefLowerBounds(pDefn, p) and
      argBound = any(Arg a | a.getParameter() = p).getLowerBound()
    |
      result = max([argBound, localBound])
    )
  }

  override float getUpperBounds() {
    // If an argument has the bound [-200, 200], but locally constrains the bound to
    // [-200, 0], we want to take the minimum of the potential upper bounds
    exists(RangeSsaDefinition pDefn, float localBound, float argBound |
      this = pDefn.getAUse(p) and
      localBound = getDefUpperBounds(pDefn, p) and
      argBound = any(Arg a | a.getParameter() = p).getUpperBound()
    |
      result = min([argBound, localBound])
    )
  }

  override predicate dependsOnChild(Expr child) { none() }
}

// This is the argument we want to propogate to function parameters.
// We check `Extension::shouldPropogateArgBounds` to see if we should
// propogate or not
class Arg extends Expr {
  Call c;
  int index;
  float lowerBound;
  float upperBound;

  Arg() {
    this = getArgumentOrParameterInitializer(c, index) and
    hasIntegralOrReferenceIntegralType(this) and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound and
    isAnyArgUserControlled(c)
  }

  Parameter getParameter() { result = c.getTarget().getParameter(index) }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}

/**
 * Handles parameters that are defined by reference
 */
class DefinedByReferenceParamRangeExpr extends ParameterRangeAnalysisExpr {
  DefinedByReferenceParamRangeExpr() {
    exists(RangeSsaDefinition defn, Call c, int i, Variable v |
      // Find the SSA definition for the argument to the defining call
      defn.getDefinition() = c.getArgument(i) and
      // Validate that the call passes by reference
      c.passesByReferenceNonConst(i, v.getAnAccess()) and
      // `this` is a use of that definition-by-reference-parameter
      this = defn.getAUse(v) and
      // The parameter which is defining this use
      p = c.getTarget().getParameter(i)
    )
  }

  override float getLowerBounds() {
    exists(RangeSsaDefinition finalDefn |
      // Get the bounds for a range SSA definition on the parameter
      result = getDefLowerBounds(finalDefn, p) and
      // Confirm that the given range definition is valid at the end of the function
      // Note: the function itself is the final basic block, so we're interested in
      //       whether the defn. is live at the end of the previous block
      finalDefn.reachesEndOfBB(p, p.getFunction().getBasicBlock())
    )
  }

  override float getUpperBounds() {
    exists(RangeSsaDefinition finalDefn |
      // Get the bounds for a range SSA definition on the parameter
      result = getDefUpperBounds(finalDefn, p) and
      // Confirm that the given range definition is valid at the end of the function
      // Note: the function itself is the final basic block, so we're interested in
      //       whether the defn. is live at the end of the previous block
      finalDefn.reachesEndOfBB(p, p.getFunction().getBasicBlock())
    )
  }

  override predicate dependsOnChild(Expr child) { none() }
}
