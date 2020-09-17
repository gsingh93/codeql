private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import fb.util.taint.TaintTracking
private import fb.util.Util
private import fb.util.taint.config.UserControlledRange
private import fb.util.range.ContainerMethodRange

pragma[inline]
private predicate isReturnExprUserControlled(Expr e) {
  any(UserControlledCallRangeFlow config).hasFlowTo(DataFlow::exprNode(e))
}

// If a call returns an integral type, the range should be the range of the return statement
class CallRange extends SimpleRangeAnalysisExpr {
  Call c;

  CallRange() {
    this = c and
    not this instanceof FunctionCallRange and
    hasIntegralType(c) and
    c.getTarget().getUnspecifiedType() instanceof IntegralType and
    // The function body must exist
    exists(c.getTarget().getBlock()) and
    exists(ReturnStmt r |
      r.getEnclosingFunction() = c.getTarget() and
      isReturnExprUserControlled(r.getExpr())
    )
  }

  Function getTarget() { result = c.getTarget() }

  override float getLowerBounds() {
    result = any(ReturnExprRange r | r.getEnclosingFunction() = c.getTarget()).getLowerBound()
  }

  override float getUpperBounds() {
    result = any(ReturnExprRange r | r.getEnclosingFunction() = c.getTarget()).getUpperBound()
  }

  override predicate dependsOnChild(Expr child) { none() }
}

class ReturnExprRange extends Expr {
  float lowerBound;
  float upperBound;

  ReturnExprRange() {
    exists(ReturnStmt r, Function f |
      hasIntegralType(f) and
      f.getUnspecifiedType() instanceof IntegralType and
      r.getEnclosingFunction() = f and
      r.getExpr() = this
    ) and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound and
    isReturnExprUserControlled(this)
  }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}
