private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import fb.util.Util
private import fb.util.range.BinaryOrAssignOperation

private class BinaryOrAssignSignedMulExpr extends BinaryOrAssignOperation {
  BinaryOrAssignSignedMulExpr() {
    (
      getOperation() instanceof MulExpr
      or
      getOperation() instanceof AssignMulExpr
    ) and
    isSignedType(getOperation().getUnderlyingType())
  }

  float getLowerBounds() {
    exists(SignedMulExprOp l, SignedMulExprOp r, float xLow, float xHigh, float yLow, float yHigh |
      l = getLeftOperand() and
      r = getRightOperand() and
      xLow = l.getLowerBound() and
      xHigh = l.getUpperBound() and
      yLow = r.getLowerBound() and
      yHigh = r.getUpperBound() and
      xLow <= xHigh and
      yLow <= yHigh and
      result = min(float x, float y | x = [xLow, xHigh] and y = [yLow, yHigh] | x * y)
    )
  }

  float getUpperBounds() {
    exists(SignedMulExprOp l, SignedMulExprOp r, float xLow, float xHigh, float yLow, float yHigh |
      l = getLeftOperand() and
      r = getRightOperand() and
      xLow = l.getLowerBound() and
      xHigh = l.getUpperBound() and
      yLow = r.getLowerBound() and
      yHigh = r.getUpperBound() and
      xLow <= xHigh and
      yLow <= yHigh and
      result = max(float x, float y | x = [xLow, xHigh] and y = [yLow, yHigh] | x * y)
    )
  }
}

/**
 * Implements range analysis for multiplication of signed multiplicati (`*` and `*=`). Note that this could lead
 * to an explosion of ranges, as there are four different possibilities for each lower and upper
 * bound, and we need to choose the min/max out of them
 */
class SignedMulExprRange extends SimpleRangeAnalysisExpr {
  BinaryOrAssignSignedMulExpr m;

  SignedMulExprRange() { this = m.getOperation() }

  BinaryOrAssignSignedMulExpr getExpr() { result = m }

  override float getLowerBounds() { result = m.getLowerBounds() }

  override float getUpperBounds() { result = m.getUpperBounds() }

  override predicate dependsOnChild(Expr child) { child = m.getAnOperand() }
}

class SignedMulExprOp extends Expr {
  BinaryOrAssignSignedMulExpr m;
  float lowerBound;
  float upperBound;

  SignedMulExprOp() {
    this = m.getAnOperand() and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound
  }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}
