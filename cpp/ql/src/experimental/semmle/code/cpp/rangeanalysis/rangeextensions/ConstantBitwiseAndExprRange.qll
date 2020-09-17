private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import semmle.code.cpp.rangeanalysis.RangeAnalysisUtils
private import fb.util.Util
private import fb.util.range.BinaryOrAssignOperation

pragma[inline]
private predicate isConstantBitwiseAndExprOp(Expr lOp, Expr rOp) {
  hasIntegralType(lOp) and
  hasIntegralType(rOp) and
  // No operands can be negative constants
  not (evaluateConstantExpr(lOp) < 0 or evaluateConstantExpr(rOp) < 0) and
  // At least one operand must be a positive constant
  (evaluateConstantExpr(lOp) > 0 or evaluateConstantExpr(rOp) > 0)
}

private predicate hasNegativeRange(ConstantBitwiseAndExprOp e) {
  e.getLowerBound() < 0 or e.getUpperBound() < 0
}

class BinaryOrAssignConstantBitwiseAndExpr extends BinaryOrAssignOperation {
  BinaryOrAssignConstantBitwiseAndExpr() {
    (
      getOperation() instanceof BitwiseAndExpr
      or
      getOperation() instanceof AssignAndExpr
    ) and
    hasIntegralType(getOperation()) and
    isConstantBitwiseAndExprOp(getLOp(getOperation()), getROp(getOperation()))
  }

  float getLowerBounds() {
    // This is not the most precise lower bound, but it's good enough for now
    // If both operands can only have positive values, the lower bound is zero
    // If an operand can have negative values, the lower bound is the minimum
    // value of the fully converted type
    exists(ConstantBitwiseAndExprOp l, ConstantBitwiseAndExprOp r |
      l = getLeftOperand() and
      r = getRightOperand() and
      (
        (hasNegativeRange(l) or hasNegativeRange(r)) and
        result = exprMinVal(getOperation())
        or
        // This technically results in two lowerBounds when the an operand range is negative,
        // but that's fine since `exprMinVal(b) <= 0`
        result = 0
      )
    )
  }

  float getUpperBounds() {
    // This is not the most precise upper bound, but it's good enough for now
    // If an operand can have negative values, the upper bound is the maximum
    // value of the fully converted type
    exists(ConstantBitwiseAndExprOp l, ConstantBitwiseAndExprOp r |
      l = getLeftOperand() and
      r = getRightOperand() and
      (
        (hasNegativeRange(l) or hasNegativeRange(r)) and
        result = exprMaxVal(getOperation())
        or
        // This technically results in two upperBounds when the an operand range is negative,
        // but that's fine since `exprMaxVal(b) >= result`
        // Handles [0, 5] & [7, 7] = [0, 5] and [0, 10] & [7, 7] = [0, 7]
        result = r.getUpperBound().minimum(l.getUpperBound())
      )
    )
  }
}

class ConstantBitwiseAndExprRange extends SimpleRangeAnalysisExpr {
  BinaryOrAssignConstantBitwiseAndExpr e;

  ConstantBitwiseAndExprRange() { this = e.getOperation() }

  BinaryOrAssignConstantBitwiseAndExpr getExpr() { result = e }

  Expr getLeftOperand() { result = e.getLeftOperand() }

  Expr getRightOperand() { result = e.getRightOperand() }

  override float getLowerBounds() { result = e.getLowerBounds() }

  override float getUpperBounds() { result = e.getUpperBounds() }

  override predicate dependsOnChild(Expr child) { child = e.getAnOperand() }
}

class ConstantBitwiseAndExprOp extends Expr {
  BinaryOrAssignConstantBitwiseAndExpr b;
  float lowerBound;
  float upperBound;

  ConstantBitwiseAndExprOp() {
    this = b.getAnOperand() and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound
  }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}
