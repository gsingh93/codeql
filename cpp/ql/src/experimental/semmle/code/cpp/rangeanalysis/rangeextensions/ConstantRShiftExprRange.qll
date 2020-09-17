private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import semmle.code.cpp.rangeanalysis.RangeAnalysisUtils
private import fb.util.Util
private import fb.util.range.BinaryOrAssignOperation

pragma[inline]
private predicate isConstantRShiftExprOp(Expr lOp, Expr rOp) {
  hasIntegralType(lOp) and
  hasIntegralType(rOp) and
  (
    // constant or non-constant l-op and constant r-op
    exists(float constROp |
      constROp = evaluateConstantExpr(rOp) and isValidShiftExprShift(constROp, lOp)
    )
    or
    // constant l-op and non-constant r-op
    exists(evaluateConstantExpr(lOp)) and not exists(evaluateConstantExpr(rOp))
  )
}

class BinaryOrAssignConstantRShiftExpr extends BinaryOrAssignOperation {
  BinaryOrAssignConstantRShiftExpr() {
    (
      getOperation() instanceof RShiftExpr
      or
      getOperation() instanceof AssignRShiftExpr
    ) and
    hasIntegralType(getOperation()) and
    isConstantRShiftExprOp(getLOp(getOperation()), getROp(getOperation()))
  }

  float getLowerBounds() {
    exists(
      ConstantRShiftExprOp l, ConstantRShiftExprOp r, int lLowerBound, int lUpperBound,
      int rLowerBound, int rUpperBound
    |
      l = getLeftOperand() and
      r = getRightOperand() and
      lLowerBound = l.getLowerBound().(int) and
      lUpperBound = l.getUpperBound().(int) and
      rLowerBound = r.getLowerBound().(int) and
      rUpperBound = r.getUpperBound().(int) and
      lLowerBound <= lUpperBound and
      rLowerBound <= rUpperBound
    |
      if
        lLowerBound < 0
        or
        not (isValidShiftExprShift(rLowerBound, l) and isValidShiftExprShift(rUpperBound, l))
      then
        // We don't want to deal with shifting negative numbers at the moment,
        // and a negative shift is implementation defined, so we set to the minimum value
        result = exprMinVal(getOperation())
      else
        // We can get the smallest value by shifting the smallest bound by the largest bound
        result = lLowerBound.bitShiftRight(rUpperBound)
    )
  }

  float getUpperBounds() {
    exists(
      ConstantRShiftExprOp l, ConstantRShiftExprOp r, int lLowerBound, int lUpperBound,
      int rLowerBound, int rUpperBound
    |
      l = getLeftOperand() and
      r = getRightOperand() and
      lLowerBound = l.getLowerBound().(int) and
      lUpperBound = l.getUpperBound().(int) and
      rLowerBound = r.getLowerBound().(int) and
      rUpperBound = r.getUpperBound().(int) and
      lLowerBound <= lUpperBound and
      rLowerBound <= rUpperBound
    |
      if
        lLowerBound < 0
        or
        not (isValidShiftExprShift(rLowerBound, l) and isValidShiftExprShift(rUpperBound, l))
      then
        // We don't want to deal with shifting negative numbers at the moment,
        // and a negative shift is implementation defined, so we set it to the maximum value
        result = exprMaxVal(getOperation())
      else
        // We can get the largest value by shifting the largest bound by the smallest bound
        result = lUpperBound.bitShiftRight(rLowerBound)
    )
  }
}

/*
 * This handles the `>>` and `>>=` operators when at least one operand is a constant (and if the
 * right operand is a constant, it must be "valid" (see `isValidShiftExprShift`)). When handling any
 * undefined behavior, it leaves the values unconstrained. From the C++ standard: "The behavior is
 * undefined if the right operand is negative, or greater than or equal to the length in bits of the
 * promoted left operand. The value of E1 >> E2 is E1 right-shifted E2 bit positions. If E1 has an
 * unsigned type or if E1 has a signed type and a non-negative value, the value of the result is the
 * integral part of the quotient of E1/2^E2. If E1 has a signed type and a negative value, the
 * resulting value is implementation-defined."
 *
 * In most cases of undefined behavior, compilers do something reasonable that we may be able to
 * model, but we can revisit this if it becomes necessary.
 *
 * Note that the implementation of `getLowerBound` and `getUpperBound` can be made more precise
 * with more work, but we won't worry about this unless we notice it's necessary in practice
 */

class ConstantRShiftExprRange extends SimpleRangeAnalysisExpr {
  BinaryOrAssignConstantRShiftExpr s;

  ConstantRShiftExprRange() { this = s.getOperation() }

  BinaryOrAssignConstantRShiftExpr getExpr() { result = s }

  Expr getLeftOperand() { result = s.getLeftOperand() }

  Expr getRightOperand() { result = s.getRightOperand() }

  override float getLowerBounds() { result = s.getLowerBounds() }

  override float getUpperBounds() { result = s.getUpperBounds() }

  override predicate dependsOnChild(Expr child) { child = s.getAnOperand() }
}

class ConstantRShiftExprOp extends Expr {
  BinaryOrAssignConstantRShiftExpr s;
  float lowerBound;
  float upperBound;

  ConstantRShiftExprOp() {
    this = s.getAnOperand() and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound
  }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}
