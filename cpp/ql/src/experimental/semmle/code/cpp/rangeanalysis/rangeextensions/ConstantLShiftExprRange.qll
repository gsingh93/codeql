private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import semmle.code.cpp.rangeanalysis.RangeAnalysisUtils
private import fb.util.Util
private import fb.util.range.BinaryOrAssignOperation

pragma[inline]
private predicate isConstantLShiftExprOp(Expr lOp, Expr rOp) {
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

bindingset[val, shift, max_val]
predicate canLShiftOverflow(int val, int shift, int max_val) {
  // val << shift = val * 2^shift > max_val => val > max_val/2^shift = max_val >> b
  val > max_val.bitShiftRight(shift)
}

class BinaryOrAssignConstantLShiftExpr extends BinaryOrAssignOperation {
  BinaryOrAssignConstantLShiftExpr() {
    (
      getOperation() instanceof LShiftExpr
      or
      getOperation() instanceof AssignLShiftExpr
    ) and
    hasIntegralType(getOperation()) and
    isConstantLShiftExprOp(getLOp(getOperation()), getROp(getOperation()))
  }

  float getLowerBounds() {
    exists(
      ConstantLShiftExprOp l, ConstantLShiftExprOp r, int lLowerBound, int lUpperBound,
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
        // and a negative shift is undefined, so we set to the minimum value
        result = exprMinVal(getOperation())
      else
        // If we have `0b01010000 << [0, 2]`, the max value for 8 bits is 0b10100000
        // (a shift of 1) but doing a shift by the upper bound would give 0b01000000.
        // So if the left shift operation causes an overflow, we just assume the max value
        // If necessary, we may be able to improve this bound in the future
        if canLShiftOverflow(lUpperBound, rUpperBound, exprMaxVal(getOperation()).(int))
        then result = exprMinVal(getOperation())
        else result = lLowerBound.bitShiftLeft(lLowerBound)
    )
  }

  float getUpperBounds() {
    exists(
      ConstantLShiftExprOp l, ConstantLShiftExprOp r, int lLowerBound, int lUpperBound,
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
        // and a negative shift is undefined, so we set it to the maximum value
        result = exprMaxVal(getOperation())
      else
        // If we have `0b01010000 << [0, 2]`, the max value for 8 bits is 0b10100000
        // (a shift of 1) but doing a shift by the upper bound would give 0b01000000.
        // So if the left shift operation causes an overflow, we just assume the max value
        // If necessary, we may be able to improve this bound in the future
        if canLShiftOverflow(lUpperBound, rUpperBound, exprMaxVal(getOperation()).(int))
        then result = exprMaxVal(getOperation())
        else result = lUpperBound.bitShiftLeft(rUpperBound)
    )
  }
}

/*
 * This handles the `<<` and `<<=` operators when at least one operand is a constant (and if the right operand
 * is a constant, it must be "valid" (see `isValidShiftExprShift`)). When handling any undefined behavior, it
 * leaves the values unconstrained. From the C++ standard: "The behavior is undefined if the right
 * operand is negative, or greater than or equal to the length in bits of the promoted left operand.
 * The value of E1 << E2 is E1 left-shifted E2 bit positions; vacated bits are zero-filled. If E1
 * has an unsigned type, the value of the result is E1 × 2 E2, reduced modulo one more than the
 * maximum value representable in the result type. Otherwise, if E1 has a signed type and
 * non-negative value, and E1 × 2 E2 is representable in the corresponding unsigned type of the
 * result type, then that value, converted to the result type, is the resulting value; otherwise,
 * the behavior is undefined."
 *
 * In most cases of undefined behavior, compilers do something reasonable that we may be able to
 * model, but we can revisit this if it becomes necessary.
 *
 * Note that the implementation of `getLowerBound` and `getUpperBound` can be made more precise
 * with more work, but we won't worry about this unless we notice it's necessary in practice
 */

class ConstantLShiftExprRange extends SimpleRangeAnalysisExpr {
  BinaryOrAssignConstantLShiftExpr s;

  ConstantLShiftExprRange() { this = s.getOperation() }

  BinaryOrAssignConstantLShiftExpr getExpr() { result = s }

  Expr getLeftOperand() { result = s.getLeftOperand() }

  Expr getRightOperand() { result = s.getRightOperand() }

  override float getLowerBounds() { result = s.getLowerBounds() }

  override float getUpperBounds() { result = s.getUpperBounds() }

  override predicate dependsOnChild(Expr child) { child = s.getAnOperand() }
}

class ConstantLShiftExprOp extends Expr {
  BinaryOrAssignConstantLShiftExpr s;
  float lowerBound;
  float upperBound;

  ConstantLShiftExprOp() {
    this = s.getAnOperand() and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound
  }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}
