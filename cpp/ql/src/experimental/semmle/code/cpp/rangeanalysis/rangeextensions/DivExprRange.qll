private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import semmle.code.cpp.rangeanalysis.RangeAnalysisUtils
private import fb.util.range.BinaryOrAssignOperation
private import fb.util.Util

private predicate isIntegralDivExpr(Operation d) {
  hasIntegralType(getLOp(d).getFullyConverted()) and
  hasIntegralType(getROp(d).getFullyConverted())
}

class BinaryOrAssignDivExpr extends BinaryOrAssignOperation {
  BinaryOrAssignDivExpr() {
    (getOperation() instanceof DivExpr or getOperation() instanceof AssignDivExpr) and
    isIntegralDivExpr(getOperation())
  }

  float getLowerBounds() {
    /*
     *        <----------|---------->
     *           neg     0     pos
     * 1. R1 negative, R2 negative
     * 2. R1 negative, R2 crosses
     * 3. R1 negative, R2 positive
     * 4. R1 crosses, R2 negative
     * 5. R1 crosses, R2 crosses
     * 6. R1 crosses, R2 positive
     * 7. R1 positive, R2 negative
     * 8. R1 positive, R2 crosses
     * 9. R1 positive, R2 positive
     * 10. R2 is zero
     */

    exists(DivExprOp l, DivExprOp r, float l1, float u1, float l2, float u2 |
      getLeftOperand() = l and
      getRightOperand() = r and
      l1 = l.getLowerBound() and
      u1 = l.getUpperBound() and
      l2 = r.getLowerBound() and
      u2 = r.getUpperBound() and
      l1 <= u1 and
      l2 <= u2
    |
      // R1 negative, R2 negative (result is positive)
      // Divide the smallest absolute value (u1) by the largest absolute value (l2)
      // l2 = 0 implies u2 = 0, which is covered by the final case
      l1 <= 0 and u1 <= 0 and l2 < 0 and u2 < 0 and result = (u1 / l2).floor().(float)
      or
      // R1 negative, R2 crosses (result is negative)
      // Divide the most negative value by 1
      l1 <= 0 and u1 <= 0 and l2 < 0 and u2 > 0 and result = l1
      or
      // R1 negative, R2 positive (result is negative)
      // Divide the most negative value (l1) by the smallest positive value (l2)
      // If l2 = 0, result = l1 / 1 = l1
      l1 <= 0 and
      u1 <= 0 and
      l2 >= 0 and
      u2 > 0 and
      result = (l1 / l2.maximum(1)).floor().(float)
      or
      // R1 crosses, R2 negative (result is negative)
      // Divide the largest positive value (u1) by the smallest absolute value (u2)
      // If u2 = 0, result = u1 / -1 = -u1
      l1 <= 0 and
      u1 >= 0 and
      l2 < 0 and
      u2 <= 0 and
      result = (u1 / u2.minimum(-1)).floor().(float)
      or
      // R1 crosses, R2 crosses (result is either)
      // Take the largest absolute value, and divide it by either 1 or -1 so it ends up as negative
      l1 < 0 and u1 > 0 and l2 < 0 and u2 > 0 and result = -1 * l1.abs().maximum(u1)
      or
      // R1 crosses, R2 positive (result is negative)
      // Divide the most negative value (l1) by the smallest positive value (l2)
      // If l2 = 0, result = l1 / 1 = l1
      l1 <= 0 and u1 >= 0 and l2 >= 0 and u2 > 0 and result = (l1 / l2.maximum(1)).floor().(float)
      or
      // R1 positive, R2 negative (result is negative)
      // Divide the largest positive value (u1) by the smallest absolute value (u2)
      // If u2 = 0, result = u1 / -1 = -u1
      l1 >= 0 and
      u1 >= 0 and
      l2 < 0 and
      u2 <= 0 and
      result = (u1 / u2.minimum(-1)).floor().(float)
      or
      // R1 positive, R2 crosses (result is negative)
      // Divide the largest positive value (u1) by -1
      l1 >= 0 and u1 >= 0 and l2 < 0 and u2 > 0 and result = -u1
      or
      // R1 positive, R2 positive (result is positive)
      // Divide the smallest positive value (l1) by the largest positive value (u2)
      // u2 = 0 implies l2 = 0, which is covered by the final case
      l1 >= 0 and u1 >= 0 and l2 >= 0 and u2 > 0 and result = (l1 / u2).floor().(float)
      //or
      // R2 is zero (result is negative)
      // NaN or Inf, so just set to min value (unbound)
      //l2 = 0 and u2 = 0 and result = exprMinVal(d)
    )
  }

  float getUpperBounds() {
    /*
     *        <----------|---------->
     *           neg     0     pos
     * 1. R1 negative, R2 negative
     * 2. R1 negative, R2 crosses
     * 3. R1 negative, R2 positive
     * 4. R1 crosses, R2 negative
     * 5. R1 crosses, R2 crosses
     * 6. R1 crosses, R2 positive
     * 7. R1 positive, R2 negative
     * 8. R1 positive, R2 crosses
     * 9. R1 positive, R2 positive
     * 10. R2 is zero
     */

    exists(DivExprOp l, DivExprOp r, float l1, float u1, float l2, float u2 |
      getLeftOperand() = l and
      getRightOperand() = r and
      l1 = l.getLowerBound() and
      u1 = l.getUpperBound() and
      l2 = r.getLowerBound() and
      u2 = r.getUpperBound() and
      l1 <= u1 and
      l2 <= u2
    |
      // R1 negative, R2 negative (result is positive)
      // Divide the largest absolute value (l1) by the smallest absolute value (u2)
      // If u2 = 0, result = l1 / -1 = -l1
      l1 <= 0 and
      u1 <= 0 and
      l2 < 0 and
      u2 <= 0 and
      result = (l1 / u2.minimum(-1)).floor().(float)
      or
      // R1 negative, R2 crosses (result is positive)
      // Divide the most negative value by -1
      l1 <= 0 and u1 <= 0 and l2 < 0 and u2 > 0 and result = -l1
      or
      // R1 negative, R2 positive (result is negative)
      // Divide the least negative value (u1) by the largest positive value (u2)
      // u2 = 0 implies l2 = 0, which is covered by the final case
      l1 <= 0 and
      u1 <= 0 and
      l2 >= 0 and
      u2 > 0 and
      result = (u1 / u2).floor().(float)
      or
      // R1 crosses, R2 negative (result is positive)
      // Divide the most negative value (l1) by the smallest absolute value (u2)
      // If u2 = 0, result = l1 / -1 = -l1
      l1 <= 0 and
      u1 >= 0 and
      l2 < 0 and
      u2 <= 0 and
      result = (l1 / u2.minimum(-1)).floor().(float)
      or
      // R1 crosses, R2 crosses (result is either)
      // Take the largest absolute value, and divide it by either 1 or -1 so it ends up as positive
      l1 < 0 and u1 > 0 and l2 < 0 and u2 > 0 and result = l1.abs().maximum(u1)
      or
      // R1 crosses, R2 positive (result is positive)
      // Divide the largest positive value (u1) by the smallest positive value (l2)
      // If l2 = 0, result = u1 / 1 = u1
      l1 <= 0 and u1 >= 0 and l2 >= 0 and u2 > 0 and result = (u1 / l2.maximum(1)).floor().(float)
      or
      // R1 positive, R2 negative (result is negative)
      // Divide the smallest positive value (l1) by the largest absolute value (l2)
      // l2 = 0 implies u2 = 0, which is covered by the final case
      l1 >= 0 and u1 >= 0 and l2 < 0 and u2 < 0 and result = (l1 / l2).floor().(float)
      or
      // R1 positive, R2 crosses (result is positive)
      // Divide the largest positive value (u1) by 1
      l1 >= 0 and u1 >= 0 and l2 < 0 and u2 > 0 and result = u1
      or
      // R1 positive, R2 positive (result is positive)
      // Divide the largest positive value (u1) by the smallest positive value (l2)
      // If l2 = 0, result = u1 / 1 = u1
      l1 >= 0 and u1 >= 0 and l2 >= 0 and u2 > 0 and result = (u1 / l2.maximum(1)).floor().(float)
      // or
      // R2 is zero (result is negative)
      // NaN or Inf, so just set to max value (unbound)
      // l2 = 0 and u2 = 0 and result = exprMaxVal(d)
    )
  }
}

/**
 * Handles division when both operands are integral types. Because many ranges will still include
 * zero even when there are explicit checks for zero, we only handle the divide by zero case when
 * the range is exactly zero. This means this won't be very useful for catching DoS bugs, but it
 * will be more useful for catching other memory corruption bugs.
 */
class DivExprRange extends SimpleRangeAnalysisExpr {
  BinaryOrAssignDivExpr d;

  DivExprRange() { this = d.getOperation() }

  override float getLowerBounds() { result = d.getLowerBounds() }

  override float getUpperBounds() { result = d.getUpperBounds() }

  override predicate dependsOnChild(Expr child) { child = d.getAnOperand() }
}

class DivExprOp extends Expr {
  BinaryOrAssignDivExpr d;
  float lowerBound;
  float upperBound;

  DivExprOp() {
    this = d.getAnOperand() and
    lowerBound = getFullyConvertedLowerBounds(this) and
    upperBound = getFullyConvertedUpperBounds(this) and
    lowerBound <= upperBound
  }

  float getLowerBound() { result = lowerBound }

  float getUpperBound() { result = upperBound }
}
