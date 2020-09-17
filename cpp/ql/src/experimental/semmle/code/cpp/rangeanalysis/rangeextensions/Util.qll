/**
 * Some utility functions. The optimizer wasn't inlining things I was expecting,
 * so I inlined most things to be safe
 */

private import cpp
private import semmle.code.cpp.rangeanalysis.SimpleRangeAnalysis

/**
 * If the argument at `index` exists for `Call c`, return that. Otherwise, if
 * the function has a default parameter at that index, return that.
 */
pragma[inline]
Expr getArgumentOrParameterInitializer(Call c, int index) {
  if exists(c.getArgument(index))
  then result = c.getArgument(index)
  else result = c.getTarget().getParameter(index).getInitializer().getExpr()
}

// If the constant right operand is negative or is greater than or equal to the number of
// bits in the left operands type, then the result is undefined. Note however that on IA-32,
// this is actually defined, as the shift value is masked with 0b00011111, but we don't
// assume we're running on IA-32. If this leads to too many FPs, we can change it
bindingset[val]
pragma[inline]
predicate isValidShiftExprShift(float val, Expr lOp) {
  val >= 0 and
  // We use getFullyConverted because we the spec says to use the *promoted* left operand
  val < (lOp.getFullyConverted().getUnderlyingType().getSize() * 8)
}

predicate isSignedType(IntegralType t) { t.isSigned() }

pragma[inline]
predicate hasIntegralType(Locatable e) {
  // We use `getUnspecifiedType` here because without it things like `const size_t` aren't
  // considered to be integral
  e.(Expr).getUnspecifiedType() instanceof IntegralType or
  e.(Parameter).getUnspecifiedType() instanceof IntegralType or
  e.(Function).getUnspecifiedType() instanceof IntegralType
}

pragma[inline]
predicate hasIntegralOrReferenceIntegralType(Locatable e) {
  exists(Type t |
    t = e.(Expr).getUnspecifiedType() or
    t = e.(Parameter).getUnspecifiedType()
  |
    if t instanceof ReferenceType then t.stripType() instanceof IntegralType else hasIntegralType(e)
  )
}

pragma[inline]
string getExprBoundAsString(Expr e) {
  if exists(lowerBound(e)) and exists(upperBound(e))
  then result = "[" + lowerBound(e) + ", " + upperBound(e) + "]"
  else result = "[unknown range]"
}

Expr getLOp(Operation o) {
  result = o.(BinaryOperation).getLeftOperand() or
  result = o.(Assignment).getLValue()
}

Expr getROp(Operation o) {
  result = o.(BinaryOperation).getRightOperand() or
  result = o.(Assignment).getRValue()
}

pragma[inline]
float evaluateConstantExpr(Expr e) {
  result = e.getValue().toFloat()
  or
  // This handles when a constant value is put into a variable
  // and the variable is used later
  exists(SsaDefinition defn, StackVariable sv |
    defn.getAUse(sv) = e and
    result = defn.getDefiningValue(sv).getValue().toFloat()
  )
}
