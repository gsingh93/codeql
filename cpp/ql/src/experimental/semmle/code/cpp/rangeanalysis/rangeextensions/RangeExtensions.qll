private import cpp
private import fb.util.taint.TaintTracking
private import fb.util.taint.TaintTracking2
private import fb.util.range.CallRange
private import fb.util.range.ConstantBitwiseAndExprRange
private import fb.util.range.ConstantLShiftExprRange
private import fb.util.range.ConstantRShiftExprRange
private import fb.util.range.DivExprRange
private import fb.util.range.SignedMulExprRange
private import fb.util.range.ContainerMethodRange
private import fb.util.range.InterProcRange
private import fb.util.Util

// Display the ranges of expressions in the path view if possible
private class ExprRangeNode extends DataFlow::ExprNode {
  pragma[inline]
  private string getIntegralBounds(Expr arg) {
    if hasIntegralOrReferenceIntegralType(arg)
    then result = getExprBoundAsString(arg)
    else result = ""
  }

  private string getOperationBounds(Operation e) {
    result =
      getExprBoundAsString(e) + " = " + getExprBoundAsString(getLOp(e)) +
        e.(Operation).getOperator() + getExprBoundAsString(getROp(e))
  }

  private string getCallBounds(Call e) {
    result =
      getExprBoundAsString(e) + "(" +
        concat(Expr arg, int i |
          arg = e.(Call).getArgument(i)
        |
          getIntegralBounds(arg) order by i, ","
        ) + ")"
  }

  override string toString() {
    exists(Expr e | e = getExpr() |
      if hasIntegralOrReferenceIntegralType(e)
      then
        exists(getOperationBounds(e)) and result = super.toString() + ": " + getOperationBounds(e)
        or
        exists(getCallBounds(e)) and result = super.toString() + ": " + getCallBounds(e)
        or
        not exists(getOperationBounds(e)) and
        not exists(getCallBounds(e)) and
        result = super.toString() + ": " + getExprBoundAsString(e)
      else result = super.toString()
    )
  }
}

// Display the ranges for parameters in the path view if possible
private class ParameterRangeNode extends DataFlow::ExplicitParameterNode {
  private string getFunctionParameterAccessString() {
    // While this may not be accurate due to the parameter being reassigned to or modified, in most
    // cases the correct bound of the parameter is the most unconstrained bound of any of its
    // accesses
    exists(float uBound, float lBound |
      uBound =
        max(any(ParameterRangeAnalysisExpr e | e.getParameter() = asParameter()).getUpperBounds()) and
      lBound =
        min(any(ParameterRangeAnalysisExpr e | e.getParameter() = asParameter()).getLowerBounds()) and
      result = super.toString() + ": [" + lBound + ", " + uBound + "]"
    )
  }

  override string toString() {
    if hasIntegralOrReferenceIntegralType(asParameter())
    then
      if exists(getFunctionParameterAccessString())
      then result = getFunctionParameterAccessString()
      else result = super.toString() + ": [unknown range]"
    else result = super.toString()
  }
}

private class ReferenceArgumentRangeNode extends DataFlow::DefinitionByReferenceNode {
  override string toString() {
    if hasIntegralOrReferenceIntegralType(asDefiningArgument())
    then result = super.toString() + ": " + getExprBoundAsString(getArgument())
    else result = super.toString()
  }
}
