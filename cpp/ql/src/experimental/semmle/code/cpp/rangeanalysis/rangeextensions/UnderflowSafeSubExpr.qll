import semmle.code.cpp.dataflow.DataFlow
import semmle.code.cpp.controlflow.Guards

/**
 * A `SubExpr` that can be inferred to be safe from underflow.
 */
abstract class UnderflowSafeSubExpr extends SubExpr { }

/**
 * An underflow safe `SubExpr` expression of this form:
 * ```
 * uint32_t a = std::min(b, c);
 * sink(c - a); // No underflow, a is guaranteed to be <= c
 * ```
 */
class SafeDueToMinSubExpr extends UnderflowSafeSubExpr {
  SafeDueToMinSubExpr() {
    exists(FunctionCall minCall |
      // Find a call to std::min
      minCall.getTarget().hasQualifiedName("std", "min") and
      // std::min flows to the right operand
      DataFlow::localFlow(DataFlow::exprNode(minCall), DataFlow::exprNode(this.getRightOperand())) and
      exists(SsaDefinition c, StackVariable cv |
        minCall.getAnArgument() = c.getAUse(cv) and
        getLeftOperand() = c.getAUse(cv)
      )
    )
  }
}

/**
 * An abstract class representing a `SubExpr` that is overflow safe due to a guard.
 *
 * Sub-classes should constrain the fields `guardSizeExpr` and `subSizeExpr` to be
 * two expressions that return the same value.
 */
abstract class SafeDueToGuardSubExpr extends UnderflowSafeSubExpr {
  Expr guardSizeExpr;
  Expr subSizeExpr;

  SafeDueToGuardSubExpr() {
    /*
     * Look for this type of pattern:
     * ```
     * if (n <= guardSizeExpr) { // gc
     *   sink(subSizeExpr - n);
     * }
     * ```
     */

    exists(GuardCondition gc, SsaDefinition n, StackVariable sv |
      exists(RelationalOperation relOp, boolean branch |
        relOp = gc and
        gc.controls(getBasicBlock(), branch)
      |
        // n <= size, size - n safe on the true branch
        relOp.getLesserOperand() = n.getAUse(sv) and
        relOp.getGreaterOperand() = guardSizeExpr and
        branch = true
        or
        // size <= n, size - n safe on false branch
        relOp.getGreaterOperand() = n.getAUse(sv) and
        relOp.getLesserOperand() = guardSizeExpr and
        branch = false
      ) and
      // size - n
      getLeftOperand() = subSizeExpr and
      getRightOperand() = n.getAUse(sv)
    )
  }
}

/**
 * An `SubExpr` expression that is overflow safe due to a guard on a function call, e.g.:
 * ```
 * if (n <= size_function()) {
 *  sink(size_function() - n);
 * }
 * ```
 */
class SafeDueToGuardOnFunctionCall extends SafeDueToGuardSubExpr {
  SafeDueToGuardOnFunctionCall() {
    guardSizeExpr.(FunctionCall).getTarget() = subSizeExpr.(FunctionCall).getTarget()
  }
}

/**
 * An `SubExpr` expression that is overflow safe due to a guard on a variable access, e.g.:
 * ```
 * if (n <= size {
 *  sink(size - n);
 * }
 * ```
 */
class SafeDueToGuardOnSsaUses extends SafeDueToGuardSubExpr {
  SafeDueToGuardOnSsaUses() {
    exists(SsaDefinition sizeDefn, StackVariable sizeVariable |
      guardSizeExpr = sizeDefn.getAUse(sizeVariable) and
      subSizeExpr = sizeDefn.getAUse(sizeVariable)
    )
  }
}
