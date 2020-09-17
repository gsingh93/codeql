/**
 * Currently any data structure method that returns a value bounded by the length of the string is
 * unconstrained ([0, 18446744073709551615]). This leads to FPs where `len++` can technically
 * overflow, but in practice this will never happen. The classes in this file limit the upper bound
 * to a smaller value, defined by getMaxStringSize().
 */

private import cpp
private import experimental.semmle.code.cpp.models.interfaces.SimpleRangeAnalysisExpr
private import fb.util.Util

private float getMaxContainerSize() {
  result = 2147483646 // INT_MAX - 1
}

/**
 * An abstract class for setting the bounds for specific methods. Mainly used so that the CallRange
 * class ignores these functions
 */
abstract class FunctionCallRange extends SimpleRangeAnalysisExpr { }

class StringMethodRange extends FunctionCallRange {
  FunctionCall c;

  StringMethodRange() {
    this = c and
    hasIntegralType(c) and
    c
        .getTarget()
        .hasQualifiedName("std", "basic_string",
          ["size", "length", "capacity", "find", "rfind", "find_first_of", "find_last_of",
              "find_first_not_of", "last"])
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class FollyRangeRange extends FunctionCallRange {
  FunctionCall c;

  FollyRangeRange() {
    this = c and
    hasIntegralType(c) and
    c.getTarget().hasQualifiedName("folly", "Range", ["size", "walk_size", "find", "find_first_of"])
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class VectorMethodRange extends FunctionCallRange {
  FunctionCall c;

  VectorMethodRange() {
    this = c and
    hasIntegralType(c) and
    c.getTarget().hasQualifiedName("std", "vector", ["size", "capacity"])
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class MapMethodRange extends FunctionCallRange {
  FunctionCall c;

  MapMethodRange() {
    this = c and
    hasIntegralType(c) and
    c
        .getTarget()
        .hasQualifiedName("std", ["unordered_map", "map", "multimap", "unordered_map"], "size")
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class SetMethodRange extends FunctionCallRange {
  FunctionCall c;

  SetMethodRange() {
    this = c and
    hasIntegralType(c) and
    c
        .getTarget()
        .hasQualifiedName("std", ["unordered_set", "set", "multiset", "unordered_multiset"], "size")
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class StdArrayRange extends FunctionCallRange {
  FunctionCall c;
  float size;

  StdArrayRange() {
    this = c and
    hasIntegralType(c) and
    c.getTarget().hasQualifiedName("std", "array", "size") and
    size =
      c.getTarget().getDeclaringType().(Class).getTemplateArgument(1).(Expr).getValue().toFloat()
  }

  override float getLowerBounds() { result = size }

  override float getUpperBounds() { result = size }

  override predicate dependsOnChild(Expr child) { none() }
}

class IOBufRange extends FunctionCallRange {
  FunctionCall c;

  IOBufRange() {
    this = c and
    hasIntegralType(c) and
    c
        .getTarget()
        .hasQualifiedName("folly", "IOBuf",
          ["length", "headroom", "tailroom", "countChainElements", "computeChainDataLength"])
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class CursorRange extends FunctionCallRange {
  FunctionCall c;

  CursorRange() {
    this = c and
    hasIntegralType(c) and
    c
        .getTarget()
        .hasQualifiedName("folly::io::detail", "CursorBase",
          ["getCurrentPosition", "length", "totalLength", "operator-"])
  }

  override float getLowerBounds() { result = 0 }

  override float getUpperBounds() { result = getMaxContainerSize() }

  override predicate dependsOnChild(Expr child) { none() }
}

class CursorAtMostRange extends FunctionCallRange {
  FunctionCall c;

  CursorAtMostRange() {
    this = c and
    hasIntegralType(c) and
    c
        .getTarget()
        .hasQualifiedName("folly::io::detail", "CursorBase",
          ["skipAtMost", "retreatAtMost", "pullAtMost", "cloneAtMost"])
  }

  override float getLowerBounds() { result = getFullyConvertedLowerBounds(c.getArgument(1)) }

  override float getUpperBounds() {
    exists(float upperBound | upperBound = getFullyConvertedUpperBounds(c.getArgument(1)) |
      result = min([upperBound, getMaxContainerSize()])
    )
  }

  override predicate dependsOnChild(Expr child) { none() }
}

/**
 * Matches the following prototype or the `min` equivalent:
 * ```
 * template< class T >
 * const T& max( const T& a, const T& b );
 * ```
 */
private predicate isStdMinMaxCall(FunctionCall c, string name) {
  name in ["min", "max"] and
  c.getTarget().hasQualifiedName("std", name) and
  // TODO: Is stripType correct here?
  c.getUnderlyingType().stripType() instanceof IntegralType and
  c.getArgument(0).getUnderlyingType().stripType() instanceof IntegralType and
  c.getArgument(1).getUnderlyingType().stripType() instanceof IntegralType and
  c.getNumberOfArguments() = 2
}

private predicate getPotentialLowerBounds(FunctionCall c, float lowerBound1, float lowerBound2) {
  lowerBound1 = getFullyConvertedLowerBounds(c.getArgument(0)) and
  lowerBound2 = getFullyConvertedLowerBounds(c.getArgument(1))
}

private predicate getPotentialUpperBounds(FunctionCall c, float upperBound1, float upperBound2) {
  upperBound1 = getFullyConvertedUpperBounds(c.getArgument(0)) and
  upperBound2 = getFullyConvertedUpperBounds(c.getArgument(1))
}

class StdMinRange extends FunctionCallRange {
  FunctionCall c;

  StdMinRange() { this = c and isStdMinMaxCall(c, "min") }

  override float getLowerBounds() {
    exists(float lowerBound1, float lowerBound2 |
      getPotentialLowerBounds(c, lowerBound1, lowerBound2) and
      result = min([lowerBound1, lowerBound2])
    )
  }

  override float getUpperBounds() {
    exists(float upperBound1, float upperBound2 |
      getPotentialUpperBounds(c, upperBound1, upperBound2) and
      result = min([upperBound1, upperBound2])
    )
  }

  override predicate dependsOnChild(Expr child) { child = c.getAnArgument() }
}

class StdMaxRange extends FunctionCallRange {
  FunctionCall c;

  StdMaxRange() { this = c and isStdMinMaxCall(c, "max") }

  FunctionCall getCall() { result = c }

  override float getLowerBounds() {
    exists(float lowerBound1, float lowerBound2 |
      getPotentialLowerBounds(c, lowerBound1, lowerBound2) and
      result = max([lowerBound1, lowerBound2])
    )
  }

  override float getUpperBounds() {
    exists(float upperBound1, float upperBound2 |
      getPotentialUpperBounds(c, upperBound1, upperBound2) and
      result = max([upperBound1, upperBound2])
    )
  }

  override predicate dependsOnChild(Expr child) { child = c.getAnArgument() }
}
