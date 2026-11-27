"""Standalone pure function contracts and reusable refined type aliases."""

from __future__ import annotations

from typing import Annotated, Optional

from temporal import Ensures, Pure, Requires, Where, implies

NonNegative = Annotated[int, Where(lambda x: x >= 0, "non-negative")]
SortedInts = Annotated[
    tuple[int, ...],
    Where(
        lambda xs: all(xs[i] <= xs[i + 1] for i in range(len(xs) - 1)),
        "sorted in non-decreasing order",
    ),
]


def integer_sqrt(n: NonNegative) -> Annotated[
    Pure[NonNegative],
    Ensures(lambda n, result: result * result <= n < (result + 1) * (result + 1)),
]:
    """Return floor(sqrt(n)) for non-negative integer n."""
    lo, hi = 0, n
    while lo <= hi:
        mid = (lo + hi) // 2
        if mid * mid <= n:
            lo = mid + 1
        else:
            hi = mid - 1
    return hi


def binary_search(
    xs: SortedInts,
    target: int,
) -> Annotated[
    Pure[Optional[NonNegative]],
    Ensures(
        lambda xs, target, result: (
            (result is None and target not in xs)
            or (result is not None and 0 <= result < len(xs) and xs[result] == target)
        )
    ),
]:
    """Return an index where xs[i] == target, or None if target is absent."""
    lo, hi = 0, len(xs) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if xs[mid] == target:
            return mid
        if xs[mid] < target:
            lo = mid + 1
        else:
            hi = mid - 1
    return None


def clamp(
    value: int,
    low: int,
    high: int,
) -> Annotated[
    Pure[int],
    Requires(lambda low, high: low <= high, "valid interval"),
    Ensures(
        lambda value, low, high, result: (
            low <= result <= high
            and implies(value < low, result == low)
            and implies(value > high, result == high)
            and implies(low <= value <= high, result == value)
        )
    ),
]:
    """Clamp value to the closed interval [low, high]."""
    if value < low:
        return low
    if value > high:
        return high
    return value
