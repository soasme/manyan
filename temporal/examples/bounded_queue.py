"""Generic behavioural Protocol (pure signatures) and concrete RingBuffer refinement."""

from __future__ import annotations

from typing import Annotated, Generic, Optional, Protocol, TypeVar

from temporal import (
    Action,
    Assume,
    Constant,
    Ensures,
    Init,
    Invariant,
    Model,
    ModelValue,
    Modifies,
    Property,
    Pure,
    Refines,
    Requires,
    State,
    Symmetry,
    WeakFairness,
    Where,
    leads_to,
    old,
    prime,
)

T = TypeVar("T")
Positive = Annotated[int, Where(lambda x: x > 0)]


class BoundedQueue(Protocol[T]):
    """Abstract behavioural protocol for a bounded FIFO queue (signatures only)."""

    capacity: Constant[Positive]
    items: State[tuple[T, ...]]

    positive_capacity: Annotated[bool, Assume(lambda s: s.capacity > 0)]
    init: Annotated[bool, Init(lambda s: s.items == ())]
    bounded: Annotated[bool, Invariant(lambda s: 0 <= len(s.items) <= s.capacity)]
    eventually_makes_space: Annotated[
        bool,
        Property(lambda s: leads_to(len(s.items) == s.capacity, len(s.items) < s.capacity)),
    ]

    def push(self, item: T) -> Annotated[
        None,
        Requires(lambda s, item: len(s.items) < s.capacity),
        Action(lambda s, item: prime(s.items) == s.items + (item,)),
        Modifies("items"),
    ]: ...

    def pop(self) -> Annotated[
        T,
        Requires(lambda s: len(s.items) > 0),
        Action(lambda s: prime(s.items) == s.items[1:]),
        Ensures(lambda s, result: result == old(s.items)[0]),
        Modifies("items"),
        WeakFairness(),
    ]: ...


class RingBuffer(Generic[T]):
    """Concrete circular-buffer implementation refining BoundedQueue[T]."""

    capacity: Constant[Positive]
    _buf: State[tuple[Optional[T], ...]]
    _head: State[int]
    _size: State[int]

    init: Annotated[
        bool,
        Init(
            lambda s: (
                s._buf == (None,) * s.capacity and s._head == 0 and s._size == 0
            )
        ),
    ]
    shape_ok: Annotated[
        bool,
        Invariant(
            lambda s: (
                len(s._buf) == s.capacity
                and 0 <= s._head < s.capacity
                and 0 <= s._size <= s.capacity
            )
        ),
    ]

    def __init__(self, capacity: Positive) -> None:
        self.capacity = capacity
        self._buf = (None,) * capacity
        self._head = 0
        self._size = 0

    @property
    def size(self) -> Pure[int]:
        return self._size

    def push(self, item: T) -> Annotated[
        None,
        Requires(lambda s, item: s._size < s.capacity),
        Action(),
        Modifies("_buf", "_size"),
    ]:
        tail = (self._head + self._size) % self.capacity
        buf = list(self._buf)
        buf[tail] = item
        self._buf = tuple(buf)
        self._size += 1

    def pop(self) -> Annotated[
        T,
        Requires(lambda s: s._size > 0),
        Action(),
        Modifies("_buf", "_head", "_size"),
        WeakFairness(),
    ]:
        item = self._buf[self._head]
        assert item is not None
        buf = list(self._buf)
        buf[self._head] = None
        self._buf = tuple(buf)
        self._head = (self._head + 1) % self.capacity
        self._size -= 1
        return item

    def refines_queue(self) -> Refines[BoundedQueue[T]]:
        """TLA+ refinement mapping: INSTANCE BoundedQueue WITH items <- ..."""
        return Refines(
            capacity=self.capacity,
            items=tuple(
                self._buf[(self._head + i) % self.capacity]
                for i in range(self._size)
            ),
        )


class Elem(ModelValue):
    pass


ELEMS = Symmetry({Elem("e1"), Elem("e2")})

ring_buffer_model = Model(
    RingBuffer,
    constants={"capacity": 3},
    domains={T: ELEMS},
)
