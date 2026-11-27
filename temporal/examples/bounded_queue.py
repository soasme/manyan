"""Generic behavioural Protocol (pure signatures) and concrete RingBuffer refinement."""

from __future__ import annotations

from typing import Annotated, Generic, Optional, Protocol, TypeVar

from temporal import (
    Action,
    Assume,
    Const,
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
)

T = TypeVar("T")
Positive = Annotated[int, Where(lambda x: x > 0)]


class BoundedQueue(Protocol[T]):
    """Abstract behavioural protocol for a bounded FIFO queue (signatures only)."""

    capacity: Const[Positive]
    items: State[tuple[T, ...]]

    positive_capacity: Annotated[Assume, lambda self: self.capacity > 0]
    init: Annotated[Init, lambda self: self.items == ()]
    bounded: Annotated[Invariant, lambda self: 0 <= len(self.items) <= self.capacity]
    eventually_drained: Annotated[
        Property, lambda self: leads_to(len(self.items) > 0, len(self.items) == 0)
    ]

    def push(self, item: T) -> Annotated[
        Action[None],
        Requires(lambda self, item: len(self.items) < self.capacity),
        Ensures(lambda self, item: self.items == old(self.items) + (item,)),
        Modifies("items"),
    ]: ...

    def pop(self) -> Annotated[
        Action[T],
        Requires(lambda self: len(self.items) > 0),
        Ensures(lambda self, result: old(self.items) == (result,) + self.items),
        Modifies("items"),
        WeakFairness(),
    ]: ...


class RingBuffer(Generic[T]):
    """Concrete circular-buffer implementation refining BoundedQueue[T]."""

    capacity: Const[Positive]
    _buf: State[tuple[Optional[T], ...]]
    _head: State[int]
    _size: State[int]

    init: Annotated[
        Init,
        lambda self: (
            self._buf == (None,) * self.capacity and self._head == 0 and self._size == 0
        ),
    ]
    shape_ok: Annotated[
        Invariant,
        lambda self: (
            len(self._buf) == self.capacity
            and 0 <= self._head < self.capacity
            and 0 <= self._size <= self.capacity
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
        Action[None],
        Requires(lambda self, item: self._size < self.capacity),
        Modifies("_buf", "_size"),
    ]:
        tail = (self._head + self._size) % self.capacity
        buf = list(self._buf)
        buf[tail] = item
        self._buf = tuple(buf)
        self._size += 1

    def pop(self) -> Annotated[
        Action[T],
        Requires(lambda self: self._size > 0),
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
