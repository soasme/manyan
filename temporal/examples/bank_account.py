"""Bank account demonstrating contracts, refined types, ghost state, and action invariants."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Annotated

from temporal import (
    Action,
    ActionInvariant,
    Assume,
    Const,
    Ensures,
    Ghost,
    Init,
    Invariant,
    Model,
    Modifies,
    Pure,
    Requires,
    State,
    Unchanged,
    Where,
    old,
    prime,
)

Positive = Annotated[int, Where(lambda x: x > 0, "positive integer")]
NonNegative = Annotated[int, Where(lambda x: x >= 0, "non-negative integer")]


@dataclass
class BankAccount:
    owner: Const[str]
    credit_limit: Const[NonNegative] = 0
    balance: State[int] = 0
    ledger: Ghost[tuple[int, ...]] = ()

    def valid_owner(self) -> Assume:
        return len(self.owner) > 0

    def init(self) -> Init:
        return self.balance == 0 and self.ledger == ()

    def within_limit(self) -> Invariant:
        return self.balance >= -self.credit_limit

    def ledger_matches_balance(self) -> Invariant:
        return sum(self.ledger) == self.balance

    def ledger_append_only(self) -> ActionInvariant:
        return (
            len(prime(self.ledger)) >= len(self.ledger)
            and prime(self.ledger)[: len(self.ledger)] == self.ledger
        )

    @property
    def available(self) -> Pure[NonNegative]:
        return self.balance + self.credit_limit

    def deposit(self, amount: Positive) -> Annotated[
        Action[None],
        Ensures(
            lambda self, amount: (
                self.balance == old(self.balance) + amount
                and self.ledger == old(self.ledger) + (amount,)
            )
        ),
        Modifies("balance", "ledger"),
    ]:
        self.balance += amount

    def withdraw(self, amount: Positive) -> Annotated[
        Action[Positive],
        Requires(
            lambda self, amount: amount <= self.balance + self.credit_limit,
            "sufficient funds",
        ),
        Ensures(
            lambda self, amount, result: (
                self.balance == old(self.balance) - amount
                and self.ledger == old(self.ledger) + (-amount,)
                and result == amount
            )
        ),
        Modifies("balance", "ledger"),
        Unchanged("owner", "credit_limit"),
    ]:
        self.balance -= amount
        return amount


small_account_model = Model(
    BankAccount,
    constants={"owner": "alice", "credit_limit": 2},
    domains={int: range(1, 4)},
    state_constraint=lambda s: len(s.ledger) <= 4,
)
