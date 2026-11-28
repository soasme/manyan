"""Bank account with signature-level contracts, refined types, ghost state, and action invariants."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Annotated, ClassVar

from temporal import (
    Action,
    ActionInvariant,
    Assume,
    Constant,
    Domain,
    Ensures,
    Ghost,
    Init,
    Invariant,
    Model,
    Modifies,
    Preserves,
    Pure,
    Requires,
    State,
    Unchanged,
    Where,
    prime,
)

Positive = Annotated[int, Where(lambda x: x > 0, "positive integer")]
NonNegative = Annotated[int, Where(lambda x: x >= 0, "non-negative integer")]


@dataclass
class BankAccount:
    owner: Constant[str]
    credit_limit: Constant[NonNegative] = 0
    balance: State[int] = 0
    ledger: Ghost[tuple[int, ...]] = ()

    valid_owner: ClassVar[Annotated[bool, Assume(lambda s: s.owner != "")]]
    init: ClassVar[Annotated[bool, Init(lambda s: s.balance == 0 and s.ledger == ())]]
    within_limit: ClassVar[Annotated[bool, Invariant(lambda s: s.balance >= -s.credit_limit)]]
    ledger_matches_balance: ClassVar[
        Annotated[bool, Invariant(lambda s: sum(s.ledger) == s.balance)]
    ]
    ledger_append_only: ClassVar[
        Annotated[
            bool,
            ActionInvariant(
                lambda s: (
                    len(prime(s.ledger)) >= len(s.ledger)
                    and prime(s.ledger)[: len(s.ledger)] == s.ledger
                )
            ),
        ]
    ]

    @property
    def available(self) -> Pure[NonNegative]:
        return self.balance + self.credit_limit

    def deposit(self, amount: Positive) -> Annotated[
        None,
        Action(
            lambda s, amount: (
                prime(s.balance) == s.balance + amount
                and prime(s.ledger) == s.ledger + (amount,)
            )
        ),
        Preserves(lambda s: s.balance >= -s.credit_limit),
        Modifies("balance", "ledger"),
    ]:
        self.balance += amount

    def withdraw(self, amount: Positive) -> Annotated[
        Positive,
        Requires(
            lambda s, amount: amount <= s.balance + s.credit_limit,
            "sufficient funds",
        ),
        Action(
            lambda s, amount: (
                prime(s.balance) == s.balance - amount
                and prime(s.ledger) == s.ledger + (-amount,)
            )
        ),
        Ensures(lambda s, amount, result: result == amount),
        Modifies("balance", "ledger"),
        Unchanged("owner", "credit_limit"),
    ]:
        self.balance -= amount
        return amount


small_account_model = Model(
    BankAccount,
    constants={"owner": "alice", "credit_limit": 2},
    domains={
        "deposit.amount": Domain.range(1, 3),
        "withdraw.amount": Domain.range(1, 3),
    },
    state_constraint=lambda s: len(s.ledger) <= 4,
)
