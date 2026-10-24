> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#why-a-short-proof-can-be-expensive) · [Context](original-context.md) · [Case index](README.md) · [Previous record](étale-derived-comparisons-share-the-equation-then-specialize.md) · [Next record](methods-and-evidence.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Why a short proof can be expensive

The kernel checks the elaborated proof and its type. In particular, it checks
definitional equality by reduction: two expressions can denote the same object
while requiring extensive unfolding to recognize that equality. An `Eq.refl`
proof can therefore be small while checking its use against the declared
equality is expensive. With nested functors, complexes and data-carrying category
instances, the important difference may be an implicit object argument or the
representation of a component's codomain.

The pinned [kernel implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/kernel/type_checker.cpp)
also compares proof types when applying proof irrelevance. Proof irrelevance
does not make conversion of those types free. Distinguish this work from
metavariable unification in the elaborator and from compiling executable code.

