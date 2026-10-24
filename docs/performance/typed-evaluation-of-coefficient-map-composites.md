> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#typed-evaluation-of-coefficient-map-composites) · [Context](original-context.md) · [Case index](README.md) · [Previous record](binary-form-section-and-geometric-point-typing.md) · [Next record](shared-full-preimage-witnesses-for-action-descent.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Typed evaluation of coefficient-map composites

The same typed-transport boundary also applies to evaluating concrete
represented-coefficient pullback equalities. The development provider
`EtaleCohomology/H0/ProperHenselian/Sections` exhausted 200000 elaborator
heartbeats at `whnf` when `ConcreteCategory.congr_hom` specialized the final
concrete unit/comparison composite. The scope owner observed this in
`remote-a435e19647de4064a96b9a7dbadcc452` and
`remote-e7a6a8ffcc8d40558b0e9df7db85b6ad`.

Keep the complete original arrows, input and output as parameters of a generic
helper:

```lean
private theorem eval_composite_of_eq {P Q R : AddCommGrpCat.{v}}
    (p : P ⟶ Q) (q : Q ⟶ R) (r : P ⟶ R) (h : p ≫ q = r)
    (x : P) (y : R) (hr : r x = y) : q (p x) = y :=
  (ConcreteCategory.congr_hom h x).trans hr
```

The concrete use supplies the proved categorical equality and a reflexive
pure represented-output equation. The original pullback, represented-sheaf
base-change isomorphism, coefficient unit and terminal transport are retained;
no concrete inverse-image carrier has to be reconstructed inside evaluation.
The owner recorded one successful provider frontend in 8.17 seconds in
`remote-d28c35d131cf46d6b38802fcabe27be4`, on source SHA-256
`d5e6e1e087d66bd805dab2c0e6d19f91ad4817437c25d4a4adcc52cee6326469`,
without a heartbeat increase. This is evidence for the actual completed
section-comparison provider. Its subsequent proper-henselian H0 and torsor
consumers were not completed by that invocation. These observations extend
the existing typed-transport finding; no matched benchmark or extra run was
introduced for the note.


