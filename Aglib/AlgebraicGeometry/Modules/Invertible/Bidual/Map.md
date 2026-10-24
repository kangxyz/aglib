# Original sheaf maps and bidual evaluation

For an actual module-sheaf map `h : M -> N`, `doubleDualMap h` applies
the original internal-Hom precomposition map twice. Evaluation is
natural for this map:

```text
bidualMap M >> doubleDualMap h = h >> bidualMap N.
```

The proof evaluates both sides on every smaller open and uses the
original restriction equation of `h`. It does not replace the internal
Hom or the evaluation by an isomorphic abstract model.

If the target is a genuine line bundle `L`, its original evaluation is
already proved invertible. Thus `extendToBidualLine L h` is the double
dual of the original map followed by the inverse of that evaluation.
Its defining compatibility is

```text
bidualMap M >> extendToBidualLine L h = h.
```

The current consumer first constructs a raw one-pole differential map
by height-one extension and proves the target's local rank-one property.
This family then extends that constructed map to the actual source
double dual. It supplies the normalization equation, without assuming
the geometric map or identifying either coefficient with a canonical
module.
