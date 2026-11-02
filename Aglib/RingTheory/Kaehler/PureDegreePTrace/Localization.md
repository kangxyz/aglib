# Localization of the original integral differential trace

Fix a normal Noetherian domain `A`, its original fraction field `K`, and a
purely inseparable field extension `L/K` of prime degree `p` in characteristic
`p`. Keep the original coefficient ring `Λ`, all displayed scalar towers,
and the original root presentation `h : IsAdjoinRootMonic L (X^p - C a)`.
Assume that `B = integralClosure A L` and the actual exterior module
`M_A = exteriorPower A (n+1) Ω_(A/Λ)` are finite over `A`. The rings may lie
in independent universes.

Let `U ≤ nonZeroDivisors A` and let the original `A`-algebra `D` localize `A`
at `U`. Retain its compatible actual map `D → K`. The public trace theorems
construct the scalar actions `Λ → D` and `D → L` by composition through the
fixed maps. They derive that `D` is a normal Noetherian domain, that the same
`K` is its fraction field, and that

```text
C = integralClosure D L,
M_D = exteriorPower D (n+1) Ω_(D/Λ)
```

are finite over `D`. No localized trace comparison is an input.

## The original maps

`integralClosure.scalarExtensionHom A D L : B →ₐ[A] C` is the literal
inclusion in the same field `L`. Its native algebra structure determines

```text
q : exteriorPower B (n+1) Ω_(B/Λ) → exteriorPower C (n+1) Ω_(C/Λ),
q = mapExterior Λ B C (n+1).
```

For `m = mapExterior Λ A D r`, `mapExteriorBidualLocalization` is exactly

```text
dualMap   = IsLocalizedModule.mapExtendScalars U m (Algebra.linearMap A D) D,
bidualMap = IsLocalizedModule.mapExtendScalars U dualMap
              (Algebra.linearMap A D) D.
```

`mapExteriorBidualLocalization_eq_twice` exports this exact whole constructor
value before evaluating an argument. It retains the original localization and
finite-presentation witnesses. This law needs only commutative coefficient/base/
target rings, Noetherian `A`, the actual compatible algebras and tower, a genuine
`U`-localization, and a finite raw exterior module. It needs no domain, fraction
field or prime-degree hypothesis from the downstream trace laws.

`mapExteriorBidualLocalization_coe_eq_twice` exports the complete underlying
function of that same constructor. It is the function image of the existing
whole LinearMap law over the original independent ring/algebra parameters,
before specializing to actual chart coefficient maps. The bundled law and all
localization/finite witnesses are unchanged. Exact owner `f4c3f5c5` passed the
normal native check (own101, 96s), including the new function companion. Its
actual affine restriction consumer remains unaccepted; this owner pass does
not establish the separate S1 proof/kernel check.

There is no arbitrary bidual comparison or alternate target coefficient.
The construction is available for every degree `r`, including zero. In the
trace laws, `r = n+1` and the target is the literal double dual of `M_D`.

## Two localization laws

`integralClosureRawTrace_localization_comp` is the original square

```text
bidualMap ∘ integralClosureRawTrace(A,K,L,h)
  = integralClosureRawTrace(D,K,L,h) ∘ q,
```

with the displayed restrictions of scalars to `A`. The original `K`, `L`,
prime-degree equality, differential degree and root presentation are the
same on both sides.

`integralClosureRawTrace_localization` identifies the whole localized map:

```text
IsLocalizedModule.mapExtendScalars U q bidualMap D
    (integralClosureRawTrace(A,K,L,h))
  = integralClosureRawTrace(D,K,L,h).
```

The localization of `q` is derived from localization of the literal
integral closure, exterior-form localization and restriction of scalars.
Finite presentation of `M_A` and its actual dual gives localization of the
native `bidualMap`. The latter property is exported as
`mapExteriorBidualLocalization_isLocalizedModule`, without installing a
global instance.

The proof first uses the original localized-evaluation law to identify the
generic value of `bidualMap`. Uniqueness on original evaluations gives the
comparison with the two existing `doubleDualToFraction` maps. Their
injectivity, the original raw-trace generic equation, and functoriality of
the original exterior maps then prove the square. Native localization
extensionality proves the second law. No new height-one or DVR argument is
made, and no reflexivity or torsion-freeness of `M_A` is assumed.

This applies in particular to the actual principal-open localization by a
nonzero element of `A`. Transport to scheme charts, sheaf restriction and
gluing, comparison with canonical proper trace, and an all-model uniform
`H1` bound remain separate geometric consumers. The result does not assert
that later stalk maps are finite or that an arbitrary normal model is
projective.

## Original generic-coordinate comparison

`mapExteriorBidualLocalization_generic` exposes the existing complete comparison
with the two original fraction-field double-dual maps. Its implementation and
all existing consumers are unchanged. The supplied coefficient and fraction-field
actions remain arbitrary compatible actions; no replacement composite action is
installed by this interface. The new actual-chart consumer is
`FiniteCoverTrace.RawChartLocalization.rawChartTrace_localization`.

The public exposure and new geometric consumer are source candidates, not a
native acceptance or performance claim. Earlier acceptance applies to the
unchanged historical source; this changed owner requires its own normal check.
