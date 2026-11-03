# Function fields and generic maps

[Basic](Basic.lean) uses the canonical `X.fromSpecStalk (genericPoint X)` and Mathlib function field. For an integral scheme it proves the actual image point, nonempty-open preimages, quasi-compactness and the specified section/germ comparison. No normality, Noetherianity or dimension bound is used.

[Normalization](Normalization.lean) proves that the generic inclusion of an integral scheme with integrally closed stalks has the original scheme as normalization. For a smooth structural morphism `p : Y ⟶ X` and an integral structural morphism `q : Z ⟶ X` (`IsIntegralHom q`), it extends an actual generic-fibre map uniquely to an `X`-morphism `Y ⟶ Z`. No intrinsic integrality condition on `Y` or `Z` is imposed. [Finite-etale generic restriction](../Morphisms/FiniteEtale/GenericFiber.lean) consumes this general extension.

These source migrations retain their recorded R5 inputs and canonical maps.
Source correspondence and native validation have separate evidence boundaries;
see the [recorded checkpoints](../../../docs/WORK_PLAN.md).

[Map](Map.lean) constructs actual dominant pullback and structural field constants from generic stalks and global germs, with their original naturality equations. [BaseChange](BaseChange.lean) transports that same map along field base change when the actual pullback remains integral. [GenericFiber](GenericFiber.lean) constructs the actual generic-fibre lift and proves it invertible for a finite dominant map of integral schemes, without Noetherianity, normality, separability or dimension assumptions. No second generic inclusion or finite-generic-fibre family predicate is defined.

[StalkMap](StalkMap.lean) extends the existing native [Map](Map.lean) with
`Scheme.functionFieldMap_stalk` and `Scheme.functionFieldUnitMap`. They use the
same actual generic stalk map, require integral source/target and dominance,
and impose no finite, smooth, Noetherian or dimension condition. The incoming
`FunctionField.Constants` and `.BaseChange` families reuse native [Map](Map.lean) and
[BaseChange](BaseChange.lean) directly; no second implementation or old namespace is created.

[Dedekind generic fibres](DedekindGenericFiber.md) construct the actual generic
lift for an integral scheme dominant over the spectrum of a Dedekind domain.
The pullback projection is dominant without assuming that the generic fibre is
integral. `DedekindGenericFiberIntegral` proves integrality of that same fibre;
the canonical function-field equivalence retains its structural-constants
triangle and original scalar actions. The separate
[DVR open-immersion theorem](../Stalk/GenericFiber/DVROpen.md) concerns the actual
fraction-field spectrum map and needs no properness or characteristic condition.

[SectionRange](SectionRange.md) characterizes regular sections on a nonempty
open of an integral scheme by membership in all original stalk images in
its function field. [Trace](Trace.md) constructs affine finite-morphism
trace for a finite dominant morphism of integral schemes with normal target;
[Trace/Sheaf](Trace/Sheaf.md) glues its original field-trace values into
`finiteStructureTrace`. [Transport](Trace/Transport.md) transports field
trace through the original commuting birational square.
[Coordinates](Trace/Coordinates.md) constructs the original trace-coordinate
and adjugate sheaf maps for the fixed finite field basis and discriminant,
with their scalar composite identities; separability supplies injectivity
where required. These feed the finite separable surface H1 bound and do not
assert a global canonical-module trace.

[OpenSquare](OpenSquare.lean) compares the original function-field maps
across a commuting open square, retaining the displayed hypotheses and
transporting finite-dimensionality and finrank through those maps.

## Finite and radicial maps of the original generic fields

[Finite](Finite.lean) owns `Scheme.functionFieldMap_finite` for finite dominant
maps of integral schemes, through the original generic-fibre isomorphism.
`Curves/Isogeny/Etale` imports this lower owner. [FiniteRadicial](FiniteRadicial.lean)
passes universal injectivity to that same function-field map and proves it
purely inseparable. No normality, perfection, characteristic or Noetherian
hypothesis is added.

[Scalars](Scalars.lean), [AffineScalars](AffineScalars.lean) and
[BirationalCharts](BirationalCharts.lean) retain generic coefficients
through the original dominant birational field map and actual nonempty
affine charts. The specified fraction field and its scalar tower are
compared through the inverse of that same field map.
[LocalSpectrum](LocalSpectrum.lean) and its
[Cartesian comparison](LocalSpectrum/BaseChange.lean) retain the original
stalk-spectrum field map and projection square.
[FlatPreimmersion](FlatPreimmersion.lean) identifies the original generic
map for a flat preimmersion; [Restriction](Restriction.lean) obtains a
field-map isomorphism from an actual nonempty isomorphism open.
[StalkInjection](StalkInjection.lean) proves injectivity of every original
stalk map for a dominant map of integral schemes, without properness,
normality, finite type or a dimension bound.
