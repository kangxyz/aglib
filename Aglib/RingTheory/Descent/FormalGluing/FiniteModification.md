# Bounded torsion and regular-conductor effectivity

`Aglib.RingTheory.Descent.FormalGluing.FiniteModification` supplies bounded
torsion comparisons, explicit submodule effectivity, the finite
cross-relation conductor ambient, regular-conductor algebra effectivity,
and its original punctured-localization comparisons. The separate upper
torsion module treats the actual torsion quotient and compatible quotient
pairs. The final scalar-extension assembly for arbitrary torsion algebras
and normalization identification remain separate obligations.

Let `R → S` be a homomorphism of commutative rings and let `J` be an ideal of
the **source** ring `R`. Assume that the actual composite

```
R → S → S / J S
```

is surjective. For an actual `S`-module `M`, with its compatible original
`R`-action, assume explicitly that `JS` annihilates `M`.

The main interface in `Algebra.Descent.FormalGluing` is
`torsionTensorEquiv`, an `S`-linear equivalence

```
S ⊗[R] M ≃ₗ[S] M.
```

Its forward map is the original action `s ⊗ m ↦ s • m`; its inverse is
literally `m ↦ 1 ⊗ m`. No flatness, Noetherianity, finiteness of `J`, or
finiteness of `M` is required. `finite_restrictScalars` adds the hypothesis
`Module.Finite S M` and proves `Module.Finite R M`, using the same underlying
module and the same finite set of generating elements. The generic scalar
generation argument is reused from `Module.Finite.of_scalar_actions_lift`;
there is no second implementation of that argument.

`linearMapOfTorsion` makes an original `R`-linear map between two such modules
`S`-linear. Its restriction is the original map. If `D` is a commutative
`S`-algebra annihilated by `JS`, `torsionTensorAlgEquiv` is the actual algebra
equivalence

```
S ⊗[R] D ≃ₐ[S] D,
```

constructed from `Algebra.Descent.counit`. Thus it preserves the unit,
multiplication, and structural map of `S`; its stated tensor and inverse
equations retain the original elements. Applying `finite_restrictScalars`
to `D` gives finiteness of the same algebra over `R` when it is finite over
`S`.

`quotient_coefficients_surjective` accepts an actual ring equivalence
`R/J ≃ S/JS` together with its equation on the original quotient maps and
supplies the coefficient-surjectivity hypothesis. This is the adapter for
the completion-specific comparison; this module does not duplicate its
construction.

The proof writes each `s∈S` as an original coefficient plus an element of
`JS`. The error acts trivially on `M`. In `S ⊗[R] M`, each generator of `JS`
has a factor from `J⊂R`, which moves across the tensor and annihilates `M`.
This proves `s ⊗ m = 1 ⊗ (s • m)` and both inverse identities. It is essential
that `J` is a source ideal: a general target ideal and a surjection onto its
quotient would not justify this tensor calculation.

## Effectivity for a submodule with bounded cokernel

Let `M` now be an arbitrary `R`-module, and let `P` be an `S`-submodule of the
actual tensor product `S ⊗[R] M`. Suppose that

```
J S • (S ⊗[R] M) ≤ P.
```

`unitPreimage P` is the actual `R`-submodule

```
Q = {m : M | 1 ⊗ m ∈ P}.
```

Under the same surjectivity of `R → S/JS`, `unitPreimage_baseChange` proves
`Q.baseChange S = P`. Here `Submodule.baseChange` is the native range of the
base change of the inclusion `Q → M`. The equality needs neither flatness
nor finiteness.

The proof first puts `JM` inside `Q`. Every tensor is a sum of pure tensors;
replace each coefficient by an original coefficient modulo `JS`. Its error
has a factor from `J`, which moves across the tensor, so the error belongs
to `Q.baseChange S`. If the original tensor lies in `P`, the remaining
original-unit tensor lies in `P` as well, hence comes from `Q`.

If `S` is flat over `R`, `unitPreimageTensorEquiv` composes the native
`Submodule.toBaseChange.toLinearEquiv` with that equality to obtain

```
S ⊗[R] Q ≃ₗ[S] P.
```

`unitPreimageTensorEquiv_apply` identifies its forward map with the base
change of the original inclusion, and `unitPreimageTensorEquiv_tmul` states
its value on the original pure tensors. `finite_unitPreimage` proves that
`Q` is finite when `R` is Noetherian and `M` is finite over `R`; no flatness
is needed for this finiteness statement.

The current consumer places an injective finite modification in the base
change of a finite ambient module whose quotient is killed by `J`. This
module theorem then constructs its original module model. The following
cross-relation construction supplies that ambient and the conductor map.

## The finite cross-relation ambient

For a coefficient family `d : ι → R`, `crossRelationMap d` is the actual
linear map with coordinates

```
x ↦ (d i * x j - d j * x i)_(i,j).
```

`crossRelations d` is its native kernel. It consists of the tuples satisfying
`d i * x j = d j * x i`. The map `crossRelationScalars d` sends an original
scalar `r` to `(r * d i)_i`. A regular member of the family makes this scalar
map injective. Each generator times a kernel vector is the scalar vector
of its corresponding coordinate; consequently the ideal generated by the
family times the whole kernel lies in the scalar range.

For a finite index type and Noetherian `R`, `finite_crossRelations` proves
the kernel finite over `R`. `crossRelationMap_baseChange` proves the literal
coordinate square under `R → S`, using the native
`TensorProduct.piScalarRight` maps and the original matrix. Under flatness,
`crossRelationsTensorEquiv` combines that square with
`LinearMap.tensorKerEquiv` to give

```
S ⊗[R] crossRelations d ≃ₗ[S]
  crossRelations (fun i ↦ algebraMap R S (d i)).
```

Its pure-tensor equation identifies coordinate `i` with
`algebraMap R S (x i) * s`. The construction requires neither a field nor
domain or regularity assumptions.

For an actual commutative `R`-algebra `D`, assume that its original
structural map is injective and every `d i • z` belongs to its original
scalar image. `conductorCoordinate` extracts the unique original
coefficient by the inverse equivalence onto that image.
`algebraMap_conductorCoordinate` records the literal multiplication
equation. These maps assemble into

```
conductorMap d : D →ₗ[R] crossRelations d.
```

The conductor map agrees with `crossRelationScalars` on the original ring.
Its image contains the generated ideal times the kernel. It is injective
when one specified generator acts injectively on `D`; that regularity is
explicit. Normality of an arbitrary finite algebra does not supply it.
For the intended normalization consumer it must come from the actual
integral-closure embedding in the fraction or total quotient ring.

These interfaces supply the concrete kernel and original conductor maps
from the regular-conductor proof. Their use over the completed coefficient
ring must retain the displayed coordinate base-change equivalence.

## The actual localization-intersection algebra

`localizationBaseMap t` is the original algebra map
`R[1/t] → S[1/t]`. For faithfully flat `R → S` and `t` regular on `R`,
`exists_scalar_of_localizationBaseMap` proves that a fraction in `R[1/t]`
whose image is an original `S`-scalar is itself an original `R`-scalar.
The proof clears an actual principal denominator and contracts the
resulting principal ideal along the faithfully flat map. It does not
assume either localized ring is a field.

For an injective original map `R → D` and a conductor condition
`tD ⊂ R`, `conductorAwayEquiv` constructs the original localization
isomorphism `R[1/t] ≃ₐ[R] D[1/t]`. Composing its inverse with the actual
map `D → D[1/t]` gives `conductorLocalizationMap`. It is injective when
`t` acts injectively on `D`; no regularity is inferred merely from
normality or finite generation.

Apply this construction to `S → D` and the image of `t∈R`.
`regularConductorSubalgebra` is the actual subalgebra of `R[1/t]` obtained
as the preimage of the conductor localization image of `D` inside
`S[1/t]`. Under regularity on `D`, `regularConductorMap` inverts that
image inclusion and gives its original algebra map to `D`.
`regularConductorMap_localization` retains the literal localization
triangle. `regularConductorBaseChange` is then the canonical algebra map

```
S ⊗[R] regularConductorSubalgebra t →ₐ[S] D,
s ⊗ e ↦ s • regularConductorMap t e.
```

Its unit and multiplication are preserved by construction. The original
scalar, inclusion, and conductor parameters remain explicit in the native
declarations. The following identification proves finiteness of this
subalgebra and bijectivity of this same algebra map.

## Identification with the original-unit kernel

Choose a finite family `d : ι → R` of conductor coefficients and a specified
index `i₀`, with `t=d i₀`. Assume that `t` is regular on `R`, its image in
`S` acts injectively on `D`, the original map `S→D` is injective, and every
`d i • z` belongs to the original image of `S`. Assume `R→S` faithfully
flat. No domain hypothesis on `S` or `D` is used.

`crossRelationFraction d i₀` maps an original kernel vector `x` to
`x i₀/t` in `R[1/t]`. The cross relations give
`d i * crossRelationFraction x=x i`. Thus this map is injective when `t`
is regular, and its image is exactly the fractions whose products by all
`d i` are original scalars. `crossRelationFraction_baseChange` and
`crossRelationFraction_conductorMap` retain the two actual localization
triangles.

`conductorTensorSubmodule` pulls the actual conductor image in the
cross-relation kernel over `S` back through `crossRelationsTensorEquiv`.
`regularConductorKernel` is its actual original-unit preimage. The already
proved conductor bound gives

```
(span (range d)) S • (S ⊗[R] crossRelations d) ≤ conductorTensorSubmodule.
```

`regularConductorKernelMap` is the original fraction map with codomain
restricted to `regularConductorSubalgebra t`. Conversely, for an element
of that subalgebra, each conductor product becomes an original scalar
over `S`; faithful-flat principal membership puts it in `R`. The fraction
range description then gives a unique original kernel vector. Injectivity
of the fraction map over `S` verifies its original-unit membership.
`regularConductorKernelEquiv` is the resulting actual `R`-linear
equivalence. For Noetherian `R`, `finite_regularConductorSubalgebra` proves
that this actual subalgebra is finite as an `R`-module.

If the original map `R→S/(span (range d))S` is surjective,
`regularConductorKernelTensorEquiv` applies the constructed submodule
effectivity theorem and inverts the actual injective conductor map.
Its pure-tensor formula agrees with the original algebra comparison after
the fraction-module equivalence. Consequently
`regularConductorBaseChange_bijective` proves that the previously constructed
algebra map is bijective, and `regularConductorAlgEquiv` packages it as

```
S ⊗[R] regularConductorSubalgebra t ≃ₐ[S] D.
```

`regularConductorAlgEquiv_tmul` retains the formula
`s ⊗ e ↦ algebraMap S D s * regularConductorMap t e`.
Unit and multiplication belong to the original subalgebra and algebra map;
they are not supplied by a coaction or transported from a proposed model.
The finiteness theorem does not require coefficient surjectivity, while the
tensor equivalence does not require Noetherianity. Their joint application
gives the finite algebra model in the regular-conductor case.

## Original punctured localizations and conductor generators

`regularConductorSubalgebra_conductor` proves that the entire original
ideal `J=span(range d)` multiplies the actual subalgebra into the original
scalar image. It is source-span induction from the generator statement.
The structural map `R→E0` is injective because `E0` is the specified
subalgebra of `R[1/t]`, with `t` regular on `R`.

If `f^n∈J`, `regularConductorAwayEquiv` proves that the original map
`R[1/f]→E0[1/f]` is an algebra isomorphism. Its surjectivity uses
`f^n e∈R` for each original `e∈E0`, and its injectivity uses the original
structural injection. The stated equation on original scalars identifies
this equivalence with `localizationBaseMap f`. These maps therefore retain
their original overlap compatibility when used on distinguished opens.

`exists_conductorFamily` starts with an actual finitely generated ideal
`J⊂R` and `t∈J`. It supplies a finite family indexed by `Option (Fin n)`
whose `none` coordinate is exactly `t` and whose generated ideal is exactly
`J`. For a Noetherian source, the original ideal is finitely generated by
the native Noetherian ideal theorem. The construction neither substitutes
another conductor ideal nor changes the chosen conductor element.

The separate [torsion module](FiniteModification/Torsion.md) constructs the
actual `Ann(t)` quotient, Artin–Rees separation, and compatible quotient
algebra. The base module does not import that upper module.

For formal algebra patching under completion base change, set `J=I^n`
after supplying the actual comparison
`R/I^n ≃ S/I^nS`. For a finite modification `S→S'`, the kernel and cokernel
may be killed by an ideal power while `S'` itself is not. The bounded-torsion
theorem therefore applies to those torsion modules, not directly to `S'`.
The regular-conductor construction instead applies to the original algebra
when the chosen conductor is proved regular on it. For the normalization
consumer this regularity must come from the literal integral-closure
embedding into the original fraction or total quotient ring; normality
alone is insufficient. For an arbitrary torsion algebra, the remaining
assembly must apply the constructed regular-conductor model to `D/Ann(t)`,
apply the bounded-torsion counits to `D/K` and `D/(Ann(t)+K)`, and prove the
original tensor comparison for the resulting finite equalizer subalgebra.
The quotient-diagonal theorem supplies the final comparison to `D` only
after that actual scalar-extension square is constructed. A coaction or
existence of the descended algebra has not been introduced as a replacement
premise, and the regular-conductor theorem alone does not close full
finite-modification effectivity.

The mathematical source is [Stacks Section 15.91, 05E5](https://stacks.math.columbia.edu/tag/05E5),
especially Lemmas 15.91.2 and 15.91.3. The stronger modification-descent
result [Lemma 15.91.17, 0ALK](https://stacks.math.columbia.edu/tag/0ALK) uses
extension and gluing effectivity; Remark 15.91.20 retains tensor and algebra
structures. Its surface application is
[Lemma 54.11.6, 0BG9](https://stacks.math.columbia.edu/tag/0BG9).
The module is a partial implementation of that route, independent of proper
Grothendieck existence and of unrestricted exceptional-curve contraction.
