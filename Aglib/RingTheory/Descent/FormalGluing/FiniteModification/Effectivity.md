# Actual finite-model and tensor assembly

`FiniteModification.Effectivity` imports the passed regular-conductor and
torsion suppliers. It constructs actual equalizer and compatible-pair
algebra comparisons, and then combines the constructed regular-conductor
model with the original bounded quotient counits. It does not import back
into either lower module.

The main theorem is `exists_finite_model`. It takes a Noetherian domain
`R`, a Noetherian faithfully flat commutative `R`-algebra `S`, and a finite
commutative `S`-algebra `D`, with the original compatible maps `R→S→D`.
Its coefficient input is an actual ring equivalence `R/I≃S/IS` together
with its required equation on every original class of `r∈R`. Its two power
bounds annihilate the literal kernel of `Algebra.linearMap S D` and the
literal quotient `D/range(Algebra.linearMap S D)`. The scalar map `S→D`
is not assumed injective, and neither a conductor nor coefficient
surjectivity at every ideal power is added as an input.

The theorem constructs a finite commutative `R`-algebra `E` and an actual
`S`-algebra equivalence `S⊗[R]E≃D`, with `s⊗1` mapping to the original
structural image of `s`. For every `f∈I`, the original
`localizationBaseMap f : R[1/f]→E[1/f]` is bijective.

The constructed intermediate theorem
`exists_finite_model_of_regular_conductor` uses the following precise inputs:

- `R` and `S` are Noetherian, `S` is faithfully flat over `R`, and `D` is
  finite as an `S`-module.
- The original structural map `S→D` is injective.
- `I⊂R`, a natural number `n`, and an original `t∈I^n` are specified, and
  `t` acts injectively on `R`.
- For every `s∈(I^n)S` and `z∈D`, the actual product `sz` belongs to the
  original image of `S`.
- For every `m`, the original composite `R→S→S/(I^m)S` is surjective.

It gives the same finite-model, tensor and punctured conclusions. There is
no regularity assumption on the original algebra `D` and no supplied model,
coaction, tensor equivalence, or quotient-compatibility oracle.

## Reduction of the original inputs

`exists_coefficient_correction` raises an error in `JS` to one in `(JI)S`
by correcting its original coefficient inside `J`. Expand the first error
as a finite sum of `a·s`, with `a∈J`, replace each `s` by an original
coefficient modulo `IS`, and collect the resulting source coefficients.
Starting with `J=I^m`, `exists_sub_mem_extendedIdeal_pow` and
`quotient_coefficients_surjective_pow` obtain every required finite-order
coefficient through the same original scalar map. These surjectivity lemmas
need neither flatness nor finite generation of `I`.

For `I≠0`, choose an original nonzero `a∈I`. The kernel power bound and
flatness force the original `S→D` to be injective: a corresponding power
of `a` acts injectively on `S` and annihilates that actual kernel. The
cokernel bound says exactly that each conductor product belongs to the
range of the original structural map, through the kernel of the actual
quotient map. Increase the cokernel exponent `n` to `n+1` and take
`t=a^(n+1)`. This supplies all the intermediate theorem's hypotheses,
with no regularity assertion about `t` on the original `D`.

For `I=0`, use `E=D` with restricted original scalars. The existing
bounded-torsion finite-generation theorem and algebra counit apply to the
zero source ideal. This branch does not require injection `S→D`.
The literal localization quantifier has `f=0`; both localizations are zero
rings, and `localizationBaseMap_zero_bijective` proves the original map
bijective. Thus the zero-ideal case is included in the native statement.

## The actual algebra construction

A finite family generating the original `I^n` retains `t` as its `none`
coordinate. Put `T=Ann_D(t)` and `D0=D/T`. The original conductor products
and regularity on `S` prove that `S→D0` is injective and the same `t` is
regular on `D0`. The existing regular-conductor construction then gives
its actual subalgebra `E0⊂R[1/t]`, original map `ψ0:E0→D0`, and actual
comparison `Θ0:S⊗E0≃D0`. Finiteness is proved by the constructed module
inside the original cross-relation kernel.

Native Artin–Rees chooses `m` so that the actual ideal
`K=((IS)^m)D` satisfies `T∩K=0`. Set `Q=D/K` and `H=D/(T+K)`. The
original extended ideal `(I^m)S` annihilates both quotients. Their actual
scalar-action counits `ΘQ:S⊗Q≃Q` and `ΘH:S⊗H≃H` are therefore algebra
equivalences, and the same coefficient comparison makes `Q` finite over
`R`.

Let `q0:D0→H` and `q1:Q→H` be the original quotient maps. The final algebra
is the actual compatible-pair subalgebra

```
E = {(e,q) ∈ E0 × Q | q0(ψ0(e)) = q1(q)}.
```

Its addition, multiplication, unit and structural map are the inherited
ones. Since it is an actual submodule of the finite product over the
Noetherian source, it is finite over `R`.

## Tensor comparison and original maps

`equalizerTransport` restricts two actual ambient algebra equivalences
along actual commuting maps. `tensorCompatiblePairEquiv` combines the
native flat tensor-equalizer equivalence with the native tensor/product
algebra equivalence. The two original coordinate squares are proved, and
its formula is literally `s⊗(a,b) ↦ (s⊗a,s⊗b)`.

The finite-model proof applies this construction to the displayed `E`.
The constructed `Θ0`, `ΘQ` and `ΘH` satisfy the two required squares by
their actual pure-tensor formulas and the `S`-linearity of `q0,q1`. Thus
`S⊗E` is identified with the actual compatible quotient pairs
`D0×_H Q`. The inverse of the original quotient diagonal identifies those
pairs with `D` because `T∩K=0`. On a pure tensor `s⊗(e,q)`, the two quotient
coordinates of the resulting element of `D` are `sψ0(e)` and `sq`.

For the punctured comparison, `f^nE0⊂R` and `f^mQ=0` imply
`f^(n+m)E⊂R` through the original scalar map. The original map `R→E` is
injective through its first coordinate `R→E0`. Clearing this actual power
of `f` proves that the original localization map is bijective. This also
retains compatibility on intersections of the original distinguished opens.

## Consumer and evidence boundary

`exists_finite_model` is the reviewed original-input entry; the intermediate
regular-source-conductor theorem remains available to direct consumers.
Both include arbitrary conductor torsion on `D`. The completion consumer
can supply its canonical mod-`I` comparison using the existing actual
completion quotient map, or use its already constructed all-power
comparisons at the intermediate entry.

The actual normalization consumer remains conditional on its original
chart-domain and base-change identifications, finite completed normalization
(F1b), and normality away from the closed fibre with the corresponding
original localization/conductor data (F2). Identifying the constructed
finite model with normalization follows after this algebra construction;
it is a separate consumer obligation. No finiteness of the desired descended
normalization is assumed to construct the model.

The mathematical basis is the independently reviewed C2 construction,
Sections 2–7, with the conditional chart application in Section 8. The
broader classical statement is [Stacks Lemma 15.91.17, 0ALK](https://stacks.math.columbia.edu/tag/0ALK).
No proper-scheme or Grothendieck-existence premise occurs in this construction.
Compilation coverage is recorded separately from this mathematical description.
