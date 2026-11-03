# The original positive exceptional comparison

For an integral locally Noetherian regular scheme `X`, a closed point `x`
with `dim O_X,x = 2`, and the actual full-point blowup `b`, this family
constructs the original map

```text
δ_E : O_X[0] → Rb_* O_X'[0] → Rb_* O(E)[0]
```

and proves it is invertible. The first arrow is the existing structural
derived unit. The second is the native derived image of the original
dualized ideal inclusion. The actual residue field is unrestricted.

`exceptionalPositiveModule` is the structure-linear dual of the original
exceptional kernel ideal. It is the underlying module of the dual of
`pointIdealLine`. `exceptionalPositiveSection` is the existing
`cartierDualIdealSection`; its value at one sends an ideal element to
its original inclusion. Thus this section has its original normalization,
rather than a chosen nonzero scalar multiple.

Tensoring the original ideal sequence by its dual and using the original
evaluation gives `exceptionalPositiveSequence`. Its quotient is the actual
pushforward of `pointNormalLine`, with the original pullback/pushforward
unit as quotient map. The existing exceptional comparison identifies that
line with `O(-1)` on the same projective line over the full residue field.

Positive cohomology vanishes by the native projective-twist theorem.
In degree zero the native endpoint-weight comparison has no weights:
two nonnegative exponents cannot sum to `-1`, and two strictly negative
exponents cannot sum to `-1`. The original affine higher-image comparison
and derived pushforward composition then show that the quotient has zero
derived image under `b`. Applying the original derived functor to the
short exact row makes the derived image of the section invertible.
The existing regular-point blowup structure-sheaf result handles the
first arrow of `δ_E`.

`exceptionalPositiveRho` is the inverse of this particular
`exceptionalPositiveDelta`. Its exported unit equation is

```text
structural derived unit ≫ Rb_*(original section) ≫ rho_E = identity.
```

The companion single-unit formula identifies `δ_E` with the native
derived unit applied to the original ordinary coefficient map. It follows
from the original coefficient-square naturality and the functor identity
law. These equations retain every scalar. On the common isomorphism open, the
structural unit is the identity and the dual ideal section sends `1` to
`1`; hence this normalization induces the original generic identity.
The exported native boundary here is the global unit equation and the
original section evaluation formula.

The current consumer is the corrected one-pole comparison
`L_X' → b*L_X ⊗ O(E)` followed by derived pushforward and the projection
formula. No other exceptional twists, canonical-module identification,
Grauert--Riemenschneider vanishing, or pure-degree-p cohomology bound is
asserted by this family.

## The same rho with a finite locally free parent coefficient

`exceptionalPositiveTensorRho` uses the original parent coefficient `E`, its
actual pullback, and the same positive exceptional module and section. Its
map is exactly the forward source tensor single unit, inverse original
projection formula, the derived target tensor applied to the original rho,
the inverse target tensor single unit, and the original target right unitor.
Only the target tensor single unit needs an invertibility witness; there is
no inverse to the source tensor single unit.

`exceptionalPositiveTensorRho_unit` proves the complete original adjunction
and positive-section insertion equation. It specializes the general section
factorization from `ProjectionFormula/StructureUnit` and the original
rho/delta inverse law. It assumes no desired coefficient square and repeats
no exceptional-cohomology argument. The intended coefficient is the actual
model differential line; an actual global one-pole map can then feed this
rho into the existing proper Serre transpose. That map, its fixed-base
normalization, and the finite-cover trace assembly are separate obligations.
The original scheme module pullback is qualified, and the unit proof retains
explicit endpoints for the same unitors, projection-formula component and
delta/rho maps. Its cancellation uses the original category and functor laws.

The whole owner at source SHA-256
`8cec70f553b7994e0eb7275a653ddc6c11c3a6a161e442ec259aa0d7c216aa42`
passed native `own168`: 64 seconds for the leaf, 73.290 seconds for the graph,
exit 0, with no aggregate guard and the owned process group gone. This accepts
the original coefficient-tensored rho construction and its complete unit law.
It does not establish the global one-pole map, fixed-base canonical
normalization, S1/F1 finite-cover trace assembly, a uniform trace-image scalar,
or the final H1 theorem; those remain separate obligations.
