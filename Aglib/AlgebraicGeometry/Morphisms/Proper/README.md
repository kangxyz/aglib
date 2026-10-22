# Proper graph closures and Chow modifications

This family supplies actual graph closures and proper modifications finite over a finite product of polynomial projective spaces. It uses the existing scheme objects and original morphisms. The separate cohomological consumers now prove proper coherent finiteness; neither the geometric construction nor that finiteness theorem takes a Chow or proper-finiteness family as an input.

[GraphClosure](GraphClosure.lean) takes `f : X → S`, `g : Y → S`, an open `U` of `X`, and an actual `S`-morphism `h : U.toScheme → Y`. Its scheme is exactly the native `Hom.image` of `pullback.lift U.ι h w`; its two projections are the native `imageι` followed by the native fiber-product projections. Pairing these projections recovers `imageι` itself.

If `g` is proper, the original projection `p` to `X` is proper. With the precise additional assumption `[QuasiCompact U.ι]`, `toSourceRestrictIso` identifies the original inverse image of `U` with `U.toScheme`: its forward map is exactly `p ∣_ U`, and its inverse is the original open-immersion lift of `Hom.toImage`. The proof uses the native open dense image of a quasi-compact immersion. Its lift over `U` is a proper open dense section, hence an isomorphism. If `U` is dense, `p` is surjective; this last result does not need quasi-compactness of `U.ι`. Properness of `f` also makes the other projection proper. No Noetherianity, reducedness, field or separated-source hypothesis is imposed on this construction.

## Geometric construction

[AffineImmersion](../../ProjectiveSpace/AffineImmersion.lean) embeds finite-type
affine schemes into actual polynomial projective charts, retaining the original
structural map. Its [affine-open transport](../../ProjectiveSpace/AffineImmersion/Open.lean)
works under local finite type. [DenseAffine](../../Properties/README.md)
supplies finite dense affine covers of every Noetherian scheme, with dense common
intersection; its neighborhood theorem only needs finitely many irreducible
components.

[Chow](Chow/README.md) forms the finite native product of the original graph
closures. `Scheme.Chow.exists_finite_projective_product_modification` constructs,
for every proper `f : X ⟶ Spec R` over a Noetherian commutative ring, a proper
surjective `p : Y ⟶ X`, a finite map `q` to a finite projective product, and a
dense open on which `p` is invertible. The original pair of projections is a
closed immersion. No reducedness, integrality, field or finite-dimensionality
premise is used; the empty source is allowed. This endpoint does not claim
scheme-theoretic dominance or the full separated finite-type Chow theorem.

## Proved cohomological consumers

The [projective base-change comparison](../../ProjectiveSpace/BaseChange/README.md)
works over every commutative ring. The
[projective-product cohomology family](../../Cohomology/Projective/Products/README.md)
then proves bounded coherent derived images along the actual projection towers
and their closed/finite composites. The
[cohomological Chow consumer](../../Cohomology/Proper/Chow/README.md) supplies one
modification, chosen independently of the coefficient, with these bounded
coherent images and finite original cohomology.

The [support-induction step](../../Cohomology/Proper/SupportInduction/README.md)
uses the actual modification-unit cone, including its possible degree `-1`,
ideal-power thickenings of the strict closed boundary and native finite
Postnikov induction. [Proper finiteness](../../Cohomology/Proper/Finiteness/README.md)
performs the Noetherian induction and proves
`Scheme.Cohomology.moduleCohomology_finite_of_proper` for every coherent
coefficient and nonnegative degree over a Noetherian affine base, on the original
`Sheaf.H` with its original structural action. It assumes no proper-finiteness
or support-induction family and no relative flatness.

[Proper higher direct images](../../Cohomology/DirectImage/Proper/README.md)
extends coherence to every locally Noetherian target, which need not be
quasi-compact. This interface does not assert a uniform global derived bound
on such a target. The geometric and cohomological route is guided by
[Stacks, Chow's lemma](https://stacks.math.columbia.edu/tag/02O2) and
[Stacks, proper coherent direct images](https://stacks.math.columbia.edu/tag/02O3);
these references are not formal premises.

[AffineStein](AffineStein.md) factors a proper `f : X ⟶ Y`, over an actual
affine open `V` of a locally Noetherian target, through
`Spec Γ(X, f ⁻¹ᵁ V)`. Its first map is the original open affinization
`(f ⁻¹ᵁ V).toSpecΓ`; its second is induced by the literal `f.app V` followed
by the original affine-chart isomorphism. Their composite is exactly `f ∣_ V`.
The first map is proper and its original structure-sheaf map is an isomorphism;
the second map is finite. The structure-sheaf isomorphism itself needs only
properness and the affine open, through the lower qcqs affinization theorem.
The intermediate scheme is the spectrum of the actual section ring, with no
identification with the raw schematic image or gluing of global factors asserted.

[Birational functions](BirationalFunctions.md) proves `IsIso f.c` for the
original structure-sheaf map of a universally closed dominant morphism between
integral schemes, with normal actual target stalks and an isomorphism on the
actual function fields. Properness is a specialization; no Noetherianity or
flatness is required.

[Connectedness from sections](ConnectedFibres.md) proves that a nonempty scheme
with only trivial idempotents in its actual global-section ring is connected.
It also proves `geometricallyConnected_of_isProper_of_isIso_c`: a proper
surjective morphism over a locally Noetherian target has geometrically connected
actual fibres when `IsIso f.c`. The proof uses the proper affine
[idempotent-image theorem](../../Cohomology/Proper/FibreFormalFunctions.lean)
and actual flat base change. Its birational specialization assumes integral
source and target, locally Noetherian normal target, properness, dominance and
invertibility of the actual function-field map. The reusable
[ordinary pushforward-stalk image theorem](../../Cohomology/Proper/FibreIdempotents.md)
is separate from this direct affine proof.

The [surface isomorphism locus](../../Surfaces/Birational/README.md) is the
maximal actual target open on which a proper dominant birational morphism is
an isomorphism. For a normal Noetherian integral target of dimension at most
two and integral source, its complement is a finite set of closed points.

[FibreDescent](FibreDescent.md) proves
`existsUnique_factor_of_isProper_of_isIso_c` for arbitrary schemes. For proper
surjective `f : X ⟶ Y` with actual `IsIso f.c`, any given `g : X ⟶ Z` that
is pointwise constant on every fibre of `f` factors through a unique actual
scheme morphism `h : Y ⟶ Z` with `f ≫ h = g`. No Noetherianity, normality,
integrality, flatness or separation of `Z` is assumed. This descends a given
map through a given quotient; it does not construct a contraction.

[Finite-fibre birational neighborhoods](QuasiFinite.md) prove that a proper
dominant morphism of integral schemes with normal target and invertible actual
function-field map is an isomorphism over a neighborhood of any finite actual
point fibre. Quasi-finiteness at every point above the target point suffices.
These statements require neither Noetherianity nor source normality, and use
the native proper quasi-finite theorem through its finite-fibre corollary.
