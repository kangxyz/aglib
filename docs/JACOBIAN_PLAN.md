# Curves, Jacobians and étale duality

This research and development plan constructs the Jacobian and its torsion
theory, computes finite-coefficient étale cohomology of curves, proves curve
duality, and then constructs principal polarization and the Weil pairing with
their comparison laws. It follows the library's
[complete-construction rule](ARCHITECTURE.md#complete-abstraction-thin-instances-and-minimal-models)
and [minimal implementation choices](INTERFACES.md#minimal-implementation-choices):
general constructors, maps and laws precede their native geometric instances.
The [implementation view](#implementation-and-open-boundary) below is the single
summary of implemented families and open targets. A planned proof route is an
obligation, not an assertion that its suppliers have been proved.

## Objects and hypotheses

Let `k` be a field and `X : FScheme k` satisfy `Curve.Properties X`: the actual
structural morphism is smooth of relative dimension one, proper and
geometrically connected. Write `g = coherentGenus k X`. Preserve the hypotheses
of each declaration; the initial finite-coefficient computations assume
algebraically closed `k`, `0 < n` and `IsUnit (n : k)`. For a finite set `D` of
closed points, use the actual open immersion `j : U ⟶ X` with image `X − D`.
The affine-complement cardinality target retains `D.Nonempty`.

| Object | Selected realization and scope |
| --- | --- |
| Picard functor | The existing fppf Picard sheaf and one representing scheme `P` on its stated locally Noetherian test site, including nonreduced tests. Functor definitions on all tests do not extend the representability theorem to all tests. |
| Jacobian | The identity component `J = Pic⁰(X/k)` of this same `P`, with its native group law. State intrinsic properties for an arbitrary representative when possible and select a witness once in the curve assembly. A rational point supplies an Abel map, not another Jacobian. |
| Line bundles and divisors | Native `LineBundle`, `PicardGroup` and the selected effective-Cartier-divisor/Hilbert representative, with its universal family and Abel classifying maps. A symmetric-power presentation is added only for an actual comparison. |
| Cohomology and Ext | Existing `Sheaf.H` and Mathlib `Abelian.Ext`, retaining genuinely independent `HasExt` universes. Ordinary constructions use these objects and their original maps. |
| Compact support | `CompactSupport.H j F r = Sheaf.H ((etaleLowerShriek j).obj F) r`, with this completion and immersion fixed. Use the actual module-unit comparison where an Ext expression must be compared with this abelian cohomology. |
| Coefficients and duals | Native constant-ring module sheaves, using `ULift (ZMod n)` where required by the existing universe. Keep their underlying-sheaf, unit, inverse-image and root-sheaf maps. Dualization is over `ZMod n`, including composite `n`. |
| Abelian varieties and torsion | Native group schemes with their stated smoothness, properness, connectedness and projectivity properties, and the actual kernels of multiplication. A basis is a later existence theorem and is not pairing data. |
| Dual and polarization | The identity component of the Picard scheme of the chosen abelian variety, with its rigidified Poincaré bundle and universal property. Discharge translation and rigidification choices at the canonical-polarization boundary. |

The [Picard plan](PICARD_PLAN.md#mathematical-targets-and-acceptance) owns the
representability scope. Generic Ext annihilation can allow `n = 0`. Finite
coefficient geometry retains positivity and invertibility where required.
For noninvertible positive levels, a perfect finite-flat group-scheme pairing
and a perfect pairing of geometric points are distinct conclusions.

## Abelian-scheme ownership

[AbelianScheme](../Aglib/AlgebraicGeometry/AbelianScheme/README.md) owns the
field-specific constructions under `OverField/`, using native group objects.
Their placement does not assert an arbitrary-base theorem. General group and
Picard suppliers and curve-only consequences retain their existing owners.

## Reusable constructions before geometric instances

Build each operation together with the formulas and laws its consumers use.
Prove whole natural-transformation, comparison, mate, composition and
unit/counit identities before evaluation at a coefficient, object or degree.
If evaluation itself carries substantial data, first prove it for variable
categories and functors. A native instance must identify the original carrier,
action and maps and discharge every new comparison or coherence input from
the original geometric data. An unsupplied mathematical premise remains open.

Keep theorem inputs to the objects, maps and conditions used by the proof.
Extract shared constructions as well as proofs to their natural owners; avoid
parallel realizations and copied private arguments. Stable constructors and
expensive independent proofs can occupy separate focused leaves when their
actual consumers and dependency graph justify the split.

| Family | Construction, laws and native consumers |
| --- | --- |
| Additive quotients | For additive commutative groups and a surjection `f : A →+ B` with `n`-divisible kernel, construct `A/nA ≃+ B/nB`, its quotient-class formula and naturality. Prove quotient maps, identity, composition and commuting-square laws for every natural `n`; specialize `B = ℤ` to `ZMod n`. The owners are [quotient groups](../Aglib/GroupTheory/QuotientGroup/Nsmul.lean) and [kernel correction](../Aglib/Algebra/Group/Subgroup/KerSurjective.lean). |
| Degree correction | For surjective `r : A →+ B` and `d : A →+ C` mapping `ker r` onto `C`, prove that `r` restricted to `ker d` is surjective. Geometric degree-one classes and their actual restriction maps then give the Picard instances, without a selected section of `r`. |
| Exact-functor Yoneda calculus | For exact additive `L : C ⥤ D` between abelian categories, construct `Ext_D^r(S, L F) × Ext_C^s(F,G) → Ext_D^(r+s)(S,L G)` by `c.comp (e.mapExactFunctor L)`. Supply the biadditive map, both coefficient naturalities, connecting identities, dual and transposed maps and their squares, with independent source and target Ext universes. See the [generic Ext family](../Aglib/Algebra/Homology/DerivedCategory/Ext/README.md). |
| Composition and adjunction | Prove natural-transformation and exact-composition laws for that same pairing. For `τ : K ≅ P ⋙ Q` and an exact adjunction `P ⊣ R`, source transport uses `τ.inv`; output transport is `τ.hom.app (R.obj B) ≫ Q.map (adj.counit.app B)`. Construct the whole transformation `R ⋙ K ⟶ Q`, its component formula and comparison coherence. Prove counit precomposition followed by `adj.extEquiv` equals the native Ext map of `R`, then derive restriction squares. |
| Annihilation and finite-module algebra | Derive Ext annihilation from `n • 𝟙 = 0` at either endpoint, preservation by additive functors, and named local canonical `ZMod n` actions and linear maps. Separately supply exactness of `Hom_(Z/n)(−, Z/n)`, finite biduality and cardinality facts. The latter are genuine algebraic inputs to perfectness. |
| Intrinsic sheaf operations | Construct the canonical module-unit/cohomology comparison, scalar forgetting, constant-unit and roots inverse image, exact extension by zero/direct image, and their original composition/base-change mates. Prove site/topos laws before scheme evaluation. Use the [module-sheaf](../Aglib/Algebra/Category/ModuleCat/Sheaf/README.md), [coefficient](../Aglib/AlgebraicGeometry/EtaleCohomology/Coefficients/Cohomology.lean) and [exceptional-operation](../Aglib/AlgebraicGeometry/EtaleCohomology/Exceptional/README.md) owners. Coefficients do not depend on Kummer merely for scalar-forgetting fullness. |
| Localization and support | Use one module/abelian localization sequence, its original unit, counit and connecting maps, and extension-by-zero comparisons. Keep the third term on the actual finite closed subscheme. Derive compact-support sequences and finite-point vanishing from the same construction; see [compact support](../Aglib/AlgebraicGeometry/EtaleCohomology/CompactSupport/README.md). |
| General Kummer sequence | Construct the global-unit quotient injection into original H¹, the map to the actual Picard torsion subgroup, their exactness and surjectivity, and the Picard quotient injection into original H². Retain original coefficient inclusion, boundary, Picard comparison, whole pullback squares and identity/composition laws. See [Kummer units](../Aglib/AlgebraicGeometry/EtaleCohomology/Kummer/UnitsQuotient.lean) and [Picard quotients](../Aglib/AlgebraicGeometry/EtaleCohomology/Picard/KummerQuotient.lean). |
| Ideals and point classes | Prove open pullback of ideals, empty-fibre triviality, point ideal/divisor class correspondence, restriction surjectivity and degree-one point classes at their weakest sufficient geometric hypotheses. Use [ideal base change](../Aglib/AlgebraicGeometry/IdealSheaf/BaseChange/OpenRestriction.lean), [point ideals](../Aglib/AlgebraicGeometry/Curves/PointDivisor/IdealClass.lean) and [curve Picard suppliers](../Aglib/AlgebraicGeometry/Curves/README.md#point-classes-and-picard-restriction). |
| Picard and group geometry | Build representability with the actual group law, identity component, base change and tangent comparison; infinitesimal lifting; smooth-group dimension from the identity tangent; and transport by actual translations. Keep the finite-fibre/specialization-chain argument below its multiplication instance. The [Picard family](../Aglib/AlgebraicGeometry/Picard/README.md) supplies the curve assembly. |
| Line bundles and abelian varieties | Construct scheme-theoretic seesaw and rigidity over the nonreduced bases required by cube, cube/square and multiplication pullback laws, degree and finite-flat/étale multiplication, then duality through the rigidified Poincaré bundle. General operations and their laws precede Jacobian specialization. |
| Finite group schemes and pairings | Construct Cartier duality, duality of actual isogeny kernels, Poincaré/Weil pairing, perfectness, functoriality and polarization alternation as group-scheme statements. Add geometric-point and Galois conclusions under their additional hypotheses. |

There is one important dependency boundary. The retained
[A4 multiplication proof](../Aglib/AlgebraicGeometry/Curves/Jacobian/Multiplication.lean)
imports `EtaleCohomology/Finiteness/KummerCurveTorsion`. Hence its instances of
[degree quotients](../Aglib/AlgebraicGeometry/Curves/Picard/DegreeQuotient.lean)
and [open divisibility](../Aglib/AlgebraicGeometry/Curves/Picard/OpenDivisibility.lean)
retain that existing étale-finiteness input. Pure point-degree and open
restriction suppliers have neither this A4 dependency nor a dependency on the
new trace. Their geometric proofs supply the degree-one class directly.
The actual import graph, rather than a universal ordering of geometry before
cohomology, determines this separation.

## Picard scheme and Jacobian

Use the general Picard construction, its precise test site, group law,
section/base-change laws and tangent statements. Shared stalk and ideal-sheaf
constructions belong below Picard. The proper integral dimension-one affine
map to the literal projective line belongs to
[curve projectivity](../Aglib/AlgebraicGeometry/Curves/Projectivity/AffineMap.lean).

For the curve, choose the existing representing witness once. Its identity
component is the same `J` throughout. The Abel morphism and Riemann–Roch
identify its image and degree-zero classes and give properness over
algebraically closed `k`. Retain the degree-stratum sign: Kleiman's Hilbert
polynomial uses the inverse line bundle. The multiplication route gives finite
surjective `[n]` and divisibility of `ker degree` over algebraically closed `k`
when `n` is invertible. It uses finite stalk dimension at the fixed identity
and a specialization-chain criterion; a claim that finite morphisms preserve
global dimension is not a supplier.

Obtain `dim J = g` from a general smooth-group dimension theorem and the
existing Picard cotangent/coherent-genus comparison. For ground-field
conclusions, compare this same representative and identity component under
field extension and descend the required properties. The algebraically closed
degree-zero and multiplication theorems alone do not discharge these
representative/component comparisons.

Projectivity has an independent route: place the proper identity component in
a quasi-projective Picard level and apply proper plus quasi-projective implies
projective. Prove factorization through an actual member of the increasing
open levels. This route needs neither cube nor the torsion-rank calculation.
Its source interfaces are [Kleiman](REFERENCES.md#the-picard-scheme), 5.11,
5.13, 5.19 and 5.24–5.26, and [Stacks](REFERENCES.md#stacksproject), Tag 0BA0;
the representing levels are in
[FineStrata](../Aglib/AlgebraicGeometry/Picard/Representability/FineStrata.lean).

## Curve cohomology and trace

Specialize the general quotients and Kummer constructions using the actual
degree and restriction suppliers. For the proper curve the two equivalences
are `Pic(X)/n ≃+ H²(X, μ_n)` and `Pic(X)/n ≃+ ZMod n`. Their composite in the
appropriate direction gives trace, with the whole-map equation

`trace ∘ Kummer.picardBoundary = curveDegreeMod`.

Thus `trace (Kummer.picardBoundary c) = degree c mod n`, and the boundary of
`O(p)` has trace `1` for a rational point. More generally,
[`Curves.picardQuotientBoundaryAddEquiv`](../Aglib/AlgebraicGeometry/EtaleCohomology/CurveCohomology/Trace.lean#L70)
applies to `k : Type u` with `[Field k] [IsSepClosed k]`, `Y : Scheme.{u}`,
and `p : Y ⟶ Spec (.of k)` with `[LocallyOfFiniteType p] [CompactSpace Y]`,
`topologicalKrullDim Y ≤ 1`, and
`[HasExt.{w} (AbelianSheaf.{u, u + 1} Y)]`. For `n > 0` invertible in both
`k` and `Γ(Y, ⊤)`, it identifies the native Picard quotient with original
`Sheaf.H.{w} (mu Y n) 2` through the original Kummer quotient boundary.
The Ext universe `w` remains independent, with no additional derived model.
This broader supplier does not extend every curve table to that field scope.

The proper table is H⁰ of roots equal to `μ_n(k)`, H¹ equal to the actual
Picard `n`-torsion subgroup, H² identified by trace, and vanishing above degree
two. H⁰ of roots allows every natural `n` over any field. The remaining rows
initially use algebraically closed `k` and positive invertible `n`. Identify
the whole H¹ map, after torsion inclusion, with the original Kummer Picard map.
Transport to constant coefficients through the actual chosen roots/constant
sheaf isomorphism. Preserve `n = 1`; no canonical basis or primitive-root
choice is part of an intrinsic statement that does not need one.

For an open missing a closed point, degree-zero Picard restriction is
surjective; A4 divisibility then gives divisibility of `Pic(U)` and vanishing
of `H^q(U, μ_n)` for `q ≥ 2`. This vanishing does not need a finite complement.
The general unit/Kummer H¹ exact sequence specializes to the same `U`, without
rebuilding its boundary or H¹ maps. For finite closed `D`, including empty
`D`, compose `CompactSupport.rootsAddEquiv` with the same proper trace to get
`H²_c(U, μ_n) ≃+ ZMod n`. The original module/abelian and roots comparisons
supply compatibility under shrinking `U`; changing completion remains separate.

The normalization above is Aglib's. Its
[frame torsor](../Aglib/AlgebraicGeometry/Picard/FrameTorsor.lean) uses
`Isom(L, O)` with scalar postcomposition; SGA uses `Isom(O, L)`.
The torsor-to-H¹ comparison and connecting signs remain to be proved.
Source locators are [Milne LEC](REFERENCES.md#milne2013lecturesetalecohomology),
v2.21, 14.2 (p. 90), 14.5 (p. 92) and 14.12 (p. 97);
[Stacks](REFERENCES.md#stacksproject), 03RN, 03RQ and 03RR;
[SGA 4](REFERENCES.md#sga4tome3), IX 4.7 and XVIII 1.1.3; and
[SGA 4½](REFERENCES.md#sga4half), [Cycle] 1.1.1–1.1.6 and 2.1.2–2.1.5.
These locators do not identify Aglib's trace with the SGA trace.

## Curve duality

Compose generic Yoneda pairing for module lower shriek with the trace on the
original cohomology group. The intended constructible pairing is

`H^r_c(U,F) × Ext^(2-r)_(U,n)(F, μ_n) → H²_c(U, μ_n) → ZMod n`.

For finite locally constant `Z/n`-module sheaves, identify the Ext term with
`H^(2-r)(U, Hom_(Z/n)(F, μ_n))` before stating the corresponding cohomological
perfectness. The module dual is over `Z/n`, rather than a field-linear dual.
The generic unsigned connecting identity has sign `+1`; against Mathlib's
`Ext.delta` on degree `s` it has sign `(-1)^(s+1)`, and the total-degree dual
square uses `(-1)^(d-r)`.

Before native perfectness, supply the following maps and their diagrams:

1. The module compact-support trace and its comparison with abelian trace on
   every map used in the argument.
2. Trace compatibility for a smaller open, using the original lower-shriek
   composition isomorphisms, counits and root pullback, with full coherence.
3. Point purity/local cohomology and the original module-Ext comparison
   `Ext^r_U(i_* (Z/n), μ_n) ≃ H^(r-2)(x, Z/n)` in the applicable degrees,
   including point-class and trace normalization.
4. Finite pushforward and pairing/trace compatibility, with the finite-map or
   finite-étale hypotheses needed by each constituent.
5. Exact dualization into `ZMod n`, and the actual sheaf-dual comparison of
   Milne Lemma 14.21, including local-to-global Ext compatibility.

Then follow [Milne LEC](REFERENCES.md#milne2013lecturesetalecohomology), 14.7,
Steps 0–7 (pp. 94–96): the constant degree-zero and degree-two cases are supplied; degree-one injectivity proceeds from
torsors and a class-killing cyclic cover; the proper case by equal finite
orders; point removal through the single localization sequence and five
lemma; and locally constant coefficients through finite pushforward and exact
sequences. Finiteness suffices for this route; it does not require a Weil
pairing or the rank `2g`. Omitted diagram arguments remain actual obligations.

Retain the constructible extension, Milne 14.20–14.21 (pp. 101–103). Its
reference to *Étale Cohomology*, p. 177, was not checked and is not an imported
proof (**citation needed**). Supply devissage and local comparison, or use
the inspected Artin route with its actual additional derived requirements:
[SGA 4½](REFERENCES.md#sga4half), [Dualité] 1.3, 2.1–2.5, 3.2 and 3.4.
Introduce any derived or cup comparison at its real consumer while retaining
the selected cohomology objects.

## Abelian varieties, multiplication and ranks

The field cube is supplied for projective geometrically integral groups. A stronger relative seesaw would require a scheme-theoretic universal triviality locus and its base-change laws. Fibrewise triviality over a nonreduced base
is insufficient; reduced-base Grauert does not supply that locus. Check the
line-bundle and cohomology suppliers against [Stacks](REFERENCES.md#stacksproject),
0BDP, 0BF0, 0BF2, 0BF3 and 0BF4.

The original cube, square and multiplication pullback laws are supplied for projective geometrically integral field groups. For an abelian variety `A`, put `d = dim A`.
With a symmetric ample line bundle, obtain `deg [n]_A = n^(2d)` for every
positive `n` from Hilbert polynomials or intersection theory. Specialize to
`deg [n]_J = n^(2g)` using the supplied B2 theorem `dim J = g`.
Supply the polynomial-degree/support-dimension theorem and
leading-coefficient/rank scaling. The unrestricted equality
`chi(f^*L^m) = rank(f) * chi(L^m)` for a finite flat map is not the available
degree argument. Relevant source locators are
[Stacks](REFERENCES.md#stacksproject), 0BF7, 0BFA, 0BFG and 0BFH;
[Milne AVs](REFERENCES.md#milne1986abelianvarieties), 7.1–7.2 and 8.2–8.3;
and [Milne AV](REFERENCES.md#milne2008abelianvarietiesnotes), I 6.4 and 7.2.

Use smoothness and the differential of `[n]` for étaleness at invertible `n`.
This branch can proceed from smooth-group dimension and the existing
multiplication differential before cube or the degree formula. Finite flatness and surjectivity for every positive `n` are supplied for projective geometrically integral commutative field groups.

For composite `n`, prove the prime-power/divisor-level kernel cardinalities
required by a general finite-module classification criterion. Annihilation
by `n` and the one cardinality `n^(2g)` alone do not identify the module with
`(Z/n)^(2g)`. Generalize the criterion used by
[rank-two torsion](../Aglib/GroupTheory/Torsion/RankTwo.lean) before the genus
specialization; no resulting basis is canonical. The future curve-rank branch
then has the explicit targets

`H¹(X, Z/n) ≃ (Z/n)^(2g)` and `#H¹(U, Z/n) = n^(2g + #D - 1)`.

These targets initially retain algebraically closed `k`, positive invertible
`n`, and `D.Nonempty` for the affine formula. The latter also needs
localization/purity and the normalized point map, or compact-support
localization followed by duality; the proper Picard/Kummer table alone does
not compute it. [Stacks](REFERENCES.md#stacksproject), 0C1Z and 0AMB, supplies
source locators for this branch, with their actual hypotheses retained.

## Dual abelian variety

Use the same Picard representability technology for a projective abelian
variety `A`, and use the supplied rigidified Poincaré bundle and line-bundle morphism; construct dual homomorphisms, biduality and isogeny laws. Properness and smoothness of
`Pic⁰(A)` need abelian-variety suppliers; curve smoothness B1 does not provide
them. The [inspected preliminary draft](REFERENCES.md#inspected-preliminary-abelian-variety-draft)
(**citation needed**), (6.6), (6.12)–(6.18), pp. 90–96, outlines the selected
coherent-cohomology route.

For that route, supply finiteness and vanishing, `H⁰ = k`, Künneth, the graded
bialgebra laws and the field-extension comparison. Require the Borel–Hopf
graded-**algebra** consequence giving `dim H¹ ≤ dim A`. The stronger
graded-bialgebra splitting asserted in draft (6.12) is not adopted. Its
theorem supplier remains open; an accurate citation does not close it.

Reuse [fppf line-bundle descent](../Aglib/AlgebraicGeometry/Descent/Modules/Fppf/LineBundleStack.lean),
adding the kernel-action/character correspondence and its base-change
coherence. For a supplied isogeny, first identify the actual kernel torsor;
general quotient existence is needed only where a consumer uses it. Prove
that character descent lands in the identity-component Picard functor.
The draft's (7.2)–(7.5), pp. 98–100, does not discharge this last step or its
quotient/descent prerequisites merely by stating the dual-kernel theorem.
Prove the ensuing Poincaré, biduality and homomorphism laws, (7.7)–(7.17),
pp. 100–104, rather than installing them as curve-specific conditional fields.

## Theta, principal polarization and Weil pairing

For `g > 0` over the initial algebraically closed field, or with a specified
rational base point, construct the translated theta locus on the selected
`J` as an actual Cartier divisor. Supply the Abel-map image and fibre,
dimension, flatness/length and ampleness arguments. Over a general field
without that point, the intrinsic theta locus is on `Pic^(g-1)`; translating
it to `J` needs additional data. Handle `g = 0` through the trivial Jacobian,
without using `W_(g-1)` at an invalid bound.

Instantiate the general line-bundle homomorphism and duality laws to prove
autoduality and principal polarization. Prove base-point/translation
independence and descent for the canonical polarization over the ground
field. This does not assert a theta line bundle on `J` defined over that
field. The source is [Milne JVs](REFERENCES.md#milne2021jacobianvarieties),
5.1 and 6.6–6.11, especially the fibre-length argument in 6.7 (p. 22).
Retain its actual Cartier, dimension and flatness requirements; a general
finite-morphism claim `normal target → fibre rank ≤ generic degree` is not
an available replacement.

Construct the Weil pairing first on the actual `n` kernels of an abelian
variety and its dual through Cartier/Poincaré duality. Prove the map,
functoriality, perfectness and dual-isogeny laws, then specialize through a
principal polarization to the Jacobian. Prove alternation, including even
`n`, and the required Galois compatibility. For every positive `n` retain the
finite-flat group-scheme statement; geometric-point perfectness retains the
prime-to-characteristic hypothesis. The existing genus-one
`PerfectWeilPairing`, with a `Fin 2` basis, is a specialized consumer.

The [inspected draft](REFERENCES.md#inspected-preliminary-abelian-variety-draft)
(**citation needed**) locates Cartier duality at (3.21)–(3.24), pp. 41–43;
dual isogeny kernels at (7.5), p. 100; theta groups at (8.1)–(8.6),
pp. 113–115; and the pairing, comparison, functoriality and alternation at
(11.11)–(11.22), pp. 162–168. Its cited quotient, descent, Borel–Hopf and
Riemann–Roch inputs remain separate suppliers. Fact (8.7) is unproved there;
the draft's chapter on Jacobians was not posted. These boundaries remain
visible when selecting the proof chain.

Finally compare the original Yoneda and cup pairings and the actual
Abel–Jacobi/Kummer/Poincaré maps. [SGA 4½](REFERENCES.md#sga4half), [Arcata]
VI (2.3.3), printed p. 70, gives the source formula
`Tr(u cup f_0^*(vbar)) = -v(u)`. Its Cartier-dual/polarization identification,
torsor conventions and boundary/cup/Yoneda signs must be matched to Aglib.
No final formula identifying Aglib's pairing with `-e_n` is asserted.

## Implementation and open boundary

The view below records supported result families on the maintained native
objects. The Ext/coefficient construction and E1–E3 received ordinary
implementation review on fixed candidates; their integrated use retains that
coverage only where source and premise correspondence holds. Scoped native
compilation, source/entry/style checks and standard-foundation audits support
the implemented families on their recorded code bases. Dependency updates
retain that evidence only after affected source and premise correspondence
and incremental checks. These checks do not prove the open suppliers or
close the planned programme.

| Targets | Supported implementation or remaining target |
| --- | --- |
| A1–A3 | **Implemented:** [Picard representation, Abel map, degree strata, identity component and degree-zero identification](../Aglib/AlgebraicGeometry/Curves/README.md). Representation is on locally Noetherian tests over any field; the stated degree-zero/image/properness results retain algebraic closedness. |
| A4 | **Implemented:** [finite surjective multiplication and degree-zero divisibility](../Aglib/AlgebraicGeometry/Curves/Jacobian/Multiplication.lean) over algebraically closed `k` for invertible `n`, with the existing étale-finiteness dependency. |
| B1 | **Implemented:** [curve Picard smoothness](../Aglib/AlgebraicGeometry/Picard/Smooth/Curve.lean), with no rational-point hypothesis in the final curve theorem. |
| E1–E3 | **Implemented:** [original trace, proper table, open vanishing and compact trace](../Aglib/AlgebraicGeometry/EtaleCohomology/README.md), supported by general quotients/Kummer and geometric point/restriction providers. Trace is normalized to Aglib's boundary; rank and SGA-sign comparison remain open. |
| E4 | **Implemented:** [compact-support cohomology and localization](../Aglib/AlgebraicGeometry/EtaleCohomology/CompactSupport/README.md) on the original extension by zero, with finite-complement and point-term comparisons. Purity is a separate target. |
| E5, D1 | **Implemented formal constructions:** [generic Ext calculus](../Aglib/Algebra/Homology/DerivedCategory/Ext/README.md), canonical module/abelian comparison, and [native pairings and coherence](../Aglib/AlgebraicGeometry/EtaleCohomology/Duality/README.md). The module trace comparisons and exact finite-module dualization are supplied; geometric perfectness remains open. |
| B2 | **Source supplied:** same `P,R,J` smoothness, geometric integrality and `dim J = g` over every field, through the original cotangent/H1 comparison. |
| B3–B4 | **Field source supplied:** normalized and rigidified families, projective geometrically integral group cube, square and multiplication laws; the unrestricted relative cube remains open. |
| B5 | **Projectivity source supplied over every field:** same `P,R,J` through Picard levels and properness descent. Numerical multiplication degree remains open. |
| B6–B7 | **Partial source supplied:** positive multiplication on the original `J` is finite, flat and surjective over every field; at invertible levels it is finite étale and surjective. The all-divisor torsion criterion is supplied. Numerical degree, geometric divisor-level cardinalities and cohomology ranks remain open. |
| D2–D6 | **Partial source supplied:** module trace and smaller-open compatibility, exact finite-module dualization, finite biduality, and constant-coefficient perfectness in degrees 0 and 2 with transposes, for finite complement including empty and positive invertible `n`. Degree-one and general lcc perfectness, purity, finite-pushforward compatibility and lcc internal-Hom/Ext comparison remain open. |
| D7 | **Open:** constructible devissage/local comparison, with the unchecked Milne EC reference and alternative Artin route kept explicit. |
| W1 | **Partial source supplied:** the same rigidified Poincaré pair and original line-bundle morphism, with their displayed field and locally Noetherian classification bounds. Dual properness and smoothness, biduality, isogeny and character-descent laws remain open. |
| W2–W3 | **Open:** [Cartier theta geometry, canonical principal polarization and general Weil pairing](#theta-principal-polarization-and-weil-pairing), with all-positive-level group-scheme and prime-to-characteristic point conclusions distinguished. |
| W4 | **Open:** original-map and sign comparison of Yoneda, cup, Kummer, Abel–Jacobi, Cartier and polarization constructions. |

## Work order and source obligations

The current consumer determines which lower construction is needed next.
Smooth-group dimension and Jacobian projectivity can advance independently
of finite-coefficient duality. Exact module duality, purity, finite
pushforward and trace coherence precede native perfectness. Seesaw/cube,
multiplication degree and the dual/finite-group-scheme branches support ranks
and principal/Weil pairing results; Weil pairing is not a prerequisite for
the chosen curve-duality route. Close original-map/sign comparisons at their
actual consumers. Separably closed-field extensions of the initial curve
tables, arithmetic applications and ℓ-adic limits are later scopes.

Use the [owning bibliography](REFERENCES.md#curves-jacobians-and-étale-duality)
and the exact versions and locators above. Source inspection and accurate
metadata do not prove imported mathematics. In particular, preserve the
nonreduced seesaw, leading-term degree, graded-algebra Borel–Hopf,
identity-component character descent, Cartier theta and sign obligations.
The preliminary draft's bibliography remains **citation needed**. Inaccessible
Mumford and Howe attributions remain unchecked and are not adopted as proof
suppliers. No new argument or source repair is supplied by this plan.
