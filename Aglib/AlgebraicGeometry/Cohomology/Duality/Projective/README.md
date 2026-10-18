# Original projective trace and Serre pairing

[Trace](Trace.lean) composes the proved original Laurent/Cech comparison
with the existing coefficient residue trace. For a commutative ring `R`, a
finite coordinate type `ι` in the same universe, and a labeling
`e : ι ≃ Fin (n+1)`, `projectiveTraceLinearEquiv` identifies unchanged actual
`Hⁿ(O(-card ι))` with `R`. The residue degree equals `-n-1`. Its forward map
`projectiveTrace` has the literal original all-minus-one coefficient formula
on the enumerated Laurent cycle, with the original cycles quotient and
positive sign. Dimension zero is included.

[Pairing](Pairing.lean) uses native module Ext and native bilinear Yoneda
composition, followed by the unchanged module-Ext/cohomology comparison and
that trace. `projectiveSerrePairing` pairs `Extʲ(M,O(-card ι))` with original
`Hⁱ(M)` when `i+j=n`, using the original structural base-ring actions.
Its coefficient naturality is actual Ext precomposition together with the
original `Sheaf.H.map`. In degree zero, `projectiveTopSerreMap` is literally
`f ↦ projectiveTrace ∘ Hⁿ(f)` on actual structure-linear morphisms.

The trace and these canonical pairings require no field, Noetherianity or
coherence hypothesis. Their definition does not assert perfectness for an
arbitrary coefficient module or arbitrary base ring. The canonical negative-twist
perfectness and coherent field duality results are proved below with their
respective hypotheses.
The separate [Laurent pairing](../README.md) gives the native
finite free monomial calculation identified with these original maps.

The focused Trace leaf passed `1792097747599653000-40503`; Pairing including
native coefficient naturality passed `1792098037339679000-47965`. The lower
residue trace bijectivity passed `1792097605655139000-37695`.

[NegativeTwists](NegativeTwists.lean) identifies actual top cohomology of
every negative integer twist with the existing native supported all-negative
Laurent piece. Its coefficient formula is exactly the original Laurent
weight trace, and its cycle formula uses the original enumerated Laurent
coefficient. The statement includes dimension zero and arbitrary common
geometric universes. The leaf passed `1792098327323069000-53908`.
The original trace/pairing public consumer passed
`1792098116747440000-49405` with only `propext`, `Classical.choice` and `Quot.sound`.

[TwistMaps](TwistMaps.lean) retains original homogeneous polynomial
multiplication into `O(-card ι)`, including the native target-degree equality
map, and its exact Laurent chain map in every degree. [PolynomialTrace](PolynomialTrace.lean)
proves the canonical top Serre map is the original product residue on actual
cycle classes. [MonomialTrace](MonomialTrace.lean) identifies this with the
existing Laurent pairing on the original complementary monomial bases.

[TwistDuality](TwistDuality.lean) extends that exact identity by linearity and
proves native `LinearMap.IsPerfPair` for the canonical pairing between actual
`Hom(O(-m-card ι), O(-card ι))` and unchanged actual `Hⁿ(O(-m-card ι))`, for
every `m : ℕ`, commutative ring `R` and labeling `ι ≃ Fin (n+1)`.
Dimension zero and arbitrary geometric universes are retained. The native
`residueTwistSerreDuality` is `toPerfPair` of that original pairing;
its application is exactly the original trace after `Sheaf.H.map` of the
original module morphism. The proof does not supply a substitute pairing.
The target leaf passed `1792100952203337000-1144`.

[Coproduct](Coproduct.lean) transfers bijectivity of the original top map to
actual finite twist coproducts, using original summand cohomology maps and
native `Sigma.desc`. [Presentation](Presentation.lean) applies Mathlib's native
kernel-diagram isomorphism theorem to the actual represented Hom row and the
represented dual of the original right-exact top-cohomology row.
[TopMapLift](TopMapLift.lean) supplies only native universe adjustments, with
exact `up`/`down` formulas retaining the original canonical top map.

[Top](Top.lean) proves coherent top Serre duality over every Noetherian
commutative base ring: `projectiveTopSerreDuality` identifies original
`Hom(M,O(-card ι))` with `Hom_R(Hⁿ(M),R)`. The actual coherent module uses the
proved two-step presentation with both negative degrees at least `card ι`;
no presentation family or duality premise is supplied. The forward map is
exactly trace after the original coefficient cohomology map, and its
coefficient naturality is recorded. Over a field, the separate
`projectiveTopSerreMap_isPerfPair` theorem upgrades the same pairing to native
perfectness in both inputs, using finiteness and reflexivity of original
cohomology. The Noetherian-ring top-Hom statement and the field perfectness
statement remain distinct. The Top leaf passed `1792102686455569000-30698`.

[Boundary](Boundary.lean) proves exact compatibility of the original Yoneda/trace pairing with the native extension class and original cohomology connecting map, with the native positive sign. [TwistExt](TwistExt.lean) uses the actual twist tensor equivalence and native adjunction on Ext to identify `Ext^q(O(a),O(b))` additively with original `H^q(O(-a+b))`. [Effacement](Effacement.lean) proves that original negative-twist cohomology is concentrated in the top degree, and that finite coproducts of `O(-N)` with `N ≥ card ι` have zero positive Ext into the actual dualizing twist. These prerequisites hold over arbitrary commutative rings and include dimension zero. The higher coherent duality argument retains the field hypothesis needed for exact linear duals.

[HigherStep](HigherStep.lean) applies the original Ext and dual-cohomology exact rows to the canonical pairing. Its sole lower diagram lemma is [the independent-universe linear-map diagram theorem](../../../../Algebra/Module/LinearMap/Exact/README.md). The field assumption supplies extension and exactness of linear functionals; the presentation terms' actual vanishing discharges the remaining conditions.

[Higher](Higher.lean) proves full complementary-degree coherent Serre duality on polynomial projective space over every field. For every `i + j = n`, `projectiveSerrePairing_isPerfPair` proves native two-sided perfectness, `projectiveSerreDuality` identifies original `Extʲ(M,O(-card ι))` with the dual of unchanged `Hⁱ(M)`, and `projectiveSerreCohomologyDuality` gives the opposite duality. The forward formulas are literally the existing Yoneda product, original module-Ext/cohomology comparison and original residue trace. Coefficient naturality uses the original maps. The actual uniform coherent presentation and its kernel are constructed inside the proof; no presentation, resolution, vanishing or duality family is a premise. Arbitrary geometric universes, all fields and dimension zero are retained.

The full Higher leaf passed `1792105567325167000-86284`. The independent public consumer passed `1792105679932958000-87897`, including arbitrary-universe lifted coordinates, both equivalences, native perfectness and dimension zero. All inspected geometric declarations use only `propext`, `Classical.choice` and `Quot.sound`; the lower linear-diagram lemma uses only `propext` and `Quot.sound`. The Noetherian-ring top-Hom theorem remains separate from this field higher-Ext theorem.

[ExtVanishing](ExtVanishing.lean) proves `projectiveDualizingExt_subsingleton_of_gt` for every coherent source and every `q > n`, including dimension zero. Its base case uses the original H⁰ injection, the proved canonical Serre duality and the original Ext exact row; higher degrees use actual coherent presentations. `projectiveDualizingExt_finite` gives finiteness over the original base field in every nonnegative degree. The scope is coherent source modules, without an ambient injective-dimension claim. The final leaf passed `1792106008215864000-92761`.

[SignedBoundary](SignedBoundary.lean) distinguishes the original extension-class composition from Mathlib's signed `Ext.δ`. `projectiveSerrePairing_extδ` keeps the exact factor `Int.negOnePow (j+1)` in the pairing with the original cohomology connecting map. It works over arbitrary commutative rings, with no coherence or field premise, and passed `1792106076971795000-93584`. The independent bounds/sign consumer passed `1792106155567419000-95038`, including arbitrary geometric universes, all-degree Ext finiteness, dimension-zero Ext vanishing, and the original signed map. All inspected declarations use only the standard three axioms.

[Derived](Derived/README.md) extends the same original trace to the actual
bounded-below derived global-section functor over arbitrary commutative
rings. Over a Noetherian base ring, `projectiveDerivedSerreDuality` identifies
every original `Ext^i(M,O(-card ι))`, for coherent module coefficients and
all `i : ℕ`, with Hom from the actual RΓ(M) to `(single_n R)[i]` in the
native derived category. Its forward map is the canonical derived trace
comparison, and its degree-zero homology formula is the original
`projectiveTopSerreMap`. No flatness or perfectness of M, regularity of R,
or field assumption is added. Dimension zero retains higher base-ring Ext.
The same [Derived](Derived/README.md) family now proves
`projectiveDerivedSerreDualityCoefficients` for every native base module J,
with literal target `(single_n J)[i]` and the original coefficient trace as
forward map. No flatness, finiteness, projectivity or injectivity of J is
required. Original source/coefficient naturality, unsigned boundary and
recovery of the ring-coefficient duality through its original unitor are
proved. The final source/public gates are `1792174659383563000-52844` /
`1792175796545791000-68922`, with nine exact standard-axiom checks and no
extra options or warnings. This is polynomial projective space over an
affine Noetherian base. The relative family below supplies the scheme-base
and chosen closed-embedding endpoints with their stated hypotheses;
internal RHom, coefficient complexes and embedding independence remain separate.

[DifferentialTrace](DifferentialTrace.lean) now constructs an actual top-form
Cech residue cycle on polynomial projective space and proves its literal
component formula: the restricted coefficient times the product of original
inverse coordinate ratios times the original differential wedge. Transport
through the SAME top-differential/twisting isomorphism gives the original
all-minus-one Laurent cycle; `differentialResidueCohomologyClass_trace` states
that the OLD projective trace of its actual ordinary cohomology class is
the original coefficient. Source `1792175490728435000-64106` and no-options
public `1792175938121194000-71706` passed nine standard-axiom checks,
including n=0 and the zero ring, without field, Noetherian, nontrivial-ring
or public Fintype assumptions. The relative family below supplies the derived
differential trace. The chosen smooth closed-embedding canonical
identification is supplied independently by [Canonical](Canonical.lean).

[Relative affine trace](Relative/README.md) extends the same normalized trace
to the actual coefficient `(∧ⁿ Ω¹) ⊗ p* N`, for every quasicoherent module
sheaf `N` on an arbitrary affine base. Its top-cohomology equivalence retains
the original coefficient/unit/residue maps and commutes with affine open
restriction. No Noetherianity or flatness of `N` is assumed. The single
canonical open coefficient map has an explicit equation identifying it with
the original restriction adjunct. [Trace/Core](Relative/Trace/Core.lean)
now constructs the actual derived trace over a separated scheme base, with its
coefficient naturality and affine differential formula.
[OpenTrace](Relative/Comparison/OpenTrace.lean) proves its derived open-restriction equation.
The all-degree coherent comparison over a Noetherian separated base, and its
linear transfer through a chosen closed embedding, are also proved for arbitrary
quasicoherent coefficients. Their forward maps retain the same actual trace.
The checked affine formula, original coefficient residue and affine unit laws
supply its normalization, as recorded in the relative family owner.

[Canonical](Canonical.lean) identifies the installed closed-immersion right
adjoint applied to the ambient top differential module with the actual single
in integer degree `n - d` of the smooth source's top differential module.
The normalized local class, generator and frame changes, common refinements,
and ordinary Hom descent determine this isomorphism. It is available over
arbitrary commutative bases, without separation or Noetherianity, and includes
zero rings, empty sources and dimension zero. No global `d ≤ n` premise is
added. [Smooth/Trace](Relative/Smooth/Trace.lean) identifies its transported
comparison with derived pushforward followed by one original trace in every
natural Ext degree. [Smooth](Relative/Smooth.lean) gives the coherent linear
duality over a Noetherian separated base and retains that exact forward formula.
Arbitrary coefficients in the general closed-embedding result retain the actual
right-adjoint object; no arbitrary-coefficient purity or embedding-independence
claim is added.
