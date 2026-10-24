# Finite-support enlargement with a coefficient-valued trace

[Enlargement.lean](Enlargement.lean) proves the algebraic part of canonical
generation using the actual scheme-module evaluation, actual cohomology
maps and a specified coefficient-valued trace. The geometric choice of a
regular hyperplane section and the resulting quotient-degree calculation
remain separate inputs.

Let \(X\) be a scheme over the specified scalar field \(k\), with its
original ring homomorphism \(\alpha:k\to\Gamma(X,\mathcal O_X)\).
The abbreviations H0 and H1 are the objects of the existing
moduleCohomologyFunctorOfHom X α in degrees zero and one. They keep the
native Sheaf.H objects and coefficient maps, including the action of
\(\alpha\).

Let \(V\) be the specified one-dimensional \(k\)-module. The comparison
inputs are an original trace equivalence
\[
\tau:H^1(X,W)\simeq_k V
\]
and coherent-source bijections
\[
D_T:\operatorname{Hom}_X(T,W)
 \simeq\operatorname{Hom}_k(H^1(X,T),V)
\]
satisfying the original forward-map law
\[
D_T(f)(x)=\tau(H^1(f)(x)).
\]
The bijections may be obtained as the underlying equivalences of linear
Serre comparisons, but their displayed forward law is required. An
arbitrary isomorphism of one-dimensional spaces is not a substitute for
the trace. No orientation \(V\simeq k\) is chosen.

For the chosen-embedding curve consumer,
\(W=\texttt{cmCurveCoefficientCanonicalModule}\ k\ \iota\ j\ n\ V\),
the actual coefficient-valued Serre producer must supply these comparisons
and the same trace. This module does not construct that producer or infer
it from a unit-coefficient theorem.

## Original finite support and splitting

HasFiniteClosedSupport names finitely many distinct closed points and
requires the original additive stalks to vanish outside them. It contains
no cohomology, splitting or generation conclusion. The existing
[finite-support cohomology](../../../../Support/Finite.lean) supplies higher
vanishing and the H0-to-supporting-stalks equivalence.
finiteSupport_isZero_of_H0 combines that equivalence with joint stalk
detection of zero. Subobjects, quotients and the intermediate cokernels
retain their actual finite support.

For an original short exact row
\[
0\longrightarrow W\xrightarrow a B\longrightarrow T\longrightarrow0
\]
with finite closed support of \(T\), splitting_originalRow proves that
nonzero \(H^1(B)\) forces a splitting of this same row. The actual
cohomology row makes \(H^1(a)\) surjective. Since \(H^1(W)\simeq V\) has
dimension one, this is an isomorphism. The inverse Hom/H1 comparison
applied to \(\tau\circ H^1(a)^{-1}\) constructs the retraction, and the
forward-map law proves its retraction equation. Native
ShortComplex.Splitting.ofExactOfRetraction then supplies the splitting.
Purity is not required for this result.

The argument is the coefficient-valued form of Stacks, Lemma 53.6.3,
[Tag 0B5E](https://stacks.math.columbia.edu/tag/0B5E). Its inputs are
comparison theorems, not a desired splitting packaged as data.

## The original evaluation image

Suppose \(X\) is locally Noetherian and
\[
0\longrightarrow W\xrightarrow a F\longrightarrow Q\longrightarrow0
\]
is the original short exact row. The enlargement theorem requires:

- coherent \(W\) and \(F\);
- finite original \(H^0(F)\);
- actual finite closed support of \(Q\), with \(h^0(Q)\ge2\);
- the trace-normalized Hom/H1 comparisons above;
- no nonzero coherent subobject of \(F\) with finite closed support.

The last condition is purity of **\(F\)** in the form used by the proof.
Purity of \(W\) alone does not supply it. In the intended application,
\(F=\Omega_C(V)\otimes L\), it follows from the genuine coefficient duality
and invertibility of \(L\). no_finiteSupport_subobject_of_comparison
supplies the corresponding consequence for \(W\) itself.

exists_finiteRow_surjective_on_sections derives finitely many sections
\(s_j:\mathcal O_X\to F\) spanning all original global sections, using the
original additive unit-Hom/global-section and H0/global-section comparisons.
The linear comparison is formed from these same maps. Its scalar law is
proved by the original scalar-center action evaluated on section one,
with the original top-open restriction of each structural scalar.
Surjectivity of this row on global sections does not assert that the row
is epi as a sheaf map.

The image of the finite row is coherent by native kernel and cokernel
closure. finiteRowToEvaluation_fac and evaluation_factors_finiteRow
retain both factorizations between the row and the original
globalSectionsEval F. Thus its coherent image represents exactly the
original evaluation image \(G\).

For \(B=G+a(W)\), the actual inclusion \(B\to F\) is coherent and every
global section of \(F\) factors through it. If \(H^1(B)=0\), the original
cohomology row and finite-support zero detection give \(F/B=0\).
Otherwise the splitting theorem and purity of \(F\) give \(B/W=0\).
Then all global sections of \(F\) land in \(W\), making the original
connecting map \(H^0(Q)\to H^1(W)\) injective, contrary to the dimension
bound.

Accordingly, epi_originalRowEvaluation_sum concludes
\[
\operatorname{Epi}\bigl(
 \operatorname{coprod.desc}(\operatorname{globalSectionsEval}F)\,a
\bigr),
\]
which is precisely \(G+a(W)=F\). The endpoint uses the original evaluation
and original inclusion. originalRowCokernelIso_hom also records that the
canonical comparison with the chosen cokernel takes its quotient map to
the supplied original quotient arrow. No arbitrary quotient isomorphism
replaces this map.

This is the finite-support mechanism of Stacks, Lemma 53.6.5,
[Tag 0B5F](https://stacks.math.columbia.edu/tag/0B5F). In the proper curve
consumer, finite H0 is supplied by moduleCohomology_finite_of_proper,
using the original structural scalar map.

## Consumer boundary

The module proves the enlargement conclusion under its displayed inputs.
It does not construct a regular hyperplane section, identify the
coefficient-valued canonical object after base change, calculate the
degree of its actual finite quotient, or prove the coefficient-valued
Serre comparison. For canonical generation the geometric consumer must
also identify the canonical inclusion locally as multiplication by a
section vanishing at the point, then apply Nakayama.

The actual surface canonical restriction, the original
\(\Gamma(X,\omega_X)\simeq\omega_A\) unit/counit comparison and its trace,
and subsequent Gorenstein or resolution consequences retain their own
suppliers. The generic enlargement theorem alone gives no native R.R3,
Gorenstein, rational double point or surface-resolution conclusion.

