# Central simple algebras and Brauer splitting

This family extends the native Mathlib `CSA`, `IsBrauerEquivalent`, and
`BrauerGroup` quotient. It does not introduce another Brauer carrier or assume
a group structure absent from the pinned Mathlib definition.

- [Split](Split.lean) constructs the scalar representative and turns a literal matrix
  algebra equivalence into native Brauer equivalence. It computes square
  dimension and proves that the determinant under that equivalence vanishes
  exactly on nonunits. Over an algebraically closed field, native Wedderburn
  theory supplies the splitting and the native quotient is a singleton.
  Quotient statements use algebras in the same universe as the field; the
  unbundled matrix-splitting statements retain arbitrary algebra universes.

- [MatrixNorm](MatrixNorm.lean) constructs the actual multivariate determinant polynomial of a
  finite-basis matrix representation. It proves homogeneous degree equal to
  matrix size, the literal evaluation formula, and extraction of a nonzero
  nonunit from a nontrivial zero. No norm is supplied as an assumption.
- [MatrixNormInvariance](MatrixNormInvariance.lean) proves that polynomial is nonzero, that an actual
  splitting makes its zero locus precisely the nonunit locus, and that its
  coefficients are independent of the splitting over an infinite field, using
  native determinant invariance rather than another Skolem–Noether proof.

- [GaloisDescent](GaloisDescent.lean) descends the coefficients of a Galois-invariant determinant
  polynomial along a finite Galois extension, preserving nonzero polynomial
  and homogeneous degree. Its invariance premise is explicitly intermediate.
- [GaloisSplittingNorm](GaloisSplittingNorm.lean) discharges that invariance for an actual splitting of
  the literal scalar extension. It constructs the Galois-twisted splitting
  and applies determinant independence. The splitting field is infinite.
- [C1GaloisSplitting](C1GaloisSplitting.lean) uses the sole `Field.IsC1` interface. For a finite
  division algebra with an actual finite Galois matrix splitting over an
  infinite splitting field, it proves dimension one and an actual algebra
  equivalence with the scalar field. The norm polynomial and its degree are
  constructed, and zeros are shown to give nonunits in the original algebra.

- [DivisionRepresentative](DivisionRepresentative.lean) applies native finite Wedderburn theory and descends
  centrality from a matrix algebra to its division coefficient algebra, producing
  a representative in the original Brauer relation. The lower helper is
  `Aglib.Algebra.Central.Matrix`.
- [ScalarExtension](ScalarExtension.lean) uses the native Azumaya multiplication map to prove
  simplicity after arbitrary field extension and hence actual splitting after
  algebraically closed extension. `Aglib.Algebra.Azumaya.CentralSimple` supplies
  that map's bijectivity from centrality and simplicity using Jacobson density.
- [MinimalPolynomial](MinimalPolynomial.lean) proves that the minimal polynomial of an integral element
  is preserved by literal scalar extension, using independence of powers.
- [SeparableElement](SeparableElement.lean) detects separability and full matrix degree of the original
  minimal polynomial from a separable characteristic polynomial in a splitting.
- [GenericSeparableElement](GenericSeparableElement.lean) constructs such an element over an **infinite**
  coefficient field: a generic resultant is nonzero on a distinct-entry diagonal
  matrix, and coefficient-field grid density supplies a nonzero evaluation.

- [MaximalSubfield](MaximalSubfield.lean) constructs an actual matrix splitting from a full-degree
  embedded subfield, using the original division algebra as a right vector
  space and native scalar multiplication and scalar-extension maps.
- [FiniteGaloisSplitting](FiniteGaloisSplitting.lean) constructs such a subfield with native `AdjoinRoot`,
  then passes matrix coefficients to the native splitting field of its separable
  minimal polynomial. Simplicity and equal dimensions yield an actual finite
  Galois matrix splitting over an **infinite** original coefficient field.
- [C1Splitting](C1Splitting.lean) assembles these constructions with the descended norm argument:
  a finite central division algebra over an infinite C1 field has dimension one,
  every native CSA actually splits as a matrix algebra, and the native Brauer
  quotient is a singleton. Its statements assume neither a reduced norm nor a
  splitting field.

This family does not identify the algebraic Brauer quotient with original
étale H². That cohomological comparison remains separate work. The intermediate
[C1GaloisSplitting](C1GaloisSplitting.lean) consumer retains an explicit finite Galois splitting
hypothesis; the later [C1Splitting](C1Splitting.lean) construction discharges it,
under the stated infinitude hypothesis, rather than silently assume it.

## Function fields and cocycle constructions

- [FunctionField](FunctionField.lean) applies the actual finite-extension Tsen theorem to obtain
  matrix splitting and a singleton native Brauer quotient over finite extensions
  of an algebraically closed rational function field.
- [AlgebraicFunctionField](AlgebraicFunctionField.lean) removes the finite-degree hypothesis using finite
  coefficient descent in the Tsen family.
- [CrossedProduct/MatrixOperators](CrossedProduct/MatrixOperators.lean) constructs weighted Galois translation
  matrices from native `groupCohomology.IsMulCocycle₂` and proves their actual
  twisted multiplication and diagonal commutation relations.
- [CrossedProduct/Algebra](CrossedProduct/Algebra.lean) forms the literal span as a native matrix subalgebra.
- [CrossedProduct/Coefficients](CrossedProduct/Coefficients.lean) constructs its coefficient-vector equivalence;
  central simplicity and extraction of a cocycle primitive are supplied by
  subsequent focused leaves. None asserts a comparison with original étale
  cohomology.
- [CrossedProduct/Center](CrossedProduct/Center.lean) computes the center by the finite-Galois fixed-field
  criterion. [CrossedProduct/Simple](CrossedProduct/Simple.lean) isolates any coefficient of an ideal element
  using the existing tensor-evaluation surjection, proving simplicity.
- [CrossedProduct/Primitive](CrossedProduct/Primitive.lean) extracts a native multiplicative primitive from a
  one-dimensional extension-field action; [CrossedProduct/C1Primitive](CrossedProduct/C1Primitive.lean) constructs
  that action from the actual CSA matrix splitting, not from an assumed action.
- [CrossedProduct/Normalization](CrossedProduct/Normalization.lean) transports primitives back from normalized
  cocycles. [C1Cocycles](C1Cocycles.lean) assembles the normalization-free finite-Galois statement.

- [FunctionFieldCocycles](FunctionFieldCocycles.lean) specializes the native primitive construction to every
  algebraic extension of an algebraically closed rational function field.

The final cocycle statement assumes neither normalization nor a
splitting/primitive existence hypothesis. The original cohomological
applications have their own [field family](../../AlgebraicGeometry/EtaleCohomology/Fields/README.md);
these algebraic results do not identify the native Brauer quotient with
original étale H2 in general.
