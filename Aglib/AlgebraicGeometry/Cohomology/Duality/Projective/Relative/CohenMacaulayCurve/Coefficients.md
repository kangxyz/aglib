# Intrinsic line coefficients for the chosen-embedding curve object

[Coefficients.lean](Coefficients.lean) extends the original unit-coefficient curve
concentration to an actual finite one-dimensional module `V` over an arbitrary
field `k`. The coefficient is exactly
`relativeTopDifferentialCoefficientsFunctor (toSpec k ι) n` evaluated at `tilde V`.
The derived object is the installed `derivedClosedImmersionRightAdjointPlus j`
on that coefficient in degree zero. Its canonical module is its own native
homology in the integer degree `(n : ℤ) - 1`.

The geometric data are an actual closed immersion `j : C ⟶ ProjectiveSpace k ι`
and an equivalence `ι ≃ Fin (n + 1)`. At every closed point `x` the hypothesis is
an element `b` of the maximal ideal of the actual stalk, regular on that stalk,
whose principal ideal has radical equal to the maximal ideal. This is the same
regular-primary parameter condition used by the unit-coefficient theorem. The
source may be nonreduced and non-Gorenstein. No positive lower bound on `n`,
normality, reducedness, smoothness, separability, perfection of the field, or
invertibility of the canonical module is imposed.

The ambient coefficient and every original homology sheaf are finitely presented
for every finite `V`, before any dimension-one or parameter hypothesis is used.
The proof uses the actual affine tilde tensor comparison, finite generation of
the tensor of finite modules, pullback of finite presentations, and the existing
finite-source derived closed-adjoint theorem. It does not choose a basis of `V`.

For concentration, a field-linear identification of `V` with `k` is used locally
inside the vanishing proof. Applying the original tilde, coefficient, single,
derived closed-adjoint, and homology functors transports the already proved
unit-coefficient vanishing in every integer degree. This identification is not
part of any public construction. `cmCurveCoefficientCanonicalIso` is instead the
installed `isoSingleHomology` for the original coefficient-valued object.
`cmCurveCoefficientCanonicalIso_homology` states that its induced map on the
object's own canonical homology, followed by the installed single-homology
normalization, is the identity.

`cmCurveDerivedResidueCoefficientCanonicalIso` substitutes the literal module
`ModuleCat.derivedResidueCoefficientLine R k`, the degree-two native homology of
the installed right-derived coinduction of `R[0]`. Here the original map `R → k`
is finite and local, `R` is regular local of dimension two, and the field action
is the original coinduced action. The existing finiteness and finrank-one
theorems supply the line conditions directly. Surjectivity of `R → k`, a
separable residue extension, and an orientation of this line are not required.
The specialized homology theorem retains the same identity normalization.

This file supplies concentration, coherence, and reconstruction for the actual
coefficient. It does not identify this canonical module with `W_C(k) ⊗ V`, prove
canonical-module base change, or provide the surface-to-curve coefficient
comparison. Compatibility with the surface counit, the positive Cartier
normalization, and the coefficient-valued Serre pairing remain separate
original-map obligations. No canonical generation, rational double point, or
resolution theorem is asserted.
