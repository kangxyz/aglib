# Original Kummer cohomology of broad curves

## Scope and exact public endpoints

Namespace: `AlgebraicGeometry.Scheme.EtaleCohomology.Curves`.
All three theorems take:

- `k : Type u`, with `Field k` and `IsSepClosed k`;
- `X : Scheme.{u}` and the actual `p : X ⟶ Spec (.of k)`;
- `[LocallyOfFiniteType p]` and `[CompactSpace X]`;
- `[HasExt.{w} (AbelianSheaf.{u, u + 1} X)]`, with arbitrary independent `w`;
- `hdim : topologicalKrullDim X ≤ 1`;
- `n : ℕ`, `hn : 0 < n`, and `hunit : IsUnit (n : k)`.

These hypotheses say that the actual scheme is finite type and has dimension
at most one over a separably closed field. The field may be imperfect, and the
scheme may be singular, reducible, or nonreduced. The empty scheme is not
excluded. No smoothness, reducedness, perfectness, arithmetic marking, Brauer
vanishing hypothesis, or replacement cohomology theory occurs in the statements.

1. `power_bijective_of_curve k X p hdim n hn hunit q hq`, for `hq : 2 ≤ q`, proves
   `Function.Bijective (Sheaf.H.map (power X n) q)` for the original multiplicative
   coefficient power map.

2. `picardBoundary_surjective_of_curve k X p hdim n hn hunit hinv` proves
   `Function.Surjective (Kummer.picardBoundary X n hn hinv)`, where
   `hinv : IsUnit (n : Γ(X, ⊤))`. This is the original Kummer boundary from the
   ordinary Picard group to original degree-two root cohomology.

3. `roots_subsingleton_H_of_curve k X p hdim n hn hunit hinv q hq`, for
   `hq : 2 < q`, proves `Subsingleton (Sheaf.H.{w} (mu X n) q)`.

The explicit `hinv` in the last two interfaces records the caller's literal
original Kummer sequence and boundary. It is supplied by structural pullback
of `hunit`; it is not an additional restriction on the curves. Derived-category
and intermediate source Ext universes are chosen internally, not required as
extra endpoint hypotheses.

## Proof route

The generic locus retains its actual Artinian stalk rings. Its original root
cohomology is controlled by actual residue fields, using the original field
vanishing theorem and legitimate root-coefficient nilpotent and purely
inseparable comparisons. The proof never asserts general invariance of Gm
under those morphisms.

On genuine affine etale tests, original represented cohomology computes the
higher direct images through the native sheafification comparison. This gives
zero first higher image and invertible multiplication by n on the remaining
positive higher images. A native derived truncation argument transfers the
scalar statement to original cohomology of the generic direct image.

The actual kernel and cokernel of the original generic-unit map are exhausted
by their finite closed support subobjects. Every original section has a genuine
local-zero support and factors through its corresponding support subobject;
no global representative of an arbitrary cokernel section is assumed. Outside
stalk vanishing uses factorization through an individual skyscraper-unit kernel,
not preservation of an infinite intersection by a stalk functor.

A finite support is represented by the literal coproduct of its residue-field
spectra and its actual finite closed immersion. The original adjunction unit
identifies the supported coefficient with a finite direct image. Native finite
exactness and separably closed component acyclicity prove positive cohomology
vanishing for each stage. Published coefficient continuity then proves actual
defect acyclicity. Continuity is computed at standard Ext universe u+2 and
transported back through `Ext.chgUniv`, so no large-index colimit-size premise
is imposed on the final Ext universe. No assertion of sectionwise filtered
colimits on arbitrary non-quasicompact tests is used.

Finally, the original kernel/cokernel long exact sequences and Kummer long
exact sequence give the three endpoints above. Their ordinary Picard and
original H maps are unchanged.
