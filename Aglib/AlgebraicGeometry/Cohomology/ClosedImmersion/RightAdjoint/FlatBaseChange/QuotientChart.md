# The original mapped-ideal quotient chart

`QuotientChart.lean` packages the geometric chart needed before constructing
local own-homology field-extension isomorphisms. It reuses
the original `quotientFlatChart_isPushout`, moved here unchanged from
`Localization`, and native `Spec` pullbacks,
Cartesian pasting and cancellation. No generic Cartesian backend is duplicated.

For the given rings R,S with their original algebra map, a chosen quotient
chart C over an affine open a, a scheme map g and an actual Cartesian affine
chart square over g, `ClosedImmersionAffineQuotientChart.baseChangeSourceMap`
is the native `pullback.lift` into the original `pullback i g`. Its two
projection laws retain the original quotient-source map and target quotient
map. `baseChangeSourceMap_isPullback` and
`baseChangeSourceMap_projection_isPullback` prove both Cartesian squares for
this same lift. Openness follows from openness of the target affine chart.

`ClosedImmersionAffineQuotientChart.baseChange` packages this source map with
ideal literally `C.ideal.map (algebraMap R S)`. The ideal and source-map
identities are definitional. No unrelated target quotient is selected.

The geometric construction requires neither flatness nor Noetherianity,
closed-immersion instances beyond the supplied genuine chart, CM conditions,
coefficient sheaves or resolutions. Its given ambient Cartesian square is
geometric input, not an assumed canonical comparison or overlap equation.

The companion imports `FiniteSource.Derived`
and the native tensor-product leaves, not `Localization`. The original quotient
pushout theorem retains its fully qualified name and is publicly reexported by
`Localization`; there is only one implementation. Native acceptance of this
lower leaf does not establish acceptance of its higher consumers. The subsequent local own-homology isomorphisms,
principal-overlap compatibility, global gluing and arbitrary-field generation
are not supplied by this chart packaging.

## Native checks and the two root repairs

The complete QuotientChart source `3f29d151` reached its actual leaf in own139
and failed ordinarily after 4.7 seconds (total 397.07 seconds). The first
reported defect was omission of the section variable H from the statement of
`baseChangeSourceMap_condition`; its proof therefore could not refer to H.w.
The source-map target also resolved bare `pullback` to the module pullback
functor rather than the categorical scheme pullback.

The repair retains the given geometric H using `include H in` for that
one theorem and qualifies only the categorical scheme-object type. All proof
bodies, arrows and the extracted quotient producer remain unchanged. The later
diagnostics from the failed version did not persist in the repaired whole-leaf
check; no independent causes are assigned to them.

Exact source `f647f015` passed the complete own140 leaf in 4.9 seconds
(9.13 seconds total, exit 0), reusing the retained suppliers. This accepts the
original quotient pushout, both chart projection laws and Cartesian squares,
and literal mapped-ideal chart packaging. The changed higher Localization
and Composition consumers were not selected and remain unaccepted.
