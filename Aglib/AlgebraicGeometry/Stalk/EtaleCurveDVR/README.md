# DVR stalks from actual curve charts

[EtaleCurveDVR](../EtaleCurveDVR.lean) gives the native `Scheme` endpoints
`dvr_at_image_of_etale_smooth_curve_chart_any_point`, its original closed-point variant,
and `dvr_at_image_of_etale_affine_line_chart`. They retain all original chart hypotheses:
an integral locally Noetherian target, the actual étale map, a smooth curve structure
over the original arbitrary field, and a nongeneric target image. They impose no source
integrality or normality and no closed-point condition in the arbitrary-point result.

`Scheme.RegularityDescent.Etale.regular_at_image` proves descent on the original
`(j.stalkMap x).hom`, with that same map's étale properties. Target-stalk
Noetherianness follows from the displayed locally Noetherian target. The source
regularity comes from the proved `Scheme.smoothFieldRegularity`, applied to the
actual smooth structure map. These chart APIs have no flat-local descent,
smooth-regularity or dimension theorem-family parameters. The general
`FlatLocalRegularityDescent` predicate is not proved or needed by this argument.

Dimension descent reuses `Scheme.ringKrullDim_stalk_eq_of_etale` on the same stalk map.
The native `Scheme.smoothOfRelativeDimension_stalk_dimension_le` supplies the all-point
upper bound at every chart point. Nongenericity supplies nonfieldness. Regularity
and dimension exactly one then yield a DVR through the native cotangent-space criterion. The affine-line structure
map is literally `Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))`.

[OpenSmoothCurveDVR](../OpenSmoothCurveDVR.lean) gives
`Scheme.smoothChart_closedPoint_dvr` for an arbitrary open chart in an integral target.
It retains smooth relative dimension one for the actual composite and closedness of
the displayed image point, and applies `Scheme.smoothFieldRegularity` and
`Scheme.smoothClosedPointDimension` internally. Its DVR transport is the inverse of
the actual `j.stalkMap q` ring equivalence. It needs neither a theorem-family input
nor global Noetherianity of the target.

The exact source files are `Stalk/EtaleCurveDVR.lean` and `Stalk/OpenSmoothCurveDVR.lean`
under `R5Lab/Aglib/AlgebraicGeometry`, packet revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`; hashes are in the module headers.
The source's general ring lemmas `ringKrullDim_le_of_flat_local` and
`dvr_of_regular_of_dim_le_one_of_not_isField` remain outside this bounded consumer cut.
Their general statements are not claimed migrated. The source smooth-curve dimension
bound is supplied by the native all-stalk theorem.
