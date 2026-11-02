# The actual initial Case-II cubic after coordinate normalization

API: [exists_original_coordinates_cubic_of_linearSquare_kernel](CaseTwoCoordinates.lean#L34).

This thin consumer uses only the unique existing producers. An honest full
linear-square canonical kernel on original maximal-ideal generators is
normalized by `exists_original_doubleLine_generators`, using actual residue
lifts and the original coordinate-map laws. On a singular rational normal
Noetherian Nagata surface, `CaseTwoCubic` then gives a true relation on those
same actual elements and proves its original residue cubic is nonzero.
The normalized kernel is retained in the result for the actual cone and
marked-chart consumers; no alternative chart or coefficient field is chosen.

The all-degree Hilbert function and full quadratic kernel have their separate
actual exceptional numerical supplier. Classifying that quadratic as a
nonzero linear square is still a separate Case-II premise here. Nonzero scalar
multiples are removed by the existing principal-ideal unit lemma. This leaf
does not claim to establish that classification, canonical generation,
Gorenstein preservation, a marked transition, or finite termination.

The ring `A` is a commutative normal Noetherian Nagata local domain of
dimension two with `NormalModificationH1Vanishing A` and is nonregular.
The input linear form is nonzero and homogeneous of degree one, and its
square generates the entire kernel on the supplied generating triple.

Present consumers: [QuadraticClassification/Core](QuadraticClassification/Core.md).
