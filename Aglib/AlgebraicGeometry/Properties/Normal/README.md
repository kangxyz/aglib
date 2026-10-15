# Normal stalks, components and connected integrality

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Properties.Normal.Basic`, defines `AlgebraicGeometry.Scheme.NormalStalks X`: every actual stalk is a domain and integrally closed. `NormalStalks.isReduced` derives reducedness. `NormalComponentsOpen` records the component-openness conclusion on locally Noetherian schemes.

[StalkComponents](StalkComponents.lean) proves the actual domain-stalk/component separation results. For a locally Noetherian scheme whose stalks are domains, irreducible components are open. [Components](Components.lean) supplies `normalComponentsOpen` and `isIntegral_of_connected_normalStalks_actual`: a connected locally Noetherian scheme with normal stalks is integral. Connectedness is the native `ConnectedSpace` premise, including its nonempty scope.

The conditional `isIntegral_of_connected_normalStalks` takes the component-openness family separately; the supplier closes that interface on the same objects. [Smooth field normality](../../Morphisms/Smooth/README.md) supplies normal stalks from regular-local algebra. No properness or dimension-one premise is used for these general component results.
