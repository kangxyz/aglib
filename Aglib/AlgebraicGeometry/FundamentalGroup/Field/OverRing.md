# OverRing

Generic Omega-valued action on finite-etale covers over Spec R, coefficient marking action, and actual restriction of the SAME normalization torsor cocycle/class. Split generic OverRing action source57–188 from normalization-specific source204–453 if that keeps imports minimal; root may assign second NEW lower leaf.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.GaloisFibreRestriction`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.

Full source SHA-256: `4f4688c26c08330b9c26221e302ff7caeda3cf52cf0f72c483ce74ee1bf8d119`.

Conditions: Do not identify Omega with AlgebraicClosure K. Source first part only requires Algebra.IsIntegral K Omega for continuity, not alg closed. Later normalization specialization retains IsGalois+IsAlgClosed, same f,Q,tau,coords,hvan.

The omitted dependency bridge is H1SchemeTorsor:350–519, 520–543, 587–747 and 749–788,
SHA-256 `0ec66c795599c228cf42bbf7f6b0a711efafbb7de5ebdc360864c40ed633d54d`. It supplies actual affine/tensor points,
the original integral-closure point comparison, coefficient marking and positive
scheme cocycle. Lower normalizationCover, normalizationGenericPoint,
normalizationSchemeAction and normalization_generic_square are reused from Basic.

The source record is provenance. New native compiler coverage is reported separately; historical acceptance does not certify this extraction.
