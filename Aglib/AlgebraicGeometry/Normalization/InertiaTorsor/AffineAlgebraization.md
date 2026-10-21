# AffineAlgebraization

Extract generic relabelTorsor, algebraize an actual affine categorical torsor action into the literal coaction A -> A tensor C, prove coaction/transporter identities, and use actual affine cover presentation/points.

Source: `R5Lab.Aglib.AlgebraicGeometry.Normalization.AffineTorsorAlgebraization`, R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`.

Full source SHA-256: `dffc1db5d857167cc6dffe8a9274644451a0523835c9fa2e1f7dae77f1fb4c88`.

Conditions: relabelTorsor has independent category/object/Hom universes v,w. Algebraization uses actual Field K, commutative A, commutative Hopf C with Coalgebra.IsCocomm and supplied TorsorAction; coefficient group and action direction are exactly the native hopfSpec construction. Preserve transporter input/output orientation. No arbitrary affine torsor existence theorem is assumed.

All displayed source proofs are retained with native maps and namespaces;
the former upstream ClassExtensionUniqueness import is replaced by the actual
lower point API. Transporter orientation remains A ⊗ A → A ⊗ C.

The source record is provenance. New native compiler coverage is reported separately; historical acceptance does not certify this extraction.
