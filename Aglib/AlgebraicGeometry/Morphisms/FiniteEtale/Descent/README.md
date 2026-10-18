# Finite-etale descent

The field and limit leaves construct finite-stage models, common morphisms,
local charts and their glued covers. Purely inseparable transport uses the
actual affine algebra, open-cover, pullback and reflection interfaces. Every
specified model, morphism lift, finite-presentation and descent input remains
part of its original statement.

The sheaf-representation leaves belong to
`AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent`. They descend the actual
represented set sheaf through affine trivializing charts and directed open
covers. `AffineSheafAlgebraDatum` keeps the actual algebra coaction and its
identity-section equations. Existing local-trivialization type extensions keep
their type's native namespace in `Scheme.EtaleH1`.

`Group` transports the actual group structure and its represented action.
Lower generic diagram lifts, naturality transport and functor automorphisms
belong to `CategoryTheory.Functor`; they do not acquire a scheme hypothesis.
Current consumers are the fundamental-group finite-stage/kernel construction,
actual finite-etale classification and small-etale finite-coefficient H1.
