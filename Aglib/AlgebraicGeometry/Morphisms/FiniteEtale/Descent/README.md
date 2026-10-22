# Finite-etale descent

The field and limit leaves construct finite-stage models, common morphisms,
local charts and their glued covers. Purely inseparable transport uses the
actual affine algebra, open-cover, pullback and reflection interfaces. Every
specified model, morphism lift, finite-presentation and descent input remains
part of its original statement.

[LimitGlobalModels](LimitGlobalModels.lean) proves
`Scheme.FiniteEtale.LimitDescent.exists_cover_of_structured_diagram` for a
small cofiltered limit with affine transitions and qcqs stages. At a
specified stage it takes a finite, locally directed thin open-cover
category with compact charts and a prescribed diagram of finite-etale
models on those charts. A compatible identification of their limit base
changes with the local restrictions of `Y : FiniteEtale c.pt` gives a
finite-etale model `Z` at a later stage `k : Over i`, together with an
isomorphism from `(baseChange (c.π.app k.left)).obj Z` to `Y`.

The sheaf-representation leaves belong to
`AlgebraicGeometry.Scheme.FiniteEtale.SheafDescent`. They descend the actual
represented set sheaf through affine trivializing charts and directed open
covers. `AffineSheafAlgebraDatum` keeps the actual algebra coaction and its
identity-section equations. Existing local-trivialization type extensions keep
their type's native namespace in `Scheme.EtaleCohomology`.

`Group` transports the actual group structure and its represented action.
Lower generic diagram lifts, naturality transport and functor automorphisms
belong to `CategoryTheory.Functor`; they do not acquire a scheme hypothesis.
Current consumers are the fundamental-group finite-stage/kernel construction,
actual finite-etale classification and small-etale finite-coefficient H1.
