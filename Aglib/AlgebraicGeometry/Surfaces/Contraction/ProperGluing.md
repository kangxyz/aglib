# Global gluing over the original base

`ProperGluing` uses `Scheme.OpenReplacement.OfOpens` to replace the actual
open `U=f⁻¹(V)` of the original scheme `X` by a supplied local target `T`.
The second chart is an actual original open `W`, intended to be `X\E`.
The source cover is `U⊔W=⊤`. The overlap map is the literal composite
`(W.ι ∣_ U) ≫ c`, where `c:U→T` is the given local contraction.

The overlap adapters start with the actual local source complement `Wlocal`,
the equation `U.ι⁻¹(W)=Wlocal`, and the local complement isomorphism
`ε:Wlocal≅C` preserving its map into `T`. They prove that the literal overlap
composite is an open immersion, that its range is exactly `C`, and, using
`c⁻¹(C)=Wlocal`, that its overlap square is cartesian. The original curve's
open-restriction comparison supplies the source-complement equation.

The module constructs the scheme `obj`, its two open charts, and
`contraction:X→obj`. The local map and the identity on `W` are its actual
chart restrictions. A supplied cartesian overlap square makes this map
proper when `c` is proper. Surjectivity of `c` gives surjectivity of the
constructed global map.

`isNoetherian_obj` uses local Noetherianity and compactness from the finite
two-chart cover. It does not infer Noetherianity from a proper surjection.
`regularStalks_obj` uses the actual chart stalks. For integral `X`, the
surjective map gives irreducibility of the target; the regular stalks give
reducedness, yielding `isIntegral_obj`.

Given the actual local structural map `q:T→V` and `c≫q=f∣_V`,
`structureMap:obj→S` glues `q≫V.ι` to the original `f` on `W`.
`contraction_structureMap` retains the original equation. The inverse
image of `V` is exactly the replacement chart, with its cartesian square
and canonical `replacementIso`.

For another base open `Z` satisfying `f⁻¹(Z)≤W`, the original restriction
of `f` is the cartesian restriction of the constructed map over `Z`.
`awayIso` and its structural equation identify the two actual inverse-image
schemes. If `V⊔Z=⊤`, properness of the original `f` and the local `q`
proves properness of `structureMap` by this two-open cover of the base.
For the contraction consumer, `Z` is the complement of the closed image
point in `S`; its inverse image lies in the unchanged complement.

An original field point `ρ:Spec k→T` is retained as `ρ≫leftι`.
If its local complement is the overlap image, the global point is a closed
immersion and the unchanged target chart is exactly its complement.
The complement isomorphism is the canonical image isomorphism of that
same open chart. `pointIdeal_comap_left` identifies the full point ideal on
the replacement chart, while `pointIdeal_comap_right` identifies its pullback
on the unchanged chart with the unit ideal. No equality between `k` and a
residue field of `S` is imposed.

Given the original exceptional immersion `i:D→X`, its actual factor
`iU:D→U`, and the original map `a:D→Spec k`, the local equality
`ρ.ker.comap c=iU.ker` and triangle `iU≫c=a≫ρ` give a cartesian square.
`point_isPullback` pastes this square with the replacement chart. The result
has the original `D`, `i`, and `a` as its literal maps.
`pointIdeal_comap_contraction` therefore identifies the full global
inverse-image point ideal with `i.ker`. `pointIdeal_cartierPullback` uses the
actual image isomorphism of `i` to transfer the original invertible ideal
module to the canonical kernel subscheme used by the blowup interface.

`contraction_isBlowup` identifies the original canonical lift to the actual
global blowup. Over the replacement chart, flat base change of blowups and
cartesian cancellation identify it with the supplied local canonical lift.
Over the unchanged chart, the actual point ideal is the unit ideal, so the
literal pullback of the blowup map is an isomorphism. These two actual open
charts cover the global blowup. Target-locality of isomorphisms proves that
the original canonical global lift is an isomorphism. No global point-blowup
recognition theorem or blowup comparison oracle is used.

These inputs are actual local geometric data, supplied by the projective
contraction kernel after projectivity of the proper inverse-image source
has been constructed. No universal projectivity or global contraction
existence proposition is assumed here.

The final proper-modification consumer must supply the affine base
neighbourhood and its two base-cover equations, construct projectivity of
the proper inverse-image source, and instantiate the projective contraction
kernel. This module proves the gluing and blowup comparisons from that actual
local output; it does not assert existence of the required local output for
an arbitrary bare surface.

Mathematical basis: the accepted proper-modification route M2–M3 in
`general-contraction-research.md`, independently reviewed on SHA-256
`fdf7e62bdf69b6d5c08bb7bd4a6a1f0430a8fd9f442c0a533419e9cc448c6118`.
The unrestricted bare-surface contraction question is outside this module.
