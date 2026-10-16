# Native exterior powers and changing coefficient rings

`Semilinear` extends Mathlib's original `exteriorPower` objects.
`exteriorPower.mapSemilinear n f` sends every original wedge to the wedge
of the images under `f`, for an arbitrary semilinear map over any
homomorphism of commutative rings. The two ring universes and two module
universes are independent. No finiteness, flatness or invertibility
hypothesis is imposed, and degree zero is included.

The construction uses the existing universal
`exteriorPower.alternatingMapLinearEquiv` with the actual target action
restricted through `Module.compHom`. `semilinearMap_ext` detects equality
on original wedges. Identity and composition are proved for this same map;
composition retains Mathlib's native `RingHomCompTriple` identifying the
displayed composite ring map. For the literal composite, that class is
supplied by `⟨rfl⟩`, with no additional mathematical premise. When the
coefficient ring is unchanged, `mapSemilinear_eq_map` identifies the map
with the existing native `exteriorPower.map`.

The immediate consumer is the actual exterior power of a presheaf of
modules: its restriction maps change coefficient rings. Module
sheafification, exterior local bases and determinant transition formulas
are subsequent interfaces. No new exterior-power quotient or substitute
module object is introduced here.

`TopDegree` proves that a displayed `Basis (Fin n) R M` identifies the
original top exterior power with `R`. The forward map is the native basis
determinant extended through the original exterior universal property;
the inverse is exactly `r ↦ r • exteriorPower.ιMulti R n b`.
`exteriorPower.ιMulti_eq_det_smul` retains this generator formula for every
wedge. `Module.Basis.exteriorPowerTopEquiv_changeBasis` gives the original
basis-change determinant, and `exteriorPowerTopEquiv_mapSemilinear` gives
the determinant of the source-basis images times the original ring-map
image of the scalar coordinate. Rank zero and trivial coefficient rings
are included; no localization, flatness or nontriviality is assumed.
The immediate consumer is the actual local top-exterior frame and its
determinant transition in the module-sheaf family.
