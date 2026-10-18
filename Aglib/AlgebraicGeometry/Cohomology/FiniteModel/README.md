# One actual finite-affine-cover model

[Basic](Basic.lean) is the sole owner of
`Scheme.Cohomology.FiniteCechCohomologyModel R ι X f U M n`. It records an
actual integer complex with finite-projective terms in `[0,n]`, its
literal map to the original finite Cech truncation, that map's
quasi-isomorphism, and the quasi-isomorphism of the same map after every
ring scalar extension. The cover and coefficient are the original native
ones. The record imposes no replacement cohomology or derived object.

For a separated source, quasicoherent coefficient relatively flat over
`Spec R`, and an actual affine cover indexed by `Fin (n+1)`, the constructor
`nonempty_finiteCechCohomologyModel_of_finite_cohomology` uses Noetherianity
and actual finite original cohomology. The original bounded Cech model is
flat by universal tensor exactness, and the sole lower algebraic
replacement constructs the finite-projective complex. The projective
and proper suppliers discharge cohomological finiteness by their proved
geometric theorems. It is not a premise of their geometric endpoints.

The methods retain the actual model-to-Cech arrow, original finite
inclusion and native Cech-derived-unit comparison. They give source
`Sheaf.H.{u+1}` with its unchanged structural ring action and the installed
native derived global sections. The literal scalar extension of the same
complex computes original cohomology of ordinary `p^*M` after every ring
map, including nonflat maps to non-Noetherian rings. The inclusion equation
retains the original integer Cech base-change arrow.

The old `ProjectiveCohomologyModel` is a transparent specialization to the
actual coordinate cover. It has no second record or replacement proof.
Its old constructor, field names, `.mk` access, methods and representative
equations remain thin delegation with the coordinate affine/cover proofs.
The independent old public consumer checks the type equality by `rfl`,
the qualified constructor and field aliases, original bounds/terms,
all-ring literal comparison, original cohomology, original inclusion
square and installed derived global sections.

The generic owner passed with receipt `1792123588832300000-59240` in
31 seconds at the default budget. The old projective wrapper passed with
receipt `1792123795908750000-61238` in 3.5 seconds. The enhanced original
`ProjectiveFiniteModelConsumer.lean` passed with receipt
`1792123861038373000-62261`; all eight inspected old declarations use only
the three standard axioms. Needed old Cech dependency headers were repaired
one leaf at a time; their mathematics was unchanged.

[BaseChange](BaseChange.lean) now owns the canonical homology-mate
normalization for every actual finite affine cover. Its unit pure-tensor
formula is the original ordinary cohomology pullback. The full linear
square identifies native `extendScalarsHomologyMap` with the unchanged
geometric `moduleCohomologyBaseChangeMap`, through the tensor of the
original source comparison and the actual target comparison. Original
cohomology remains in universe `u+1` and the model in universe `u`.
No homology preservation or flatness of the ring map is assumed, and no
unconditional degreewise invertibility is asserted. The generic source
passed `1792124393452869000-69075` in 13 seconds; the old projective
wrapper passed `1792124530024031000-70518` in 4.3 seconds. The unchanged
original `ProjectiveFiniteModelBaseChangeConsumer.lean` passed
`1792124584660258000-71578`, with only the three standard axioms for all
three inspected comparison declarations.

[Derived](Derived.lean) owns the same scalar-extended complex's native
bounded-below packing, actual arrow to integer Cech, literal original
integer base-change square, its quasi-isomorphism and installed derived
global-sections comparison after every ring map. The new ring needs no
Noetherianity or flatness. The generic source passed with receipt
`1792124722224644000-72758` in 3.3 seconds; the old projective wrapper
passed `1792125107996662000-77649` in 3 seconds. The unchanged original
`ProjectiveDerivedBaseChangeConsumer.lean` passed with receipt
`1792125137568494000-78077`; all four inspected old declarations use only
the three standard axioms. Both the localized actual comparison and the
original Cech/injective-resolution derived unit remain explicit.

The existing actual chain-representative and tilde-counit comparison consumers remain separate
and unchanged. The direct-image object comparison in [Perfect](Perfect.lean)
below uses exact tilde's original derived units. It must not be conflated
with the old chosen chain-normalized isomorphism before their normalization
equality is proved.
Ordinary `p^*M` is not identified with `Lp^*M` from relative base flatness
alone.

[Perfect](Perfect.lean) applies native tilde to the same original complex
and to its literal scalar extensions. `sheafModelPlus` and
`baseChangeSheafModelPlus` have the original strict bounds `[0,n]` and
native `strictPerfect`. The object isomorphisms
`derivedPushforwardObjectIso` and
`baseChangeDerivedPushforwardObjectIso` use the sole affine-base derived
transport, original section comparisons and proved actual counit. They
represent installed `Rf_*` and the corresponding actual direct image of
ordinary `p^*M` over every new ring. No Noetherianity or flatness of that
new ring, termwise quasicoherence of a pushed resolution, or global-section
exactness is assumed. There is no second base-changed model record.

The distinct `ObjectIso` names retain the boundary from the existing
chosen chain-normalized projective isomorphisms: equality with those maps
has not been proved by this object transport. Canonical degreewise maps
remain normalized by `BaseChange`; no extra same-map derived claim is
inferred here. Strict perfectness over a noncoherent new ring is not a
cohomological finiteness claim. The generic perfect source passed
`1792125445227839000-80330` in 5.9 seconds at the default budget. The
independent same-complex/all-base-change consumer passed
`1792125511710106000-80608`; all nine inspected declarations use only the
three standard axioms.

The unconditional [proper supplier](../Proper/FiniteModel.lean), with its
[focused guide](../Proper/FiniteModel/README.md), now discharges this
constructor's original cohomological-finiteness input using actual proper
finiteness. It internally chooses an actual finite affine cover, constructs
this same data, and gives one `P` representing native source and all-ring
ordinary pulled-coefficient direct images after tilde. Only the original
ring is Noetherian. Its independent consumer also checks the unchanged
original degreewise cohomology map on the constructed proper model.

[Fibers](Fibers.lean) is the sole model-level owner of the comparison
`fiberCohomologyDimension_eq_finrank`. The original ordinary fibre and its
unchanged structural residue-field action agree with native homology of
the literal residue-field scalar extension of this same `D`. The method
uses actual affine/cover proofs, quasicoherence, separation and relative
flatness; it does not assume degreewise base-change exactness or need
Noetherianity once the data is supplied. The generic source passed
`1792126383798956000-86934` in 30 seconds; the old projective wrapper
passed `1792126437887773000-87565` in 2.7 seconds. The unchanged original
Euler public consumer passed `1792126574816467000-88998`, and the
arbitrary-universe proper-model consumer passed
`1792126612714972000-90284`, all inspected declarations using only the
three standard axioms. The proper consumer constructs the same model
internally, including the lifted finite index and empty-source case.

[BaseChangeCriterion](BaseChangeCriterion.lean) detects epimorphy and
invertibility of the original geometric cohomology base-change map by the
same property of the original native homology mate on `D`. It uses the
proved full linear square and actual source/target linear equivalences,
retaining the different cohomology/model carrier universes. No new map,
Noetherianity or flatness of the ring map is introduced. The generic leaf
passed `1792126694651736000-91004` in 4.7 seconds; the old wrapper passed
`1792126747172015000-91610` in 2.8 seconds. The unchanged original Grauert
consumer passed `1792126773999586000-91838`. The arbitrary-universe proper
consumer passed `1792126810983862000-92117`, checking one internally
constructed proper `D` for every target ring and degree. All inspected
comparison declarations use only the three standard axioms.

[LocalCriterion](LocalCriterion.lean) transports the original local
homology criteria through this same model's canonical comparison square.
Over a local ring, surjectivity of the original residue-field comparison
in degree `q` gives invertibility of the original geometric comparison
after every ring map. Under surjectivity in degree `q+1`, unchanged
`H^(q+1)` is free exactly when the original degree-`q` residue map is
surjective. In degree zero its own residue surjectivity gives freeness,
using the actual strict lower bound to kill the negative predecessor.
These criteria require neither reducedness nor Noetherianity once `D`
is supplied. They keep explicit surjectivity of the original maps; local
constancy of fibre dimensions is not substituted for it. The generic leaf
passed `1792127030339470000-94713` in 7.5 seconds; its arbitrary-universe
public consumer passed `1792127067654411000-95174`, all three inspected
declarations using only the standard axioms. The geometric basic-open
residue/free-locus normalization is supplied by
[BaseChangeLocus](BaseChangeLocus.lean), described below.

[Semicontinuity](Semicontinuity.lean) owns the original fibre-dimension
upper-semicontinuity proof for this same actual `D`. Native finite-complex
semicontinuity is transported by the sole fibre comparison; no reducedness
or Noetherianity is added to the model-level statement. The generic leaf
passed `1792127364358077000-97613` in 2.7 seconds; the exact old projective
wrapper passed `1792127403413653000-98249` in 2.6 seconds and its unchanged
public consumer passed `1792127442874241000-98742`. The internally
constructed proper specialization passed `1792127464110134000-98959` and
its arbitrary-universe public consumer `1792127490598539000-99293`.
All inspected declarations use only the standard three axioms.

[EulerCharacteristic](EulerCharacteristic.lean) owns the equality of the
unchanged intrinsic fibre Euler characteristic with native homological
Euler characteristic, and its local constancy. Actual strict bounds of
`D` prove support of the original alternating sum; no replacement bounded
numerical function is defined. Reducedness and Noetherianity are not
additional model-level inputs. The generic source passed
`1792127562426416000-99796` in 2.7 seconds, old wrapper
`1792127605022548000-229` in 2.6 seconds, and unchanged original consumer
`1792127629970824000-658`. The proper specialization passed
`1792127713517360000-1604` in 2.7 seconds and its arbitrary-universe
consumer `1792127734693142000-1911`. All inspected declarations use only
the standard three axioms.

[Grauert/Global](Grauert/Global.lean) owns the original constant-dimension
criterion on this same `D`. It retains `IsReduced R`: local constancy of
original ordinary fibre-cohomology dimension gives projectivity of
unchanged cohomology and invertibility of the original geometric
base-change map after every ring map. The base need not be local; the
model-level proof needs no Noetherian hypothesis. Geometric suppliers
separately provide actual cohomological finiteness; projectivity alone is
not used to infer it over a noncoherent ring. Generic source
`1792127811719014000-2710` passed in 2.8 seconds, exact old wrapper
`1792127923492986000-3850` in 2 seconds, and unchanged original public
consumer `1792128019349233000-4538`. The actual proper specialization
passed `1792128253009558000-6846` in 7 seconds and independent public
consumer `1792128281150102000-7131`. All inspected declarations use only
the standard three axioms. These constant-dimension criteria retain their
reducedness guard, unlike the explicit residue-map-surjectivity criteria.

[Grauert](Grauert.lean) owns the original constant-dimension freeness
criterion on this same `D` over a reduced local ring. Both `IsReduced R`
and `IsLocalRing R` remain explicit; no Noetherianity is added at model
level. The unchanged original structural action is retained on `Sheaf.H`.
Generic source `1792128341342631000-7609` passed in 2.7 seconds, old
projective wrapper `1792128390040003000-8348` in 4.1 seconds, and unchanged
original public consumer `1792128437382519000-9057`. The proper local
specialization passed `1792128482923431000-9755` in 3.3 seconds and its
independent arbitrary-universe public consumer
`1792128564293877000-10712`. All inspected declarations use only the
standard three axioms. All six old numerical-owner extractions are now
closed; their exact old theorem signatures and geometric endpoints are
preserved. [BaseChangeLocus](BaseChangeLocus.lean) supplies the basic-open
residue/free-locus step. Neighbourhood freeness with its adjacent-degree
condition and the arbitrary-perfect-complex relative-Tor tier remain
separate obligations.

[BaseChangeLocus](BaseChangeLocus.lean) now supplies the previously separate
basic-open original-map conclusion. For this same supplied `D`, surjectivity
of the original degree-`q` comparison to `p.asIdeal.ResidueField` gives
`r ∉ p.asIdeal` such that every `τ : Localization.Away r →+* B` makes the
original `moduleCohomologyBaseChangeMap f (τ.comp (algebraMap R _)) M q`
invertible. The proof uses the actual outgoing cokernel's native free locus,
localizes `D.complex.sc q`, and applies the unchanged native mate composition
identity before the original geometric comparison square. No new localized
model, reducedness, Noetherianity, or target-ring flatness is assumed. The
original morphism, coefficient and ordinary fibre products are retained.
A general-target sheaf descent and neighbourhood freeness with its
adjacent-degree condition remain further steps.
