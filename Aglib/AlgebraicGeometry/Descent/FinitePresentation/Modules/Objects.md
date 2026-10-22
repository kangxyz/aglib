# Finitely presented module objects on actual scheme limits

[Objects.lean](Objects.lean) descends an actual finitely presented
quasicoherent module over a cofiltered limit of qcqs schemes with affine
transition maps. The rings and original stage maps have no Noetherian,
flatness or injectivity restriction.

`Scheme.Modules.exists_model_above_of_isLimit D c hc i₀ M` takes the
actual limiting cone, a prescribed stage, and the actual fp module on the
limit. It produces a later stage `j → i₀`, an fp module `N` on `D.obj j`,
and a native isomorphism `(pullback (c.π.app j)).obj N ≅ M`. It assumes
compactness and quasi-separatedness of each stage and affine transition
maps. A desired module model or a desired descent family is not an input.

The proof uses induction on compact opens of the actual limit. A local
model records a compact stage open whose exact inverse image is the
original limit open, an fp module on that stage open, and a native
pullback isomorphism to the restriction of `M`. The affine case uses
[Affine](Affine.lean) and the native affine-open model theorem. Rebase
uses the original transition map and cone equation. The open diagram is
the native `opensDiagram`; its auxiliary cone has the original open as
its literal point and is limiting by the native open-subscheme limit
theorem.

For a binary union, the actual two local models first move to one common
stage. Their overlap at the limit is chosen as the literal pullback of
the original stage overlap. `exists_binary_overlap_of_squares` constructs
its original chart projections by native pullback lifts, proves their
universal property, and retains every original projection equation. The
existing `baseChangeDiagram` and `baseChangeCone` are therefore the actual
overlap system.

The original transition isomorphism is transported through native
`pullbackSquareIso` components and descended with its inverse by
[Properties](Properties.lean). Both chart modules then pull back to the
resulting later stage. The native Zariski module stack glues them to an
actual fp object. The recovering isomorphism retains the original
transition through the square-cone component identity and
`lift_conjugate_recovery` from [Maps](Maps.lean), followed by native full
faithfulness of module descent. No reflection of a property through an
arbitrary scalar map is used. Finally, the native eventual-top-open
lemma supplies a whole later stage, and the native top-open isomorphism
recovers an actual module on that stage.

`exists_binary_finitePresentation_glued` is the underlying binary object
gluing result. It supplies genuine native descent data: the two self
transitions are identities, and the cocycles follow from the two inverse
equations. Its local recovering isomorphisms retain the original overlap
map. `nonempty_iso_of_binary_restrictions` glues compatible actual local
isomorphisms between two original global module sheaves.

`exists_model_on_baseChanges` specializes the global theorem to the
literal base changes of an already given qcqs scheme model. It uses
`Scheme.baseChangeDiagram`, its actual limiting cone, and the original
cone projection as the recovering pullback map. The ring-colimit form is
`exists_model_on_baseChanges_of_isColimit`: for the original filtered
ring functor, cocone, stage `i` and given scheme over `Spec (F.obj i)`, it
returns an original later ring arrow `q : i → j`, a module on the literal
`pullback (Spec.map (F.map q)) f`, and the specified canonical native
pullback isomorphism to the original limit module. This also applies to
an already given finitely presented qcqs scheme model; the module result
only needs its quasi-compact and quasi-separated structural map.

`exists_common_models_on_affine_baseChanges` additionally places a finite
family of actual affine-chart module models at one common stage, using
native cofilteredness and the original pullback composition comparisons.
Finite global diagrams are handled in the separate [Diagrams](Diagrams.lean)
owner. Eventual original-stage isomorphisms and local rank one are handled
in [Properties](Properties.lean).
