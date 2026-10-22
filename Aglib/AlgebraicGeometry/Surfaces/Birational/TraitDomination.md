# Regular common domination over the original trait

Import `Aglib.AlgebraicGeometry.Surfaces.Birational.TraitDomination`.

`exists_regular_commonDomination` retains the original domain DVR R, its specified fraction field F, the original proper flat integral source p:X→Spec R, an original proper integral target q:Y→Spec R, and the supplied isomorphism e over F between their literal generic fibres. The source X is regular with dimension at most two. Target regularity and a separate target-flatness premise are not needed. No excellence or existence of a regular model of an arbitrary singular seed is assumed.

The result constructs an actual finite `PointBlowupChain β` with source W and actual projections β:W→X and γ:W→Y. W is integral, regular, Noetherian and of dimension at most two. Its original structure map β≫p=γ≫q is proper and flat. Both projections are proper, surjective and birational over their original targets. Original Noetherianity of X is derived from properness over the DVR.

The literal generic-fibre isomorphisms eX and eY have forward maps equal to the native `Over.pullback (baseMap R F)` images of β and γ. They satisfy exactly eX≪≫e=eY. These equalities retain the original first projections and the original maps to Spec F, rather than replacing the generic fibres by function-field models.

`genericToSourceFibre` lifts the original generic-point map of X into its actual open generic fibre. `genericToGraph` then enters the actual graph of the specified e. Its original source projection and base triangles are exact, and it is dominant onto that integral graph. The genuine common-domination producer extends this original generic map from a regular point-blowup chain. Separatedness forces the first graph projection to be β. The resulting graph map h is retained, with h≫toSource=β and h≫toTarget=γ; it too is proper, surjective and birational, and its original generic-fibre map is an isomorphism.

The original chain generic comparison and original graph comparisons prove the second generic map is eX.hom≫e.hom. The two actual open generic fibres are dense in their integral models. Transporting the specified generic isomorphism through their canonical open-image isomorphisms constructs the actual partial isomorphisms used for birationality. The original structure map is flat by the native integral-dominant Dedekind criterion, through actual injective stalk maps and torsion-free modules.

For any supplied original sections sX and sY whose literal generic sections agree under e, the same W admits a unique sW with sW≫β=sX, sW≫γ=sY and sW≫(β≫p)=identity. The lift is the unique lift of the original sX through the proper β and its literal generic inverse. The given e-compatibility, original generic projection equations and separatedness of q force the second equation with the original sY. No alternative point or section is substituted.

All lower inputs are the actual native graph, point-chain, common-domination, Dedekind-flatness and proper-section suppliers. Native evidence is recorded separately against the exact source vector. This theorem starts with the given regular source X; it does not establish existence of a regular model from arbitrary initial singular data.
