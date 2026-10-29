# Ext pairings for duality on the small étale site

Coefficients are genuine module sheaves `ModuleSheaf X Λ` over the constant ring sheaf of an
arbitrary ring `Λ : Type (u+1)`; sheaves of `ℤ/n`-modules (`Sh(X_et, n)`, Milne LEC p. 102) are
the case `Λ = ULift (ZMod n)`, for every `n`. `Ext` is Mathlib's `Abelian.Ext` in that category
and `HasExt` is a displayed size hypothesis (standard instances: `HasExt.standard`,
`SheafOfModules.hasExt`). The morphism `j : U ⟶ X` is étale (open immersions in the duality
application). Extension by zero is `moduleLowerShriek j Λ` with
`moduleLowerShriekAdjunction : j_! ⊣ moduleInverseImage j Λ`.

| Source | Interface |
| --- | --- |
| [ModuleCohomology](ModuleCohomology.lean) | `moduleUnitExtAddEquiv`: `Ext^q(Λ_X, G) ≃+ Sheaf.H (toSheaf G) q` among `Λ_X`-modules (Milne LEC p. 102), natural in `G` (`Sheaf.H.map`) and sending postcomposition with `hS.extClass` to `Sheaf.H.δ` of the underlying sequence. Étale specialization at independent Ext universes of `Sheaf.ModuleCoefficients.moduleExtCohomologyAddEquivLargeScalars`; at the standard universes it is `etaleModuleExtCohomologyAddEquivLargeScalars` by `rfl`. |
| [LowerShriekExt](LowerShriekExt.lean) | `moduleLowerShriekExt` (`Functor.mapExtAddHom` of `j_!`) with Yoneda composition, `mk₀` and `extClass`; `moduleLowerShriekExtEquiv` (`Adjunction.extEquiv`): `Ext^q(j_! A, B) ≃+ Ext^q(A, j^* B)`, compatible with Yoneda composition on both sides. |
| [LowerShriekCohomology](LowerShriekCohomology.lean) | `moduleLowerShriekCohomologyAddEquiv`: `Ext^r(Λ_X, j_! F) ≃+ Sheaf.H ((etaleLowerShriek j).obj (toSheaf F)) r` on the original objects (for an open immersion into a complete curve, `H^r_c(U, F)` of Milne LEC p. 92), natural in `F` and sending the module connecting map of `j_!` of a short exact sequence to `Sheaf.H.δ` of the abelian extension by zero of the underlying sequence. |
| [YonedaPairing](YonedaPairing.lean) | `moduleLowerShriekPairing c e h = c.comp (e.mapExactFunctor j_!) h`: `H^r_c(U, F) × Ext^s(F, G) → H^t_c(U, G)` (Milne LEC p. 103, "The pairing"). Biadditive (`moduleLowerShriekPairingHom`); natural in `F` and `G`; connecting maps with sign `+1` against precomposition with `extClass` (Mathlib `Ext.contravariantSequence`) and `(-1)^(s+1)` against Mathlib's signed `Ext.δ`; `moduleLowerShriekPairingDualHom` into total degree `d ≥ r` (`d = 2` for curves) with its three squares. |
| [RootsOfUnity](RootsOfUnity.lean) | `moduleRootsOfUnity X n`: the sheaf `μ_n` as a module sheaf over the constant ring `ULift (ZMod n)`, with `moduleRootsOfUnityUnderlyingIso` to `GroupCohomology.Kummer.Coefficients.mu X n`. |

The groups carry no `Λ`-linear structure from Mathlib's `Ext/Linear.lean`: the module-sheaf
categories have no `Linear` instance, so bilinearity is biadditivity. The trace
`H^2_c(U, μ_n) ≅ ℤ/n`, perfectness and local cohomology at points are not asserted here. No
production module consumes this family yet; it serves Poincaré duality for curves (Milne LEC
Thm 14.7, p. 93, and Thm 14.20, p. 101).
