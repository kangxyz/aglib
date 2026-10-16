/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Coherent.Localization.Fractions
public import Aglib.AlgebraicGeometry.Modules.Coherent.Extension.Subobjects

/-!
# Fullness of the coherent quotient comparison

The specified quasicoherent direct-image criterion implies fullness of the actual quotient
comparison. Locally Noetherian geometry supplies the criterion.
-/

/-!
Source: frozen dirty Quillen `6db56ddd3fdb898ef5de29d5fe51a0c61f9ba116`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/SubobjectExtension.lean`.
SHA-256: `c3d895a552379d147cf37e13109c25c3d5f82b4144b50fd96f8e70b5987cdf79`.
`Quillen/AlgebraicGeometry/Scheme/Coherent/Localization/Fullness.lean`.
SHA-256: `61afed4d0f4e8a0a3ffbefa660420929f4823a2a75701f5a9115cad7f0bbe9ec`.
Selected original statements and proofs; canonical lower APIs replace the recorded source wrappers.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ModuleCat
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open CategoryTheory.ExactCategory
namespace AlgebraicGeometry.Scheme.Modules.Coherent
variable {U X : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- Quasicoherent open pushforward, once proved geometrically, suffices for
fullness of the genuine coherent support quotient. -/
theorem quotientCoherentRestriction_full_of_quasicoherent_pushforward
    (hPush : ∀ (M : U.Modules), M.IsQuasicoherent →
      ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent) :
    (quotientCoherentRestriction j).Full := by
  apply quotientCoherentRestriction_full_of_subobject_extension j
  intro H A i hi
  have : Mono i := hi
  have : (cokernel i.hom).IsQuasicoherent := quasicoherent_cokernel i.hom
  have : ((Scheme.Modules.pushforward j).obj (cokernel i.hom)).IsQuasicoherent :=
    hPush _ inferInstance
  exact affineLocallyFiniteType_subobject_extension_of_quasicoherent_pushforward j H A i

/-- The canonical functor from the actual support quotient is full.
Faithfulness and exactness were already proved in `Quotient`. -/
instance quotientCoherentRestriction_full : (quotientCoherentRestriction j).Full := by
  apply quotientCoherentRestriction_full_of_quasicoherent_pushforward j
  intro M hM
  have : M.IsQuasicoherent := hM
  exact quasicoherent_pushforward_open_of_locallyNoetherian j M

end AlgebraicGeometry.Scheme.Modules.Coherent
