/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.EtaleCover
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Coefficients.Underlying

/-! # Joint conservativity of original native module inverse images -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
universe u v
variable (Λ : Type (u + 1)) [Ring Λ] {S : Scheme.{u}} {ι : Type v}
  (U : ι → S.Etale)
  (hU : ∀ s : S, ∃ (i : ι) (x : (U i).left), (U i).hom x = s)

include hU in
/-- The actual inverse images on a jointly surjective étale family detect
isomorphisms of native constant-ring module sheaves, for any coefficient ring. -/
theorem isIso_of_module_etale_inverseImages {F G : ModuleSheaf S Λ} (a : F ⟶ G)
    (ha : ∀ i, IsIso ((moduleInverseImage (U i).hom Λ).map a)) : IsIso a := by
  have : IsIso ((SheafOfModules.toSheaf (constantRing S Λ)).map a) := by
    apply isIso_of_etale_inverseImages U hU
    intro i
    have : IsIso ((moduleInverseImage (U i).hom Λ).map a) := ha i
    apply (NatIso.isIso_map_iff (moduleInverseImageUnderlyingIso Λ (U i).hom) a).mp
    change IsIso ((SheafOfModules.toSheaf (constantRing (U i).left Λ)).map
      ((moduleInverseImage (U i).hom Λ).map a))
    infer_instance
  exact isIso_of_reflects_iso a (SheafOfModules.toSheaf (constantRing S Λ))

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
