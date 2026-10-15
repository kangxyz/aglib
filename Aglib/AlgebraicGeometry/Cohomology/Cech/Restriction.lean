/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Cech.Comparison
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
/-!
# Geometric restriction of the original Cech complex

For an open immersion, `restrictPreimagePresheafIso` identifies sections of
the actual restricted module sheaf with sections on intersections with the
open image. `cechRestrictIso` compares the original additive Cech complexes
for any family contained in that image and its geometric inverse image.
The comparison is built from actual section restriction isomorphisms.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w v v' v'' u u' u''
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped Simplicial
namespace AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Cech
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] (M : Y.Modules)

/-- The natural isomorphism identifying sections of `M.restrict j` on inverse-image opens with
sections of `M` on intersections with the image of `j`. -/
def restrictPreimagePresheafIso :
    (Opens.map j.base).op ⋙ (M.restrict j).presheaf ≅
      (intersectFunctor j.opensRange).op ⋙ M.presheaf := by
  refine NatIso.ofComponents (fun U => M.restrictAppIso j (j ⁻¹ᵁ U.unop) ≪≫
    M.presheaf.mapIso (eqToIso (show U.unop ⊓ j.opensRange = j ''ᵁ j ⁻¹ᵁ U.unop by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_comm])).op) ?_
  intro U V h
  dsimp
  rw [Scheme.Modules.map_restrictAppIso_hom_assoc]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

/-- The isomorphism from the Cech complex of `M` on the family `U` to that of `M.restrict j` on the
inverse-image family, when every `U i` lies in `j`'s image. -/
def cechRestrictIso {ι : Type u} (U : ι → Y.Opens) (hU : ∀ i, U i ≤ j.opensRange) :
    ((cechComplexFunctor U).obj M.presheaf) ≅
      ((cechComplexFunctor (fun i => j ⁻¹ᵁ U i)).obj (M.restrict j).presheaf) := by
  let : (Opens.map j.base).IsRightAdjoint := j.opensFunctorAdjunction.isRightAdjoint
  exact (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cechCosimplicialIntersectIso U M.presheaf j.opensRange hU) ≪≫
    (cechComplexFunctor U).mapIso (restrictPreimagePresheafIso j M).symm ≪≫
    (AlgebraicTopology.alternatingCofaceMapComplex _).mapIso
      (cechCosimplicialChangeIso (Opens.map j.base) U (M.restrict j).presheaf)

end AlgebraicGeometry.Scheme.Modules
