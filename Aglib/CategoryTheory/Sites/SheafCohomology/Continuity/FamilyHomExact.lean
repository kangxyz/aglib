/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.FiniteFreeHom
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Exact Hom sequences from sectionwise surjectivity on a family

Only sections on the specified component objects are required to lift. No global
sectionwise epimorphism or projectivity of the free representable sheaf is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf.ModuleCoefficients

universe v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {ι : Type (max u v)} (U : ι → C)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Section lifts on each component lift a map from its free presheaf family. -/
theorem freeFamilyHom_surjective {F G : Sheaf J AddCommGrpCat.{max u v}}
    (g : F ⟶ G) (hs : ∀ i, Function.Surjective (g.hom.app (op (U i)))) :
    Function.Surjective (fun f : Presheaf.Cech.familyPresheaf U ⋙ AddCommGrpCat.free ⟶
      F.obj => f ≫ g.hom) := by
  classical
  intro f
  choose s hs using fun i => hs i (Presheaf.Cech.freeFamilyHomEquiv U G.obj f i)
  refine ⟨(Presheaf.Cech.freeFamilyHomEquiv U F.obj).symm s, ?_⟩
  apply (Presheaf.Cech.freeFamilyHomEquiv U G.obj).injective
  funext i
  change g.hom.app (op (U i))
    (((Presheaf.Cech.freeFamilyHomEquiv U F.obj).symm s).app (op (U i))
      (FreeAbelianGroup.of ⟨i, 𝟙 _⟩)) = Presheaf.Cech.freeFamilyHomEquiv U G.obj f i
  have h := congrFun ((Presheaf.Cech.freeFamilyHomEquiv U F.obj).apply_symm_apply s) i
  rw [Presheaf.Cech.freeFamilyHomEquiv_apply] at h
  rw [h]
  exact hs i

variable [HasSheafify J AddCommGrpCat.{max u v}]

/-- The native Hom functor applied to a sheaf short exact sequence is short exact
when its right-hand map is surjective on this actual Hom group. -/
theorem presheafHom_shortExact
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v})
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hs : Function.Surjective (fun f : P ⟶ S.X₂.obj => f ≫ S.g.hom)) :
    (S.map (sheafToPresheaf J AddCommGrpCat ⋙
      preadditiveCoyoneda.obj (op P))).ShortExact := by
  let T := sheafToPresheaf J AddCommGrpCat ⋙ preadditiveCoyoneda.obj (op P)
  let : Mono S.f := hS.mono_f
  let : Epi (T.map S.g) := (AddCommGrpCat.epi_iff_surjective _).mpr hs
  exact {
    exact := hS.exact.map_of_mono_of_preservesKernel T inferInstance inferInstance
    mono_f := by
      change Mono ((preadditiveCoyoneda.obj (op P)).map
        ((sheafToPresheaf J AddCommGrpCat).map S.f))
      infer_instance
    epi_g := by
      change Epi (T.map S.g)
      infer_instance }

/-- A free-family Hom sequence needs surjectivity only on its component sections. -/
theorem freeFamilyHom_shortExact
    (S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})) (hS : S.ShortExact)
    (hs : ∀ i, Function.Surjective (S.g.hom.app (op (U i)))) :
    (S.map (sheafToPresheaf J AddCommGrpCat ⋙
      preadditiveCoyoneda.obj
        (op (Presheaf.Cech.familyPresheaf U ⋙ AddCommGrpCat.free)))).ShortExact :=
  presheafHom_shortExact _ S hS (freeFamilyHom_surjective U S.g hs)

end CategoryTheory.Sheaf.ModuleCoefficients
