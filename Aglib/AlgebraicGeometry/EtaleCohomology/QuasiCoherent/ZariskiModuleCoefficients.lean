/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.QuasiCoherent.ZariskiModuleComparison

/-! # Naturality of the original Zariski module identification -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent

/-- The open-section comparison preserves actual module coefficient morphisms. -/
theorem openPullbackSectionsIso_coefficient_naturality (X : Scheme.{u})
    {F G : X.Modules} (g : F ⟶ G) (U : X.Opens) (s : Γ((pullback U.ι).obj F, ⊤)) :
    (openPullbackSectionsIso X G U).hom
        (Scheme.Modules.Hom.app ((pullback U.ι).map g) ⊤ s) =
      Scheme.Modules.Hom.app g U ((openPullbackSectionsIso X F U).hom s) := by
  rw [openPullbackSectionsIso_hom_apply, openPullbackSectionsIso_hom_apply]
  have h := congrArg (fun k => Scheme.Modules.Hom.app k ⊤ s)
    ((restrictFunctorIsoPullback U.ι).inv.naturality g)
  refine (congrArg (fun t : Γ(G.restrict U.ι, ⊤) =>
    G.presheaf.map (eqToHom U.ι_image_top.symm).op t) h).trans ?_
  exact (ConcreteCategory.congr_hom
    (g.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op)
    (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback U.ι).inv.app F) ⊤ s)).symm

/-- The open inclusion comparison has identity components before applying the section functor. -/
theorem zariskiModuleIso_hom_app (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) :
    (zariskiModuleIso X F).hom.hom.app (op U) =
      (zariskiModulePresheafIso X F).hom.app (op U) := by
  change (𝟙 _) ≫ (additiveSectionsPresheaf X F).map (𝟙 _) ≫
    (zariskiModulePresheafIso X F).hom.app (op U) = _
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

/-- The actual lifted module comparison still has the original section components. -/
theorem zariskiModuleIso_hom_down (X : Scheme.{u}) (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens)
    (s : ((zariskiRestriction X).obj (additiveCoefficient X F)).obj.obj (op U)) :
    (((zariskiModuleIso X F).hom.hom.app (op U)) s).down =
      (openPullbackSectionsIso X F U).hom s.down := by
  rw [zariskiModuleIso_hom_app]
  rfl

/-- The original module-to-sheaf coefficient map commutes with the actual site restriction iso. -/
theorem zariskiModuleIso_naturality (X : Scheme.{u}) {F G : X.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (g : F ⟶ G) :
    (zariskiRestriction X).map (additiveCoefficientMap X g) ≫ (zariskiModuleIso X G).hom =
      (zariskiModuleIso X F).hom ≫
        (Sheaf.BasisAcyclicity.valueLift.{u,u,u,u+1} (Opens.grothendieckTopology X)).map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map g) := by
  ext U s
  apply ULift.ext
  change (((zariskiModuleIso X G).hom.hom.app U)
    (((additiveCoefficientMap X g).hom.app ((opensToEtale X).op.obj U)) s)).down = _
  rw [zariskiModuleIso_hom_down]
  change (openPullbackSectionsIso X G U.unop).hom
    (Scheme.Modules.Hom.app ((pullback U.unop.ι).map g) ⊤ s.down) =
      Scheme.Modules.Hom.app g U.unop
        ((((zariskiModuleIso X F).hom.hom.app U) s).down)
  rw [zariskiModuleIso_hom_down]
  exact openPullbackSectionsIso_coefficient_naturality X g U.unop s.down

end AlgebraicGeometry.Scheme.EtaleCohomology.QuasiCoherent
