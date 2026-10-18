/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Current interface basis: 46f53465aaf3b0167049e9c8e9e2294111bb4281.
Original construction and mathematical provenance are retained below. -/
public import Aglib.AlgebraicGeometry.Cohomology.EtaleH1.PullbackCoherence

/-! Composition of actual étale H¹ pullback, including the constant transport.

Construction prerequisite for `K2-018#eq:k2018-pointed-character`, on frozen
interface basis `7f86e4a1763cc4ec35e9b0a8acd659750355a0de`.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.EtaleH1
universe u
attribute [local instance] hasSheafifyLarge

/-- The identity étale object is the fixed terminal object. -/
abbrev etaleTerminal (X : Scheme.{u}) : X.Etale := Scheme.Etale.mk (𝟙 X)

/-- The terminal structure on the identity etale object of `X`. -/
def etaleTerminalIsTerminal (X : Scheme.{u}) : IsTerminal (etaleTerminal X) :=
  MorphismProperty.Over.mkIdTerminal (@Etale : MorphismProperty Scheme.{u}) X

/-- Canonical preservation of the fixed terminal object. -/
def siteBaseChangeTerminalIso {X S : Scheme.{u}} (f : S ⟶ X) :
    (siteBaseChange f).obj (etaleTerminal X) ≅ etaleTerminal S :=
  ((etaleTerminalIsTerminal X).isTerminalObj (siteBaseChange f)).uniqueUpToIso
    (etaleTerminalIsTerminal S)

/-- The global-sections functor obtained by evaluation at the identity etale object of `X`. -/
abbrev globalSections (X : Scheme.{u}) : AbelianSheaf.{u, u + 1} X ⥤ AddCommGrpCat.{u + 1} :=
  (sheafSections (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj (op (etaleTerminal X))

/-- The adjunction between the constant abelian sheaf functor and global sections on `X`. -/
def constantAdjunction (X : Scheme.{u}) :
    constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⊣ globalSections X :=
  constantSheafAdj _ _ (etaleTerminalIsTerminal X)

/-- The direct-image functor on abelian sheaves induced by small-etale base change along `f`. -/
abbrev directImage {X S : Scheme.{u}} (f : S ⟶ X) :
    AbelianSheaf.{u, u + 1} S ⥤ AbelianSheaf.{u, u + 1} X :=
  (siteBaseChange f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- The inverse-image/direct-image adjunction on abelian sheaves for `f`. -/
abbrev inverseImageAdjunction {X S : Scheme.{u}} (f : S ⟶ X) :
    inverseImage f ⊣ directImage f :=
  (siteBaseChange f).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
    (Scheme.smallEtaleTopology X) (Scheme.smallEtaleTopology S)

/-- Global sections commute with actual direct image via terminal transport. -/
def directImageGlobalSectionsIso {X S : Scheme.{u}} (f : S ⟶ X) :
    directImage f ⋙ globalSections X ≅ globalSections S :=
  NatIso.ofComponents (fun L => L.obj.mapIso (siteBaseChangeTerminalIso f).symm.op)
    (fun q => (q.hom.naturality (siteBaseChangeTerminalIso f).inv.op).symm)

/-- An adjunction-mate description with a fixed terminal object at every base. -/
def inverseImageConstantCanonicalIso {X S : Scheme.{u}} (f : S ⟶ X) :
    constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1} ⋙ inverseImage f ≅
      constantSheaf (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1} :=
  Adjunction.leftAdjointCompIso (constantAdjunction X) (inverseImageAdjunction f)
    (constantAdjunction S) (directImageGlobalSectionsIso f)

/-- The fixed-terminal mate is the already constructed constant-sheaf transport. -/
theorem inverseImageConstantCanonicalIso_eq {X S : Scheme.{u}} (f : S ⟶ X) :
    inverseImageConstantCanonicalIso f = inverseImageConstantIso f := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  let cAdj := constantAdjunction X
  let adj := inverseImageAdjunction f
  let targetAdj := constantSheafAdj (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}
    ((etaleTerminalIsTerminal X).isTerminalObj (siteBaseChange f))
  apply ((cAdj.comp adj).homEquiv _ _).injective
  refine Eq.trans (unit_conjugateEquiv_symm (constantAdjunction S)
    (cAdj.comp adj) (directImageGlobalSectionsIso f).inv A).symm ?_
  refine Eq.trans ?_ (Adjunction.homEquiv_leftAdjointUniq_hom_app
    (cAdj.comp adj) targetAdj A).symm
  change (toSheafify (Scheme.smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj A)).app
      (op (etaleTerminal S)) ≫
    (sheafify (Scheme.smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj A)).map
      (siteBaseChangeTerminalIso f).hom.op =
    (toSheafify (Scheme.smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj A)).app
      (op ((siteBaseChange f).obj (etaleTerminal X)))
  exact ((toSheafify (Scheme.smallEtaleTopology S) ((Functor.const S.Etaleᵒᵖ).obj A)).naturality
    (siteBaseChangeTerminalIso f).hom.op).symm.trans (Category.id_comp _)

/-- Actual direct-image composition induced by base change of test schemes. -/
def directImageCompIso {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) :
    directImage g ⋙ directImage f ≅ directImage (g ≫ f) :=
  Functor.sheafPushforwardContinuousComp' (siteBaseChangeComp f g).symm
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology X)
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology T)

/-- Right-adjoint coherence is the uniqueness of maps between terminal objects. -/
theorem directImageGlobalSectionsIso_comp {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) :
    Functor.isoWhiskerLeft (directImage g) (directImageGlobalSectionsIso f) ≪≫
      directImageGlobalSectionsIso g =
    (Functor.associator (directImage g) (directImage f) (globalSections X)).symm ≪≫
      Functor.isoWhiskerRight (directImageCompIso f g) (globalSections X) ≪≫
        directImageGlobalSectionsIso (g ≫ f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext L
  change L.obj.map ((siteBaseChange g).map (siteBaseChangeTerminalIso f).inv).op ≫
      L.obj.map (siteBaseChangeTerminalIso g).inv.op =
    L.obj.map ((siteBaseChangeComp f g).hom.app (etaleTerminal X)).op ≫
      L.obj.map (siteBaseChangeTerminalIso (g ≫ f)).inv.op
  rw [← L.obj.map_comp, ← L.obj.map_comp]
  apply congrArg L.obj.map
  exact congrArg Quiver.Hom.op
    ((((etaleTerminalIsTerminal X).isTerminalObj (siteBaseChange f)).isTerminalObj
      (siteBaseChange g)).hom_ext _ _)

/-- The actual inverse-image composition is compatible with constant sheaves. -/
theorem inverseImageComp_constant {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (A : AddCommGrpCat.{u + 1}) :
    (inverseImageComp f g).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) ≫
      (inverseImage g).map ((inverseImageConstantIso f).hom.app A) ≫
        (inverseImageConstantIso g).hom.app A =
      (inverseImageConstantIso (g ≫ f)).hom.app A := by
  have h := Adjunction.leftAdjointCompIso_assoc
    (constantAdjunction X) (inverseImageAdjunction f) (inverseImageAdjunction g)
    (constantAdjunction S) (inverseImageAdjunction (g ≫ f)) (constantAdjunction T)
    (directImageGlobalSectionsIso f) (directImageCompIso f g)
    (directImageGlobalSectionsIso (g ≫ f)) (directImageGlobalSectionsIso g)
    (directImageGlobalSectionsIso_comp f g)
  have hA := congrArg (fun e => e.hom.app A) h
  change (inverseImageComp f g).inv.app
      ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) ≫
      (inverseImageConstantCanonicalIso (g ≫ f)).hom.app A =
    (inverseImage g).map ((inverseImageConstantCanonicalIso f).hom.app A) ≫
      (inverseImageConstantCanonicalIso g).hom.app A at hA
  rw [inverseImageConstantCanonicalIso_eq, inverseImageConstantCanonicalIso_eq,
    inverseImageConstantCanonicalIso_eq] at hA
  rw [← hA]
  simp

/-- Inverse constant transports satisfy the corresponding composition formula. -/
theorem inverseImageComp_constant_inv {X S T : Scheme.{u}}
    (f : S ⟶ X) (g : T ⟶ S) (A : AddCommGrpCat.{u + 1}) :
    (inverseImageConstantIso (g ≫ f)).inv.app A ≫
      (inverseImageComp f g).hom.app
        ((constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj A) =
    (inverseImageConstantIso g).inv.app A ≫
      (inverseImage g).map ((inverseImageConstantIso f).inv.app A) := by
  apply (cancel_mono ((inverseImage g).map ((inverseImageConstantIso f).hom.app A) ≫
    (inverseImageConstantIso g).hom.app A)).mp
  simp only [Category.assoc]
  rw [inverseImageComp_constant]
  simp [← Functor.map_comp_assoc]

section Cohomology
universe w w' w''
variable {X S T : Scheme.{u}}
variable [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
variable [HasExt.{w'} (AbelianSheaf.{u, u + 1} S)]
variable [HasExt.{w''} (AbelianSheaf.{u, u + 1} T)]

/-- Actual scheme H¹ pullback composes contravariantly, with its canonical
coefficient identification. -/
theorem h1Pullback_comp (f : S ⟶ X) (g : T ⟶ S)
    (L : AbelianSheaf.{u, u + 1} X) (a : H1Etale X L) :
    coefficientMap ((inverseImageComp f g).hom.app L) (h1Pullback (g ≫ f) L a) =
      h1Pullback g ((inverseImage f).obj L) (h1Pullback f L a) := by
  change ((Abelian.Ext.mk₀ _).comp (a.mapExactFunctor (inverseImage (g ≫ f)))
      (zero_add 1)).comp (Abelian.Ext.mk₀ ((inverseImageComp f g).hom.app L)) (add_zero 1) =
    (Abelian.Ext.mk₀ _).comp
      (((Abelian.Ext.mk₀ _).comp (a.mapExactFunctor (inverseImage f))
        (zero_add 1)).mapExactFunctor (inverseImage g)) (zero_add 1)
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mapExactFunctor_comp_mk₀_natTransApp,
    Abelian.Ext.comp_mapExactFunctor, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_mk₀]
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Abelian.Ext.mk₀_comp_mk₀_assoc]
  congr 2
  exact inverseImageComp_constant_inv f g _

end Cohomology
end AlgebraicGeometry.Scheme.EtaleH1

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 8e2dd9530a1b459baf470c1c10ea958c17c1fdfcc85024b67398e5b166115073.
Definitions, hypotheses and universes are retained modulo native names. -/
