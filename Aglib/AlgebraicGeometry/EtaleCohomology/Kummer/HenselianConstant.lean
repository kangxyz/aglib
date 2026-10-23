/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.HenselianConstant.Cover
public import Aglib.AlgebraicGeometry.EtaleCohomology.H1.ConstantFinite.Basic
public import Aglib.AlgebraicGeometry.EtaleCohomology.Kummer.CoefficientBaseChange

/-!
# Actual constant-root coefficients over a strictly henselian local base

The coefficient map is the native constant-sheaf adjoint of actual cyclic
coordinates on global root sections. Its underlying set map is the map of the
actual split root cover; hence it is an isomorphism. No arithmetic marking,
perfectness, completeness or Noetherianity premise is retained.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Group
open scoped CategoryTheory.MonObj
open AlgebraicGeometry.Scheme.FiniteEtale
open GroupCohomology.Kummer.Coefficients GroupCohomology.Kummer.CoefficientBaseChange

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant

universe u
attribute [local instance] hasSheafifyLarge

private theorem map_factor_through_iso {C D E : Type*}
    [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : C ⥤ E) (H : D ⥤ E) (e : F ⋙ H ≅ G)
    {A B : C} {L : D} (a : A ⟶ B) (c : F.obj B ⟶ L)
    (d : G.obj B ⟶ H.obj L) (hc : H.map c = e.hom.app B ≫ d) :
    e.inv.app A ≫ H.map (F.map a ≫ c) = G.map a ≫ d := by
  have hn : G.map a ≫ e.inv.app B = e.inv.app A ≫ H.map (F.map a) :=
    e.inv.naturality a
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, ← hn]
  rw [Category.assoc, hc, ← Category.assoc (e.inv.app B),
    e.inv_hom_id_app, Category.id_comp]

private theorem forget_constant_adjoint (X : Scheme.{u})
    (A : AddCommGrpCat.{u + 1}) (L : AbelianSheaf.{u, u + 1} X)
    (e : A ⟶ (globalSections X).obj L) :
    ((constantCommuteCompose (Scheme.smallEtaleTopology X)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).inv.app A) ≫
      (underlyingSetFunctor X).map (((constantAdjunction X).homEquiv A L).symm e) =
    ((constantSheafAdj (Scheme.smallEtaleTopology X) (Type (u + 1))
      (etaleTerminalIsTerminal X)).homEquiv _ _).symm
        ((CategoryTheory.forget AddCommGrpCat.{u + 1}).map e) := by
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
  exact map_factor_through_iso
    (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1})
    (CategoryTheory.forget AddCommGrpCat.{u + 1} ⋙
      constantSheaf (Scheme.smallEtaleTopology X) (Type (u + 1)))
    (underlyingSetFunctor X)
    (constantCommuteCompose (Scheme.smallEtaleTopology X)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})) e _ _
    (constantSheafAdj_counit_w (Scheme.smallEtaleTopology X)
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) L (etaleTerminalIsTerminal X)).symm

private theorem trivialCoverConstantIso_adjoint (X : Scheme.{u})
    (A : Type u) [Finite A] :
    ((constantSheafAdj (Scheme.smallEtaleTopology X) (Type (u + 1))
      (etaleTerminalIsTerminal X)).homEquiv _ _)
        (trivialCoverConstantIso X A).inv =
      ↾(fun a : ULift.{u + 1} A =>
        ULift.up (trivialCoverSection X A (etaleTerminal X) a.down)) := by
  change (constantPresheafAdj (Type (u + 1)) (etaleTerminalIsTerminal X)).homEquiv _ _
    ((sheafificationAdjunction (Scheme.smallEtaleTopology X) (Type (u + 1))).homEquiv
      ((Functor.const X.Etaleᵒᵖ).obj (ULift.{u + 1} A))
      (finiteCoverSectionSheaf (trivialCover X A))
      (((sheafificationAdjunction (Scheme.smallEtaleTopology X) (Type (u + 1))).homEquiv
        ((Functor.const X.Etaleᵒᵖ).obj (ULift.{u + 1} A))
        (finiteCoverSectionSheaf (trivialCover X A))).symm
          (constantTrivialPresheafMap X A))) = _
  rw [Equiv.apply_symm_apply]
  rfl

variable (R : Type u) [CommRing R] [HenselianLocalRing R]
  [IsSepClosed (IsLocalRing.ResidueField R)]
  (n : ℕ) (hn : 0 < n) (hinv : IsUnit (n : Γ(Spec (.of R), ⊤)))

attribute [local instance] Over.cartesianMonoidalCategory
/-- The native commutative group structure on the actual scheme of n-th roots. -/
local instance : CommGrpObj (MultiplicativeGroup.rootsScheme (Spec (.of R)) n) :=
  MultiplicativeGroup.rootsCommGroup (Spec (.of R)) n

/-- The actual cyclic coordinate map on the original global sections of mu_n. -/
def globalRootValues :
    ConstantFinite.value (ULift.{u} (ZMod n)) ≅
      (globalSections (Spec (.of R))).obj (mu (Spec (.of R)) n) :=
  ((AddEquiv.ulift.trans
    (AddEquiv.ulift.trans (globalRootCoordinates R n hn hinv))).trans
    AddEquiv.ulift.symm).toAddCommGrpIso

/-- The additive coefficient map is defined through the native constant-sheaf adjunction. -/
def constantRootMap :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of R)) ⟶ mu (Spec (.of R)) n :=
  ((constantAdjunction (Spec (.of R))).homEquiv _ _).symm
    (globalRootValues R n hn hinv).hom

/-- Its exact adjunction normalization is the original map of global root sections. -/
theorem constantRootMap_adjoint :
    ((constantAdjunction (Spec (.of R))).homEquiv _ _)
      (constantRootMap R n hn hinv) = (globalRootValues R n hn hinv).hom :=
  Equiv.apply_symm_apply _ _

/-- The underlying set map is the sheaf map of the actual split root cover. -/
theorem constantRootMap_underlying :
    let : NeZero n := ⟨hn.ne'⟩
    ((constantCommuteCompose (Scheme.smallEtaleTopology (Spec (.of R)))
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).inv.app
          (ConstantFinite.value (ULift.{u} (ZMod n)))) ≫
      (underlyingSetFunctor (Spec (.of R))).map (constantRootMap R n hn hinv) =
    (trivialCoverConstantIso (Spec (.of R)) (ULift.{u} (ZMod n))).inv ≫
      (finiteCoverSectionSheafFunctor (Spec (.of R))).map (rootCoverMap R n hn hinv) := by
  let : NeZero n := ⟨hn.ne'⟩
  rw [constantRootMap, forget_constant_adjoint]
  apply ((constantSheafAdj (Scheme.smallEtaleTopology (Spec (.of R))) (Type (u + 1))
    (etaleTerminalIsTerminal (Spec (.of R)))).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
    trivialCoverConstantIso_adjoint]
  ext a
  apply ULift.ext
  change (globalRootCoordinates R n hn hinv a.down.down).toMul =
    trivialCoverSection (Spec (.of R)) (ULift.{u} (ZMod n))
      (etaleTerminal (Spec (.of R))) a.down ≫
      (rootCoverMap R n hn hinv).hom
  apply Over.OverMorphism.ext
  have h := congrArg (fun k => k.left) (rootCoverMap_component R n hn hinv a.down)
  change (globalRootCoordinates R n hn hinv a.down.down).toMul.left =
    (𝟙 (Spec (.of R)) ≫
      (trivialCoverι (Spec (.of R)) (ULift.{u} (ZMod n)) a.down).hom.left) ≫
        (rootCoverMap R n hn hinv).hom.left
  rw [Category.id_comp]
  exact h.symm

/-- The actual additive coefficient map is invertible because its finite-cover map is. -/
instance constantRootMap_isIso : IsIso (constantRootMap R n hn hinv) := by
  let : NeZero n := ⟨hn.ne'⟩
  let : IsIso (rootCoverMap R n hn hinv) := (rootCoverIso R n hn hinv).isIso_hom
  let e := (constantCommuteCompose (Scheme.smallEtaleTopology (Spec (.of R)))
    (CategoryTheory.forget AddCommGrpCat.{u + 1})).app (ConstantFinite.value (ULift.{u} (ZMod n)))
  have : IsIso (e.inv ≫ (underlyingSetFunctor (Spec (.of R))).map
      (constantRootMap R n hn hinv)) := by
    have heq : e.inv ≫ (underlyingSetFunctor (Spec (.of R))).map
        (constantRootMap R n hn hinv) =
      (trivialCoverConstantIso (Spec (.of R)) (ULift.{u} (ZMod n))).inv ≫
        (finiteCoverSectionSheafFunctor (Spec (.of R))).map (rootCoverMap R n hn hinv) :=
      constantRootMap_underlying R n hn hinv
    rw [heq]
    infer_instance
  have : IsIso ((underlyingSetFunctor (Spec (.of R))).map
      (constantRootMap R n hn hinv)) := IsIso.of_isIso_comp_left e.inv _
  exact isIso_of_reflects_iso _ (underlyingSetFunctor (Spec (.of R)))

/-- A genuine constant/root coefficient isomorphism over any strictly henselian local ring. -/
def constantRootIso :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) (Spec (.of R)) ≅ mu (Spec (.of R)) n :=
  asIso (constantRootMap R n hn hinv)

/-- Pull the same chosen base isomorphism to an arbitrary scheme over the base. -/
def constantRootIsoOver {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) :
    ConstantFinite.coefficient (ULift.{u} (ZMod n)) X ≅ mu X n :=
  ((inverseImageConstantIso p).app (ConstantFinite.value (ULift.{u} (ZMod n)))).symm ≪≫
    (inverseImage p).mapIso (constantRootIso R n hn hinv) ≪≫ rootsPullbackIso p n hn hinv

end AlgebraicGeometry.Scheme.EtaleCohomology.Kummer.HenselianConstant
