/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Counit
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Hom
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FrameSections

/-!
# The original top class on the common sheaf model

The actual model section is represented by the original ordered Koszul
class, original coefficient frame and original tilde/counit homology map.
Its quotient coordinate is the original ring representative. Equality on
its global class-one section consequently detects actual sheaf arrows.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u w
namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} (s : List A)

/-- The literal quotient ring of the original ordered regular list. -/
abbrev regularListQuotientRing : CommRingCat.{u} := .of (A ⧸ Ideal.ofList s)

/-- The literal quotient map, retained in the installed spectral closed immersion. -/
abbrev regularListQuotientMap : A ⟶ regularListQuotientRing s :=
  CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s))

variable (hs : RingTheory.Sequence.IsWeaklyRegular A s)
  {L : (Spec A).Modules} [L.IsQuasicoherent]
  (J : InjectiveResolution L) (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of A A)
  [HasExt.{w} (ModuleCat.{u} A)]

local instance : (moduleSpecΓFunctor (R := regularListQuotientRing s)).Additive :=
  moduleSpecΓFunctor_additive _

/-- The original class on the actual model, before the native derived-unit comparison. -/
def regularListModelTopClass (r : A) (U : (Spec (regularListQuotientRing s)).Opens) :
    ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (s.length : ℤ)).val.obj (op U) := by
  let K := closedImmersionRightAdjointRegularListResolutionComplex s J
  let G := ((moduleSpecΓFunctor (R := regularListQuotientRing s)).mapHomologicalComplex
    (.up ℤ)).obj K
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (regularListQuotientRing s) (.up ℤ) K) :=
    closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
  let ξ := (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J
    s.length).symm ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r).comp
      (Ext.mk₀ e.inv) (add_zero s.length))
  exact (Complex.tildeGlobalSectionsHomologyIso (regularListQuotientRing s) (.up ℤ) K
    (s.length : ℤ)).hom.val.app (op U)
      (tilde.toOpen (G.homology (s.length : ℤ)) U ξ)

/-- The original model top frame evaluates the same original class to its ring representative. -/
theorem regularListModelTopClass_unitFrame (r : A)
    (U : (Spec (regularListQuotientRing s)).Opens) :
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom.val.app
        (op U) (regularListModelTopClass s hs J e r U) =
      tilde.toOpen (ModuleCat.of (regularListQuotientRing s) (regularListQuotientRing s)) U
        (Ideal.Quotient.mk (Ideal.ofList s) r) := by
  let B := regularListQuotientRing s
  let K := closedImmersionRightAdjointRegularListResolutionComplex s J
  let G := ((moduleSpecΓFunctor (R := B)).mapHomologicalComplex (.up ℤ)).obj K
  let : QuasiIso (Complex.tildeGlobalSectionsCounit B (.up ℤ) K) :=
    closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
  exact tildeFrame_class B (G.homology (s.length : ℤ)) (K.homology (s.length : ℤ))
    (Complex.tildeGlobalSectionsHomologyIso B (.up ℤ) K (s.length : ℤ))
    (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J e)
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom s hs J e)
    (closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J s.length)
    ((ChainComplex.Koszul.topExtClass s hs (ModuleCat.of A A) r).comp
      (Ext.mk₀ e.inv) (add_zero s.length))
    (Ideal.Quotient.mk (Ideal.ofList s) r)
    (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class s hs J e r) U

/-- Class one is the actual section-one generator in the original model frame. -/
theorem regularListModelTopClass_one (U : (Spec (regularListQuotientRing s)).Opens) :
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom.val.app
        (op U) (regularListModelTopClass s hs J e (1 : A) U) =
      (1 : Γ(Spec (regularListQuotientRing s), U)) := by
  have h := regularListModelTopClass_unitFrame s hs J e (1 : A) U
  rw [map_one] at h
  exact h.trans (tilde_toOpen_self_one (R := regularListQuotientRing s) U)

/-- The original global class-one section detects equality of actual arrows from model homology.
The target is arbitrary, with no quasicoherence assumption. -/
theorem regularListModelTopClass_hom_ext_global
    {N : (Spec (regularListQuotientRing s)).Modules}
    {f g : (closedImmersionRightAdjointRegularListResolutionComplex s J).homology
      (s.length : ℤ) ⟶ N}
    (hfg : f.val.app (op ⊤) (regularListModelTopClass s hs J e (1 : A) ⊤) =
      g.val.app (op ⊤) (regularListModelTopClass s hs J e (1 : A) ⊤)) : f = g := by
  let Z := Spec (regularListQuotientRing s)
  let F := closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e
  let ξ := regularListModelTopClass s hs J e (1 : A) ⊤
  have hi : F.inv.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤)) = ξ := by
    have h := regularListModelTopClass_one s hs J e ⊤
    have hcancel := congrArg (fun z => z.val.app (op ⊤) ξ) F.hom_inv_id
    exact (congrArg (F.inv.val.app (op ⊤)) h.symm).trans hcancel
  apply (cancel_epi F.inv).mp
  apply (unitHomGlobalSectionsEquiv Z N).injective
  change f.val.app (op ⊤) (F.inv.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤))) =
    g.val.app (op ⊤) (F.inv.val.app (op ⊤) (1 : Z.ringCatSheaf.obj.obj (op ⊤)))
  exact (congrArg (f.val.app (op ⊤)) hi).trans
    (hfg.trans (congrArg (g.val.app (op ⊤)) hi).symm)

end AlgebraicGeometry.Scheme.Modules
