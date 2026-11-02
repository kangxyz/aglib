/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.CurveOpenConstants
public import Aglib.AlgebraicGeometry.EtaleCohomology.Vanishing.FiniteEtaleDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.ModuleCoefficients.FiniteEtaleDescent
public import Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GaloisSylowCover

/-! # Curve vanishing for actual Galois-trivialized coefficients

The actual Galois cover relative to its Sylow quotient has a p-group deck
group. Its literal trivialization, transported by the original triangle,
gives vanishing on a supplied finite completion of that quotient. The
prime-to-p degree and original trace descend vanishing to the original open.
The finite completion and its zero-dimensional closed boundary are geometric
data, not an assumed cohomological-dimension theorem.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing

open Constructible.Modules

universe u r e

attribute [local instance] hasSheafifyLarge ModuleCat.Sheaf.hasSheafify

/-- Prime-killed coefficients with an actual finite Galois trivialization have
zero high cohomology after extension by zero, once the actual Sylow quotient
is completed by a finite map from a proper curve with zero-dimensional boundary.
The coefficient ring may have any independent universe and characteristic. -/
theorem subsingleton_H_etaleLowerShriek_of_galois_finite_completion
    {k : Type u} [Field k] [IsSepClosed k]
    {X U C D : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
    (j : U ⟶ X) [IsOpenImmersion j] [ConnectedSpace U]
    (R : Type r) [CommRing R] [Finite R]
    (Y : Scheme.FiniteEtale U) [PreGaloisCategory.IsGalois Y]
    [Surjective Y.obj.hom] [ConnectedSpace Y.obj.left]
    [CompactSpace Y.obj.left] [QuasiSeparatedSpace Y.obj.left]
    (p : ℕ) [Fact p.Prime] (P : Sylow p (Aut Y))
    (b : C ⟶ X) [IsFinite b]
    (j' : (Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup).obj.left ⟶ C)
    [IsOpenImmersion j']
    (sq : IsPullback j'
      (Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup).obj.hom b j)
    (i : D ⟶ C) [IsClosedImmersion i]
    (hcomp : Set.range j' = (Set.range i)ᶜ)
    (hdimC : topologicalKrullDim C ≤ 1) (hdimD : topologicalKrullDim D ≤ 0)
    (F : ModuleSheaf R U) (M : ModuleCat.{u + 1} R) [Module.Finite R M]
    (hM : ∀ m : M, p • m = 0)
    (t : (moduleInverseImage R Y.obj.hom).obj F ≅
      (constantSheaf Y.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M)
    (q : ℕ) (hq : 2 < q) :
    Subsingleton (Sheaf.H.{e}
      ((etaleLowerShriek j).obj ((moduleUnderlying R U).obj F)) q) := by
  let Z : Scheme.FiniteEtale U :=
    Scheme.FiniteEtale.galoisSubgroupQuotient Y P.toSubgroup
  let V : Scheme.FiniteEtale Z.obj.left :=
    Scheme.FiniteEtale.galoisSubgroupRelative Y P.toSubgroup
  let : ConnectedSpace Z.obj.left := inferInstance
  let : PreGaloisCategory.IsGalois V :=
    Scheme.FiniteEtale.galoisSubgroupRelative_isGalois Y P.toSubgroup
  let : Surjective V.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupRelative_surjective Y P.toSubgroup
  let : ConnectedSpace V.obj.left := inferInstanceAs (ConnectedSpace Y.obj.left)
  let : CompactSpace V.obj.left := inferInstanceAs (CompactSpace Y.obj.left)
  let : QuasiSeparatedSpace V.obj.left := inferInstanceAs (QuasiSeparatedSpace Y.obj.left)
  let : HasExt.{u + 2} (AbelianSheaf.{u, u + 1} C) := HasExt.standard _
  let E := (moduleInverseImage R Z.obj.hom).obj F
  have htriangle : V.obj.hom ≫ Z.obj.hom = Y.obj.hom :=
    Scheme.FiniteEtale.galoisSubgroupQuotientπ_structure Y P.toSubgroup
  let t' : (moduleInverseImage R V.obj.hom).obj E ≅
      (constantSheaf V.obj.left.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M :=
    ((moduleInverseImageComp R Z.obj.hom V.obj.hom).app F).symm ≪≫
      eqToIso (congrArg (fun a => (moduleInverseImage R a).obj F) htriangle) ≪≫ t
  let : Subsingleton (Sheaf.H.{u + 2} ((etaleLowerShriek j').obj
      ((moduleUnderlying R Z.obj.left).obj E)) q) :=
    subsingleton_H_etaleLowerShriek_of_pGroup_trivialization
      (b ≫ f) j' i hcomp hdimD hdimC R V p
      (Scheme.FiniteEtale.galoisSylowRelative_isPGroup Y P) E M hM t' q hq
  let A := (moduleUnderlying R U).obj F
  let d : (moduleUnderlying R Z.obj.left).obj E ≅ (inverseImage Z.obj.hom).obj A :=
    (moduleInverseImageUnderlyingIso R Z.obj.hom).app F
  let : Subsingleton (Sheaf.H.{u + 2} ((etaleLowerShriek j').obj
      ((inverseImage Z.obj.hom).obj A)) q) :=
    (cohomologyMapIso_bijective ((etaleLowerShriek j').mapIso d) q).surjective.subsingleton
  have hpF : p • 𝟙 F = 0 :=
    moduleSheaf_nsmul_id_eq_zero_of_trivialization R Y.obj.hom F M p hM t
  have hpA : p • 𝟙 A = 0 := by
    have hmap := congrArg (moduleUnderlying R U).map hpF
    simpa only [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_zero] using hmap
  exact subsingleton_H_etaleLowerShriek_of_finiteEtale_coprime
    Z j b j' sq P.toSubgroup.index
    (Scheme.FiniteEtale.galoisSubgroupQuotient_finrank Y P.toSubgroup)
    A p (Scheme.FiniteEtale.galoisSylow_index_coprime Y P) hpA q

end AlgebraicGeometry.Scheme.EtaleCohomology.Vanishing
