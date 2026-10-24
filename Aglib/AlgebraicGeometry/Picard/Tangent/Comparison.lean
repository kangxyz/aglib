/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Picard.Tangent.Cech.Scaling
public import Aglib.AlgebraicGeometry.Picard.Comparison.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.Invertible.LocalRing
public import Aglib.Algebra.Group.Subgroup.KerEquiv
public import Mathlib.RingTheory.DualNumber

/-!
# The vertical maps of Kleiman's Square (5.11.4)

Let `k` be a field, `X : FScheme k` with structure map `p`, `X[ε] = X ×_k Spec k[ε]` with closed
fibre `i : X ⟶ X[ε]` (`DualNumbers.inclusion`), and `F = Pic_{X/k,(fppf)}`
(`(fppfPicardSheaf p).obj`). The closed point `ρ : Spec k ⟶ Spec k[ε]` and the scaling
`µ_a : ε ↦ a ε` are the morphisms `DualNumbers.closedPointOver k : Over.mk (𝟙 (Spec k)) ⟶
Over.mk (dualMap k)` and `DualNumbers.scaleOver k a` of `k`-schemes. They induce on the fibres
`X ×_k -` the closed fibre `i` (through `pullback.fst : X ×_k Spec k ≅ X`,
`familyClosedPoint_eq`, `inv_pullback_fst_familyClosedPoint`) and `dualScale a`
(`familyScale_eq`).

* `DualNumbers.toFppfDualNumbers X : Pic(X[ε]) →+ F(k[ε])` and
  `DualNumbers.toFppfClosedFibre X : Pic(X) →+ F(k)` are the quotient maps to the relative Picard
  functor `P_{X/k}` followed by the sheafification unit `toFppfPicardSheaf p`. They are the
  vertical maps of Kleiman's Square (5.11.4), which commutes by naturality of the unit:
  `F(ρ) ∘ toFppfDualNumbers X = toFppfClosedFibre X ∘ i^*`
  (`fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers`). They are natural for `µ_a`, which acts
  on `Pic(X[ε])` by pullback along `dualScale a`
  (`fppfPicardSheaf_map_scaleOver_toFppfDualNumbers`). The induced map of the horizontal kernels
  is `DualNumbers.picardKerToFppf X : ker(i^*) →+ ker F(ρ)`.
* If `p` is proper and flat with geometrically integral fibres, both vertical maps are injective,
  hence so is `picardKerToFppf X`: Kleiman, *The Picard scheme*, arXiv:math/0504020v1, Thm 2.5(1),
  p. 18, together with `Pic(Spec k) = Pic(Spec k[ε]) = 0` for the local rings `k` and `k[ε]`
  (`Scheme.Modules.Invertible.subsingleton_picardGroup_of_isLocalRing`; compare Kleiman, Ex. 2.3,
  p. 17, for `Pic_X(A) ≅ P_{X/S}(A)` at a local ring `A`).
* If moreover `p` has a section (`IsSplitEpi p`), both vertical maps are bijective (Kleiman,
  Thm 2.5(2), p. 18; [Stacks 0B9N](https://stacks.math.columbia.edu/tag/0B9N)), and
  `DualNumbers.fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X :
  ker F(ρ) ≃+ ker(i^*)` has inverse `picardKerToFppf X`. It carries `F(µ_a)` to pullback along
  `dualScale a` (`DualNumbers.dualScaleKer`).

Kleiman (proof of Thm 5.11, pp. 43–44) assumes that `Pic_{X/k}` represents the étale sheaf; the
vertical maps of his Square (5.11.4) go from `H^1(𝒪^*_{X_T})` to the étale sheaf, and they are
isomorphisms by Exercise 2.3 over an algebraically closed field. Here the top row is
`i^* : Pic(X[ε]) → Pic(X)`, the vertical maps are those of the fppf sheafification, and bijectivity
comes from Thm 2.5(2) with a section, over any field. No `H^1(𝒪^*)` is used.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme.OverField
open AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

universe u

namespace AlgebraicGeometry.Scheme

namespace RelativePicard

variable {S X : Scheme.{u}} (p : X ⟶ S)

/-- If `Pic(T) = 0`, the quotient map `Pic(X ×_S T) ⟶ P_{X/S}(T)` is injective. -/
theorem quotientProjection_app_injective_of_subsingleton (T : (Over S)ᵒᵖ)
    (hT : Subsingleton (PicardGroup T.unop.left)) :
    Function.Injective ((quotientProjection p).app T).hom := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have ha' : a ∈ baseImage p T := by
    rw [← quotientProjection_app_ker]
    exact AddMonoidHom.mem_ker.mpr ha
  obtain ⟨b, rfl⟩ := ha'
  have hb : b = 0 := hT.allEq _ _
  rw [hb, map_zero]

/-- If `Pic(T) = 0`, the quotient map `Pic(X ×_S T) ⟶ P_{X/S}(T)` is bijective. -/
theorem quotientProjection_app_bijective_of_subsingleton (T : (Over S)ᵒᵖ)
    (hT : Subsingleton (PicardGroup T.unop.left)) :
    Function.Bijective ((quotientProjection p).app T).hom :=
  ⟨quotientProjection_app_injective_of_subsingleton p T hT, quotientProjection_app_surjective p T⟩

end RelativePicard

namespace DualNumbers

open RelativePicard

section Ring

variable (k : Type u) [CommRing k]

/-- The closed point `ρ : Spec k ⟶ Spec k[ε]` (from `ε ↦ 0`) as a morphism of `k`-schemes. -/
def closedPointOver : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk (dualMap k) :=
  Over.homMk (closedPoint k) (closedPoint_dualMap k)

/-- `Spec µ_a : Spec k[ε] ⟶ Spec k[ε]` (from `ε ↦ a ε`) as a morphism of `k`-schemes. -/
def scaleOver (a : k) : Over.mk (dualMap k) ⟶ Over.mk (dualMap k) :=
  Over.homMk (scaleMap k a) (scaleMap_dualMap k a)

@[simp]
theorem closedPointOver_left : (closedPointOver k).left = closedPoint k :=
  rfl

@[simp]
theorem scaleOver_left (a : k) : (scaleOver k a).left = scaleMap k a :=
  rfl

/-- `µ_a` fixes the closed point. -/
@[reassoc (attr := simp)]
theorem closedPointOver_scaleOver (a : k) :
    closedPointOver k ≫ scaleOver k a = closedPointOver k :=
  Over.OverMorphism.ext (closedPoint_scaleMap k a)

variable {k} {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The map `X ×_k Spec k ⟶ X[ε]` of fibres induced by the closed point, typed between the literal
fibre products. -/
def familyClosedPoint : pullback sX (𝟙 (Spec (.of k))) ⟶ dualScheme k sX :=
  (familyScheme sX).map (closedPointOver k)

/-- Through `pullback.fst : X ×_k Spec k ≅ X`, the closed point induces the closed fibre
`i : X ⟶ X[ε]`. -/
theorem familyClosedPoint_eq :
    familyClosedPoint sX = pullback.fst sX (𝟙 (Spec (.of k))) ≫ inclusion k sX := by
  apply pullback.hom_ext
  · rw [Category.assoc, inclusion_projection, Category.comp_id]
    exact familyScheme_map_fst sX (closedPointOver k)
  · rw [Category.assoc, inclusion_snd, ← Category.assoc, pullback.condition, Category.comp_id]
    exact familyScheme_map_snd sX (closedPointOver k)

/-- Under the isomorphism `pullback.fst : X ×_k Spec k ≅ X`, the map of fibres induced by the
closed point is the closed fibre `i : X ⟶ X[ε]`. -/
theorem inv_pullback_fst_familyClosedPoint :
    inv (pullback.fst sX (𝟙 (Spec (.of k)))) ≫ familyClosedPoint sX = inclusion k sX := by
  rw [familyClosedPoint_eq, IsIso.inv_hom_id_assoc]

/-- Pullback along an isomorphism is bijective on Picard groups. -/
private theorem pullbackHom_bijective_of_isIso {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsIso f] :
    Function.Bijective (pullbackHom f) := by
  have e₁ : ∀ c, pullbackHom (inv f) (pullbackHom f c) = c := fun c => by
    rw [← AddMonoidHom.comp_apply, ← pullbackHom_comp, IsIso.inv_hom_id, pullbackHom_id,
      AddMonoidHom.id_apply]
  have e₂ : ∀ c, pullbackHom f (pullbackHom (inv f) c) = c := fun c => by
    rw [← AddMonoidHom.comp_apply, ← pullbackHom_comp, IsIso.hom_inv_id, pullbackHom_id,
      AddMonoidHom.id_apply]
  exact ⟨Function.LeftInverse.injective e₁, Function.RightInverse.surjective e₂⟩

/-- The map `X[ε] ⟶ X[ε]` of fibres induced by `µ_a`, typed between the literal fibre products. -/
def familyScale (a : k) : dualScheme k sX ⟶ dualScheme k sX :=
  (familyScheme sX).map (scaleOver k a)

/-- `µ_a` induces the scaling `dualScale a` of `X[ε]`. -/
theorem familyScale_eq (a : k) : familyScale sX a = dualScale k sX a := by
  apply pullback.hom_ext
  · rw [dualScale_projection]
    exact familyScheme_map_fst sX (scaleOver k a)
  · rw [dualScale_snd]
    exact familyScheme_map_snd sX (scaleOver k a)

end Ring

section Field

variable {k : Type u} [Field k] (X : FScheme k)

/-- The left vertical map of Kleiman's Square (5.11.4):
`Pic(X[ε]) → P_{X/k}(k[ε]) → Pic_{X/k,(fppf)}(k[ε])`. -/
def toFppfDualNumbers :
    PicardGroup (dualScheme k X.hom) →+
      (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k))) :=
  ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app (op (Over.mk (dualMap k)))).hom

/-- The right vertical map of Kleiman's Square (5.11.4):
`Pic(X) ≅ Pic(X ×_k Spec k) → P_{X/k}(k) → Pic_{X/k,(fppf)}(k)`. -/
def toFppfClosedFibre :
    PicardGroup X.left →+ (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (𝟙 (Spec (.of k))))) :=
  ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
    (op (Over.mk (𝟙 (Spec (.of k)))))).hom.comp (pullbackHom (pullback.fst X.hom (𝟙 _)))

/-- The value of the left vertical map on a class: its image in `P_{X/k}(k[ε])`
(`quotientProjection`), followed by the unit `toFppfPicardSheaf`. -/
theorem toFppfDualNumbers_apply (c : PicardGroup (dualScheme k X.hom)) :
    toFppfDualNumbers X c = ((toFppfPicardSheaf X.hom).app (op (Over.mk (dualMap k)))).hom
      (((quotientProjection X.hom).app (op (Over.mk (dualMap k)))).hom c) :=
  rfl

/-- **Kleiman's Square (5.11.4) commutes** (arXiv:math/0504020v1, proof of Thm 5.11, p. 43), with
top row `i^* : Pic(X[ε]) → Pic(X)` and bottom row `F(ρ) : F(k[ε]) → F(k)`, by naturality of the
sheafification unit. -/
theorem fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers
    (c : PicardGroup (dualScheme k X.hom)) :
    ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom (toFppfDualNumbers X c) =
      toFppfClosedFibre X (pullbackHom (inclusion k X.hom) c) := by
  calc ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom (toFppfDualNumbers X c)
      = ((quotientProjection X.hom ≫ toFppfPicardSheaf X.hom).app
          (op (Over.mk (𝟙 (Spec (.of k)))))).hom (pullbackHom (familyClosedPoint X.hom) c) :=
        (NatTrans.naturality_apply (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom)
          (closedPointOver k).op c).symm
    _ = toFppfClosedFibre X (pullbackHom (inclusion k X.hom) c) := by
        rw [familyClosedPoint_eq, pullbackHom_comp]
        rfl

/-- `F(µ_a)` corresponds to pullback along `dualScale a` under the left vertical map. -/
theorem fppfPicardSheaf_map_scaleOver_toFppfDualNumbers (a : k)
    (c : PicardGroup (dualScheme k X.hom)) :
    ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom (toFppfDualNumbers X c) =
      toFppfDualNumbers X (pullbackHom (dualScale k X.hom a) c) := by
  calc ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom (toFppfDualNumbers X c)
      = toFppfDualNumbers X (pullbackHom (familyScale X.hom a) c) :=
        (NatTrans.naturality_apply (quotientProjection X.hom ≫ toFppfPicardSheaf X.hom)
          (scaleOver k a).op c).symm
    _ = toFppfDualNumbers X (pullbackHom (dualScale k X.hom a) c) := by
        rw [familyScale_eq]

/-- The map of the horizontal kernels of Square (5.11.4), `ker(i^*) → ker F(ρ)`: the
restriction of the left vertical map (Kleiman, proof of Thm 5.11, p. 43). -/
def picardKerToFppf :
    (pullbackHom (inclusion k X.hom)).ker →+
      ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker :=
  ((toFppfDualNumbers X).comp (pullbackHom (inclusion k X.hom)).ker.subtype).codRestrict _
    fun c => by
      have h := fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers X c
      rw [AddMonoidHom.mem_ker.mp c.2, map_zero] at h
      exact AddMonoidHom.mem_ker.mpr h

@[simp]
theorem coe_picardKerToFppf (c : (pullbackHom (inclusion k X.hom)).ker) :
    (picardKerToFppf X c : (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      toFppfDualNumbers X c :=
  rfl

/-- The kernel map is compatible with `µ_a`: pullback along `dualScale a` goes to `F(µ_a)`. -/
theorem coe_picardKerToFppf_dualScaleKer (a : k) (c : (pullbackHom (inclusion k X.hom)).ker) :
    (picardKerToFppf X (dualScaleKer k X.hom a c) :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom (picardKerToFppf X c) :=
  (fppfPicardSheaf_map_scaleOver_toFppfDualNumbers X a c).symm

section Injective

variable [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

/-- **Kleiman, Thm 2.5(1), at `k[ε]`**: for `p` proper and flat with geometrically integral fibres,
the left vertical map `Pic(X[ε]) → Pic_{X/k,(fppf)}(k[ε])` is injective, since `Pic(k[ε]) = 0`. -/
theorem toFppfDualNumbers_injective_of_isProper_of_flat_of_geometricallyIntegral :
    Function.Injective (toFppfDualNumbers X) :=
  (toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral X.hom
    (op (Over.mk (dualMap k)))).comp
    (quotientProjection_app_injective_of_subsingleton X.hom (op (Over.mk (dualMap k)))
      (inferInstanceAs (Subsingleton (PicardGroup (Spec (.of (DualNumber k)))))))

/-- **Kleiman, Thm 2.5(1), at `k`**: for `p` proper and flat with geometrically integral fibres,
the right vertical map `Pic(X) → Pic_{X/k,(fppf)}(k)` is injective, since `Pic(k) = 0`. -/
theorem toFppfClosedFibre_injective_of_isProper_of_flat_of_geometricallyIntegral :
    Function.Injective (toFppfClosedFibre X) := by
  have hfst : Function.Bijective (pullbackHom (pullback.fst X.hom (𝟙 (Spec (.of k))))) :=
    pullbackHom_bijective_of_isIso _
  exact ((toFppfPicardSheaf_app_injective_of_isProper_of_flat_of_geometricallyIntegral X.hom
    (op (Over.mk (𝟙 (Spec (.of k)))))).comp
    (quotientProjection_app_injective_of_subsingleton X.hom (op (Over.mk (𝟙 (Spec (.of k)))))
      (inferInstanceAs (Subsingleton (PicardGroup (Spec (.of k))))))).comp hfst.1

/-- The map of the horizontal kernels of Square (5.11.4) is injective. -/
theorem picardKerToFppf_injective_of_isProper_of_flat_of_geometricallyIntegral :
    Function.Injective (picardKerToFppf X) := fun _ _ h =>
  Subtype.ext (toFppfDualNumbers_injective_of_isProper_of_flat_of_geometricallyIntegral X
    (congrArg Subtype.val h))

end Injective

section Section

variable [IsSplitEpi X.hom] [IsProper X.hom] [Flat X.hom] [GeometricallyIntegral X.hom]

/-- **Kleiman, Thm 2.5(2), at `k[ε]`**: if moreover `p` has a section, the left vertical map
`Pic(X[ε]) → Pic_{X/k,(fppf)}(k[ε])` is bijective. -/
theorem toFppfDualNumbers_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral :
    Function.Bijective (toFppfDualNumbers X) :=
  (((relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X.hom).app
      (op (Over.mk (dualMap k)))).addCommGroupIsoToAddEquiv.bijective).comp
    (quotientProjection_app_bijective_of_subsingleton X.hom (op (Over.mk (dualMap k)))
      (inferInstanceAs (Subsingleton (PicardGroup (Spec (.of (DualNumber k)))))))

/-- **Kleiman, Thm 2.5(2), at `k`**: if moreover `p` has a section, the right vertical map
`Pic(X) → Pic_{X/k,(fppf)}(k)` is bijective. -/
theorem toFppfClosedFibre_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral :
    Function.Bijective (toFppfClosedFibre X) := by
  have hfst : Function.Bijective (pullbackHom (pullback.fst X.hom (𝟙 (Spec (.of k))))) :=
    pullbackHom_bijective_of_isIso _
  exact ((((relativeFppfIsoOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X.hom).app
      (op (Over.mk (𝟙 (Spec (.of k)))))).addCommGroupIsoToAddEquiv.bijective).comp
    (quotientProjection_app_bijective_of_subsingleton X.hom (op (Over.mk (𝟙 (Spec (.of k)))))
      (inferInstanceAs (Subsingleton (PicardGroup (Spec (.of k))))))).comp hfst

/-- **The tangent kernel of `Pic_{X/k,(fppf)}` with a section** (the vertical maps of Kleiman's
Square (5.11.4), arXiv:math/0504020v1, proof of Thm 5.11, pp. 43–44, through Thm 2.5(2), p. 18,
instead of Exercise 2.3). For a field `k` and `p : X ⟶ Spec k` proper and flat with geometrically
integral fibres and with a section,
`ker(Pic_{X/k,(fppf)}(k[ε]) → Pic_{X/k,(fppf)}(k)) ≃+ ker(Pic(X[ε]) → Pic(X))`.
The inverse is `picardKerToFppf X`. -/
def fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral :
    ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker ≃+
      (pullbackHom (inclusion k X.hom)).ker :=
  (AddMonoidHom.kerAddEquivOfComm (pullbackHom (inclusion k X.hom))
    ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom
    (AddEquiv.ofBijective (toFppfDualNumbers X)
      (toFppfDualNumbers_bijective_of_isSplitEpi_of_isProper_of_flat_of_geometricallyIntegral X))
    (toFppfClosedFibre X)
    (toFppfClosedFibre_injective_of_isProper_of_flat_of_geometricallyIntegral X)
    fun c => (fppfPicardSheaf_map_closedPointOver_toFppfDualNumbers X c).symm).symm

/-- The inverse of the equivalence is the map of horizontal kernels. -/
theorem fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_apply
    (c : (pullbackHom (inclusion k X.hom)).ker) :
    (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm c =
      picardKerToFppf X c :=
  rfl

/-- The value of the inverse on a class `c ∈ ker(i^*)`: its image in `P_{X/k}(k[ε])`, followed by
the unit `toFppfPicardSheaf`. -/
theorem coe_fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_apply
    (c : (pullbackHom (inclusion k X.hom)).ker) :
    ((fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm c :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((toFppfPicardSheaf X.hom).app (op (Over.mk (dualMap k)))).hom
        (((quotientProjection X.hom).app (op (Over.mk (dualMap k)))).hom
          (c : PicardGroup (dualScheme k X.hom))) :=
  rfl

/-- The inverse carries pullback along `dualScale a` to `F(µ_a)`. -/
theorem fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_dualScaleKer
    (a : k) (c : (pullbackHom (inclusion k X.hom)).ker) :
    ((fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm
        (dualScaleKer k X.hom a c) :
        (fppfPicardSheaf X.hom).obj.obj (op (Over.mk (dualMap k)))) =
      ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom
        ((fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm c) :=
  coe_picardKerToFppf_dualScaleKer X a c

/-- The equivalence carries `F(µ_a)` on `ker F(ρ)` to pullback along `dualScale a`. -/
theorem fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_map_scaleOver
    (a : k) (t : ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker)
    (h : ((fppfPicardSheaf X.hom).obj.map (scaleOver k a).op).hom t ∈
      ((fppfPicardSheaf X.hom).obj.map (closedPointOver k).op).hom.ker) :
    fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X ⟨_, h⟩ =
      dualScaleKer k X.hom a
        (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X t) := by
  apply (fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral X).symm.injective
  rw [AddEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [fppfPicardKerEquivOfIsSplitEpiOfIsProperOfFlatOfGeometricallyIntegral_symm_dualScaleKer,
    AddEquiv.symm_apply_apply]

end Section

end Field

end DualNumbers

end AlgebraicGeometry.Scheme
