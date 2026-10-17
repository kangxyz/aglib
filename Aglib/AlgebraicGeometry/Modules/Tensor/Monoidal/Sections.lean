/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# The monoidal structure on pure section tensors

The associator of scheme modules sends the nested pure tensor
`moduleTensorSection (moduleTensorSection m n) o` to `moduleTensorSection m
(moduleTensorSection n o)`. Since local isomorphisms of module presheaves are stable under
tensor products, morphisms out of a nested tensor product of arbitrary module sheaves are
determined by their values on nested pure section tensors, in either bracketing
(`moduleTensor_nested_hom_ext`, `moduleTensor_nested_hom_ext_left`). No local-freeness or
line-bundle hypothesis is needed.

The whiskerings act on the corresponding factor of a pure section tensor
(`whiskerRight_moduleTensorSection`, `whiskerLeft_moduleTensorSection`), the inverse unitors send
a section `m` to `1 ⊗ m` and `m ⊗ 1` (`leftUnitor_inv_moduleTensorSection`,
`rightUnitor_inv_moduleTensorSection`), and the braiding exchanges the two factors
(`braiding_hom_moduleTensorSection`).
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory MonoidalCategory BraidedCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The associator on nested pure section tensors. -/
theorem associator_hom_moduleTensorSection (M N O : X.Modules) (U : X.Opens) (m : Γ(M, U))
    (n : Γ(N, U)) (o : Γ(O, U)) :
    (α_ M N O).hom.val.app (op U)
        (moduleTensorSection X (M ⊗ N) O U (moduleTensorSection X M N U m n) o) =
      moduleTensorSection X M (N ⊗ O) U m (moduleTensorSection X N O U n o) :=
  tensorSheafAssociator_hom_tmul X M N O (op U) m n o

/-- The inverse associator on nested pure section tensors. -/
theorem associator_inv_moduleTensorSection (M N O : X.Modules) (U : X.Opens) (m : Γ(M, U))
    (n : Γ(N, U)) (o : Γ(O, U)) :
    (α_ M N O).inv.val.app (op U)
        (moduleTensorSection X M (N ⊗ O) U m (moduleTensorSection X N O U n o)) =
      moduleTensorSection X (M ⊗ N) O U (moduleTensorSection X M N U m n) o :=
  tensorSheafAssociator_inv_tmul X M N O (op U) m n o

/-- A right whiskering acts on the first factor of a pure section tensor. -/
theorem whiskerRight_moduleTensorSection {M M' : X.Modules} (f : M ⟶ M') (N : X.Modules)
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (f ▷ N).val.app (op U) (moduleTensorSection X M N U m n) =
      moduleTensorSection X M' N U (f.val.app (op U) m) n :=
  moduleTensorCoefficientMap_section f N U m n

/-- A left whiskering acts on the second factor of a pure section tensor. -/
theorem whiskerLeft_moduleTensorSection (M : X.Modules) {N N' : X.Modules} (g : N ⟶ N')
    (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (M ◁ g).val.app (op U) (moduleTensorSection X M N U m n) =
      moduleTensorSection X M N' U m (g.val.app (op U) n) :=
  moduleTensorLeftFunctor_map_section M g U m n

/-- The inverse left unitor sends a section `m` to the pure tensor `1 ⊗ m`. -/
theorem leftUnitor_inv_moduleTensorSection (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    (λ_ M).inv.val.app (op U) m =
      moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U (1 : Γ(X, U)) m := by
  have h : (λ_ M).hom.val.app (op U)
      (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U (1 : Γ(X, U)) m) = m :=
    (tensorLeftUnitIso_hom_section X M U 1 m).trans (one_smul _ m)
  calc (λ_ M).inv.val.app (op U) m
      = (λ_ M).inv.val.app (op U) ((λ_ M).hom.val.app (op U)
          (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U (1 : Γ(X, U)) m)) :=
        congrArg _ h.symm
    _ = ((λ_ M).hom ≫ (λ_ M).inv).val.app (op U)
          (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U (1 : Γ(X, U)) m) :=
        rfl
    _ = _ := by rw [Iso.hom_inv_id]; rfl

/-- The inverse right unitor sends a section `m` to the pure tensor `m ⊗ 1`. -/
theorem rightUnitor_inv_moduleTensorSection (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    (ρ_ M).inv.val.app (op U) m =
      moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m (1 : Γ(X, U)) := by
  have h : (ρ_ M).hom.val.app (op U)
      (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m (1 : Γ(X, U))) = m :=
    (tensorRightUnitIso_hom_section X M U m 1).trans (one_smul _ m)
  calc (ρ_ M).inv.val.app (op U) m
      = (ρ_ M).inv.val.app (op U) ((ρ_ M).hom.val.app (op U)
          (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m (1 : Γ(X, U)))) :=
        congrArg _ h.symm
    _ = ((ρ_ M).hom ≫ (ρ_ M).inv).val.app (op U)
          (moduleTensorSection X M (SheafOfModules.unit X.ringCatSheaf) U m (1 : Γ(X, U))) :=
        rfl
    _ = _ := by rw [Iso.hom_inv_id]; rfl

-- The section modules of the presheaf tensor carry their `Γ(X, U)`-module structures only up
-- to unfolding the structure-sheaf presheaf; this needs the transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- The braiding of scheme modules exchanges the two factors of a pure section tensor. -/
theorem braiding_hom_moduleTensorSection (M N : X.Modules) (U : X.Opens) (m : Γ(M, U))
    (n : Γ(N, U)) :
    (β_ M N).hom.val.app (op U) (moduleTensorSection X M N U m n) =
      moduleTensorSection X N M U n m := by
  have h := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).naturality
    (β_ ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M)
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N)).hom
  exact (congrArg (fun q ↦ q.app (op U) (m ⊗ₜ[Γ(X, U)] n)) h).symm

private theorem associatedSheaf_map_unit_apply {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj}
    (f : P ⟶ Q) (U : X.Opens) (x : P.obj (op U)) :
    ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map f).val.app (op U)
        (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P).app (op U) x) =
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app Q).app (op U)
        (f.app (op U) x) :=
  (congrArg (fun q ↦ q.app (op U) x)
    ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).naturality f)).symm

-- The section modules of the presheaf tensor carry their `Γ(X, U)`-module structures only up
-- to unfolding the structure-sheaf presheaf; this needs the transparency override.
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of a right-nested tensor product of arbitrary module sheaves are determined by
their values on nested pure section tensors. -/
theorem moduleTensor_nested_hom_ext (L M N : X.Modules) {G : X.Modules}
    {f g : (moduleTensorLeftFunctor X L).obj ((moduleTensorLeftFunctor X M).obj N) ⟶ G}
    (h : ∀ (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)),
      f.val.app (op U) (moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
          (moduleTensorSection X M N U m n)) =
        g.val.app (op U) (moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
          (moduleTensorSection X M N U m n))) :
    f = g := by
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
  let B := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let C := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj N
  let u := SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf
  let φ : (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).obj (A ⊗ (B ⊗ C)) ⟶
      (moduleTensorLeftFunctor X L).obj ((moduleTensorLeftFunctor X M).obj N) :=
    (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map (𝟙 A ⊗ₘ u.app (B ⊗ C))
  have hiso : IsIso φ := isIso_associatedSheaf_map_whiskerLeft_unit X A (B ⊗ C)
  have hepi : Epi φ := @IsIso.epi_of_iso _ _ _ _ φ hiso
  apply (cancel_epi φ).mp
  have hvalue (k : (moduleTensorLeftFunctor X L).obj ((moduleTensorLeftFunctor X M).obj N) ⟶ G)
      (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
      ((φ ≫ k).val.app (op U))
          ((u.app (A ⊗ (B ⊗ C))).app (op U) (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))) =
        k.val.app (op U) (moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
          (moduleTensorSection X M N U m n)) := by
    change k.val.app (op U) (((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
        (𝟙 A ⊗ₘ u.app (B ⊗ C))).val.app (op U)
          ((u.app (A ⊗ (B ⊗ C))).app (op U) (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n)))) = _
    erw [associatedSheaf_map_unit_apply (𝟙 A ⊗ₘ u.app (B ⊗ C)) U
      (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))]
    rfl
  apply (_root_.PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 _)).homEquiv _ _ |>.injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro l x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    simp only [Adjunction.homEquiv_unit]
    exact (hvalue _ U.unop l m n).trans ((h U.unop l m n).trans (hvalue _ U.unop l m n).symm)
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Morphisms out of a left-nested tensor product of arbitrary module sheaves are determined by
their values on nested pure section tensors. -/
theorem moduleTensor_nested_hom_ext_left (L M N : X.Modules) {G : X.Modules}
    {f g : (moduleTensorLeftFunctor X ((moduleTensorLeftFunctor X L).obj M)).obj N ⟶ G}
    (h : ∀ (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)),
      f.val.app (op U) (moduleTensorSection X ((moduleTensorLeftFunctor X L).obj M) N U
          (moduleTensorSection X L M U l m) n) =
        g.val.app (op U) (moduleTensorSection X ((moduleTensorLeftFunctor X L).obj M) N U
          (moduleTensorSection X L M U l m) n)) :
    f = g := by
  have key : (α_ L M N).inv ≫ f = (α_ L M N).inv ≫ g := by
    apply moduleTensor_nested_hom_ext
    intro U l m n
    have e : (α_ L M N).inv.val.app (op U)
        (moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
          (moduleTensorSection X M N U m n)) =
        moduleTensorSection X ((moduleTensorLeftFunctor X L).obj M) N U
          (moduleTensorSection X L M U l m) n :=
      associator_inv_moduleTensorSection L M N U l m n
    change f.val.app (op U) ((α_ L M N).inv.val.app (op U) _) =
      g.val.app (op U) ((α_ L M N).inv.val.app (op U) _)
    rw [e]
    exact h U l m n
  exact (cancel_epi (α_ L M N).inv).1 key

end AlgebraicGeometry.Scheme.Modules
