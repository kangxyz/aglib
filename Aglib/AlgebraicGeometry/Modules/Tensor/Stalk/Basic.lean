/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Stalk.Map

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorStalkIso.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 83]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Original sheaf tensor commutes naturally with module stalks

The canonical comparison and its inverse both keep the pure-section germ
formula. No flatness, quasicoherence, or noetherian hypothesis is imposed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry TopologicalSpace Opposite

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Linear maps from the original tensor stalk are determined by original pure-section germs. -/
theorem moduleTensorStalk_hom_ext (X : Scheme.{u}) (x : X) (M N : X.Modules)
    {P : ModuleCat.{u} (X.presheaf.stalk x)}
    {f g : (moduleStalk X x).obj ((moduleTensorLeftFunctor X M).obj N) ⟶ P}
    (h : ∀ (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)),
      f (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t)) =
        g (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t))) : f = g := by
  apply (moduleStalkSkyscraperHomEquiv X x ((moduleTensorLeftFunctor X M).obj N) P).injective
  apply moduleTensor_hom_ext
  intro U s t
  funext hx
  exact h U hx.down s t

/-- The original sheaf tensor stalk is the tensor of the two original module stalks. -/
def moduleTensorStalkIso (X : Scheme.{u}) (x : X) (M N : X.Modules) :
    (moduleStalk X x).obj ((moduleTensorLeftFunctor X M).obj N) ≅
      (moduleStalk X x).obj M ⊗ (moduleStalk X x).obj N where
  hom := moduleTensorStalkHom X x M N
  inv := moduleTensorStalkInv X x M N
  hom_inv_id := by
    apply moduleTensorStalk_hom_ext X x M N
    intro U hx s t
    change moduleTensorStalkInv X x M N
      (moduleTensorStalkHom X x M N
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t))) = _
    rw [moduleTensorStalkHom_germ, moduleTensorStalkInv_tmul_germ]
    rfl
  inv_hom_id := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    obtain ⟨U, hx, s, t, rfl, rfl⟩ := exists_two_module_germ_representatives X x M N m n
    change moduleTensorStalkHom X x M N (moduleTensorStalkInv X x M N
      (M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t)) = _
    rw [moduleTensorStalkInv_tmul_germ, moduleTensorStalkHom_germ]
    rfl

/-- The actual comparison retains the original pure-section germ formula. -/
theorem moduleTensorStalkIso_hom_germ (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (moduleTensorStalkIso X x M N).hom
        (((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
          (moduleTensorSection X M N U s t)) =
      M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t :=
  moduleTensorStalkHom_germ X x M N U hx s t

/-- Its inverse retains the original tensor of germ representatives. -/
theorem moduleTensorStalkIso_inv_tmul_germ (X : Scheme.{u}) (x : X) (M N : X.Modules)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(M, U)) (t : Γ(N, U)) :
    (moduleTensorStalkIso X x M N).inv
        (M.presheaf.germ U x hx s ⊗ₜ[X.presheaf.stalk x] N.presheaf.germ U x hx t) =
      ((moduleTensorLeftFunctor X M).obj N).presheaf.germ U x hx
        (moduleTensorSection X M N U s t) :=
  moduleTensorStalkInv_tmul_germ X x M N U hx s t

end AlgebraicGeometry.Scheme.Modules
