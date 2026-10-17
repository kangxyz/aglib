/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Equivalence.Sections
public import Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.Frames
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sheafification

/-!
# Multiplication by global twist sections on tensor twists

A global section `s` of `O(a)` multiplies the twist factor of `O(d) ⊗ F`, giving the natural
transformation `twistingTensorMultiply` from tensoring by `O(d)` to tensoring by `O(a + d)`.
Nested original pure tensors `l ⊗ (t ⊗ n)` determine morphisms out of `O(e) ⊗ (O(d) ⊗ F)`,
because the line bundle `O(e)` preserves the sheafification unit
(`isIso_line_tensor_sheafificationUnit`). Consequently, if multiplication by `s` kills
`O(d) ⊗ F`, it kills every further twist `O(e) ⊗ (O(d) ⊗ F)`.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace AlgebraicGeometry.Scheme.Modules

private theorem associatedSheaf_map_unit_apply_aux {X : Scheme.{u}}
    {P Q : PresheafOfModulesOfCommRing.{u} X.sheaf.obj} (f : P ⟶ Q)
    (U : X.Opens) (x : P.obj (op U)) :
    ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map f).val.app (op U)
        (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P).app (op U) x) =
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app Q).app (op U)
        (f.app (op U) x) := by
  have h := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).naturality f
  exact (congrArg (fun q => q.app (op U) x) h).symm

-- The section modules of the presheaf tensor carry their `Γ(X, U)`-module structures only up
-- to unfolding the structure-sheaf presheaf; this needs the backward transparency rule.
set_option backward.isDefEq.respectTransparency false in
/-- Morphisms out of a nested tensor with an outer line bundle are determined by their values
on nested original pure tensors. -/
theorem moduleTensor_nested_hom_ext_of_line {X : Scheme.{u}} (L M N : X.Modules)
    {κ : Type v} (Y : κ → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
    (eL : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)
    {G : X.Modules}
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
  let η := SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf
  let φ : (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).obj (A ⊗ (B ⊗ C)) ⟶
      (moduleTensorLeftFunctor X L).obj ((moduleTensorLeftFunctor X M).obj N) :=
    (lineTensorLeftUnitComparison X L M).app N
  have hiso : IsIso φ := isIso_line_tensor_sheafificationUnit L Y j hc eL (B ⊗ C)
  have hepi : Epi φ := @IsIso.epi_of_iso _ _ _ _ φ hiso
  apply (cancel_epi φ).mp
  have hvalue (k : (moduleTensorLeftFunctor X L).obj ((moduleTensorLeftFunctor X M).obj N) ⟶ G)
      (U : X.Opens) (l : Γ(L, U)) (m : Γ(M, U)) (n : Γ(N, U)) :
      ((φ ≫ k).val.app (op U))
          ((η.app (A ⊗ (B ⊗ C))).app (op U) (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))) =
        k.val.app (op U) (moduleTensorSection X L ((moduleTensorLeftFunctor X M).obj N) U l
          (moduleTensorSection X M N U m n)) := by
    change k.val.app (op U) (((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
        (𝟙 A ⊗ₘ η.app (B ⊗ C))).val.app (op U)
          ((η.app (A ⊗ (B ⊗ C))).app (op U) (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n)))) = _
    erw [associatedSheaf_map_unit_apply_aux (𝟙 A ⊗ₘ η.app (B ⊗ C)) U
      (l ⊗ₜ[Γ(X, U)] (m ⊗ₜ[Γ(X, U)] n))]
    rfl
  apply (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)).homEquiv _ _
    |>.injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro l x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    simp only [Adjunction.homEquiv_unit]
    exact (hvalue _ U.unop l m n).trans ((h U.unop l m n).trans (hvalue _ U.unop l m n).symm)
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

-- The pure tensor uses the `Γ(X, U)`-module structures of the presheaf tensor factors.
set_option backward.isDefEq.respectTransparency false in
/-- A pure tensor with zero coefficient section is zero. -/
theorem moduleTensorSection_zero_right {X : Scheme.{u}} (E M : X.Modules) (U : X.Opens)
    (e : Γ(E, U)) : moduleTensorSection X E M U e 0 = 0 := by
  unfold moduleTensorSection SheafOfModulesOfCommRing.tensorSection
  rw [TensorProduct.tmul_zero, map_zero]

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- The standard coordinate charts cover projective space. -/
theorem exists_coordinateOpen_mem (x : ProjectiveSpace R ι) :
    ∃ (i : ι) (y : (coordinateOpen R ι i).toScheme), (coordinateOpen R ι i).ι y = x := by
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (show x ∈ iSup (coordinateOpen R ι) by rw [iSup_coordinateOpen_eq_top]; trivial)
  exact ⟨i, ⟨x, hi⟩, rfl⟩

/-- Multiplication by a global section `s` of `O(a)` on the twist factor: the natural
transformation from tensoring by `O(d)` to tensoring by `O(a + d)`. -/
def twistingTensorMultiply (a d : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤)) :
    moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d) ⟶
      moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι (a + d)) :=
  moduleTensorCoefficientMap (ProjectiveSpace R ι) (twistingMultiplyGlobal R ι a d s)

/-- On an original pure tensor, twist multiplication multiplies the twist factor. -/
theorem twistingTensorMultiply_section (a d : ℤ) (s : (twistingSheaf R ι a).val.obj (op ⊤))
    (F : (ProjectiveSpace R ι).Modules) (U : (ProjectiveSpace R ι).Opens)
    (t : Γ(twistingSheaf R ι d, U)) (n : Γ(F, U)) :
    ((twistingTensorMultiply R ι a d s).app F).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F U t n) =
      moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (a + d)) F U
        (twistingSectionMul R ι a d U
          ((twistingSheaf R ι a).val.map (homOfLE le_top).op s) t) n :=
  moduleTensorCoefficientMap_section (twistingMultiplyGlobal R ι a d s) F U t n

/-- Transport along an equality of twist degrees keeps every matching chart function. -/
theorem twistingSection_eqToHom_val {c c' : ℤ} (h : c = c') {U : (ProjectiveSpace R ι).Opens}
    (x : Γ(twistingSheaf R ι c, U)) (i : ι) :
    ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U) x).val i = x.val i := by
  subst h
  rfl

/-- Moving a factor between the two sides of a product of twist sections, after transport
along the corresponding equality of degrees. -/
theorem twistingSectionMul_swap (a d e : ℤ) (h : e + (a + d) = a + e + d)
    (U : (ProjectiveSpace R ι).Opens) (s : (twistingSheaf R ι a).val.obj (op U))
    (l : (twistingSheaf R ι e).val.obj (op U)) (t : (twistingSheaf R ι d).val.obj (op U)) :
    (eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U)
        (twistingSectionMul R ι e (a + d) U l (twistingSectionMul R ι a d U s t)) =
      twistingSectionMul R ι (a + e) d U (twistingSectionMul R ι a e U s l) t := by
  apply Subtype.ext
  funext i
  refine (twistingSection_eqToHom_val R ι h _ i).trans ?_
  change l.val i * (s.val i * t.val i) = s.val i * l.val i * t.val i
  ring

/-- Vanishing of a pure tensor is invariant under transport along an equality of twist
degrees. The equality is eliminated before any transport is evaluated. -/
theorem moduleTensorSection_eqToHom_eq_zero {c c' : ℤ} (h : c = c')
    (F : (ProjectiveSpace R ι).Modules) (U : (ProjectiveSpace R ι).Opens)
    (x : (twistingSheaf R ι c).val.obj (op U)) (n : Γ(F, U))
    (hx : moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι c) F U x n = 0) :
    moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι c') F U
      ((eqToHom (congrArg (twistingSheaf R ι) h)).val.app (op U) x) n = 0 := by
  subst h
  exact hx

-- Section types of twists and of `Γ` agree only after unfolding the module presheaf.
set_option backward.isDefEq.respectTransparency false in
/-- If multiplication by a global twist section kills `O(d) ⊗ F`, it kills every further twist
`O(e) ⊗ (O(d) ⊗ F)`. -/
theorem twistingTensorMultiply_app_tensor_eq_zero (a d e : ℤ)
    (s : (twistingSheaf R ι a).val.obj (op ⊤)) (F : (ProjectiveSpace R ι).Modules)
    (hF : (twistingTensorMultiply R ι a d s).app F = 0) :
    (twistingTensorMultiply R ι a e s).app
      ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj F) = 0 := by
  rw [← cancel_mono ((twistingTensorCompIso R ι (a + e) d).hom.app F), zero_comp]
  apply moduleTensor_nested_hom_ext_of_line (twistingSheaf R ι e) (twistingSheaf R ι d) F
    (fun i => (coordinateOpen R ι i).toScheme) (fun i => (coordinateOpen R ι i).ι)
    (exists_coordinateOpen_mem R ι) (twistingRestrictUnitIso R ι e)
  intro U l t n
  let s' := (twistingSheaf R ι a).val.map (homOfLE (le_top : U ≤ ⊤)).op s
  have hzero : moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (a + d)) F U
      (twistingSectionMul R ι a d U s' t) n = 0 := by
    rw [← twistingTensorMultiply_section, hF]
    rfl
  have hinner : moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (e + (a + d))) F U
      (twistingSectionMul R ι e (a + d) U l (twistingSectionMul R ι a d U s' t)) n = 0 := by
    rw [← twistingTensorCompIso_hom_section R ι e (a + d) F U l, hzero,
      moduleTensorSection_zero_right, map_zero]
  have houter : moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι (a + e + d)) F U
      (twistingSectionMul R ι (a + e) d U (twistingSectionMul R ι a e U s' l) t) n = 0 := by
    have hdeg : e + (a + d) = a + e + d := by ring
    rw [← twistingSectionMul_swap R ι a d e hdeg U s' l t]
    exact moduleTensorSection_eqToHom_eq_zero R ι hdeg F U _ n hinner
  change ((twistingTensorCompIso R ι (a + e) d).hom.app F).val.app (op U)
      (((twistingTensorMultiply R ι a e s).app _).val.app (op U)
        (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι e) _ U l
          (moduleTensorSection (ProjectiveSpace R ι) (twistingSheaf R ι d) F U t n))) = 0
  rw [twistingTensorMultiply_section, twistingTensorCompIso_hom_section]
  exact houter

end AlgebraicGeometry.ProjectiveSpace
