/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Gluing.Cohomologous
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
# Tensor products of glued line bundles

For unit cocycles `c` and `c'` on the same open cover `U` of a scheme `X`, the product cocycle
`c * c'` has the transition units `cᵢⱼ c'ᵢⱼ`.

* `UnitCocycle.sectionMul`: matching local functions of `c` and `c'` multiply componentwise to
  matching local functions of `c * c'`; this is bilinear and commutes with restriction.
* `UnitCocycle.tensorMap`: the section product descends through the module-sheafification
  adjunction to the sheafified tensor product, `c.sheaf ⊗ c'.sheaf ⟶ (c * c').sheaf`.
* `UnitCocycle.tensorIso`: the pure tensors of the chart generators glue to its inverse.
* `UnitCocycle.classOf_lineBundle_mul`: the class of the line bundle glued from `c * c'` is the
  sum of the classes glued from `c` and `c'`.

This is the additivity half of the classical description of line bundles trivialized on a
fixed cover by Čech 1-cocycles of `𝒪_X^*` (compare Stacks, Tag 0B8R, for torsors). It
generalizes the projective-twist case `ProjectiveSpace.twistingTensorIso`, whose proof it
follows. No hypothesis on `X` or on the cover is used beyond `iSup U = ⊤`.
-/

@[expose] public section

noncomputable section


open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens}

/-- The product of two unit cocycles on the same cover. -/
instance : Mul (UnitCocycle U) where
  mul c c' := ⟨fun i j => c.transition i j * c'.transition i j, fun i j k V hi hj hk => by
    simp only [map_mul]
    rw [← c.cocycle i j k V hi hj hk, ← c'.cocycle i j k V hi hj hk, mul_mul_mul_comm]⟩

@[simp]
theorem mul_transition (c c' : UnitCocycle U) (i j : ι) :
    (c * c').transition i j = c.transition i j * c'.transition i j := rfl

@[simp]
theorem mul_transitionOn (c c' : UnitCocycle U) (i j : ι) {V : X.Opens} (hi : V ≤ U i)
    (hj : V ≤ U j) :
    (c * c').transitionOn i j hi hj = c.transitionOn i j hi hj * c'.transitionOn i j hi hj :=
  map_mul _ _ _

variable (c c' : UnitCocycle U)

/-- Componentwise multiplication of matching local functions. -/
def sectionMul (V : X.Opens) (s : c.Sections V) (t : c'.Sections V) : (c * c').Sections V := by
  refine ⟨fun i => s.val i * t.val i, ?_⟩
  intro W hWV i j hi hj
  change sectionRestrict X (le_inf hWV hi) (s.val i * t.val i) =
    ((c * c').transitionOn i j hi hj : Γ(X, W)) *
      sectionRestrict X (le_inf hWV hj) (s.val j * t.val j)
  rw [map_mul, s.property W hWV i j hi hj, t.property W hWV i j hi hj, map_mul,
    mul_transitionOn, Units.val_mul]
  ring

@[simp]
theorem sectionMul_apply (V : X.Opens) (s : c.Sections V) (t : c'.Sections V) (i : ι) :
    (sectionMul c c' V s t).val i = s.val i * t.val i := rfl

/-- The section product is bilinear over the functions on the open. -/
def sectionMulLinear (V : X.Opens) :
    c.Sections V →ₗ[Γ(X, V)] c'.Sections V →ₗ[Γ(X, V)] (c * c').Sections V where
  toFun s := {
    toFun := sectionMul c c' V s
    map_add' t v := by
      apply Subtype.ext
      funext i
      change s.val i * (t.val i + v.val i) = s.val i * t.val i + s.val i * v.val i
      exact mul_add _ _ _
    map_smul' r t := by
      apply Subtype.ext
      funext i
      change s.val i * (sectionRestrict X inf_le_left r * t.val i) =
        sectionRestrict X inf_le_left r * (s.val i * t.val i)
      ring }
  map_add' s t := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    funext i
    change (s.val i + t.val i) * v.val i = s.val i * v.val i + t.val i * v.val i
    exact add_mul _ _ _
  map_smul' r s := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext i
    change (sectionRestrict X inf_le_left r * s.val i) * t.val i =
      sectionRestrict X inf_le_left r * (s.val i * t.val i)
    exact mul_assoc _ _ _

/-- The section product commutes with every restriction of the module presheaves. -/
theorem sectionMul_map {V W : X.Opens} (f : op V ⟶ op W) (s : c.Sections V)
    (t : c'.Sections V) :
    (c * c').sheaf.val.map f (sectionMul c c' V s t) =
      sectionMul c c' W (c.sheaf.val.map f s) (c'.sheaf.val.map f t) := by
  apply Subtype.ext
  funext i
  change sectionRestrict X (inf_le_inf (leOfHom f.unop) le_rfl) (s.val i * t.val i) =
    sectionRestrict X (inf_le_inf (leOfHom f.unop) le_rfl) (s.val i) *
      sectionRestrict X (inf_le_inf (leOfHom f.unop) le_rfl) (t.val i)
  exact map_mul _ _ _

/-- In each chart, the section product is the product of the chart coordinates. -/
theorem localSectionsEquiv_sectionMul (i : ι) {V : X.Opens} (hV : V ≤ U i)
    (s : c.Sections V) (t : c'.Sections V) :
    (c * c').localSectionsEquiv i hV (sectionMul c c' V s t) =
      c.localSectionsEquiv i hV s * c'.localSectionsEquiv i hV t := by
  change sectionRestrict X (le_inf le_rfl hV) (s.val i * t.val i) =
    sectionRestrict X (le_inf le_rfl hV) (s.val i) * sectionRestrict X (le_inf le_rfl hV) (t.val i)
  exact map_mul _ _ _

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- The section product of the generators is the generator of the product cocycle. -/
theorem sectionMul_generator (i : ι) {V : X.Opens} (hV : V ≤ U i) :
    sectionMul c c' V (c.generator i hV) (c'.generator i hV) = (c * c').generator i hV := by
  apply ((c * c').localSectionsEquiv i hV).injective
  rw [localSectionsEquiv_sectionMul, localSectionsEquiv_generator, localSectionsEquiv_generator,
    localSectionsEquiv_generator, mul_one]

/-- The section product as a map from the pointwise tensor presheaf. -/
def tensorPresheafMap :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) c.sheaf.val c'.sheaf.val ⟶
      (c * c').sheaf.val where
  app V := ModuleCat.ofHom (TensorProduct.lift (sectionMulLinear c c' V.unop))
  naturality {V W} f := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro s t
    change sectionMul c c' W.unop (c.sheaf.val.map f s) (c'.sheaf.val.map f t) =
      (c * c').sheaf.val.map f (sectionMul c c' V.unop s t)
    exact (sectionMul_map c c' f s t).symm

/-- The multiplication `c.sheaf ⊗ c'.sheaf ⟶ (c * c').sheaf`, descended from the section
product by the module-sheafification adjunction. -/
def tensorMap : (moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf ⟶ (c * c').sheaf :=
  ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)).homEquiv _ _).symm
    (tensorPresheafMap c c')

/-- The multiplication sends a pure tensor section to the section product. -/
theorem tensorMap_section (V : X.Opens) (s : Γ(c.sheaf, V)) (t : Γ(c'.sheaf, V)) :
    (tensorMap c c').val.app (op V) (moduleTensorSection X c.sheaf c'.sheaf V s t) =
      sectionMul c c' V s t := by
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf)
    c.sheaf.val c'.sheaf.val
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)
  have h : adj.homEquiv P (c * c').sheaf (tensorMap c c') = tensorPresheafMap c c' :=
    (adj.homEquiv _ _).apply_symm_apply _
  exact congrArg (fun φ : P ⟶ (c * c').sheaf.val => φ.app (op V) (s ⊗ₜ[Γ(X, V)] t)) h

/-- Pure tensor sections multiply the two scalars. -/
theorem moduleTensorSection_smul_smul (E M : X.Modules) (V : X.Opens) (r t : Γ(X, V))
    (s : Γ(E, V)) (v : Γ(M, V)) :
    moduleTensorSection X E M V (r • s) (t • v) = (r * t) • moduleTensorSection X E M V s v := by
  let η : (Γ(E, V) ⊗[Γ(X, V)] Γ(M, V)) →ₗ[Γ(X, V)]
      Γ((moduleTensorLeftFunctor X E).obj M, V) :=
    (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) E.val M.val)).app
        (op V)).hom
  change η ((r • s) ⊗ₜ[Γ(X, V)] (t • v)) = (r * t) • η (s ⊗ₜ[Γ(X, V)] v)
  rw [TensorProduct.smul_tmul_smul, η.map_smul]

/-- The pure tensor of the chart generators on a subopen of a chart. -/
def tensorGenerator (i : ι) {V : X.Opens} (hV : V ≤ U i) :
    Γ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf, V) :=
  moduleTensorSection X c.sheaf c'.sheaf V (c.generator i hV) (c'.generator i hV)

theorem tensorGenerator_restrict (i : ι) {V W : X.Opens} (h : V ≤ W) (hW : W ≤ U i) :
    ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf).val.map (homOfLE h).op
        (tensorGenerator c c' i hW) = tensorGenerator c c' i (h.trans hW) := by
  change ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf).presheaf.map (homOfLE h).op _ = _
  rw [tensorGenerator, moduleTensorSection_restrict]
  change moduleTensorSection X c.sheaf c'.sheaf V
    (c.sheaf.val.map (homOfLE h).op (c.generator i hW))
    (c'.sheaf.val.map (homOfLE h).op (c'.generator i hW)) = _
  rw [c.generator_restrict i (homOfLE h) hW, c'.generator_restrict i (homOfLE h) hW]
  rfl

/-- The tensor generators have the transition law of the product cocycle. -/
theorem tensorGenerator_transition (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :
    tensorGenerator c c' j hj =
      ((c * c').transitionOn i j hi hj : Γ(X, V)) • tensorGenerator c c' i hi := by
  unfold tensorGenerator
  rw [c.generator_transition i j hi hj, c'.generator_transition i j hi hj,
    moduleTensorSection_smul_smul, mul_transitionOn, Units.val_mul]

/-- The multiplication sends the tensor generator to the generator of the product cocycle. -/
theorem tensorMap_generator (i : ι) {V : X.Opens} (hV : V ≤ U i) :
    (tensorMap c c').val.app (op V) (tensorGenerator c c' i hV) = (c * c').generator i hV := by
  rw [tensorGenerator, tensorMap_section]
  exact sectionMul_generator c c' i hV

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem tensorGenerator_compatible (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf).val.map (homOfLE hj).op
        (tensorGenerator c c' j le_rfl) =
      ((c * c').transitionOn i j hi hj).val •
        ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf).val.map (homOfLE hi).op
          (tensorGenerator c c' i le_rfl) := by
  rw [tensorGenerator_restrict c c' j hj le_rfl, tensorGenerator_restrict c c' i hi le_rfl]
  exact tensorGenerator_transition c c' i j hi hj

variable (hU : iSup U = ⊤)

/-- The inverse of the multiplication, glued from the tensor generators. -/
def tensorInv : (c * c').sheaf ⟶ (moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf :=
  (c * c').homOfLocalSections _ hU (fun i => tensorGenerator c c' i le_rfl)
    (tensorGenerator_compatible c c')

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
/-- On a subopen of a chart the inverse is the chart coordinate times the tensor
generator. -/
theorem tensorInv_local (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ((c * c').sheaf, V)) :
    (tensorInv c c' hU).val.app (op V) s =
      (c * c').localSectionsEquiv i hi s • tensorGenerator c c' i hi := by
  have h := (c * c').homOfLocalSections_apply
    ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf) hU
    (fun j => tensorGenerator c c' j le_rfl) (tensorGenerator_compatible c c') i V hi s
  change (tensorInv c c' hU).val.app (op V) s =
    (c * c').localSectionsEquiv i hi s •
      ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf).val.map (homOfLE hi).op
        (tensorGenerator c c' i le_rfl) at h
  rw [tensorGenerator_restrict c c' i hi le_rfl] at h
  exact h

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem tensorInv_map : tensorInv c c' hU ≫ tensorMap c c' = 𝟙 (c * c').sheaf := by
  apply (c * c').hom_ext_generator hU
  intro i
  change (tensorMap c c').val.app (op (U i))
      ((tensorInv c c' hU).val.app (op (U i)) ((c * c').generator i le_rfl)) =
    (c * c').generator i le_rfl
  rw [tensorInv_local c c' hU i (U i) le_rfl, val_app_smul, tensorMap_generator,
    localSectionsEquiv_generator, one_smul]

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem tensorMap_inv_local (i : ι) (V : X.Opens) (hi : V ≤ U i) (s : Γ(c.sheaf, V))
    (t : Γ(c'.sheaf, V)) :
    (tensorInv c c' hU).val.app (op V)
        ((tensorMap c c').val.app (op V) (moduleTensorSection X c.sheaf c'.sheaf V s t)) =
      moduleTensorSection X c.sheaf c'.sheaf V s t := by
  rw [tensorMap_section, tensorInv_local c c' hU i V hi, localSectionsEquiv_sectionMul,
    tensorGenerator, ← moduleTensorSection_smul_smul, c.localSectionsEquiv_smul_generator,
    c'.localSectionsEquiv_smul_generator]

-- Sections `Γ(M, V)` and their `X.ringCatSheaf` scalars match `Γ(X, V)` only after unfolding.
set_option backward.isDefEq.respectTransparency false in
theorem tensorMap_inv :
    tensorMap c c' ≫ tensorInv c c' hU = 𝟙 ((moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf) := by
  apply moduleTensor_hom_ext
  intro V s t
  let T := (moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩
    (fun i => V ⊓ U i) V (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, hU, inf_top_eq])
  intro i
  change T.val.map (homOfLE inf_le_left).op
      ((tensorInv c c' hU).val.app (op V)
        ((tensorMap c c').val.app (op V) (moduleTensorSection X c.sheaf c'.sheaf V s t))) =
    T.val.map (homOfLE inf_le_left).op (moduleTensorSection X c.sheaf c'.sheaf V s t)
  rw [← PresheafOfModules.naturality_apply (tensorInv c c' hU).val,
    ← PresheafOfModules.naturality_apply (tensorMap c c').val]
  change (tensorInv c c' hU).val.app (op (V ⊓ U i))
      ((tensorMap c c').val.app (op (V ⊓ U i))
        (T.presheaf.map (homOfLE inf_le_left).op
          (moduleTensorSection X c.sheaf c'.sheaf V s t))) =
    T.presheaf.map (homOfLE inf_le_left).op (moduleTensorSection X c.sheaf c'.sheaf V s t)
  rw [moduleTensorSection_restrict]
  exact tensorMap_inv_local c c' hU i _ inf_le_right _ _

/-- The sheafified tensor product of two glued sheaves is the glued sheaf of the product
cocycle; the forward map is the section product. -/
def tensorIso : (moduleTensorLeftFunctor X c.sheaf).obj c'.sheaf ≅ (c * c').sheaf where
  hom := tensorMap c c'
  inv := tensorInv c c' hU
  hom_inv_id := tensorMap_inv c c' hU
  inv_hom_id := tensorInv_map c c' hU

/-- The line bundle glued from a product cocycle is the tensor product: its class is the sum of
the two classes. -/
theorem classOf_lineBundle_mul :
    classOf X ((c * c').lineBundle hU) =
      classOf X (c.lineBundle hU) + classOf X (c'.lineBundle hU) := by
  rw [← classOf_tensor]
  exact (class_eq_iff X _ _).mpr ⟨(tensorIso c c' hU).symm⟩

end AlgebraicGeometry.Scheme.Modules.Invertible.UnitCocycle
