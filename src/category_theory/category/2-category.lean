import category_theory.category
import category_theory.concrete_category

universes w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace category_theory

-- https://ncatlab.org/nlab/show/bicategory
class two_category_struct (obj : Type u₁) extends category_struct.{v₁} obj :=
[hom_cats : Π (a b : obj), category.{w₁} (a ⟶ b)]
(left_whisker : Π {a b c : obj} {f g : a ⟶ b} (h : b ⟶ c) (η : f ⟶ g), f ≫ h ⟶ g ≫ h)
(right_whisker : Π {a b c : obj} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h), f ≫ g ⟶ f ≫ h)
(left_unitor : Π {a b : obj} (f : a ⟶ b), 𝟙 _ ≫ f ≅ f)
(right_unitor : Π {a b : obj} (f : a ⟶ b), f ≫ 𝟙 _ ≅ f)
(associator : Π {a b c d : obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d), (f ≫ g) ≫ h ≅ f ≫ g ≫ h)

attribute [instance] two_category_struct.hom_cats

notation f ` ◀ ` η:50 := two_category_struct.right_whisker f η
notation η ` ▶ ` f:50 := two_category_struct.left_whisker f η

notation `λ_` := two_category_struct.left_unitor
notation `ρ_` := two_category_struct.right_unitor
notation `α_` := two_category_struct.associator

-- https://ncatlab.org/nlab/show/bicategory
class two_category (obj : Type u₁) extends two_category_struct.{w₁ v₁} obj :=
(left_whisker_id' : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), 𝟙 f ▶ g = 𝟙 (f ≫ g) . obviously)
(id_right_whisker' : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), f ◀ 𝟙 g = 𝟙 (f ≫ g) . obviously)
(left_whisker_comp' : ∀ {a b c : obj} {f g h : a ⟶ b} (i : b ⟶ c) (η : f ⟶ g) (θ : g ⟶ h),
  (η ▶ i) ≫ (θ ▶ i) = ((η ≫ θ) ▶ i) . obviously)
(right_whisker_comp' : ∀ {a b c : obj} {f : a ⟶ b} (g h i : b ⟶ c) (η : g ⟶ h) (θ : h ⟶ i),
  (f ◀ η) ≫ (f ◀ θ) = (f ◀ (η ≫ θ)) . obviously)
(left_unitor_naturality' : ∀ {a b : obj} (f g : a ⟶ b) (η : f ⟶ g),
  (𝟙 _ ◀ η) ≫ (λ_ g).hom = (λ_ f).hom ≫ η . obviously)
(right_unitor_naturality' : ∀ {a b : obj} (f g : a ⟶ b) (η : f ⟶ g),
  (η ▶ 𝟙 _) ≫ (ρ_ g).hom = (ρ_ f).hom ≫ η . obviously)
(associator_naturality_right' : ∀ {a b c d : obj} (f : a ⟶ b) (g : b ⟶ c) (h i : c ⟶ d) (η : h ⟶ i),
  ((f ≫ g) ◀ η) ≫ (associator f g i).hom = (associator f g h).hom ≫ (f ◀ (g ◀ η)) . obviously)
(associator_naturality_middle' : ∀ {a b c d} (f : a ⟶ b) {g h : b ⟶ c} (i : c ⟶ d) (η : g ⟶ h),
  ((f ◀ η) ▶ i) ≫ (associator f h i).hom = (associator f g i).hom ≫ (f ◀ (η ▶ i)) . obviously)
(associator_naturality_left' : ∀ {a b c d : obj} {f g : a ⟶ b} (h : b ⟶ c) (i : c ⟶ d) (η : f ⟶ g),
  ((η ▶ _) ▶ _) ≫ (associator g h i).hom = (associator f h i).hom ≫ (η ▶ _) . obviously)
(exchange' : ∀ {a b c : obj} {f g : a ⟶ b} {h i : b ⟶ c} (η : f ⟶ g) (θ : h ⟶ i),
  (_ ◀ θ) ≫ (η ▶ _) = (η ▶ _) ≫ (_ ◀ θ) . obviously)
(triangle' : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c),
  (associator f _ g).hom ≫ (_ ◀ (λ_ g).hom) = ((ρ_ f).hom ▶ g) . obviously)
(pentagon' : ∀ {a b c d e : obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (i : d ⟶ e),
    ((associator f g h).hom ▶ i) ≫ (associator f (g ≫ h) i).hom ≫ (f ◀ (associator g h i).hom)
  = (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom . obviously)

restate_axiom two_category.left_whisker_id'
restate_axiom two_category.id_right_whisker'
restate_axiom two_category.left_whisker_comp'
restate_axiom two_category.right_whisker_comp'
restate_axiom two_category.left_unitor_naturality'
restate_axiom two_category.right_unitor_naturality'
restate_axiom two_category.associator_naturality_right'
restate_axiom two_category.associator_naturality_middle'
restate_axiom two_category.associator_naturality_left'
restate_axiom two_category.exchange'
restate_axiom two_category.triangle'
restate_axiom two_category.pentagon'

attribute [simp] two_category.left_whisker_id two_category.id_right_whisker
attribute [simp, reassoc]
  two_category.left_whisker_comp
  two_category.right_whisker_comp
  two_category.left_unitor_naturality
  two_category.right_unitor_naturality
  two_category.associator_naturality_right
  two_category.associator_naturality_middle
  two_category.associator_naturality_left
  two_category.exchange
  two_category.triangle
  two_category.pentagon

open two_category

variables (C : Type u₁) [two_category.{w₁ v₁} C]
variables (D : Type u₂) [two_category.{w₂ v₂} D]
variables (E : Type u₃) [two_category.{w₃ v₃} E]

-- https://ncatlab.org/nlab/show/pseudofunctor
structure pseudofunctor :=
(P : C → D)
(func : Π {x y : C}, functor (x ⟶ y) (P x ⟶ P y))
(ids : Π (x : C), 𝟙 (P x) ≅ func.obj (𝟙 x))
(comps : Π {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
  func.obj f ≫ func.obj g ≅ func.obj (f ≫ g))
(comps_natural_left' : ∀ {x y z : C} {f f' : x ⟶ y} (g : y ⟶ z) (η : f ⟶ f'),
  (comps f g).hom ≫ func.map (η ▶ _) = (func.map η ▶ _) ≫ (comps f' g).hom
    . obviously)
(comps_natural_right' : ∀ {x y z : C} (f : x ⟶ y) {g g' : y ⟶ z} (η : g ⟶ g'),
  (comps f g).hom ≫ func.map (_ ◀ η) = (_ ◀ func.map η) ≫ (comps f g').hom
    . obviously)
(left_unitors' : ∀ {x y : C} (f : x ⟶ y),
  ((ids _).hom ▶ _) ≫ (comps _ _).hom ≫ func.map (λ_ f).hom = (λ_ _).hom
    . obviously)
(right_unitors' : ∀ {x y : C} (f : x ⟶ y),
  (_ ◀ (ids _).hom) ≫ (comps _ _).hom ≫ func.map (ρ_ f).hom = (ρ_ _).hom
    . obviously)
(assoc' : ∀ {w x y z : C} (f : w ⟶ x) (g : x ⟶ y) (h : y ⟶ z),
  (α_ _ _ _).hom ≫ (_ ◀ (comps _ _).hom) ≫ (comps _ _).hom =
  ((comps _ _).hom ▶ _) ≫ (comps _ _).hom ≫ func.map (α_ f g h).hom . obviously)

restate_axiom pseudofunctor.comps_natural_left'
restate_axiom pseudofunctor.comps_natural_right'
restate_axiom pseudofunctor.left_unitors'
restate_axiom pseudofunctor.right_unitors'
restate_axiom pseudofunctor.assoc'

attribute [simp, reassoc]
  pseudofunctor.comps_natural_left
  pseudofunctor.comps_natural_right
  pseudofunctor.left_unitors
  pseudofunctor.right_unitors
  pseudofunctor.assoc

def pseudofunctor.id : pseudofunctor C C :=
{ P := λ X, X,
  func := λ X Y, 𝟭 _,
  ids := λ X, iso.refl _,
  comps := λ X Y Z f g, iso.refl _ }

def pseudofunctor.comp (P : pseudofunctor C D) (Q : pseudofunctor D E) :
  pseudofunctor C E :=
{ P := λ X, Q.P (P.P X),
  func := λ X Y, pseudofunctor.func P ⋙ pseudofunctor.func Q,
  ids := λ X, Q.ids (P.P X) ≪≫ (pseudofunctor.func Q).map_iso (P.ids _),
  comps := λ X Y Z f g, Q.comps _ _ ≪≫ (pseudofunctor.func Q).map_iso (P.comps _ _),
  comps_natural_left' := λ X Y Z f f' g η,
  begin
    dsimp,
    rw [category.assoc, ←functor.map_comp, P.comps_natural_left, functor.map_comp,
      Q.comps_natural_left_assoc],
  end,
  comps_natural_right' := λ X Y Z f g g' η,
  begin
    dsimp,
    rw [category.assoc, ←functor.map_comp, P.comps_natural_right, functor.map_comp,
      Q.comps_natural_right_assoc],
  end,
  left_unitors' := λ X Y f,
  begin
    dsimp,
    rw [category.assoc, ←left_whisker_comp_assoc, ←Q.comps_natural_left_assoc, ←functor.map_comp,
      ←functor.map_comp, P.left_unitors, Q.left_unitors],
  end,
  right_unitors' := λ X Y f,
  begin
    dsimp,
    rw [category.assoc, ←right_whisker_comp_assoc, ←Q.comps_natural_right_assoc, ←functor.map_comp,
      ←functor.map_comp, P.right_unitors, Q.right_unitors],
  end,
  assoc' := λ W X Y Z f g h,
  begin
    dsimp,
    sorry
  end }

variables {C D E}

structure CAT :=
{α : Type u₁}
[str : category.{v₁} α]

instance : has_coe_to_sort CAT :=
{ S := Type u₁,
  coe := CAT.α }

instance str (C : CAT.{v₁ u₁}) : category.{v₁} C := C.str

instance : two_category CAT.{v₁ u₁} :=
{ hom := λ X Y, X ⥤ Y,
  id := λ X, 𝟭 _,
  comp := λ X Y Z f g, f ⋙ g,
  left_unitor := λ X Y, functor.right_unitor,
  right_unitor := λ X Y, functor.left_unitor,
  left_whisker := λ X Y Z f g h α, whisker_right α _,
  right_whisker := λ X Y Z f g h α, whisker_left _ α,
  associator := λ X Y Z W f g h, functor.associator _ _ _ }

end category_theory
