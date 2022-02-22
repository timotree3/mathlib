import model_theory.quotients
import order.filter.germ
import order.filter.ultrafilter

universes u v
variables {α : Type*} (M : α → Type*) (u : ultrafilter α)

open_locale filter
open filter

namespace first_order
namespace language

open Structure

variables {L : language.{u v}} [Π a, L.Structure (M a)]

namespace dgerm

instance setoid_prestructure : L.prestructure (dgerm_setoid ↑u M) :=
{ to_structure := { fun_map := λ n f x a, fun_map f (λ i, x i a),
             rel_map := λ n r x, ∀ᶠ (a : α) in ↑u, rel_map r (λ i, x i a) },
  fun_equiv := λ n f x y xy, begin
    refine mem_of_superset (Inter_mem.2 xy) (λ a ha, _),
    rw set.mem_Inter at ha,
    simp only [set.mem_set_of_eq],
    exact congr rfl (funext ha),
  end,
  rel_equiv := λ n r x y xy, begin
    rw ← iff_eq_eq,
    refine ⟨λ hx, _, λ hy, _⟩,
    { refine mem_of_superset (inter_mem hx (Inter_mem.2 xy)) _,
      rintro a ⟨ha1, ha2⟩,
      simp only [set.mem_Inter, set.mem_set_of_eq] at *,
      rw ← funext ha2,
      exact ha1 },
    { refine mem_of_superset (inter_mem hy (Inter_mem.2 xy)) _,
      rintro a ⟨ha1, ha2⟩,
      simp only [set.mem_Inter, set.mem_set_of_eq] at *,
      rw funext ha2,
      exact ha1 },
  end,
  .. dgerm_setoid ↑u M }

variables {M} {u}

instance Structure : L.Structure (dgerm ↑u M) := language.quotient_structure

lemma fun_map_cast {n : ℕ} (f : L.functions n) (x : fin n → (Π a, M a)) :
  fun_map f (λ i, ((x i) : dgerm ↑u M)) = λ a, fun_map f (λ i, x i a) :=
by apply fun_map_quotient_mk

lemma realize_term_cast {β : Type*} (x : β → (Π a, M a)) (t : L.term β) :
  realize_term (λ i, ((x i) : dgerm ↑u M)) t = λ a, realize_term (λ i, x i a) t :=
begin
  convert @realize_term_quotient_mk L _  (dgerm_setoid ↑u M) (dgerm.setoid_prestructure M u) _ x t,
  ext a,
  induction t,
  { refl },
  { simp only [realize_term, t_ih],
    refl }
end

variables [Π a : α, nonempty (M a)]

theorem realize_bounded_formula_cast {β : Type*} {n : ℕ} (φ : L.bounded_formula β n)
  (x : β → (Π a, M a)) (v : fin n → (Π a, M a)) :
  realize_bounded_formula (dgerm ↑u M) φ (λ (i : β), (x i)) (λ i, (v i)) ↔
    ∀ᶠ (a : α) in ↑u, realize_bounded_formula (M a) φ (λ (i : β), x i a) (λ i, v i a) :=
begin
  induction φ with _ _ _ _ _ _ _ _ m a0 a1 a2 a3 a4 a5 a6 a7 a8 a9,
  { simp },
  { have h2 : ∀ a : α, sum.elim (λ (i : β), x i a) (λ i, v i a) = λ i, sum.elim x v i a,
    { intro a,
      ext i,
      cases i;
      simp, },
    simp only [realize_bounded_formula, (sum.comp_elim coe x v).symm, h2, realize_term_cast],
    exact quotient.eq' },
  { have h2 : ∀ a : α, sum.elim (λ (i : β), x i a) (λ i, v i a) = λ i, sum.elim x v i a,
    { intro a,
      ext i,
      cases i;
      simp, },
    simp only [realize_bounded_formula, (sum.comp_elim coe x v).symm, h2, realize_term_cast],
    unfold rel_map,
    rw quotient.lift,
    change quotient.lift _ _ (quotient.fin_choice (λ _, ⟦_⟧)) ↔ _,
    simp_rw [quotient.fin_choice_eq, quotient.lift_mk] },
  { simp only [realize_bounded_formula, a2 v, a3 v],
    rw ultrafilter.eventually_imp },
  { simp only [realize_bounded_formula],
    transitivity (∀ (m : Π (a : α), M a), realize_bounded_formula (dgerm ↑u M) a5
      (λ (i : β), ↑(x i)) (fin.cons (↑m : dgerm ↑u M) (coe ∘ v))),
    { exact (@forall_quotient_iff _ (dgerm_setoid ↑u M) _) },
    have h' : ∀ (m : Π a, M a) (a : α), (λ (i : fin (a4 + 1)), (fin.cons m v : _ → Π a, M a) i a) =
      fin.cons (m a) (λ (i : fin a4), v i a),
    { intros m a,
      ext i,
      apply fin.induction_on i,
      { refl },
      { intros i hi,
        simp only [fin.cons_succ] } },
    simp only [← fin.comp_cons, a6, h'],
    refine ⟨λ h, _, λ h m, _⟩,
    { contrapose! h,
      simp_rw [← ultrafilter.eventually_not, not_forall] at h,
      refine ⟨λ a : α, classical.epsilon (λ m : M a, ¬ realize_bounded_formula (M a)
        a5 (λ i, x i a) (fin.cons m (λ i, v i a))), _⟩,
      rw [← ultrafilter.eventually_not],
      refine filter.mem_of_superset h (λ a ha, classical.epsilon_spec ha) },
    { rw filter.eventually_iff at *,
      exact filter.mem_of_superset h (λ a ha, ha (m a)) } }
end

theorem realize_formula_cast {β : Type*} (φ : L.formula β) (x : β → (Π a, M a)) :
  realize_formula (dgerm ↑u M) φ (λ i, ((x i) : dgerm ↑u M)) ↔
    ∀ᶠ (a : α) in u, realize_formula (M a) φ (λ i, (x i a)) :=
begin
  simp_rw [realize_formula],
  convert realize_bounded_formula_cast φ x fin_zero_elim,
  { simp },
  ext,
  rw iff_eq_eq,
  refine congr rfl _,
  simp,
end

/-- Łoś's Theorem : A sentence is true in an ultraproduct if and only if the set of structures it is
  true in is in the ultrafilter. -/
theorem realize_sentence (φ : L.sentence) :
  realize_sentence (dgerm ↑u M) φ ↔ ∀ᶠ (a : α) in u, realize_sentence (M a) φ :=
begin
  simp_rw [realize_sentence],
  convert realize_formula_cast φ pempty.elim,
  { simp only [eq_iff_true_of_subsingleton] },
  swap,
  { apply_instance },
  ext a,
  rw iff_eq_eq,
  refine congr rfl _,
  simp,
end
end dgerm

namespace Theory

/-! The Compactness Theorem
theorem is_satisfiable_iff_is_finitely_satisfiable {T : L.Theory} :
  T.is_satisfiable ↔ T.is_finitely_satisfiable :=
⟨Theory.is_satisfiable.is_finitely_satisfiable, λ h, begin
  classical,
  unfold is_finitely_satisfiable at h,
  let M : Π (T0 : {T0 : finset L.sentence // ↑T0 ⊆ T}), Type (max u v) :=
    λ T0, (h T0.1 T0.2).some_model,
  by_cases hinf : infinite {T0 : finset L.sentence // ↑T0 ⊆ T},
  { haveI := hinf,
    haveI : Π (T0 : {T0 : finset L.sentence // ↑T0 ⊆ T}), L.Structure (M T0) :=
      λ T0, is_satisfiable.some_model_structure (h T0.1 T0.2),
   haveI : (filter.at_top : filter ({T0 : finset L.sentence // ↑T0 ⊆ T})).ne_bot,
    { convert @at_top_ne_bot {T0 : finset L.sentence // ↑T0 ⊆ T}
        _ (subtype.semilattice_sup (λ x y hx hy, _)),
      rw [finset.sup_eq_union, finset.coe_union],
      exact set.union_subset hx hy, },
    refine ⟨dgerm ↑(ultrafilter.of filter.at_top) M, _, dgerm.Structure, _⟩,
    { haveI : Π (T0 : {T0 : finset L.sentence // ↑T0 ⊆ T}), inhabited (M T0),
      { exact λ T0, classical.inhabited_of_nonempty
        (is_satisfiable.nonempty_some_model (h T0.1 T0.2)) },
      exact nonempty_of_inhabited },
    intros φ hφ,
    rw dgerm.realize_sentence,
    rw filter.eventually,
  },
end⟩
-/

end Theory

end language
end first_order
