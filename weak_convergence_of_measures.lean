/-
Copyright (c) 2021 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import tactic
import weak_dual
import measure_theory.integral.bochner


noncomputable theory
open measure_theory
open set
open filter
open_locale topological_space bounded_continuous_function ennreal nnreal

section finite_measures
/-!
### Finite measures
In this section, we define the `Type` of finite measures on a given measurable space. This type
will be equipped with the topology of weak convergence of measures when the measurable space is
a topological space equipped with its Borel sigma-algebra.
-/

variables {α : Type} [measurable_space α]

/-- Finite measures are defined as the subtype of measures that have the property of being finite
measures (i.e., their total mass is finite). -/
def finite_measures (α : Type*) [measurable_space α] : Type :=
{ μ : measure α // finite_measure μ }

namespace finite_measures

instance has_zero {α : Type*} [measurable_space α] : 
  has_zero (finite_measures α) :=
⟨{ val := 0,
   property := measure_theory.finite_measure_zero, }⟩

instance finite_measure_add {α : Type*} [measurable_space α]
  (μ ν : measure α) [finite_measure μ] [finite_measure ν] :
  finite_measure (μ + ν) :=
{ measure_univ_lt_top := begin 
    simp only [measure.coe_add, pi.add_apply, ennreal.add_lt_top],
    exact ⟨measure_lt_top μ univ, measure_lt_top ν univ⟩,
  end, }

instance {α : Type*} [measurable_space α] : has_add (finite_measures α) :=
{ add := (λ (μ ν : finite_measures α), 
  { val := μ.val + ν.val,
    property := @finite_measures.finite_measure_add _ _ _ _ μ.prop ν.prop, }), }

instance : inhabited (finite_measures α) := { default := 0 }

/-- A finite measure can be interpreted as a measure. -/
def to_measure (μ : finite_measures α) : (measure_theory.measure α) := subtype.val μ

instance to_measure.finite_measure (μ : finite_measures α) :
  finite_measure μ.to_measure := μ.prop

instance (α : Type*) [measurable_space α] :
  has_coe_to_fun (finite_measures α) := ⟨(λ _, set α → ℝ≥0), 
    (λ μ, (λ s, (μ.val.measure_of s).to_nnreal))⟩

lemma to_fun_eq_to_measure_to_nnreal (ν : finite_measures α) :
  (ν : set α → ℝ≥0) = λ s, (ν.to_measure s).to_nnreal := rfl

lemma to_measure_eq_val (ν : finite_measures α) : ν.to_measure = ν.val := rfl

lemma to_measure_injective : 
  function.injective (@finite_measures.to_measure α ‹measurable_space α›) :=
by { intros μ ν, exact subtype.eq, }

lemma to_measure_zero :
  (@finite_measures.to_measure α ‹measurable_space α›) 0 = 0 := rfl

lemma to_measure_add (μ ν : finite_measures α) :
  μ.to_measure + ν.to_measure = (μ + ν).to_measure := rfl

/-- The (total) mass of a finite measure `μ` is `μ univ`, i.e., the cast to `nnreal` of
`μ.to_measure univ`. -/
def mass {α : Type*} [measurable_space α] (μ : finite_measures α) : ℝ≥0 := μ univ

lemma mass_def {α : Type*} [measurable_space α] {μ : finite_measures α} :
  μ.mass = μ univ := rfl

@[simp] lemma mass_ennreal {α : Type*} [measurable_space α]
  {μ : finite_measures α} : (μ.mass : ℝ≥0∞) = μ.to_measure univ :=
begin
  apply ennreal.coe_to_nnreal,
  exact ennreal.lt_top_iff_ne_top.mp (μ.prop).measure_univ_lt_top,
end

instance {α : Type*} [measurable_space α] : 
  add_comm_monoid (finite_measures α) :=
(@finite_measures.to_measure_injective α ‹measurable_space α›).add_comm_monoid
    (@finite_measures.to_measure α ‹measurable_space α›)
    finite_measures.to_measure_zero finite_measures.to_measure_add

--TODO: Make `finite_measures α` an `ℝ≥0`-module, so that it makes sense (later)
--      to define a continuous linear map `finite_measures α → weak_dual ℝ≥0 (α →ᵇ ℝ≥0)`.
--instance finite_measures.module : module ℝ≥0 (finite_measures α) := sorry

end finite_measures -- end namespace

end finite_measures -- end section



section probability_measures
/-!
### Probability measures
In this section, we define the `Type` of probability measures on a given measurable space. This
type will be equipped with the topology of weak convergence of measures when the measurable space
is a topological space equipped with its Borel sigma-algebra.

There is a coercion (embedding) to finite measures on the same space.
-/

variables {α : Type} [measurable_space α]

/-- Probability measures are defined as the subtype of measures that have the property of being
probability measures (i.e., their total mass is one). -/
def probability_measures (α : Type) [measurable_space α] : Type :=
{μ : measure α // probability_measure μ}

namespace probability_measures

instance [inhabited α] : inhabited (probability_measures α) :=
⟨{ val := measure_theory.measure.dirac (default α),
   property := measure_theory.measure.dirac.probability_measure, }⟩

/-- A probability measure can be interpreted as a measure. -/
def to_measure (μ : probability_measures α) : (measure_theory.measure α) := μ.val

instance to_measure.probability_measure (μ : probability_measures α) :
  probability_measure μ.to_measure := μ.prop

instance (α : Type*) [measurable_space α] :
  has_coe_to_fun (probability_measures α) := ⟨(λ _, set α → ℝ≥0), 
    (λ μ, (λ s, (μ.val.measure_of s).to_nnreal))⟩

lemma to_fun_eq_to_measure_to_nnreal (ν : probability_measures α) :
  (ν : set α → ℝ≥0) = λ s, (ν.to_measure s).to_nnreal := rfl

@[simp]
lemma to_fun_univ (ν : probability_measures α) : ν univ = 1 :=
begin
  rw [to_fun_eq_to_measure_to_nnreal, ←ennreal.one_to_nnreal],
  exact congr_arg ennreal.to_nnreal ν.prop.measure_univ,
end

lemma to_measure_eq_val (ν : probability_measures α) : ν.to_measure = ν.val := rfl

lemma to_measure_injective : 
  function.injective (@probability_measures.to_measure α ‹measurable_space α›) :=
by { intros μ ν, exact subtype.eq, }

instance has_coe_to_finite_measures (α : Type*) [measurable_space α] :
  has_coe (probability_measures α) (finite_measures α) :=
{ coe := λ μ , { val := μ.val,
                 property := begin
                   have key : (1 : ennreal) < ⊤ := ennreal.one_lt_top,
                   rw [←μ.prop.measure_univ] at key,
                   exact ⟨key⟩,
                 end, }}

/-- A probability measure can be interpreted as a finite measure. -/
def to_finite_measure (μ : probability_measures α) : (finite_measures α) := μ

@[simp]
lemma to_finite_measure_to_measure_eq_to_measure (ν : probability_measures α) :
  (ν.to_finite_measure).to_measure = ν.to_measure := rfl

lemma to_finite_measure_to_measure_eq_val (ν : probability_measures α) :
  (ν.to_finite_measure).to_measure = ν.val := rfl

@[simp]
lemma to_finite_measure_to_fun_eq_to_fun (ν : probability_measures α) :
  (ν.to_finite_measure : set α → ℝ≥0) = (ν : set α → ℝ≥0) := rfl

@[simp]
lemma to_finite_measure_mass (μ : probability_measures α) :
  μ.to_finite_measure.mass = 1 :=
begin
  unfold finite_measures.mass,
  rw [←μ.to_fun_univ, to_finite_measure_to_fun_eq_to_fun],
end

end probability_measures -- end namespace

end probability_measures -- end section



section various_lemmas

-- NOTE: Eh, what is the right way to do this `nnreal_mul_ennreal_to_nnreal`?
-- If this deserves to be added, then perhaps in `data.real.ennreal`?
-- It seems like a typical coercion issue to me, although it is only used once here.
lemma nnreal_mul_ennreal_to_nnreal (c : ℝ≥0) (z : ℝ≥0∞) :
  c * z.to_nnreal = ((c : ℝ≥0∞) * z).to_nnreal :=
begin
  by_cases z_infty : z = ⊤,
  { rw z_infty,
    simp only [ennreal.top_to_nnreal, ennreal.to_nnreal_mul_top, mul_zero], },
  { have z_lt_top : z < ⊤ := ennreal.lt_top_iff_ne_top.mpr z_infty,
    simp only [ennreal.to_nnreal_mul, ennreal.to_nnreal_coe], },
end

-- NOTE: I have been almost wondering why the following is not the definition of
-- boundedness. I have not found it in the library, but believe it should be there.
-- Is `topology.continuous_function.bounded` the appropriate place? The proof needs golf, though.
lemma bounded_continuous_function.radius_bounded {α β : Type*}
  [topological_space α] [metric_space β] (f : α →ᵇ β) (z : β):
  ∃ (c : ℝ), ∀ (a : α), dist z (f(a)) ≤ c :=
begin
  cases f.bounded with c hc ,
  by_cases is_empty α,
  { use 0, intros a, exfalso, exact is_empty_iff.mp h a, },
  cases not_is_empty_iff.mp h with a₀,
  use (dist z (f(a₀))) + c,
  intros a,
  have le : ∀ (y : ℝ), y + (dist (f(a₀)) (f(a))) ≤ y + c := λ y, add_le_add rfl.ge (hc a₀ a),
  exact (dist_triangle z (f(a₀)) (f(a))).trans (le _),
end

-- NOTE: The following is a "special case" of the above. I think it is also worthwhile, although
-- it is not needed in this file. If it should be added, what is the right place? 
lemma bounded_continuous_function.norm_bounded {α β : Type*}
  [topological_space α] [normed_group β] (f : α →ᵇ β) :
  ∃ (c : ℝ), ∀ x, ∥ f x ∥ ≤ c :=
begin
  have norm_eq_dist : ∀ (z : β), ∥ z ∥ = dist 0 z := λ z, congr_fun (dist_zero_left).symm z,
  simp_rw [norm_eq_dist],
  exact bounded_continuous_function.radius_bounded f 0,
end

-- NOTE: The following is another "special case". While special, I think it may be worthwhile.
-- If so, what is the right place? How to golf?
lemma bounded_continuous_function.nnreal.upper_bound {α : Type*} [topological_space α]
  (f : α →ᵇ ℝ≥0) : ∃ (c : nnreal), (∀ x, f(x) ≤ c) :=
begin
  have val_eq_dist_nnreal : ∀ (z : ℝ≥0), (z : ℝ) = dist 0 z,
  { intros z,
    simp only [nnreal.dist_eq, nnreal.coe_zero, zero_sub, nnreal.abs_eq, abs_neg], },
  cases bounded_continuous_function.radius_bounded f 0 with c hc,
  simp_rw ←val_eq_dist_nnreal at hc,
  use (max c 0).to_nnreal,
  intros x,
  apply (@real.le_to_nnreal_iff_coe_le (f x) _ (le_max_right c 0)).mpr,
  apply (hc x).trans (le_max_left c 0),
end

-- NOTE: This one is not actually needed in the current version with nonnegative test functions.
-- It will be needed later. If this doesn't exist yet, then after golfing the proof, this might
-- be appropriate in `measure_theory.function.L1_space` (not in
-- `topology.continuous_function.bounded` because of imports?).
lemma bounded_continuous_function.integrable {α β: Type}
  [topological_space α] [measurable_space α] [opens_measurable_space α]
  [normed_group β] [measurable_space β] [borel_space β]
  (μ : measure α) [finite_measure μ] (f : α →ᵇ β) : integrable f μ :=
begin
  set f' := ennreal.of_real ∘ norm ∘ f with hf' ,
  suffices : lintegral μ f' < ⊤ ,
  { have ae_mble : @ae_measurable α β ‹measurable_space β› ‹measurable_space α› f μ
    := continuous.ae_measurable f.continuous μ,
    exact ⟨ ae_mble , (has_finite_integral_iff_norm f).mpr this ⟩, } ,
  have bdd : ∀ (x : α), f' x ≤ ennreal.of_real (∥ f ∥) ,
  { intros x,
    exact ennreal.of_real_le_of_real (bounded_continuous_function.norm_coe_le_norm f x), },
  have integr_bdd := @lintegral_mono α _ μ _ _ bdd,
  set c' := ennreal.of_real (∥ f ∥) with hc',
  have const_integr : lintegral μ (λ x , c') = c' * (μ(univ)) := by rw lintegral_const,
  have total : c' * (μ(univ)) < ⊤,
  { apply ennreal.mul_lt_top ennreal.of_real_lt_top
      (‹finite_measure μ›).measure_univ_lt_top, },
  rw ← const_integr at total,
  exact lt_of_le_of_lt integr_bdd total,
end

-- NOTE: I believe this is useful, but what is the right place?
-- `measure_theory.function.L1_space`? `topology.continuous_function.bounded`?
lemma bounded_continuous_function.coe_nnreal_comp_measurable {α : Type*} [topological_space α]
  [measurable_space α] [opens_measurable_space α] (f : α →ᵇ ℝ≥0) : 
  measurable ((coe : ℝ≥0 → ℝ≥0∞) ∘ f) :=
measurable.comp measurable_coe_nnreal_ennreal (continuous.measurable f.continuous)

-- NOTE: The following is probably too special for anywhere else, but is a useful standalone
-- lemma here.
lemma lintegral_lt_top_of_bounded_continuous_to_nnreal {α : Type*} [topological_space α]
  [measurable_space α] (μ : measure α) [μ_fin : finite_measure μ] (f : α →ᵇ ℝ≥0) :
  lintegral μ ((coe : ℝ≥0 → ℝ≥0∞) ∘ f) < ⊤ :=
begin
  cases bounded_continuous_function.nnreal.upper_bound f with c hc,
  have le' : (coe : ℝ≥0 → ℝ≥0∞) ∘ f ≤ (λ (x : α), c),
  by { intros x, simp only [hc, ennreal.coe_le_coe], },
  apply lt_of_le_of_lt (@lintegral_mono _ _ μ _ _ le'),
  rw lintegral_const,
  exact ennreal.mul_lt_top ennreal.coe_lt_top μ_fin.measure_univ_lt_top,
end

-- TODO: What to do with this? Hmm... I've ended up using it quite regularly in the definitions
-- of certain topologies.
lemma tendsto_induced_iff {α β γ : Type*} {F : filter γ} [topological_space β]
  {f : α → β} {xs : γ → α} {x : α} :
  tendsto xs F (@nhds α (topological_space.induced f infer_instance) x) ↔
    tendsto (λ i, f(xs(i))) F (𝓝 (f(x))) :=
begin
  split,
  { intros conv_induced,
    have f_cont := @continuous_induced_dom α β f infer_instance,
    have key := @continuous.tendsto α β
      (topological_space.induced f infer_instance) infer_instance f f_cont,
    exact tendsto.comp (key x) conv_induced, },
  { intros conv_image,
    rw nhds_induced,
    exact map_le_iff_le_comap.mp conv_image, },
end

end various_lemmas



section weak_convergence_of_measures

/-!
### The topology of weak convergence of measures
In this section, we define the topology of weak convergence on the set of Borel probability
measures and on the set of finite Borel measures on a topological space.
-/

/- NOTE / TODO:
The pairing of measures with test functions are called `test_against_nn` since the test functions
are taken to be `ℝ≥0`-valued in the definition of the topology (this allows us to use the Lebesgue
integral `lintegral`, but requires some coercions). It seems natural to later add `test_against`
for pairings via Bochner integrals (`integral`) with (bounded continuous) functions with values
in an arbitrary Banach spaces, especially with values in `ℝ` and `ℂ`. -/

variables {α : Type} [measurable_space α] [topological_space α]

/-- The pairing of a (Borel) probability measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure. This
is `probability_measures.test_against'`. -/
abbreviation probability_measures.test_against_nn
  (μ : probability_measures α) (f : α →ᵇ nnreal) : ℝ≥0 :=
(lintegral μ.to_measure ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)).to_nnreal

lemma probability_measures.test_against_nn_def (μ : probability_measures α) {f : α →ᵇ nnreal} :
  μ.test_against_nn f = (lintegral μ.to_measure ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)).to_nnreal := by refl

/-- The pairing of a finite (Borel) measure `μ` with a nonnegative bounded continuous
function is obtained by (Lebesgue) integrating the (test) function against the measure. This
is `finite_measures.test_against'`. -/
abbreviation finite_measures.test_against_nn
  (μ : finite_measures α) (f : α →ᵇ nnreal) : ℝ≥0 :=
(lintegral μ.to_measure ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)).to_nnreal

lemma finite_measures.test_against_nn_def (μ : finite_measures α) {f : α →ᵇ nnreal} :
  μ.test_against_nn f = (lintegral μ.to_measure ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)).to_nnreal := by refl

lemma finite_measures.test_against_nn_coe_eq {μ : finite_measures α} {f : α →ᵇ nnreal} :
  (μ.test_against_nn f : ℝ≥0∞) = lintegral μ.to_measure ((coe : ℝ≥0 → ℝ≥0∞) ∘ f) :=
begin
  have key_lt := lintegral_lt_top_of_bounded_continuous_to_nnreal μ.to_measure f,
  exact ennreal.coe_to_nnreal (ennreal.lt_top_iff_ne_top.mp key_lt),
end

lemma probability_measures.test_against_nn_coe_eq {μ : probability_measures α} {f : α →ᵇ nnreal} :
  (μ.test_against_nn f : ℝ≥0∞) = lintegral μ.to_measure ((coe : ℝ≥0 → ℝ≥0∞) ∘ f) :=
begin
  have key_lt := lintegral_lt_top_of_bounded_continuous_to_nnreal μ.to_measure f,
  exact ennreal.coe_to_nnreal (ennreal.lt_top_iff_ne_top.mp key_lt),
end

@[simp]
lemma probability_measures.to_finite_measure_test_against_nn_eq_test_against_nn (α : Type*)
  [measurable_space α] [topological_space α] {μ : probability_measures α} {f : α →ᵇ nnreal} :
  μ.to_finite_measure.test_against_nn f = μ.test_against_nn f := rfl

lemma finite_measures.test_against_nn_const (μ : finite_measures α) (c : ℝ≥0) :
  μ.test_against_nn (bounded_continuous_function.const α c) = c * μ.mass :=
begin
  rw finite_measures.test_against_nn_def,
  have eq : (coe : ℝ≥0 → ℝ≥0∞) ∘ (bounded_continuous_function.const α c) = (λ x, (c : ennreal)),
  by refl,
  rw [eq, lintegral_const, ennreal.to_nnreal_mul],
  simp only [mul_eq_mul_left_iff, ennreal.to_nnreal_coe, finite_measures.mass_def],
  left,
  refl,
end

lemma probability_measures.test_against_nn_const (μ : probability_measures α) (c : ℝ≥0) :
  μ.test_against_nn (bounded_continuous_function.const α c) = c :=
begin
  have key := finite_measures.test_against_nn_const μ.to_finite_measure c,
  simp only [mul_one, probability_measures.to_finite_measure_mass] at key,
  exact key,
end

lemma finite_measures.test_against_nn_mono (μ : finite_measures α)
  {f g : α →ᵇ ℝ≥0} (f_le_g : (f : α → ℝ≥0) ≤ g) :
  μ.test_against_nn f ≤ μ.test_against_nn g :=
begin
  repeat { rw finite_measures.test_against_nn_def, },
  apply ennreal.coe_le_coe.mp,
  repeat { rw ennreal.coe_to_nnreal, },
  { apply lintegral_mono,
    intros x,
    apply ennreal.coe_mono, 
    exact f_le_g x, },
  repeat { apply ennreal.lt_top_iff_ne_top.mp,
           apply lintegral_lt_top_of_bounded_continuous_to_nnreal, },
end

lemma probability_measures.test_against_nn_mono (μ : probability_measures α)
  {f g : α →ᵇ ℝ≥0} (f_le_g : (f : α → ℝ≥0) ≤ g) :
  μ.test_against_nn f ≤ μ.test_against_nn g :=
begin
  have key := finite_measures.test_against_nn_mono μ.to_finite_measure f_le_g,
  simp only [probability_measures.to_finite_measure_test_against_nn_eq_test_against_nn] at key,
  exact key,
end

lemma continuous_bounded_nn_add_comp_coe {β : Type*} [topological_space β] {f₁ f₂ : β →ᵇ ℝ≥0} :
  (coe : ℝ≥0 → ℝ≥0∞) ∘ (f₁ + f₂) = ( ((coe : ℝ≥0 → ℝ≥0∞) ∘ f₁) + ((coe : ℝ≥0 → ℝ≥0∞) ∘ f₂)) :=
by { funext x, simp only [ennreal.coe_add, pi.add_apply, function.comp_app], }

lemma continuous_bounded_nn_smul_comp_coe {β : Type*} [topological_space β] {c : ℝ≥0}
  {f : β →ᵇ ℝ≥0} :
  (coe : ℝ≥0 → ℝ≥0∞) ∘ (c • f) = c • ( ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)) :=
begin
  funext x,
  simpa only [algebra.id.smul_eq_mul, function.comp_app, pi.smul_apply, ennreal.coe_mul],
end

lemma continuous_bounded_nn_smul_eq {β : Type*} [topological_space β] {c : ℝ≥0} {f : β →ᵇ ℝ≥0} :
  (c • (f : β → ℝ≥0)) = ((c • f) : β →ᵇ ℝ≥0) := by refl

lemma continuous_bounded_nn_smul_comp_coe' {β : Type*} [topological_space β] {c : ℝ≥0} {f : β →ᵇ ℝ≥0} :
  (coe : ℝ≥0 → ℝ≥0∞) ∘ (c • f) = c • ( ((coe : ℝ≥0 → ℝ≥0∞) ∘ f)) :=
begin
  funext x,
  simpa only [algebra.id.smul_eq_mul, function.comp_app, pi.smul_apply, ennreal.coe_mul],
end

variables [opens_measurable_space α] -- [borel_space α]

lemma finite_measures.test_against_nn_add (μ : finite_measures α) (f₁ f₂ : α →ᵇ ℝ≥0) :
  μ.test_against_nn (f₁ + f₂) = μ.test_against_nn f₁ + μ.test_against_nn f₂ :=
begin
  rw ← ennreal.to_nnreal_add
    (lintegral_lt_top_of_bounded_continuous_to_nnreal μ.to_measure f₁)
    (lintegral_lt_top_of_bounded_continuous_to_nnreal μ.to_measure f₂),
  rw ← @lintegral_add _ _ μ.to_measure _ _
    f₁.coe_nnreal_comp_measurable f₂.coe_nnreal_comp_measurable,
  refl,
end

lemma finite_measures.test_against_nn_smul (μ : finite_measures α) (c : ℝ≥0) (f : α →ᵇ ℝ≥0) :
  μ.test_against_nn (c • f) = c * μ.test_against_nn f :=
begin
  have key_smul := @lintegral_mul_const _ _ μ.to_measure c _ f.coe_nnreal_comp_measurable,
  simp_rw mul_comm at key_smul,
  repeat { rw finite_measures.test_against_nn_def, },
  rw [nnreal_mul_ennreal_to_nnreal, ←key_smul],
  rw [←continuous_bounded_nn_smul_eq, @continuous_bounded_nn_smul_comp_coe _ _ c f],
  refl,
end

/-- Integration against a finite_measure defines a linear map from nonnegative bounded continuous
functions to nonnegative real numbers. -/
def finite_measures.test_against_nn_linear_map (μ : finite_measures α) :
  linear_map ℝ≥0 (α →ᵇ ℝ≥0) ℝ≥0 :=
{ to_fun := μ.test_against_nn,
  map_add' := finite_measures.test_against_nn_add μ,
  map_smul' := finite_measures.test_against_nn_smul μ, }

lemma nnreal.le_add_dist (a b : ℝ≥0) : a ≤ b + (dist a b).to_nnreal :=
begin
  suffices : (a : ℝ) ≤ (b : ℝ) + (dist a b),
  { have coe_eq : (coe : ℝ≥0 → ℝ) (b + (dist a b).to_nnreal) = (b : ℝ) + dist a b,
    { rw nnreal.coe_add,
      simp only [real.coe_to_nnreal', max_eq_left_iff, add_right_inj],
      exact dist_nonneg, },
    rw ←coe_eq at this,
    apply nnreal.coe_le_coe.mp this, },
  have key : abs (a-b : ℝ) ≤ (dist a b) := by refl,
  linarith [le_of_abs_le key],
end

lemma finite_measures.lipschitz_estimate (μ : finite_measures α) (f g : α →ᵇ ℝ≥0) :
  μ.test_against_nn f ≤ μ.test_against_nn g + (dist f g).to_nnreal * μ.mass :=
begin
  have coe_eq : ennreal.of_real (dist f g) = ((dist f g).to_nnreal : ℝ≥0∞) := by refl,
  rw ←finite_measures.test_against_nn_const μ (dist f g).to_nnreal,
  rw ←finite_measures.test_against_nn_add,
  repeat { rw finite_measures.test_against_nn_def, },
  apply ennreal.coe_le_coe.mp,
  repeat { rw ennreal.coe_to_nnreal, },
  { apply lintegral_mono,
    have le_dist : ∀ x, dist (f x) (g x) ≤ (dist f g)
    := bounded_continuous_function.dist_coe_le_dist,
    have le' : ∀ x, f(x) ≤ g(x) + (dist f g).to_nnreal,
    { intros x,
      apply (nnreal.le_add_dist (f x) (g x)).trans,
      rw add_le_add_iff_left,
      exact real.to_nnreal_mono (le_dist x), },
    have le : ∀ x, (f(x) : ℝ≥0∞) ≤ (g(x) : ℝ≥0∞) + ennreal.of_real (dist f g),
    { intros x,
      rw [coe_eq, ←ennreal.coe_add],
      exact ennreal.coe_mono (le' x), },
    exact le, },
  repeat { apply ennreal.lt_top_iff_ne_top.mp,
           apply lintegral_lt_top_of_bounded_continuous_to_nnreal, },
end

lemma finite_measures.test_against_nn_lipschitz (μ : finite_measures α) :
  lipschitz_with μ.mass μ.test_against_nn :=
begin
  rw lipschitz_with_iff_dist_le_mul,
  intros f₁ f₂,
  suffices : abs (μ.test_against_nn f₁ - μ.test_against_nn f₂ : ℝ) ≤ μ.mass * (dist f₁ f₂),
  { rwa nnreal.dist_eq, },
  apply (@abs_le ℝ _ _ _ _ _).mpr,
  split,
  { have key' := μ.lipschitz_estimate f₂ f₁,
    rw mul_comm at key',
    suffices : ↑(μ.test_against_nn f₂) ≤ ↑(μ.test_against_nn f₁) + ↑(μ.mass) * dist f₁ f₂,
    { linarith, },
    have key := nnreal.coe_mono key',
    rwa [nnreal.coe_add, nnreal.coe_mul, real.coe_to_nnreal, dist_comm] at key,
    exact dist_nonneg, },
  { have key' := μ.lipschitz_estimate f₁ f₂,
    rw mul_comm at key',
    suffices : ↑(μ.test_against_nn f₁) ≤ ↑(μ.test_against_nn f₂) + ↑(μ.mass) * dist f₁ f₂,
    { linarith, },
    have key := nnreal.coe_mono key',
    rwa [nnreal.coe_add, nnreal.coe_mul, real.coe_to_nnreal] at key,
    exact dist_nonneg, },
end

lemma probability_measures.test_against_nn_lipschitz (μ : probability_measures α) :
  lipschitz_with 1 μ.test_against_nn :=
begin
  have key := μ.to_finite_measure.test_against_nn_lipschitz,
  rwa μ.to_finite_measure_mass at key,
end

/-- A finite measure can be interpreted as an element of the (weak) dual of nonnegative
bounded continuous functions, the duality pairing being integration. -/
def finite_measures.to_weak_dual_of_bcnn (μ : finite_measures α) :
  weak_dual ℝ≥0 (α →ᵇ ℝ≥0) :=
{ to_fun := μ.test_against_nn,
  map_add' := finite_measures.test_against_nn_add μ,
  map_smul' := finite_measures.test_against_nn_smul μ,
  cont := μ.test_against_nn_lipschitz.continuous, }

/-
--TODO: Need `ℝ≥0`-module structure on `finite_measures α`.
--      Currently only `add_comm_monoid` is implemented.
def finite_measures.to_weak_dual_of_bounded_continuous_nn :
  finite_measures α →L[ℝ≥0] weak_dual ℝ≥0 (α →ᵇ ℝ≥0) := sorry
-/

/-- A probability measure can be interpreted as an element of the (weak) dual of nonnegative
bounded continuous functions (random variables), the duality pairing being integration (expected
value). -/
def probability_measures.to_weak_dual_of_bcnn (μ : probability_measures α) :
  weak_dual ℝ≥0 (α →ᵇ ℝ≥0) :=
{ to_fun := μ.test_against_nn,
  map_add' := μ.to_finite_measure.test_against_nn_add,
  map_smul' := μ.to_finite_measure.test_against_nn_smul,
  cont := μ.test_against_nn_lipschitz.continuous, }

lemma finite_measures.test_against_eq_to_weak_dual_test (μ : finite_measures α) :
  (μ.to_weak_dual_of_bcnn : (α →ᵇ ℝ≥0) → ℝ≥0) = μ.test_against_nn := by refl

lemma probability_measures.test_against_eq_to_weak_dual_test (μ : probability_measures α) :
  (μ.to_weak_dual_of_bcnn : (α →ᵇ ℝ≥0) → ℝ≥0) = μ.test_against_nn := by refl

/-- The topology of weak convergence on `finite_measures α` is inherited (induced) from the weak-*
topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function `finite_measures.to_weak_dual_of_bcnn`. -/
instance : topological_space (finite_measures α) :=
topological_space.induced
  (λ (μ : finite_measures α), μ.to_weak_dual_of_bcnn) infer_instance

/-- The topology of weak convergence on `probability_measures α`. This is inherited (induced) from
the weak-*  topology on `weak_dual ℝ≥0 (α →ᵇ ℝ≥0)` via the function 
`probability_measures.to_weak_dual_of_bcnn`. -/
instance : topological_space (probability_measures α) :=
topological_space.induced
  (λ (μ : probability_measures α), μ.to_weak_dual_of_bcnn) infer_instance

/- Integration of (nonnegative bounded continuous) test functions against finite Borel measures
depends continuously on the measure. -/
lemma finite_measures.to_weak_dual_continuous :
  continuous (@finite_measures.to_weak_dual_of_bcnn α _ _ _) :=
continuous_induced_dom

/- Integration of (nonnegative bounded continuous) test functions against Borel probability
measures depends continuously on the measure. -/
lemma probability_measures.to_weak_dual_continuous :
  continuous (@probability_measures.to_weak_dual_of_bcnn α _ _ _) :=
continuous_induced_dom

/- The canonical mapping from probability measures to finite measures is an embedding. -/
lemma probability_measures.coe_embedding (α : Type*)
  [measurable_space α] [topological_space α] [opens_measurable_space α] :
  embedding (coe : probability_measures α → finite_measures α) :=
{ induced := begin
    have key := @induced_compose (probability_measures α) (finite_measures α) _ _ coe
      (@finite_measures.to_weak_dual_of_bcnn α _ _ _),
    exact key.symm,
  end,
  inj := begin
    intros μ ν h,
    apply subtype.eq,
    rw [←μ.to_finite_measure_to_measure_eq_val, ←ν.to_finite_measure_to_measure_eq_val],
    apply congr_arg _ h,
  end, }

lemma probability_measures.tendsto_nhds_iff_to_finite_measures_tendsto_nhds {δ : Type*}
  (F : filter δ) {μs : δ → probability_measures α} {μ₀ : probability_measures α} :
  tendsto μs F (𝓝 μ₀) ↔ tendsto (coe ∘ μs) F (𝓝 (μ₀.to_finite_measure)) :=
embedding.tendsto_nhds_iff (probability_measures.coe_embedding α)

lemma finite_measures.tendsto_iff_weak_star_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measures α} {μ : finite_measures α} :
  tendsto μs F (𝓝 μ) ↔
    tendsto (λ i, (μs(i)).to_weak_dual_of_bcnn)
      F (𝓝 μ.to_weak_dual_of_bcnn) :=
by apply tendsto_induced_iff

theorem finite_measures.tendsto_iff_forall_test_against_nn_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measures α} {μ : finite_measures α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0),
    tendsto (λ i, (μs(i)).to_weak_dual_of_bcnn f)
      F (𝓝 (μ.to_weak_dual_of_bcnn f)) :=
by rw [finite_measures.tendsto_iff_weak_star_tendsto,
       weak_dual.tendsto_iff_forall_test_tendsto]

theorem finite_measures.tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → finite_measures α} {μ : finite_measures α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0),
    tendsto (λ i, lintegral (μs(i)).to_measure (coe ∘ f)) F (𝓝 (lintegral μ.to_measure (coe ∘ f))) :=
begin
  rw finite_measures.tendsto_iff_forall_test_against_nn_tendsto,
  simp_rw finite_measures.test_against_eq_to_weak_dual_test,
  simp_rw ←finite_measures.test_against_nn_coe_eq,
  simp_rw ennreal.tendsto_coe,
end

/-- The usual definition of weak convergence of probability measures is given in terms of sequences
of probability measures: it is the requirement that the integrals of all continuous bounded
functions against members of the sequence converge. This version is a characterization using
nonnegative bounded continuous functions. -/
theorem probability_measures.tendsto_iff_forall_lintegral_tendsto {γ : Type*} {F : filter γ}
  {μs : γ → probability_measures α} {μ : probability_measures α} :
  tendsto μs F (𝓝 μ) ↔
  ∀ (f : α →ᵇ ℝ≥0),
    tendsto (λ i, lintegral (μs(i)).to_measure (coe ∘ f)) F (𝓝 (lintegral μ.to_measure (coe ∘ f))) :=
begin
  rw [probability_measures.tendsto_nhds_iff_to_finite_measures_tendsto_nhds,
      finite_measures.tendsto_iff_forall_lintegral_tendsto],
  refl,
end

end weak_convergence_of_measures
