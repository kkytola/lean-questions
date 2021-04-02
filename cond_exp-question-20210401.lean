import tactic 
import measure_theory.integration
import measure_theory.measurable_space

noncomputable theory
open set 
open classical
open measure_theory
open measurable_space
open_locale ennreal



namespace cond_exp



def is_subsigmaalg {S : Type*} (Γ₁ Γ₂ : measurable_space S ) : Prop :=
  ∀ (E : set S ) , (Γ₁.is_measurable' E) → (Γ₂.is_measurable' E)

lemma is_subsigmaalg_iff_le {S : Type*} {Γ₁ Γ₂ : measurable_space S } :
  is_subsigmaalg Γ₁ Γ₂ ↔ Γ₁ ≤ Γ₂ :=
begin
  split ,
  { intros hsub E hE ,
    exact hsub E hE , } ,
  { intros hle E hE ,
    exact hle E hE , } ,
end

@[simp]
lemma self_is_subsigmaalg {S : Type*} (Γ : measurable_space S ) :
  is_subsigmaalg Γ Γ := by { intros E hE , exact hE , }

@[simp]
lemma self_le_self_sigmaalg {S : Type*} (Γ : measurable_space S ) :
  Γ ≤ Γ := by { intros E hE , exact hE , }

lemma self_is_subsigmaalg' {S : Type*} (Γ : measurable_space S ) :
  is_subsigmaalg Γ Γ :=
begin
  have key : Γ ≤ Γ ,
  { intros E hE ,
    exact hE , } , 
  rwa is_subsigmaalg_iff_le ,
end

def is_trivial_sigmaalg {S : Type*} (Γ : measurable_space S ) : Prop :=
  ∀ (E : set S ) , (Γ.is_measurable' E) → (E = ∅ ∨ E = univ) 

@[simp]
lemma trivial_is_subsigmaalg {S : Type*}
  (Γtriv Γ : measurable_space S ) [htriv : is_trivial_sigmaalg Γtriv] :
  is_subsigmaalg Γtriv Γ :=
begin
  intros E hE , 
  have key := htriv E hE ,
  cases key with hemp huniv ,
  { rw hemp ,
    exact measurable_space.is_measurable_empty Γ , } , 
  { rw huniv ,
    have mbleuniv := (Γ.is_measurable_compl ∅ Γ.is_measurable_empty) ,
    simp at mbleuniv ,
    exact mbleuniv , } ,
end

@[simp]
lemma trivial_le_sigmaalg {S : Type*}
  (Γtriv Γ : measurable_space S ) [htriv : is_trivial_sigmaalg Γtriv] :
  Γtriv ≤ Γ :=
begin
  have key := ( @trivial_is_subsigmaalg S Γtriv Γ htriv ) ,
  rw ← is_subsigmaalg_iff_le ,
  exact key ,
end

lemma mble_of_submble {S T : Type*} [measurable_space T] (f : S → T)
  (Γsub Γfull : measurable_space S ) [hsub : Γsub ≤ Γfull] :
  (@measurable S T Γsub _ f) → (@measurable S T Γfull _ f) :=
begin
  intros hf B hB ,
  exact hsub (f⁻¹' B) (hf hB) ,
end

structure cond_exp_enn {S : Type*} (f : S → ennreal)
  (Γsub Γfull : measurable_space S ) [hsub : Γsub ≤ Γfull]
  (μ : @measure_theory.measure S Γfull) :=
  -- In the current version I am not requiring measurability
  --     [hf : @measurable S ennreal Γfull _ f]
  -- and integrability. I even failed to state integrability,
  -- the following does not work:
  --     [hintble : measure_theory.has_finite_integral f μ]
  -- Also I'm not requiring that the measure is a
  -- probability measure.
  --     [hproba : probability_measure μ]
  -- All of these would almost always
  -- be needed, so should they be a part of the definition?
    ( to_fun : S → ennreal )
    ( is_submeasurable : @measurable S ennreal Γsub _ to_fun )
    ( equal_subintegrals : ∀ (E : set S) , Γsub.is_measurable' E →
        ∫⁻ x in E , to_fun(x) ∂ μ = ∫⁻ x in E , f(x) ∂ μ )



-- Of course there should be a coercion to function,
-- just pick the `to_fun`! Somehow, I did not manage to
-- make this work at all...
@[instance]
def cond_exp_enn.has_coe_to_fun {S : Type*} 
  {Γsub Γfull : measurable_space S} [hsub : is_subsigmaalg Γsub Γfull]
  {f : S → ennreal} {μ : @measure_theory.measure S Γfull} :
  has_coe_to_fun (@cond_exp_enn S f Γsub Γfull hsub μ)  :=
{ coe := sorry ,
  F := sorry ,
}


lemma cond_exp_enn_full {S : Type*} 
  {Γ : measurable_space S}
  {f : S → ennreal} [hf : @measurable S ennreal Γ _ f]
  {μ : @measure_theory.measure S Γ} :
  @cond_exp_enn S f Γ Γ (self_le_self_sigmaalg Γ) μ :=
{ to_fun := f ,
  is_submeasurable := hf ,
  equal_subintegrals := by { intros E hE , refl , } ,
}

lemma cond_exp_enn_trivial {S : Type*} 
  {Γtriv Γ : measurable_space S} [htriv  : is_trivial_sigmaalg Γtriv]
  {f : S → ennreal} [hf : @measurable S ennreal Γ _ f]
  {μ : @measure_theory.measure S Γ} [hproba : probability_measure μ] :
  @cond_exp_enn S f Γtriv Γ (@trivial_le_sigmaalg S Γtriv Γ htriv) μ :=
{ to_fun := ( λ (z : S) , ( ∫⁻ x , f(x) ∂ μ ) ) ,
  is_submeasurable := by simp , 
  equal_subintegrals :=
  begin
    intros E hE ,
    have key := htriv E hE ,
    cases key with hemp huniv ,
    { rw hemp ,
      simp , } , 
    { rw huniv ,
      simp ,
      rw hproba.measure_univ ,
      simp , } , 
  end
}



end cond_exp
