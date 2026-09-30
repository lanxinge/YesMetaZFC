import YesMetaZFC.Model.ReducedProduct.Structure

/-! # 带显式见证拼接条件的 Łoś 定理

一般 ZF 背景下不能把逐点存在无条件变成一个全域截面。`Witness_m` 只要求在滤子
意义下拼接原公式的见证，保留最弱的实际消费边界。`WitnessData_m` 是可供调用的
显式充分条件；此文件不从存在命题构造该数据，也不假装超滤性质本身蕴含选择。
-/

namespace YesMetaZFC.Logic.FirstOrder.ReducedProduct
open Model SetTheory
universe u v w x y
variable {σ : Signature.{u, v, w}} {I : Type x}
variable (ℳ : I → Structure.{u, v, w, max x y} σ) (U : Filter I)

/-- 存在公式在大集上有见证时，可由某个截面在大集上见证；仅为 Prop 合同。 -/
def Witness_m (h : Nonempty_m ℳ) : Prop :=
  ∀ {b f s} (φ : Formula σ (s :: b) f) (ρ : Env (product_m ℳ h) b f),
    U.sets (fun i => ∃ a, Formula.satisfies ((ρ.map (projection_m ℳ h i).map).pushBound a) φ) →
      ∃ a : (i : I) → (ℳ i).Carrier s,
        U.sets (fun i => Formula.satisfies ((ρ.map (projection_m ℳ h i).map).pushBound (a i)) φ)

/-- 给定的全域见证运算；只有存在成立时要求返回见证，数据由调用者显式提供。 -/
structure WitnessData_m where
  value : ∀ (i : I) {b f s}, Formula σ (s :: b) f → Env (ℳ i) b f → (ℳ i).Carrier s
  satisfies : ∀ (i : I) {b f s} (φ : Formula σ (s :: b) f) (ρ : Env (ℳ i) b f),
    (∃ a, Formula.satisfies (ρ.pushBound a) φ) →
      Formula.satisfies (ρ.pushBound (value i φ ρ)) φ

theorem witness_of_data_m (F : WitnessData_m ℳ) (h : Nonempty_m ℳ) : Witness_m ℳ U h := by
  intro b f s φ ρ hφ
  exact ⟨fun i => F.value i φ (ρ.map (projection_m ℳ h i).map),
    U.upward hφ (fun i hi => F.satisfies i φ _ hi)⟩

/-- 仅针对本指标及排序载体的关系选择原则；不是库自动假定的公理。 -/
def Choice_m : Prop :=
  ∀ s (P : (i : I) → (ℳ i).Carrier s → Prop),
    (∀ i, ∃ a, P i a) → ∃ a : (i : I) → (ℳ i).Carrier s, ∀ i, P i (a i)

theorem witness_of_choice_m (hC : Choice_m ℳ) (h : Nonempty_m ℳ) : Witness_m ℳ U h := by
  intro b f s φ ρ hφ
  let P i a := Formula.satisfies ((ρ.map (projection_m ℳ h i).map).pushBound a) φ
  obtain ⟨d⟩ := h s
  have he (i : I) : ∃ a, (∃ b, P i b) → P i a := by
    rcases Classical.em (∃ a, P i a) with hi | hi
    · obtain ⟨a, ha⟩ := hi
      exact ⟨a, fun _ => ha⟩
    · exact ⟨d i, fun ha => False.elim (hi ha)⟩
  obtain ⟨a, ha⟩ := hC s (fun i a => (∃ b, P i b) → P i a) he
  exact ⟨a, U.upward hφ (fun i hi => ha i hi)⟩

theorem los_m (h : Nonempty_m ℳ) (hU : U.IsUltrafilter) (hW : Witness_m ℳ U h)
    {b f} (φ : Formula σ b f) (ρ : Env (product_m ℳ h) b f) :
    Formula.satisfies (ρ.map (quotient_m ℳ U h).map) φ ↔
      U.sets (fun i => Formula.satisfies (ρ.map (projection_m ℳ h i).map) φ) := by
  induction φ with
  | falsum => exact (U.const_iff_l hU.1 False).symm
  | truth => exact (U.const_iff_l hU.1 True).symm
  | rel r ts =>
      change (structure_m ℳ U h).relInterp r _ ↔ _
      rw [← (quotient_m ℳ U h).arguments_eval_eq]
      exact (relation_class_m ℳ U h r (ts.eval ρ)).trans
        (U.pointwise_l (fun i => by rw [(projection_m ℳ h i).arguments_eval_eq]; rfl))
  | equal t t' =>
      change t.eval _ = t'.eval _ ↔ _
      rw [← (quotient_m ℳ U h).term_eval_eq, ← (quotient_m ℳ U h).term_eval_eq]
      exact (Germ_l.class_eq_l U (t.eval ρ) (t'.eval ρ)).trans
        (U.pointwise_l (fun i => by
          change (projection_m ℳ h i).map _ _ = (projection_m ℳ h i).map _ _ ↔ _
          rw [(projection_m ℳ h i).term_eval_eq, (projection_m ℳ h i).term_eval_eq]
          rfl))
  | neg φ ih => exact (not_congr (ih _)).trans (U.neg_iff_l hU _).symm
  | conj φ ψ ih jh => exact (and_congr (ih _) (jh _)).trans (U.and_iff_l _ _).symm
  | disj φ ψ ih jh => exact (or_congr (ih _) (jh _)).trans (U.or_iff_l hU _ _).symm
  | imp φ ψ ih jh => exact (imp_congr (ih _) (jh _)).trans (U.imp_iff_l hU _ _).symm
  | iff φ ψ ih jh => exact (iff_congr (ih _) (jh _)).trans (U.iff_iff_l hU _ _).symm
  | existsE s φ ih =>
      have k (a : (i : I) → (ℳ i).Carrier s) :
          Formula.satisfies ((ρ.map (quotient_m ℳ U h).map).pushBound (Germ_l.class_l U a)) φ ↔
            U.sets (fun i => Formula.satisfies
              ((ρ.map (projection_m ℳ h i).map).pushBound (a i)) φ) := by
        simpa only [Env.map_pushBound] using! ih (ρ.pushBound a)
      constructor
      · rintro ⟨a, ha⟩
        revert ha
        refine Germ_l.induction_l U (A := fun i => (ℳ i).Carrier s)
          (P := fun a => Formula.satisfies ((ρ.map (quotient_m ℳ U h).map).pushBound a) φ →
            U.sets (fun i => Formula.satisfies (ρ.map (projection_m ℳ h i).map) (.existsE s φ))) a ?_
        intro a ha
        exact U.upward ((k a).mp ha) (fun i hi => ⟨a i, hi⟩)
      · intro hφ
        obtain ⟨a, ha⟩ := hW φ ρ hφ
        exact ⟨Germ_l.class_l U a, (k a).mpr ha⟩
  | forallE s φ ih =>
      have k (a : (i : I) → (ℳ i).Carrier s) :
          Formula.satisfies ((ρ.map (quotient_m ℳ U h).map).pushBound (Germ_l.class_l U a)) φ ↔
            U.sets (fun i => Formula.satisfies
              ((ρ.map (projection_m ℳ h i).map).pushBound (a i)) φ) := by
        simpa only [Env.map_pushBound] using! ih (ρ.pushBound a)
      constructor
      · intro hφ
        apply Classical.byContradiction
        intro hn
        have hn := (U.neg_iff_l hU _).mpr hn
        have he := U.upward hn (fun _ hi => Classical.not_forall.mp hi)
        obtain ⟨a, ha⟩ := hW (.neg φ) ρ he
        exact (U.neg_iff_l hU _).mp ha ((k a).mp (hφ (Germ_l.class_l U a)))
      · intro hφ a
        refine Germ_l.induction_l U (A := fun i => (ℳ i).Carrier s)
          (P := fun a => Formula.satisfies ((ρ.map (quotient_m ℳ U h).map).pushBound a) φ) a ?_
        intro a
        exact (k a).mpr (U.upward hφ (fun i hi => hi (a i)))

/-- 见证拼接恰好是完整 Łoś 所需条件，不只是一个方便但过强的充分假设。 -/
theorem los_iff_witness_m (h : Nonempty_m ℳ) (hU : U.IsUltrafilter) :
    (∀ {b f} (φ : Formula σ b f) (ρ : Env (product_m ℳ h) b f),
      Formula.satisfies (ρ.map (quotient_m ℳ U h).map) φ ↔
        U.sets (fun i => Formula.satisfies (ρ.map (projection_m ℳ h i).map) φ)) ↔
      Witness_m ℳ U h := by
  refine ⟨?_, fun hW => los_m ℳ U h hU hW⟩
  intro hL b f s φ ρ hφ
  obtain ⟨a, ha⟩ := (hL (.existsE s φ) ρ).mpr hφ
  revert ha
  refine Germ_l.induction_l U (A := fun i => (ℳ i).Carrier s)
    (P := fun a => Formula.satisfies ((ρ.map (quotient_m ℳ U h).map).pushBound a) φ →
      ∃ c : (i : I) → (ℳ i).Carrier s, U.sets (fun i =>
        Formula.satisfies ((ρ.map (projection_m ℳ h i).map).pushBound (c i)) φ)) a ?_
  intro a ha
  refine ⟨a, ?_⟩
  have k := (hL φ (ρ.pushBound a)).mp (by simpa only [Env.map_pushBound] using! ha)
  simpa only [Env.map_pushBound] using! k

/-- 若大集上的每个因子满足理论，则超积满足该理论；不要求理论可数。 -/
theorem models_m (h : Nonempty_m ℳ) (hU : U.IsUltrafilter) (hW : Witness_m ℳ U h)
    (T : Theory σ) (hT : ∀ φ, T φ → U.sets (fun i => φ.TrueIn (ℳ i))) :
    Theory.Models (structure_m ℳ U h) T := by
  intro φ hφ
  have k := (los_m ℳ U h hU hW φ Env.empty).mpr
  simpa only [Env.map_empty, Formula.TrueIn] using!
    k (by simpa only [Env.map_empty, Formula.TrueIn] using hT φ hφ)

end YesMetaZFC.Logic.FirstOrder.ReducedProduct
