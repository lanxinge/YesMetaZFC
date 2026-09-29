import YesMetaZFC.Model.Forcing.Domain

/-! # 完整一阶公式的名称真值

直接使用原内在类型 AST。量词的见证稠密集取相对名称域上的布尔值族；子公式
要求递归传递到各个实际赋值，不假设扩张中的量词已有真值对应。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean Logic Logic.FirstOrder SetTheory
universe u v
variable {B : Type v} (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B)

def Fm_generic_l (U : Filter_l 𝔹.toBA_alg) : {b f : SortContext ℒ} →
    Formula ℒ b f → (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f → Prop
  | _, _, .falsum, _ | _, _, .truth, _ | _, _, .equal _ _, _ | _, _, .rel _ _, _ => True
  | _, _, .neg φ, ρ => Fm_generic_l U φ ρ
  | _, _, .conj φ ψ, ρ | _, _, .disj φ ψ, ρ | _, _, .imp φ ψ, ρ | _, _, .iff φ ψ, ρ =>
      Fm_generic_l U φ ρ ∧ Fm_generic_l U ψ ρ
  | _, _, .forallE _ φ, ρ =>
      BF_meets_l U (sup_dense_l 𝔹 (fun a => 𝔹.neg (BV_str.value 𝔹 (domain_str_l 𝔹 N) φ (ρ.pushBound a)))) ∧
      ∀ a, Fm_generic_l U φ (ρ.pushBound a)
  | _, _, .existsE _ φ, ρ =>
      BF_meets_l U (sup_dense_l 𝔹 (fun a => BV_str.value 𝔹 (domain_str_l 𝔹 N) φ (ρ.pushBound a))) ∧
      ∀ a, Fm_generic_l U φ (ρ.pushBound a)

theorem val_formula_iff_l (U : Filter_l 𝔹.toBA_alg) (hU : U.Maximal_l)
    (hN : ∀ G H, N.mem G → N.mem H → Name_generic_l 𝔹 U G H)
    {b f : SortContext ℒ} (φ : Formula ℒ b f)
    (ρ : (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f) (h : Fm_generic_l 𝔹 N U φ ρ) :
    U.mem (BV_str.value 𝔹 (domain_str_l 𝔹 N) φ ρ) ↔
      φ.satisfies (ρ.map (val_map_l 𝔹 N U.mem).map) := by
  induction φ with
  | falsum => exact ⟨hU.1, False.elim⟩
  | truth => exact ⟨fun _ => trivial, fun _ => U.top_mem⟩
  | equal t t' =>
    rw [BV_str.value_equal]
    change _ ↔ t.eval (ρ.map _) = t'.eval (ρ.map _)
    rw [← (val_map_l 𝔹 N U.mem).term_eval_eq, ← (val_map_l 𝔹 N U.mem).term_eval_eq]
    exact (ext_atomic_l 𝔹 N U hU (t.eval ρ).1 (t'.eval ρ).1 (t.eval ρ).2 (t'.eval ρ).2
      (hN _ _ (t.eval ρ).2 (t'.eval ρ).2)).1
  | rel r ts =>
    rw [BV_str.value_rel]
    change _ ↔ (ext_model_l N U.mem).relInterp r (ts.eval (ρ.map _))
    rw [← (val_map_l 𝔹 N U.mem).arguments_eval_eq]
    cases r
    cases ts.eval ρ with | cons G ts =>
      cases ts with | cons H ts =>
        cases ts
        exact val_mem_iff_l 𝔹 U hU G.1 H.1 (hN _ _ G.2 H.2)
  | neg φ ih => exact (neg_mem_iff_l U hU _).trans (not_congr (ih ρ h))
  | conj φ ψ ih jh =>
    exact (meet_mem_iff_l U _ _).trans (and_congr (ih ρ h.1) (jh ρ h.2))
  | disj φ ψ ih jh =>
    exact (join_mem_iff_l U hU _ _).trans (or_congr (ih ρ h.1) (jh ρ h.2))
  | imp φ ψ ih jh =>
    exact (imp_mem_iff_l U hU _ _).trans (imp_congr (ih ρ h.1) (jh ρ h.2))
  | iff φ ψ ih jh =>
    exact (iff_mem_iff_l U hU _ _).trans (iff_congr (ih ρ h.1) (jh ρ h.2))
  | forallE s φ ih =>
    rw [BV_str.value_all, inf_mem_iff_l 𝔹 U hU.1 _ h.1]
    constructor
    · intro k x
      obtain ⟨a, rfl⟩ := val_map_surjective_l 𝔹 N U.mem s x
      simpa only [Env.map_pushBound] using (ih (ρ.pushBound a) (h.2 a)).mp (k a)
    · intro k a
      apply (ih (ρ.pushBound a) (h.2 a)).mpr
      simpa only [Env.map_pushBound] using k ((val_map_l 𝔹 N U.mem).map s a)
  | existsE s φ ih =>
    rw [BV_str.value_ex, sup_mem_iff_l 𝔹 U hU.1 _ h.1]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(val_map_l 𝔹 N U.mem).map s a,
        by simpa only [Env.map_pushBound] using (ih (ρ.pushBound a) (h.2 a)).mp ha⟩
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := val_map_surjective_l 𝔹 N U.mem s x
      exact ⟨a, (ih (ρ.pushBound a) (h.2 a)).mpr (by simpa only [Env.map_pushBound] using hx)⟩

end YesMetaZFC.Model.Forcing
