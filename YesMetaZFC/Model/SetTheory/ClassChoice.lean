import YesMetaZFC.Model.SetTheory.LevyReflection.Closure
import YesMetaZFC.SetTheory.IndexedChoice
import YesMetaZFC.SetTheory.Card.FiniteParameters

/-! # 可定义类上的内部带指标依赖选择

反射的见证闭包先给出包含参数与初值的实际累积层，再在该集合上应用选择。
有效性由原公式的内部 ω 归纳保持；名称无需预先给定秩界，ω 无需外部标准。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

/-- 类状态与转移均由原公式给出；只在构造出的集合层内使用对象选择公理。 -/
theorem ZFC.class_indexed_choice_l (hZFC : M.Models ZFC) {n}
    (V : BinarySchema n) (φ : UnarySchema (n+2)) (ρ : Env M n)
    {ω o a} (hω : M.IsOmega ω) (ho : ∀ x, ¬ M.mem x o) (ha : V.denote ρ o a)
    (ht : ∀ i j x, M.mem i ω → M.SuccessorOf j i → V.denote ρ i x →
      ∃ y, V.denote ρ j y ∧ φ.denote ((ρ.push i).push x) y) :
    ∃ X F, M.IsSetFunctionFromTo I F ω X ∧ M.PairMember I o a F ∧
      (∀ i x, M.PairMember I i x F → V.denote ρ i x) ∧
      ∀ i j x y, M.SuccessorOf j i → M.PairMember I i x F → M.PairMember I j y F →
        φ.denote ((ρ.push i).push x) y := by
  classical
  have hZF := ZFC.models_zf_l hZFC
  -- 一步见证同时携带下一个指标的有效性，故反射闭包保存真正的递归不变量。
  let e : Fin n → Term (n+4) := fun i => .bound ⟨i.val+4, by omega⟩
  let ψ : UnarySchema (n+2) := {
    body := .conj (.existsE (.conj (Formula.isSuccessor .newest (.bound 3))
      (binary_pred_m V e .newest (.bound 1)))) φ.body
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e, φ.freeClosed] }
  have hψ i x y : ψ.denote ((ρ.push i).push x) y ↔
      (∃ j, M.SuccessorOf j i ∧ V.denote ρ j y) ∧ φ.denote ((ρ.push i).push x) y := by
    simp only [UnarySchema.denote, ψ, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
      Formula.satisfies_isSuccessor_iff, binary_pred_sat_l]
    rfl
  let t : Fin (n+2) → M.Domain := Fin.cases a (Fin.cases ω ρ.bound)
  obtain ⟨A, _, h⟩ := ZF.finite_params_l I hZF hω t
  have hA i : M.mem (t i) A := (h _).mpr ⟨i, rfl⟩
  obtain ⟨α, X, hX, hAX, hc⟩ := ZF.lr_closed_layer_l I hZF hω [⟨n+2, ψ⟩] A
  have htr := ZF.v_transitive_l I hZF hX
  have haX : M.mem a X := htr A hAX a (hA 0)
  have hωX : M.mem ω X := htr A hAX ω (hA 1)
  have hρX i : M.mem (ρ.bound i) X := htr A hAX _ (hA i.succ.succ)
  have step i x (hi : M.mem i ω) (hx : M.mem x X) (hv : V.denote ρ i x) :
      ∃ y, M.mem y X ∧ ψ.denote ((ρ.push i).push x) y := by
    obtain ⟨j, hj, _⟩ := hω.1.2 i hi
    obtain ⟨y, hy, hxy⟩ := ht i j x hi hj hv
    exact hc ⟨n+2, ψ⟩ (by simp) ((ρ.push i).push x)
      (Fin.cases hx (Fin.cases (htr ω hωX i hi) hρX)) ⟨y, (hψ i x y).mpr ⟨⟨j, hj, hy⟩, hxy⟩⟩
  -- 对层中无效对象作常值延拓；下方内部归纳证明实际路径绝不进入此分支。
  let f : Fin (n+2) → Term (n+4) := Fin.cases (.bound 1) (Fin.cases (.bound 2) e)
  have hfc : ∀ i, (f i).freeSupport = [] := Fin.cases rfl (Fin.cases rfl (fun _ => rfl))
  let θ : UnarySchema (n+3) := {
    body := .disj (.conj (binary_pred_m V e (.bound 2) (.bound 1)) (pred_m ψ f .newest))
      (.conj (.neg (binary_pred_m V e (.bound 2) (.bound 1))) (Formula.extensionalEq .newest (.bound 3)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, e, hfc] }
  have hθ i x y : θ.denote (((ρ.push a).push i).push x) y ↔
      (V.denote ρ i x ∧ ψ.denote ((ρ.push i).push x) y) ∨ (¬ V.denote ρ i x ∧ y = a) := by
    have he : (⟨fun k => (f k).eval ((((ρ.push a).push i).push x).push y),
        ((((ρ.push a).push i).push x).push y).free⟩ : Env M (n+2)) =
        (ρ.push i).push x := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))), rfl⟩
    simp only [UnarySchema.denote, θ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, binary_pred_sat_l, pred_sat_l]
    rw [he]
    rfl
  obtain ⟨F, hF, hz, hf⟩ := ZFC.indexed_choice_l I hZFC θ (ρ.push a) hω haX (by
    intro i x hi hx
    by_cases hv : V.denote ρ i x
    · obtain ⟨y, hy, hxy⟩ := step i x hi hx hv
      exact ⟨y, hy, (hθ i x y).mpr (Or.inl ⟨hv, hxy⟩)⟩
    · exact ⟨a, haX, (hθ i x a).mpr (Or.inr ⟨hv, rfl⟩)⟩)
  have valid : ∀ i, M.mem i ω → ∀ x, M.PairMember I i x F → V.denote ρ i x := by
    apply hω.induction (fun i => ∀ x, M.PairMember I i x F → V.denote ρ i x)
    · let t : Fin n → Term (n+3) := fun i => .bound ⟨i.val+3, by omega⟩
      let η : UnarySchema (n+1) := {
        body := .forallE (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 2))
          (binary_pred_m V t (.bound 1) .newest))
        freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, t] }
      obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF η (ρ.push F) ω
      refine ⟨C, fun i => (hC i).trans (and_congr_right fun _ => ?_)⟩
      simp only [η, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
        Formula.satisfies_orderedPairMem_iff I, binary_pred_sat_l]
      rfl
    · intro z hz' x hzx
      have he := hZF.1.eq_of_same_members z o (fun t => iff_of_false (hz' t) (ho t))
      have hx := hF.1.2 z x a hzx (hz z hz')
      exact hx.symm ▸ he.symm ▸ ha
    · intro i hi ih j hj y hjy
      obtain ⟨x, _, hix⟩ := hF.2.2 i hi
      have hv := ih x hix
      rcases (hθ i x y).mp (hf i j x y hj hix hjy) with h | h
      · obtain ⟨⟨k, hk, hy⟩, _⟩ := (hψ i x y).mp h.2
        exact hZF.1.eq_of_same_members k j (fun t => (hk t).trans (hj t).symm) ▸ hy
      · exact (h.1 hv).elim
  refine ⟨X, F, hF, hz o ho, fun i x hi => valid i (hF.input_mem_of_pairMember hi) x hi, ?_⟩
  intro i j x y hj hix hjy
  rcases (hθ i x y).mp (hf i j x y hj hix hjy) with h | h
  · exact ((hψ i x y).mp h.2).2
  · exact (h.1 (valid i (hF.input_mem_of_pairMember hix) x hix)).elim

end YesMetaZFC.SetTheory
