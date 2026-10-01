import YesMetaZFC.Model.Forcing.External.FormulaGeneric
import YesMetaZFC.Model.FirstOrder.Valuation
import YesMetaZFC.Model.SetTheory.CountableSyntax

/-! # 原公式及有限赋值的可数性

复用原内在语法的单射编码和异质值列。只在存在证明中取得枚举，不定义不可计算
解码器；量词真值本身与语法编码无关。本层只为一次同时满足全部公式提供调度。
-/

namespace YesMetaZFC.Model.Forcing
open Boolean Logic Logic.FirstOrder SetTheory
open Automation.SyntaxNatCoding Automation.RelationalTranslation Automation.ModelClosure
open FirstOrder.Completeness.Henkin
universe u v w

variable {B : Type v} (𝔹 : CB_alg B) (N : Name_domain_l.{u, v} B)
  (e : Nat → {G : BV_graph.{u, v} B // N.mem G})

private def values_enum_l : (ss : SortContext ℒ) → Nat →
    Values (domain_str_l 𝔹 N).Carrier ss
  | [], _ => .nil
  | _ :: ss, n => .cons (e (NatPairing.first n)) (values_enum_l ss (NatPairing.second n))

private theorem values_enum_surjective_l (he : Function.Surjective e) {ss}
    (ts : Values (domain_str_l 𝔹 N).Carrier ss) : ∃ n, values_enum_l 𝔹 N e ss n = ts := by
  induction ts with
  | nil => exact ⟨0, rfl⟩
  | cons a ts ih =>
    obtain ⟨i, rfl⟩ := he a
    obtain ⟨j, hj⟩ := ih
    exact ⟨NatPairing.pair i j, by simp only [values_enum_l, NatPairing.first_pair,
      NatPairing.second_pair, hj]⟩

private def env_enum_l (b f : SortContext ℒ) (n : Nat) :
    (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f where
  boundVal := valuesAssignment (values_enum_l 𝔹 N e b (NatPairing.first n))
  freeVal := valuesAssignment (values_enum_l 𝔹 N e f (NatPairing.second n))

private theorem env_enum_surjective_l (he : Function.Surjective e) {b f}
    (ρ : (domain_str_l 𝔹 N).Env 𝔹.toBA_alg b f) : ∃ n, env_enum_l 𝔹 N e b f n = ρ := by
  obtain ⟨i, hi⟩ := values_enum_surjective_l 𝔹 N e he (valuesOfAssignment ρ.boundVal)
  obtain ⟨j, hj⟩ := values_enum_surjective_l 𝔹 N e he (valuesOfAssignment ρ.freeVal)
  refine ⟨NatPairing.pair i j, Env.ext ?_ ?_⟩
  · intro s k
    simp only [env_enum_l, NatPairing.first_pair, hi, assignment_values]
  · intro s k
    simp only [env_enum_l, NatPairing.second_pair, hj, assignment_values]

/-- 可数名称域上的全部有限参数公式实例可同时枚举；无需假设任何模型公理。 -/
theorem fm_query_enumeration_l (he : Function.Surjective e) :
    ∃ Q : Nat → Fm_query_l 𝔹 N, Function.Surjective Q := by
  obtain ⟨q, hq⟩ := enum_exists_l query_coding_l ⟨[], [], .truth, 0⟩
  let Q n : Fm_query_l 𝔹 N :=
    ⟨(q n).bound, (q n).free, (q n).formula, env_enum_l 𝔹 N e _ _ (q n).parameter⟩
  refine ⟨Q, ?_⟩
  rintro ⟨b, f, φ, ρ⟩
  obtain ⟨j, hj⟩ := env_enum_surjective_l 𝔹 N e he ρ
  obtain ⟨i, hi⟩ := hq ⟨b, f, φ, j⟩
  refine ⟨i, ?_⟩
  dsimp only [Q]
  rw [hi, hj]

end YesMetaZFC.Model.Forcing
