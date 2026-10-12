import YesMetaZFC.Model.SetTheory.Internal.FlatTypeNames

/-! # 用原名字列移动类型的实现元组

同一内部有限名字列可重复、置换指定点和集合常量。下面的有界矩阵生成
该列的平坦赋值；原 Kuratowski 元组仅用于证明，不改动任何类型查询码。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def tm_assign0_m {d} (ω Z A e ν E n h : Term d) : Formula 1 d := set[d] ⟪
  ∀ i ∈ ⌜n⌝ₛ, ∀ x ∈ ⌜A⌝ₛ, ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, i, x, ⌜h⌝ₛ) ↔
    (∃ a ∈ ⌜Z⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, a, ⌜E⌝ₛ) ∧ ⌜tn_value_m⌝ₚ(⌜e⌝ₛ, ⌜e⌝ₛ, ⌜ν⌝ₛ, a, x))⟫
derive_free_closed tm_assign0_m

theorem tm_assign0_delta_l {d} (ω Z A e ν E n h : Term d) :
    (tm_assign0_m ω Z A e ν E n h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (fp_entry0_delta_l ..) (.existsMem _
    (.conj (rd_entry0_delta_l ..) (.disj (rd_entry0_delta_l ..)
      (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (kpair0_delta_l ..)))))))

def Tm_assign_d (K : FlatPairing.convention.Interpretation M) (Z A e ν E n h : M.Domain) : Prop :=
  ∀ i, M.mem i n → ∀ x, M.mem x A → (M.PairMember K i x h ↔
    ∃ a, M.mem a Z ∧ Rd_entry_d i a E ∧ Tn_value_d e e ν a x)

theorem tm_assign0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω Z A e ν E n h : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tm_assign0_m ω Z A e ν E n h) ↔
      Tm_assign_d (fp_interpretation_l hKPi) (Z.eval ρ) (A.eval ρ) (e.eval ρ) (ν.eval ρ)
        (E.eval ρ) (n.eval ρ) (h.eval ρ) := by
  have entry i x := fp_entry0_sat_l hKPi ((ρ.push i).push x) ω.weaken.weaken
    (.newest : Term (d+1)).weaken .newest h.weaken.weaken
    (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [tm_assign0_m, Tm_assign_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, entry,
    rd_entry0_sat_l (KPi.models_iff_l.mp hKPi).1.1, tn_value_sat_l (KPi.models_iff_l.mp hKPi).1.1,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem tm_assign_iff_l {Z A e ν E n h s : M.Domain} (names : Fn0_d n Z E)
    (assign : Tn_assign_d e e ν E s) (tuple : Fn0_d n A s) (flat : M.IsSetFunctionFromTo K h n A) :
    Tm_assign_d K Z A e ν E n h ↔ Sx_graph_d Q K s h := by
  have fn := fn0_function_l (ZF.modelsKP hZF) tuple
  have read i x : (∃ a, M.mem a Z ∧ Rd_entry_d i a E ∧ Tn_value_d e e ν a x) ↔ Rd_entry_d i x s :=
    ⟨fun ⟨a, _, ha, hx⟩ => (assign.2 i x).mpr ⟨a, ha, hx⟩,
      fun hx => by
        obtain ⟨a, ha, hx⟩ := (assign.2 i x).mp hx
        exact ⟨a, (fn0_function_l (ZF.modelsKP hZF) names).output_mem_of_pairMember ha, ha, hx⟩⟩
  constructor
  · intro matrix i x
    by_cases hi : M.mem i n
    · by_cases hx : M.mem x A
      · exact (matrix i hi x hx).trans (read i x)
      · exact iff_of_false (fun h => hx (flat.output_mem_of_pairMember h)) (fun h => hx (fn.output_mem_of_pairMember h))
    · exact iff_of_false (fun h => hi (flat.input_mem_of_pairMember h)) (fun h => hi (fn.input_mem_of_pairMember h))
  · exact fun agree i _ x _ => (agree i x).trans (read i x).symm

end YesMetaZFC.SetTheory.Internal
