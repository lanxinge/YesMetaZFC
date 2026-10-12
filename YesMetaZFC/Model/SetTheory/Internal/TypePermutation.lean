import YesMetaZFC.Model.SetTheory.Internal.FlatTypeNames
import YesMetaZFC.Model.SetTheory.Internal.TransitiveFunctionFormula
import YesMetaZFC.SetTheory.FlatPairing.RankObjects

/-! # 原类型元组的有限排列

排列图保留原 Kuratowski 编码，元组采用平坦图。矩阵只在给定有限定义域及
对象域上比较坐标；从实际排列与实际赋值直接构造排列后的元组。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tp_perm_d (K : FlatPairing.convention.Interpretation M) (m A π g h : M.Domain) : Prop :=
  ∀ i, M.mem i m → ∀ x, M.mem x A →
    (M.PairMember K i x h ↔ ∃ j, M.mem j m ∧ Rd_entry_d i j π ∧ M.PairMember K j x g)

def tp_perm0_m {d} (ω m A π g h : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜m⌝ₛ, ∀ x ∈ ⌜A⌝ₛ,
  ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, i, x, ⌜h⌝ₛ) ↔
    (∃ j ∈ ⌜m⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, j, ⌜π⌝ₛ) ∧ ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, j, x, ⌜g⌝ₛ))⟫
derive_free_closed tp_perm0_m

theorem tp_perm0_delta_l {d} (ω m A π g h : Term d) : (tp_perm0_m ω m A π g h).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (fp_entry0_delta_l ..) (.existsMem _ (.conj (rd_entry0_delta_l ..) (fp_entry0_delta_l ..)))))

theorem tp_perm0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω m A π g h : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tp_perm0_m ω m A π g h) ↔
      Tp_perm_d (fp_interpretation_l hKPi) (m.eval ρ) (A.eval ρ) (π.eval ρ) (g.eval ρ) (h.eval ρ) := by
  have left i x := fp_entry0_sat_l hKPi ((ρ.push i).push x) ω.weaken.weaken
    (.newest : Term (d+1)).weaken .newest h.weaken.weaken (by simpa only [Definitional.Term.eval_weaken] using hω)
  have right i x j := fp_entry0_sat_l hKPi (((ρ.push i).push x).push j) ω.weaken.weaken.weaken
    .newest (.newest : Term (d+2)).weaken g.weaken.weaken.weaken (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [tp_perm0_m, Tp_perm_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff, left, right,
    rd_entry0_sat_l (KPi.models_iff_l.mp hKPi).1.1, Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

/-- 给定的有限排列产生实际元组图；构造只用 ZF，不选择任何外部序列。 -/
theorem tp_permute_l {ω m A π g : M.Domain} (hω : M.IsOmega ω) (hm : M.mem m ω)
    (hp : M.IsSetBijectionFromTo Q π m m) (hg : M.IsSetFunctionFromTo K g ω A) :
    ∃ h, M.IsSetFunctionFromTo K h m A ∧ Tp_perm_d K m A π g h := by
  let ρ : Env M 3 := ⟨Fin.cases π (Fin.cases g (fun _ => ω)), fun _ => g⟩
  let φ : BinarySchema 3 := { body := .existsE (.conj (rd_entry0_m (.bound 2) .newest (.bound 3))
    (fp_entry0_m (.bound 5) .newest (.bound 1) (.bound 4))) }
  have sat i x : φ.denote ρ i x ↔ ∃ j, Rd_entry_d i j π ∧ M.PairMember K j x g := by
    have entry j := fp_entry0_sat_l (ZF.models_kpi_l hZF) (((ρ.push i).push x).push j)
      (.bound 5) .newest (.bound 1) (.bound 4) hω
    simp only [φ, BinarySchema.denote, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, rd_entry0_sat_l hZF.1,
      entry]
    rfl
  obtain ⟨h, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF K φ ρ
    (fun i hi => by
      obtain ⟨j, hj, hij⟩ := hp.1.1.2.2 i hi
      obtain ⟨x, _, hx⟩ := hg.2.2 j (hω.transitive hZF m hm j hj)
      exact ⟨x, (sat i x).mpr ⟨j, hij, hx⟩⟩)
    (fun i _ x y hx hy => by
      obtain ⟨j, hij, hjx⟩ := (sat i x).mp hx
      obtain ⟨k, hik, hky⟩ := (sat i y).mp hy
      exact hg.1.2 j x y hjx (hp.1.1.1.2 i k j hik hij ▸ hky))
    (fun i x _ hx => by obtain ⟨j, _, hjx⟩ := (sat i x).mp hx; exact hg.output_mem_of_pairMember hjx)
  refine ⟨h, fn, fun i hi x _ => (graph i x).trans ((and_iff_right hi).trans ((sat i x).trans ?_))⟩
  exact ⟨fun ⟨j, hij, hjx⟩ => ⟨j, hp.1.1.output_mem_of_pairMember hij, hij, hjx⟩,
    fun ⟨j, _, hij, hjx⟩ => ⟨j, hij, hjx⟩⟩

/-- 自然数域上的原排列图属于 Vω，因而属于每个包含 ω 的外层。 -/
theorem tp_permutation_rank_l {ω η Y m π : M.Domain} (hω : M.IsOmega ω) (hY : V_d Q η Y)
    (hw : M.mem ω Y) (hm : M.mem m ω) (hp : M.IsSetBijectionFromTo Q π m m) : M.mem π Y := by
  obtain ⟨W, hW⟩ := ZF.v_exists_l Q hZF (hω.isOrdinal hZF)
  have hπ := ZF.v_relation_mem_l Q hZF hW (hω.isLimitOrdinal hZF) (ZF.v_ordinal_mem_l Q hZF hW hm)
    (fn0_of_function_l (ZF.modelsKP hZF) hp.1.1).1
  exact ZF.v_transitive_l Q hZF hY W
    (ZF.v_mem_l Q hZF hW hY (ZF.v_ordinal_height_l hZF hY (hω.isOrdinal hZF) hw)) π hπ

end YesMetaZFC.SetTheory.Internal
