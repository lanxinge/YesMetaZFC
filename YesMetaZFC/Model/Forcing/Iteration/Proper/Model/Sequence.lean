import YesMetaZFC.Model.Forcing.Iteration.Proper.Model.Support
import YesMetaZFC.Model.Forcing.Proper.Elementary.Cofinal
import YesMetaZFC.Model.Forcing.Proper.Master.Basic

/-! # 极限 proper 构造的实际内部指标与稠密集序列

同一个内部 ω 同时编号共尾阶段及 N 的全部稠密集。阶段取自 N∩β，且 N 中
可数支撑条件的全部非平凡坐标已落在 γ=sup(N∩β) 以下。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project SetTheory.Internal
universe u
variable {M : SetTheory.Structure.{u}}

/-- 内部可数 N 的全部稠密集可在原 ZF 中枚举；载体本身作为默认稠密集。 -/
theorem mstr_dense_sequence_l (hZF : M.Models ZF) {ω N D V}
    (hN : M.CardinalLessOrEqual (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) N ω)
    (hD : M.mem D N) (L : Cond_order_d M D V D) :
    ∃ E, M.IsSetFunctionFromTo (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) E ω N ∧
      (∀ i X, Entry_d M i X E → Dense_set_d M D V D X) ∧
      ∀ X, M.mem X N → Dense_set_d M D V D X → ∃ i, M.mem i ω ∧ Entry_d M i X E := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let ρ : Env M 2 := (⟨fun _ => D, fun _ => D⟩ : Env M 1).push V
  let φ : UnarySchema 2 := { body := dense_set_m (.bound 2) (.bound 1) (.bound 2) .newest }
  obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF φ ρ N
  have mem X : M.mem X C ↔ M.mem X N ∧ Dense_set_d M D V D X :=
    (hC X).trans (and_congr_right fun _ => dense_set_sat_l M hZF.1 _ _ _ _ _)
  have hDC : M.mem D C := (mem D).mpr ⟨hD,
    (fun p hp => ⟨hp, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) D (he ▸ hp)⟩),
    fun p hp hn => ⟨p, ⟨hp, hn, L.refl p hp⟩, hp⟩⟩
  obtain ⟨f, hf⟩ := ZF.exists_inclusionInjection hZF I (fun X hX => ((mem X).mp hX).1)
  obtain ⟨g, hg⟩ := hN
  obtain ⟨h, hh⟩ := ZF.exists_compositionInjection hZF I hf hg
  obtain ⟨E, hE, he⟩ := ZF.injection_retract_l I hZF hh (fun _ h => h) hDC
  refine ⟨E, hE.mono_target_l I (fun X hX => ((mem X).mp hX).1),
    fun _ _ hi => ((mem _).mp (hE.output_mem_of_pairMember hi)).2, fun X hXN hX => ?_⟩
  obtain ⟨i, hi, hXi⟩ := hh.1.2.2 X ((mem X).mpr ⟨hXN, hX⟩)
  exact ⟨i, hi, he X i hXi⟩

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

/-- 一次构造极限证明所需的两张内部 ω 图，并证明原 N 条件的支撑界。 -/
theorem row_model_sequence_l {ω χ H c T d N S β α D V}
    (hω : M.IsOmega ω) (hχ : M.IsRegularCardinal I χ) (hωχ : M.mem ω χ) (hH : H_d I χ H)
    (hT : ∀ x y, M.PairMember I x y T ↔ M.mem x H ∧ M.mem y H ∧ M.mem x y)
    (hSub : Ssub_d I c d H T N S) (hElem : Selem_d I ω c d)
    (hN : M.CardinalLessOrEqual I N ω) (hωN : M.mem ω N)
    (hβ : M.IsLimitOrdinal β) (hβN : M.mem β N) (hαβ : M.mem α β) (hαN : M.mem α N)
    (hD : M.mem D N) (L : Cond_order_d M D V D) :
    ∃ A γ F E, (∀ x, M.mem x A ↔ M.mem x N ∧ M.mem x β) ∧
      M.IsCofinalSubset A γ ∧ M.MemberSubset γ β ∧ M.IsSetFunctionFromTo I F ω A ∧
      M.IsCofinalNondecreasingOrdinalSequence I F ω γ ∧
      (∀ i x, Entry_d M i x F → M.mem α x) ∧ M.IsSetFunctionFromTo I E ω N ∧
      (∀ i X, Entry_d M i X E → Dense_set_d M D V D X) ∧
      (∀ X, M.mem X N → Dense_set_d M D V D X → ∃ i, M.mem i ω ∧ Entry_d M i X E) ∧
      ∀ p, M.mem p N → Row_d M β p → Row_supp_d I true ω p → Row_d M γ p := by
  obtain ⟨A, γ, F, hA, hγ, hγβ, hF, hc, hα⟩ := selem_cofinal_sequence_l I hZF hω
    (ZF.h_transitive_l I hZF hH) hT hSub hElem hN hβ hβN hαβ hαN
  obtain ⟨E, hE, hd, he⟩ := mstr_dense_sequence_l hZF hN hD L
  refine ⟨A, γ, F, E, hA, hγ, hγβ, hF, hc, hα, hE, hd, he, fun p hp hr hs => ?_⟩
  exact ⟨hr.graph, hr.functional, fun i s his => hγ.2.1 i ((hA i).mpr
    ⟨row_supp_subset_model_l hZFC hω hχ hωχ hH hT hSub hElem hωN hp hs i s his, hr.domain i s his⟩)⟩

end YesMetaZFC.Model.Forcing.Internal
