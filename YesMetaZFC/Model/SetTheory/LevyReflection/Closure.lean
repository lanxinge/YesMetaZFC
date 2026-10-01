import YesMetaZFC.Model.SetTheory.LevyReflection.Chain
import YesMetaZFC.SetTheory.CumulativeUnion
import YesMetaZFC.SetTheory.CountableChain

/-! # 有限反射族在任意高累积层中的见证闭包

实际内部 ω 链的并仍是一层 V。有限参数由已有的内部有限序列截取定理归入
同一阶段，下一阶段便提供见证；这一步不使用外部枚举模型对象。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project Internal
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

theorem lr_params_bound_l (hZF : M.Models ZF) {ω P Q X} (hω : M.IsOmega ω)
    (hQ : M.IsSetFunctionFromTo I Q ω P) (hm : Cc_increasing_d I Q) (hu : Cc_union_d I Q X)
    (hX : ∃ x, M.mem x X) {n} (v : Fin n → M.Domain) (hv : ∀ i, M.mem (v i) X) :
    ∃ j Y, M.PairMember I j Y Q ∧ ∀ i, M.mem (v i) Y := by
  obtain ⟨k, hk⟩ := Classical.axiomOfChoice (fun i : Fin n => num_exists_l (ZF.modelsKP hZF) i.val)
  obtain ⟨d, hd⟩ := num_exists_l (ZF.modelsKP hZF) n
  have hinj : Function.Injective k := fun i j hij => Fin.ext
    (num_injective_l (ZF.modelsKP hZF) (hk i) (hij.symm ▸ hk j))
  obtain ⟨E, hE⟩ := ZF.exists_functionSpace hZF I ω X
  obtain ⟨f, hf, he⟩ := senv_params_l I hZF hE hX k v hinj (fun i => num_mem_l hZF.1 hω (hk i)) hv
  obtain ⟨g, hg⟩ := ZF.exists_restriction hZF I f d
  have hdω := num_mem_l hZF.1 hω hd
  have hgX := hg.isSetFunctionFromTo ((hE f).mp hf) (hω.transitive hZF d hdω)
  obtain ⟨j, Y, hj, hy⟩ := ZF.cc_fseq_bound_l I hZF hω hQ hm hu hdω hgX
  exact ⟨j, Y, hj, fun i => hy.output_mem_of_pairMember
    ((hg.2 (k i) (v i)).mpr ⟨num_lt_l hZF.1 (hk i) hd i.isLt, he i⟩)⟩

/-- 任意有限见证族都有任意高的实际 V 层，对其中全部参数统一闭合。 -/
theorem ZF.lr_closed_layer_l (hZF : M.Models ZF) {ω} (hω : M.IsOmega ω)
    (Φ : Lr_family) (A : M.Domain) : ∃ α X, V_d I α X ∧ M.mem A X ∧ Lr_step_d Φ X X := by
  obtain ⟨β, B, hB, hAB⟩ := v_cover_l I hZF A
  obtain ⟨P, Q, hQ, hz, hs⟩ := lr_chain_l I hZF hω Φ B
  have ascend {i j Y Z} (hij : M.SuccessorOf j i) (hi : M.PairMember I i Y Q)
      (hj : M.PairMember I j Z Q) : M.MemberSubset Y Z := by
    obtain ⟨⟨α, hZ⟩, hyZ, _⟩ := (hs i j Y Z hij hi hj).cover_l I hZF
    exact v_transitive_l I hZF hZ Y hyZ
  have inc := cc_increasing_of_successor_l I hZF hω hQ (fun _ _ _ _ => ascend)
  have layers {i Y} (hi : M.PairMember I i Y Q) : ∃ α, V_d I α Y := by
    classical
    by_cases he : ∃ j, M.mem j i
    · obtain ⟨j, hjω, hij⟩ := hω.exists_predecessor_of_mem_of_nonempty hZF (hQ.input_mem_of_pairMember hi) he
      obtain ⟨Z, _, hj⟩ := hQ.2.2 j hjω
      exact ((hs j i Z Y hij hj hi).cover_l I hZF).1
    · have h0 : ∀ x, ¬ M.mem x i := fun x hx => he ⟨x, hx⟩
      exact hQ.1.2 i B Y (hz i h0) hi ▸ ⟨β, hB⟩
  obtain ⟨C, hC⟩ := exists_range_of_setFunction hZF I hQ.1 hQ.2.1
  obtain ⟨X, hX⟩ := KP.exists_union (modelsKP hZF) C
  have hu : Cc_union_d I Q X := fun x => (hX x).trans
    ⟨fun ⟨Y, hY, hx⟩ => (hC Y).mp hY |>.elim fun i hi => ⟨i, Y, hi, hx⟩,
      fun ⟨i, Y, hi, hx⟩ => ⟨Y, (hC Y).mpr ⟨i, hi⟩, hx⟩⟩
  obtain ⟨α, hV⟩ := v_union_l I hZF hX (fun Y hY => (hC Y).mp hY |>.elim fun _ hi => layers hi)
  obtain ⟨e, he, _⟩ := hω.1.1
  have hAX := (hu A).mpr ⟨e, B, hz e he, hAB⟩
  refine ⟨α, X, hV, hAX, fun q hq ρ hρ hx => ?_⟩
  obtain ⟨i, Y, hi, hy⟩ := lr_params_bound_l I hZF hω hQ inc hu ⟨A, hAX⟩ ρ.bound hρ
  obtain ⟨j, hij, hjω⟩ := hω.1.2 i (hQ.input_mem_of_pairMember hi)
  obtain ⟨Z, _, hj⟩ := hQ.2.2 j hjω
  obtain ⟨x, hxZ, hx⟩ := ((hs i j Y Z hij hi hj).cover_l I hZF).2.2 q hq ρ hy hx
  exact ⟨x, (hu x).mpr ⟨j, Z, hj, hxZ⟩, hx⟩

end YesMetaZFC.SetTheory
