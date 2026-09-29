import YesMetaZFC.Model.Forcing.GroundTransfer
import YesMetaZFC.SetTheory.PartialFunctionCCC

/-! # 内部可数链条件与有限部分函数实例

反链只量化模型内集合，条件的相容性由实际内部非零共同加强定义。
有限部分函数的可数链条件对任意源集成立；没有外部有限性或外部可数性假设。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable (M : SetTheory.Structure.{u})

def Cmp_d (B R z p q : M.Domain) : Prop :=
  ∃ r, Below_d M B R z r p ∧ Entry_d M r q R

def Antichain_d (B R z A : M.Domain) : Prop :=
  (∀ p, M.mem p A → M.mem p B ∧ p ≠ z) ∧
    ∀ p q, M.mem p A → M.mem q A → Cmp_d M B R z p q → p = q

def Ccc_d {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (ω B R z : M.Domain) : Prop :=
  ∀ A, Antichain_d M B R z A → M.CardinalLessOrEqual I A ω

/-- 参数化有限部分函数偏序及其可数链条件由原 ZFC 自动装配。 -/
theorem fn_order_ccc_l (hZFC : M.Models ZFC) {ω Y} (hω : M.IsOmega ω)
    (hY : M.CardinalLessOrEqual (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) Y ω) (X : M.Domain) : ∃ B R,
    (∀ p, M.mem p B ↔ Fn_d (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω X Y p) ∧
    (∀ p q, Entry_d M p q R ↔ M.mem p B ∧ M.mem q B ∧ M.MemberSubset q p) ∧
    Cond_order_d M B R B ∧ Ccc_d M (kpair_interpretation_l M hZFC.1
      (KP.exists_pair (ZF.modelsKP (ZFC.models_zf_l hZFC)))) ω B R B := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  obtain ⟨B, hB⟩ := ZF.fn_set_l I hZF ω X Y
  obtain ⟨R, hR, O⟩ := subset_order_l M hZF B
  refine ⟨B, R, hB, hR, O, fun A hA => ?_⟩
  apply ZFC.fn_ccc_l I hZFC hω hY (fun p hp => (hB p).mp (hA.1 p hp).1)
  intro p q hp hq hpq
  obtain ⟨r, hr, hrp, hrq⟩ := ZF.fn_union_l I hZF hω
    ((hB p).mp (hA.1 p hp).1) ((hB q).mp (hA.1 q hq).1) hpq
  have hrB := (hB r).mpr hr
  exact hA.2 p q hp hq ⟨r,
    ⟨hrB, fun he => KP.mem_irrefl_d (ZF.modelsKP hZF) B (he ▸ hrB),
      (hR r p).mpr ⟨hrB, (hA.1 p hp).1, hrp⟩⟩,
    (hR r q).mpr ⟨hrB, (hA.1 q hq).1, hrq⟩⟩

end YesMetaZFC.Model.Forcing.Internal
