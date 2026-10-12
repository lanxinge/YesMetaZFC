import YesMetaZFC.Model.SetTheory.Internal.OrdinalAdditionSource
import YesMetaZFC.SetTheory.Ord.FiniteTail

/-! # 极限秩层中的有限尾长绝对性

尾段基点不超过被分解的序数，因而属于同一传递秩层；
加法历史的存在性直接复用原序数加法的秩层绝对性。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF) {η Y : M.Domain}
  (hη : M.IsLimitOrdinal η) (hY : V_d (kp_pair_l (ZF.modelsKP hZF)) η Y)
  (ny : Nonempty {x // M.mem x Y})
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
local notation "T" => ZF.v_transitive_l I hZF hY
local notation "N" => rt_model_l Y ny
local notation "J" => rt_pair_l T ny (And.left hZF) (sc_v_pair_l hZF hη hY)

theorem rt_ot_tail_l (ω n ν : (N).Domain) :
    Ot_tail_d J ω n ν ↔ Ot_tail_d I ω.val n.val ν.val := by
  have zero (a : (N).Domain) : (∀ x, ¬ (N).mem x a) ↔ ∀ x, ¬ M.mem x a.val :=
    ⟨fun h x hx => h ⟨x, T a.val a.property x hx⟩ hx, fun h x => h x.val⟩
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨a, ha, base, sum⟩
    have oa := (rt_ordinal_iff_l T ny (ZF.modelsKP hZF) a).mp ha
    exact ⟨a.val, oa, (or_congr (zero a) (rt_limit_l T ny (ZF.modelsKP hZF) a)).mp base,
      (rt_oa_l hZF hη hY ny a n ν oa).mp sum⟩
  · rintro ⟨a, ha, base, sum⟩
    have hAY : M.mem a Y := (ZF.ordinalAddition_left_eq_or_mem hZF I sum.right_isOrdinal sum).elim
      (fun eq => eq.symm ▸ ν.property) (T ν.val ν.property a)
    let a' : (N).Domain := ⟨a, hAY⟩
    exact ⟨a', (rt_ordinal_iff_l T ny (ZF.modelsKP hZF) a').mpr ha,
      (or_congr (zero a') (rt_limit_l T ny (ZF.modelsKP hZF) a')).mpr base,
      (rt_oa_l hZF hη hY ny a' n ν ha).mpr sum⟩

include hη hY in
theorem ot_tail_source_l {d} (ρ : Env (N) d) (ω n ν : Term d) :
    Formula.satisfies ρ (ot_tail_m (𝒞 := kpair_convention_l) ω n ν) ↔
      Ot_tail_d I (ω.eval ρ).val (n.eval ρ).val (ν.eval ρ).val :=
  (ot_tail_sat_l J (rt_model_ext_l hZF.1 T ny) ρ ω n ν).trans (rt_ot_tail_l hZF hη hY ny ..)

end YesMetaZFC.SetTheory.Internal
