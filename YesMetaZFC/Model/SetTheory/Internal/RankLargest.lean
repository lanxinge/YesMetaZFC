import YesMetaZFC.SetTheory.FlatPairing.CumulativeSource
import YesMetaZFC.Model.SetTheory.Internal.LargestSet

/-! # 最大序数对应的前一秩层

公式直接断言“ν 是最大序数且 X=Vν”。平坦递归历史使这条原公式
在 V(η+1) 中精确识别 Vη，η 可以是后继序数。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Sv_max_d (ν : M.Domain) : Prop :=
  M.IsOrdinal ν ∧ ∀ α, M.IsOrdinal α → M.MemberSubset α ν

def sv_max_m {d} (ν : Term d) : Formula 1 d := .conj (Formula.isOrdinal ν)
  (.forallE (.imp (Formula.isOrdinal .newest) (Formula.subset .newest ν.weaken)))
derive_free_closed sv_max_m

theorem sv_max_sat_l {d} (ρ : Env M d) (ν : Term d) :
    Formula.satisfies ρ (sv_max_m ν) ↔ Sv_max_d (ν.eval ρ) := by
  simp only [sv_max_m, Sv_max_d, Formula.satisfies_conj_iff, Formula.satisfies_isOrdinal_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  rfl

def sv_last_m {d} (X : Term d) : Formula 1 d := .existsE
  (.conj (sv_max_m .newest) (v_m FlatPairing.convention .newest X.weaken))
derive_free_closed sv_last_m

variable {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
  {ω ν μ X Y : M.Domain} (hω : M.IsOmega ω) (hV : V_d I ν X) (hW : V_d I μ Y)
  (hs : M.SuccessorOf μ ν) (hωY : M.mem ω Y)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "N" => rt_model_l Y (Nonempty.intro (Subtype.mk ω hωY))
local notation "J" => fp_rank_interpretation_l I hZF hω hW hωY
include hZF hV hW hs

theorem sv_max_rank_l (a : (N).Domain) : Sv_max_d a ↔ a.val = ν := by
  have trans := ZF.v_transitive_l I hZF hW
  have ho := v_ordinal_l I hV
  have hνY := ZF.v_ordinal_mem_l I hZF hW hs.predecessor_mem
  let v : (N).Domain := ⟨ν, hνY⟩
  have bound (b : (N).Domain) (hb : (N).IsOrdinal b) : M.MemberSubset b.val ν := by
    have hb' := (rt_ordinal_iff_l trans (Nonempty.intro (Subtype.mk ω hωY)) (ZF.modelsKP hZF) b).mp hb
    rcases (hs b.val).mp (ZF.v_ordinal_height_l hZF hW hb' b.property) with lt | eq
    · exact ho.transitive b.val lt
    · exact fun x hx => (eq x).mp hx
  constructor
  · rintro ⟨ha, greatest⟩
    have hv := greatest v (rt_ordinal_l trans (Nonempty.intro (Subtype.mk ω hωY)) v ho)
    exact hZF.1.eq_of_same_members a.val ν (fun x => ⟨bound a ha x,
      fun hx => hv ⟨x, trans ν hνY x hx⟩ hx⟩)
  · intro eq
    have av : a = v := Subtype.ext eq
    subst a
    exact ⟨rt_ordinal_l trans (Nonempty.intro (Subtype.mk ω hωY)) v ho, fun b hb x hx => bound b hb x.val hx⟩

include hω

/-- 源内公式唯一识别前一层，所有编码历史均自动回收。 -/
theorem sv_last_rank_l {d} (ρ : Env N d) (A : Term d) :
    Formula.satisfies ρ (sv_last_m A) ↔ (A.eval ρ).val = X := by
  have trans := ZF.v_transitive_l I hZF hW
  have hνY := ZF.v_ordinal_mem_l I hZF hW hs.predecessor_mem
  let v : (N).Domain := ⟨ν, hνY⟩
  simp only [sv_last_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    sv_max_sat_l, v_sat_l J (rt_model_ext_l hZF.1 trans (Nonempty.intro (Subtype.mk ω hωY))),
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  constructor
  · rintro ⟨a, greatest, layer⟩
    have eq := (sv_max_rank_l I hZF hV hW hs hωY a).mp greatest
    have same := (rt_fp_v_l I hZF hω hW hωY hV hs a (A.eval ρ)).mp layer
    exact ZF.v_unique_l Q hZF (eq ▸ same) ((v_pairing_l I Q hZF).mp hV)
  · intro eq
    exact ⟨v, (sv_max_rank_l I hZF hV hW hs hωY v).mpr rfl,
      (rt_fp_v_l I hZF hω hW hωY hV hs v (A.eval ρ)).mpr (eq.symm ▸ (v_pairing_l I Q hZF).mp hV)⟩

/-- 原七条最大集合指令与文献中的“最大序数 ν 所对应的 Vν”在秩层上完全一致。 -/
theorem sv_last_top_l {d} (ρ : Env N d) (A : Term d) :
    Formula.satisfies ρ (sv_last_m A) ↔ Sr_top_d Y (A.eval ρ).val := by
  have top := sr_top_power_l (ZF.v_successor_l I hZF hV hW hs)
  exact (sv_last_rank_l I hZF hω hV hW hs hωY ρ A).trans
    ⟨fun eq => eq.symm ▸ top, fun h => h.unique_l hZF.1 top⟩

end YesMetaZFC.SetTheory.Internal
