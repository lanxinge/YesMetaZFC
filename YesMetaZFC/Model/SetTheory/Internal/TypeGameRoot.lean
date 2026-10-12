import YesMetaZFC.Model.SetTheory.Internal.TypeSource
import YesMetaZFC.Model.SetTheory.Internal.TypeGameNodeSource

/-! # 空根的单个类型查询

唯一附加坐标条件为 ∅∈v₀。它不规定历史标签的位置；空集由外延性识别，
查询本身没有新增集合常量。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_root_query_d (I : kpair_convention_l.Interpretation M) (ω e n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ c X R r δ T S, Smem_d I c X R → M.TransitiveSet X →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d e S r → (M.mem q T ↔ M.mem e S)

def tg_root_m {d} (S : Term d) : Formula 1 d := set[d] ⟪∃ e ∈ ⌜S⌝ₛ, ∀ x ∈ e, ⊥⟫
derive_free_closed tg_root_m

theorem tg_root_delta_l {d} (S : Term d) : (tg_root_m S).IsDelta0 :=
  .existsMem _ (.forallMem _ .falsum)

theorem tg_root_sat_l (hE : Extensional M) {e : M.Domain} (he : ∀ x, ¬ M.mem x e)
    {d} (ρ : Env M d) (S : Term d) : Formula.satisfies ρ (tg_root_m S) ↔ M.mem e (S.eval ρ) := by
  simp only [tg_root_m, Formula.satisfies_existsMem_iff, Formula.satisfies_forallMem_iff,
    Formula.satisfies_falsum_iff]
  exact ⟨fun ⟨z, hz, empty⟩ => hE.eq_of_same_members z e (fun x => iff_of_false (empty x) (he x)) ▸ hz,
    fun h => ⟨e, h, he⟩⟩

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_root_query_l {ω e n U D : M.Domain} (hω : M.IsOmega ω)
    (he : ∀ x, ¬ M.mem x e) (hen : M.mem e n) (pool : Tt_pool_d I ω n U D) :
    ∃ q, Tg_root_query_d I ω e n U D q := by
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool (tg_root_m .newest)
    (tg_root_m_freeClosed _ rfl) (fun _ : Fin 1 => e) (fun _ => Or.inl hen)
  refine ⟨q, hq, fun c X R r δ T S model trans type rS => ?_⟩
  let a : (smdl_structure_l I (R := R) type.model.2.1).Domain := ⟨S, (type.tuple.bound_l rS).2⟩
  let ρ : Env (smdl_structure_l I (R := R) type.model.2.1) 1 := ⟨fun _ => a, fun _ => a⟩
  exact (read c X R r δ T type ρ (fun _ => Or.inl rS)).trans
    ((smem_delta_image_l I model trans (tg_root_delta_l .newest) ρ).trans
      (tg_root_sat_l hZF.1 he (image_env_l Subtype.val ρ) .newest))

end YesMetaZFC.SetTheory.Internal
