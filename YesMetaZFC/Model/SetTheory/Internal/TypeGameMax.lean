import YesMetaZFC.Model.SetTheory.Internal.TypeSource
import YesMetaZFC.Model.SetTheory.Internal.RankLargest
import YesMetaZFC.Model.SetTheory.Internal.Sigma1Substructure

/-! # 末位最大序数查询准确固定实现高度

不预设见证秩层是后继层。原公式的真值本身推出层高为末位序数加一。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def Tg_max_query_d (I : kpair_convention_l.Interpretation M) (ω l n U D q : M.Domain) : Prop :=
  M.mem q D ∧ ∀ ν X c R r δ T α, V_d I ν X → Smem_d I c X R →
    Tt_realized_d I ω c X R n r δ U D T → Rd_entry_d l α r → (M.mem q T ↔ M.SuccessorOf ν α)

variable (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem tt_max_query_l {ω l n U D : M.Domain} (hω : M.IsOmega ω)
    (hl : M.mem l n) (pool : Tt_pool_d I ω n U D) : ∃ q, Tg_max_query_d I ω l n U D q := by
  obtain ⟨q, hq, read⟩ := tt_fixed_query_l hZF hω pool (sv_max_m .newest)
    (sv_max_m_freeClosed _ rfl) (fun _ : Fin 1 => l) (fun _ => Or.inl hl)
  refine ⟨q, hq, fun ν X c R r δ T α hX model type rα => ?_⟩
  let nx : Nonempty {x // M.mem x X} := ⟨⟨α, (type.tuple.bound_l rα).2⟩⟩
  let a : (rt_model_l X nx).Domain := ⟨α, (type.tuple.bound_l rα).2⟩
  let ρ : Env (rt_model_l X nx) 1 := ⟨fun _ => a, fun _ => a⟩
  let η : Env (smdl_structure_l I (R := R) type.model.2.1) 1 := ⟨ρ.bound, ρ.free⟩
  have ht := ZF.v_transitive_l I hZF hX
  have first := (read c X R r δ T type η (fun _ => Or.inl rα)).trans
    ((smem_formula_l I model nx (sv_max_m .newest) ρ).symm.trans (sv_max_sat_l ρ .newest))
  refine first.trans ⟨sv_max_successor_l hZF hX nx a, ?_⟩
  intro hs
  have hα := (v_ordinal_l I hX).mem hs.predecessor_mem
  refine ⟨rt_ordinal_l ht nx a hα, fun b hb x hx => ?_⟩
  have ob := (rt_ordinal_iff_l ht nx (ZF.modelsKP hZF) b).mp hb
  rcases (hs b.val).mp (ZF.v_ordinal_height_l hZF hX ob b.property) with lt | eq
  · exact hα.transitive b.val lt x.val hx
  · exact (eq x.val).mp hx

end YesMetaZFC.SetTheory.Internal
