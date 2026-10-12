import YesMetaZFC.SetTheory.LargeCardinal.TypeStretchSource
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderQuality
import YesMetaZFC.Model.SetTheory.Internal.TypeDomain
import YesMetaZFC.Model.SetTheory.Internal.SourceInaccessibleUp

/-! # 原扩展器检验与完整类型伸展的合并读取

任意通过检验的候选扩展器都自动产生良基超幂。支撑的源内不可达性在
实际 Vδ 中向上读取，再构造秩层枚举；κ 型的整个查询域给出类型的秩界。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}}

def et_quality_m {d} (ω κ L X F t D v : Term d) : Formula 1 d :=
  .conj (ex_quality_m ω κ L X F) (et_stretch_m ω κ L X F t D v)
derive_free_closed et_quality_m

theorem et_quality_delta_l {d} (ω κ L X F t D v : Term d) : (et_quality_m ω κ L X F t D v).IsDelta0 :=
  .conj (ex_quality_delta_l ..) (et_stretch_delta_l ..)

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem et_quality_sat_l {d δ K R n B U Q} (ρ : Env M d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d hZF (ω.eval ρ) (κ.eval ρ) K (X.eval ρ) R)
    (hX : V_d I δ (X.eval ρ)) (hδ : M.IsLimitOrdinal δ) (hκL : M.mem (κ.eval ρ) (L.eval ρ))
    (hn : M.mem n (ω.eval ρ)) (hB : V_d I (κ.eval ρ) B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = κ.eval ρ)
    (pool : Tt_pool_d I (ω.eval ρ) n U Q) (type : M.MemberSubset (t.eval ρ) Q) :
    Formula.satisfies ρ (et_quality_m ω κ L X F t D v) ↔
      It_local_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) ∧
      Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ) ∧
      Ex_strength_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (X.eval ρ) (F.eval ρ) ∧
      Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
  have read (loc : It_local_d (ω.eval ρ) (X.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ))
      (inacc : Sc_inaccessible_d (ω.eval ρ) (X.eval ρ) (L.eval ρ)) :
      Formula.satisfies ρ (et_stretch_m ω κ L X F t D v) ↔
        Et_stretch_d hZF (ω.eval ρ) (κ.eval ρ) (L.eval ρ) (F.eval ρ) (X.eval ρ) R (t.eval ρ) (D.eval ρ) (v.eval ρ) := by
    obtain ⟨above, regular, strong⟩ := sc_v_inaccessible_up_l hZF hδ hX inacc
    have hLX : M.mem (L.eval ρ) (X.eval ρ) := by obtain ⟨_, _, h, _, _⟩ := loc; exact h
    have hLδ := ZF.v_ordinal_height_l hZF hX regular.isCardinal.1 hLX
    obtain ⟨V, hV⟩ := ZF.v_exists_l I hZF regular.isCardinal.1
    have hUV := tt_constants_rank_l hZF hV regular.isLimitOrdinal hκL hB constants
    have hQV := pool.rank_mem_l hZF source.omega hV regular.isLimitOrdinal
      (ZF.v_ordinal_mem_l I hZF hV above) hn hUV
    exact et_stretch_closed_l hZFC ρ ω κ L X F t D v source
      (sc_v_bounded_omega_closed_l hZF hδ hX source.omega_mem) (sc_v_power_l hZF hδ hX) loc regular.isLimitOrdinal
      (ep_relative_rank_l hZFC source hX hδ hLδ above regular strong hV)
      (ZF.v_ordinal_mem_l I hZF hV hκL) (ZF.v_subset_mem_l I hZF hV hQV type)
  rw [et_quality_m, Formula.satisfies_conj_iff, ex_quality_sat_l hZF ρ ω κ L X F source]
  exact ⟨fun ⟨⟨loc, inacc, strength⟩, h⟩ => ⟨loc, inacc, strength, (read loc inacc).mp h⟩,
    fun ⟨loc, inacc, strength, h⟩ => ⟨⟨loc, inacc, strength⟩, (read loc inacc).mpr h⟩⟩

theorem et_quality_source_l {T : M.Domain} (hT : M.TransitiveSet T) (nt : Nonempty {x // M.mem x T})
    {d δ K R n B U Q} (ρ : Env (rt_model_l T nt) d) (ω κ L X F t D v : Term d)
    (source : Ep_source_d hZF (ω.eval ρ).val (κ.eval ρ).val K (X.eval ρ).val R)
    (hX : V_d I δ (X.eval ρ).val) (hδ : M.IsLimitOrdinal δ) (hκL : M.mem (κ.eval ρ).val (L.eval ρ).val)
    (hn : M.mem n (ω.eval ρ).val) (hB : V_d I (κ.eval ρ).val B)
    (constants : ∀ x, M.mem x U ↔ M.mem x B ∨ x = (κ.eval ρ).val)
    (pool : Tt_pool_d I (ω.eval ρ).val n U Q) (type : M.MemberSubset (t.eval ρ).val Q) :
    Formula.satisfies ρ (et_quality_m ω κ L X F t D v) ↔
      It_local_d (ω.eval ρ).val (X.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val ∧
      Sc_inaccessible_d (ω.eval ρ).val (X.eval ρ).val (L.eval ρ).val ∧
      Ex_strength_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (X.eval ρ).val (F.eval ρ).val ∧
      Et_stretch_d hZF (ω.eval ρ).val (κ.eval ρ).val (L.eval ρ).val (F.eval ρ).val
        (X.eval ρ).val R (t.eval ρ).val (D.eval ρ).val (v.eval ρ).val := by
  have read := et_quality_sat_l hZFC (δ := δ) (K := K) (R := R) (n := n) (B := B) (U := U) (Q := Q)
    (image_env_l (M := rt_model_l T nt) (N := M) Subtype.val ρ) ω κ L X F t D v
  simp only [eval_image_env_l (M := rt_model_l T nt) (N := M) Subtype.val ρ] at read
  exact (rt_model_delta_l hT nt (et_quality_delta_l ..) ρ).trans (read source hX hδ hκL hn hB constants pool type)

end YesMetaZFC.SetTheory.LargeCardinal
