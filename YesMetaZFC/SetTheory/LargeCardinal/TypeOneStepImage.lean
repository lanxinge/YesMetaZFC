import YesMetaZFC.SetTheory.LargeCardinal.TypeOneStep
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderCriticalPoint
import YesMetaZFC.Model.SetTheory.Internal.SubtypeReboundImage

/-! # 一步伸展中的实际像子类型

读取伸展证书中的同一超幂，不另选嵌入。原投影查询先进入类型集合的像，
随后统一更换上域参数为实际 j(κ)；支撑界保证候选域严格低于 j(κ)。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ee_one_step_d.image_l {ω κ δ n u τ m w b a z B U D η A c₀ R₀ r : M.Domain}
    {σ : Fin 7 → M.Domain} {q : Ee_queries_d M}
    (hω : M.IsOmega ω) (hδ : M.IsLimitOrdinal δ)
    (prog : Ts_program_d hZF ω n b σ a z) (language : Ee_language_d hZF ω κ n B U D q)
    (hA : V_d I η A) (model : Smem_d I c₀ A R₀) (type : Tt_realized_d I ω c₀ A R₀ n r δ U D u)
    (hτ : M.IsLimitOrdinal τ) (hmm : M.mem m ω)
    (step : Ee_one_step_d hZF ω κ δ n u τ m w b σ z) :
    ∃ X K R L F c d Y S j κ' U' D' u', V_d I δ X ∧ Ep_source_d hZF ω κ K X R ∧
      M.mem L δ ∧ M.mem κ L ∧ M.mem τ L ∧ It_local_d ω X κ L F ∧ Sc_inaccessible_d ω X L ∧
      Ex_strength_d hZF ω κ L X F ∧ Smem_d I c X R ∧ Smem_d I d Y S ∧ It_ultra_d hZF ω κ L F c d j ∧
      Wd_crit_d I X j κ κ' ∧ M.MemberSubset L κ' ∧ M.IsLimitOrdinal κ' ∧
      Rd_entry_d U U' j ∧ Rd_entry_d D D' j ∧ Rd_entry_d u u' j ∧ Tt_pool_d I ω n U' D' ∧
      Ts_subtype_d ω n κ' τ m U' w b σ z u' := by
  obtain ⟨ℓ, X, K, R, L, F, C, V, Q, v, _, hℓ, hτℓ, _, hX, source, hLδ, hκL, hℓL,
    loc, inacc, strength, _, _, _, stretch, subtype⟩ := step
  obtain ⟨c, d, Y, S, j, u', mx, my, ultra, huu, cut⟩ := stretch
  have hj := ultra.elementary_l hZF mx.1 my.1
  have hY := ultra.transitive_l hZF my.1
  have theory := source.theory.map_l I hZF hω source.transitive hY mx my hj
  have hκδ := hδ.1.transitive L hLδ κ hκL
  have hUX := tt_constants_rank_l hZF hX hδ hκδ language.rank language.constants
  have hDX := language.pool.rank_mem_l hZF hω hX hδ source.omega_mem prog.finite hUX
  obtain ⟨κ', _, hκj⟩ := hj.1.1.2.2 κ source.cardinal_mem
  obtain ⟨U', _, hU⟩ := hj.1.1.2.2 U hUX
  obtain ⟨D', _, hD⟩ := hj.1.1.2.2 D hDX
  have κlimit := (hj.limit_l hZF hω source.transitive hY mx my hκj).mp language.limit
  have hκU := (hj.member_l I hZF hω mx my hκj hU).mp ((language.constants κ).mpr (Or.inr rfl))
  obtain ⟨P, hP, power⟩ := sc_v_power_l hZF hδ hX K source.finite_mem
  have family := loc.measures_l hZF source.omega (source.read_source_l hZF) source.code source.theory
    (sf_finite_power_l hZF source.omega source.transitive source.code source.theory source.finite hP power)
  have ord := loc.ordinals_l (ZF.modelsKP hZF) source.transitive
  have below : M.MemberSubset ω L := fun i hi => ord.2.transitive κ hκL i (source.below i hi)
  have bound := ultra.support_l hZF source family (loc.coherent_l hZF (source.read_source_l hZF)) (loc.atoms_l hZF (source.read_source_l hZF))
    (loc.normal_l hZF (source.read_source_l hZF)) ord.1 ord.2 below mx my hκj
  have critical := ultra.critical_l hZF source family source (fun _ _ _ _ _ _ => Iff.rfl) loc hκL mx my hκj
  have hτL := ord.2.transitive ℓ hℓL τ hτℓ
  have sub : Ts_subtype_d ω n ℓ τ m V w b σ z u' := by
    obtain ⟨ht, nm, q₀, code, hq⟩ := subtype
    exact ⟨ht, nm, q₀, code, ((cut q₀).mp hq).2⟩
  have nat k (hk : M.mem k ω) := (tt_constants_finite_l hZF hω hk language.limit language.rank language.constants).2
  have hwU := (tt_constants_finite_l hZF hω prog.finite language.limit language.rank language.constants).1
  have image := hj.subtype_rebound_l hZF hω hX hδ source.omega_mem hY mx my theory prog hUX hU hD huu
    hA model type hwU nat hℓ κlimit hτ (bound τ hτL) hκU hmm sub
  obtain ⟨N, E, N', E', _, _, _, _, _, names, seq, product⟩ :=
    hj.type_full_l hZF hω hX hδ source.omega_mem hY mx my theory prog.finite hUX hU hD type.pool
  exact ⟨X, K, R, L, F, c, d, Y, S, j, κ', U', D', u', hX, source, hLδ, hκL, hτL,
    loc, inacc, strength, mx, my, ultra, critical, bound, κlimit, hU, hD, huu, ⟨N', E', names, seq, product⟩, image⟩

end YesMetaZFC.SetTheory.LargeCardinal
