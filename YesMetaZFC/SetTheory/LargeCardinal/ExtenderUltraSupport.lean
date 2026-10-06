import YesMetaZFC.SetTheory.LargeCardinal.IterationStep
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSupportBound

/-! # 指定实际超幂的支撑界

直接读取原常值箭头与坐标代表，证明 L≤j(κ)。该界对应输入中的同一张
超幂图，供所属源强度证书在自身超幂和跨源施加时读取。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem It_ultra_d.support_l {ω κ K L X R F c d N S j Γ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (atoms : Ea_atoms_d ω κ L F) (normal : En_source_d ω κ L X F)
    (hκ : M.IsOrdinal κ) (hL : M.IsOrdinal L) (below : M.MemberSubset ω L)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d hZF ω κ L F c d j)
    (hκj : Rd_entry_d κ Γ j) : M.MemberSubset L Γ := by
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, A, p, T, V, q, b, C, W, i, e,
    mx, nx, system, limit, model, wc, bij, he, _, constants, _, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  have fixed := (ep_seed_collapse_l hZF source hκ.transitive hL.transitive below family coherent atoms normal
    system limit wc (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  obtain ⟨H, hκH, hHΓ⟩ := (js.2 κ Γ).mp hκj
  obtain ⟨u, a, E, f, D, _, sf, fc, hfE, pair, huH⟩ := constants κ H hκH
  have fv : Ep_repr_d q a f H := ⟨u, E, pair, hfE, huH⟩
  obtain ⟨hfX, n, hnω, ha, D₀, space, fn⟩ := fv.source_l hZF family system limit
  have eq := fn.domain_eq_l hZF.1 (sf.function_l source.transitive)
  subst D₀
  exact ep_value_support_l hZF source family system limit model hn he fixed (fv.index_l hZF system limit)
    hnω ha space hfX (sf.function_l source.transitive) fc ⟨H, fv, hHΓ⟩

end YesMetaZFC.SetTheory.LargeCardinal
