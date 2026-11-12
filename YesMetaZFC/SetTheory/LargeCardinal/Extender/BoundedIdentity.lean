import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawOwnedCopy
import YesMetaZFC.SetTheory.LargeCardinal.Extender.TupleValue

/-! # 原有界池中恒等代表的实际值

先在同一个原超幂中逐坐标读取支撑列，再由有界坍塌图的唯一性
识别原池节点的值。此结论随后进入所属模型的实际反射规则。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Eb_collapse_d.identity_l {ω κ K L X R F c d j N S B A Q Y e u a f : M.Domain}
    (source : Ep_source_d I ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (atoms : Ea_atoms_d ω κ L F)
    (normal : En_source_d ω κ L X F) (hκ : M.TransitiveSet κ) (hL : M.TransitiveSet L)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d I ω κ L F c d j)
    (hB : M.mem B X) (trans : M.TransitiveSet B) (collapse : Eb_collapse_d ω κ L K X B F A Q Y e)
    (hu : M.mem u A) (pair : KPair_d M u a f) (id : ∀ s x, Rd_entry_d s x f → s = x) :
    Rd_entry_d u a e := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, D, p, T, V, q, b, C, W, i, g,
    mx, nx, system, limit, model, wc, bij, he, _, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  obtain ⟨J₀, P, G, U, R₁, pool, indices, _, _, _, _, range, membership, _, edges, map, _⟩ := collapse
  have eq := hZF.1.eq_of_same_members J₀ J (fun a => (indices a).trans (system.indices a).symm)
  subst J₀
  obtain ⟨B', _, hBB⟩ := hj.1.1.2.2 B hB
  have tr := smap_delta_l I hZF source.omega source.transitive hN hm hn hj (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => B, fun _ => B⟩ ⟨fun _ => B', fun _ => B'⟩ (fun _ => hBB)
  have relation x y (hx : M.mem x B) (hy : M.mem y B) : Rd_entry_d x y R₁ ↔ Rd_entry_d x y R :=
    (rt_mem_graph_l (ZF.modelsKP hZF) membership x y).trans
      ⟨fun h => (hm.2 x y).mpr ⟨source.transitive B hB x hx, source.transitive B hB y hy, h.2.2⟩,
        fun h => ⟨hx, hy, ((hm.2 x y).mp h).2.2⟩⟩
  obtain ⟨H, hBH, hHB⟩ := (js.2 B B').mp hBB
  obtain ⟨v, a₀, E₀, f₀, D₀, _, sf, fc, hfE, pv, hvH⟩ := constants B H hBH
  have fv : Ep_repr_d q a₀ f₀ H := ⟨v, E₀, pv, hfE, hvH⟩
  have hB' := (Formula.satisfies_isTransitive_iff ..).mp (tr.mp ((Formula.satisfies_isTransitive_iff ..).mpr trans))
  -- 两张图都满足原池的同一坍塌递归，故逐节点恢复原求值图。
  obtain ⟨t, evaluation, values, _⟩ := pool.evaluation_l hZF source family system limit hB range relation edges wc bij
    (sf.function_l source.transitive) fc fv hHB hB'
  have values := (map.graph_unique_l hZF evaluation).symm ▸ values
  -- 恒等函数的每个坐标由原序数种子读取，函数外延性识别整条支撑。
  obtain ⟨n, a', D', f', hnω, haJ, fa, space, hf, ff, pu⟩ := pool.read_l (ZF.modelsKP hZF) (source.finite_l (ZF.modelsKP hZF)) hu
  obtain ⟨ea, ef⟩ := kpair_injective_l M pu pair
  subst a' f'
  have fg : Fn0_d D' D' f := ff.retarget_l (fun s x hsx => id s x hsx ▸ (ff.bound_l hsx).1)
  obtain ⟨r, fr, rs⟩ := fn0_identity_l (ZF.modelsKP hZF) n
  have comp B s (fs : Fn0_d n B s) : Cp0_d n n B r s s := ⟨fs, fun x hx => by
    obtain ⟨y, hy, hxy⟩ := fs.2.1 x hx
    exact ⟨x, hx, y, hy, (rs x x).mpr ⟨hx, rfl⟩, hxy, hxy⟩⟩
  have fixed := (ep_seed_collapse_l hZF source hκ hL family coherent atoms normal system limit wc
    (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1)).2
  obtain ⟨E, value, hEa⟩ := ep_tuple_value_l hZFC source family coherent system limit model hN hn he fixed
    haJ hnω hnω fa fr (comp L a fa) space space hf fg
    (fun s x hsx => id s x hsx ▸ comp κ s ((space s).mp (fg.bound_l hsx).1))
  exact (values u a).mpr ⟨hu, E, ⟨a, f, pair, value⟩, hEa⟩

end YesMetaZFC.SetTheory.LargeCardinal
