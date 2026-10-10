import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedNodes
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEdge

/-! # 有界共同支撑关系就是原极限关系的逆像

从原直接极限的共同后继读取测度一约束；反向实际拉回两函数并使用同分量
原子方程。比较的始终是原 `Ep_repr_d` 给出的同一批商元素。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem eb_edge_iff_l {ω κ K L X R₀ R F J O Z A p T S q C W B V R' a f b g D Q E H : M.Domain}
    (source : Ep_source_d hZF ω κ K X R₀) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hB : M.MemberSubset B X) (measures : ∀ a U, Rd_entry_d a U F → M.mem U V)
    (relation : ∀ x y, M.mem x B → M.mem y B → (Rd_entry_d x y R' ↔ Rd_entry_d x y R))
    (ff : Fn0_d D B f) (gg : Fn0_d Q B g) (fv : Ep_repr_d q a f E) (gv : Ep_repr_d q b g H) :
    Eb_edge_d ω κ L B J K V R' F a f b g ↔ Rd_entry_d E H W := by
  obtain ⟨hfX, m, hm, ha, D', hd, hf⟩ := fv.source_l hZF family system limit
  obtain ⟨hgX, n, hn, hb, Q', hq, hg⟩ := gv.source_l hZF family system limit
  have ed := hf.domain_eq_l hZF.1 ff
  have eq := hg.domain_eq_l hZF.1 gg
  subst D' Q'
  constructor
  · rintro ⟨c, hcJ, U, _, hcU, P, hPU, m', _, n', _, l, hl, r, _, t, _, hr, ht, hc, hca, hcb, point⟩
    have em := hca.1.domain_eq_l hZF.1 ha
    have en := hcb.1.domain_eq_l hZF.1 hb
    subst m' n'
    obtain ⟨Y, _, hy⟩ := source.space_l hZF hl
    obtain ⟨f', _, _, pf, fv'⟩ := ep_repr_reindex_l hZF source family system limit hm hl hr hcJ hc hca hd hy hfX hf fv
    obtain ⟨g', _, _, pg, gv'⟩ := ep_repr_reindex_l hZF source family system limit hn hl ht hcJ hc hcb hq hy hgX hg gv
    have ultra := family.at_l hZF.1 hcU hc hy
    apply (ep_repr_atoms_l hZF family system limit hcU fv' gv').2.mpr
    refine ⟨P, hPU, fun s hs => ?_⟩
    obtain ⟨u, _, v, _, x, hx, y, hyB, ru, tv, ux, vy, xy⟩ := point s hs
    have sf := (hy s).mp (ultra.base.bounds P hPU s hs)
    exact ⟨x, hB x hx, y, hB y hyB,
      (pf.2.2 s u sf ru x).mpr ux, (pg.2.2 s v sf tv y).mpr vy, (relation x y hx hyB).mp xy⟩
  · intro edge
    obtain ⟨u, B₀, hu, hfB, huE⟩ := fv
    obtain ⟨v, B₁, hv, hgB, hvH⟩ := gv
    obtain ⟨c, w, z, hwc, hzc, huw, hvz, hwz⟩ := (limit.relation u v E H huE hvH).mp edge
    obtain ⟨P, U, hcU, hPU, m', n', l, r, t, f', g', hr, ht, hc, hca, hcb, pf, pg, point⟩ :=
      ee_common_edge_l hZF family system hu hv hfB hgB hwc hzc huw hvz hwz
    have em := hca.1.domain_eq_l hZF.1 ha
    have en := hcb.1.domain_eq_l hZF.1 hb
    subst m' n'
    have hcJ := (system.projection.bound_l hwc).2
    obtain ⟨l', hl, hc', _⟩ := (system.indices c).mp hcJ
    have el := hc'.domain_eq_l hZF.1 hc
    subst l'
    have rk := (source.finite r).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF)
      (hr.mono_target_l fun i hi => source.below i (source.omega.transitive hZF l hl i hi))⟩
    have tk := (source.finite t).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF)
      (ht.mono_target_l fun i hi => source.below i (source.omega.transitive hZF l hl i hi))⟩
    obtain ⟨Y, _, hy⟩ := source.space_l hZF hl
    have ultra := family.at_l hZF.1 hcU hc hy
    refine ⟨c, hcJ, U, measures c U hcU, hcU, P, hPU, m, hm, n, hn, l, hl, r, rk, t, tk, hr, ht, hc, hca, hcb, fun s hs => ?_⟩
    have sf := (hy s).mp (ultra.base.bounds P hPU s hs)
    obtain ⟨u, ru⟩ := cp0_exists_l (ZF.modelsKP hZF) hr sf
    obtain ⟨v, tv⟩ := cp0_exists_l (ZF.modelsKP hZF) ht sf
    obtain ⟨x, _, y, _, sx, sy, xy⟩ := point s hs
    have ux := (pf.2.2 s u sf ru x).mp sx
    have vy := (pg.2.2 s v sf tv y).mp sy
    have hx := (ff.bound_l ux).2
    have hyB := (gg.bound_l vy).2
    exact ⟨u, (source.finite u).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) ru.1⟩,
      v, (source.finite v).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) tv.1⟩,
      x, hx, y, hyB, ru, tv, ux, vy, (relation x y hx hyB).mpr xy⟩

end YesMetaZFC.SetTheory.LargeCardinal
