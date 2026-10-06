import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceInclusion
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative
import YesMetaZFC.SetTheory.LargeCardinal.IterationStep

/-! # 同源同扩展器的实际超幂唯一

相同代表给出两份原始商之间的满同构。复合第二个塌缩后，Mostowski
唯一性识别两个实际传递集合；常值代表的支撑无关性再识别超幂嵌入本身。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_unique_l {ω κ K L X R F c d j N S d' j' N' S' : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (hn' : Smem_d I d' N' S')
    (ultra : It_ultra_d hZF ω κ L F c d j) (ultra' : It_ultra_d hZF ω κ L F c d' j') :
    N = N' ∧ d = d' ∧ j = j' := by
  have hN := ultra.transitive_l hZF hn.1
  have hN' := ultra'.transitive_l hZF hn'.1
  obtain ⟨X₀, R₀, N₀, S₀, J, O, Z, A, p, T, V, q, b, C, W, i, e,
    mx, nx, system, limit, _, wc, bij, _, hi, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₀ N₀ S₀
  obtain ⟨X₀, R₀, N₀, S₀, J', O', Z', A', p', T', V', q', b', C', W', i', e',
    mx', nx', system', limit', _, wc', bij', _, hi', constants', hj', js'⟩ := ultra'
  obtain ⟨ex, er⟩ := smdl_unique_l I mx'.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx'.1 hn'.1
  subst X₀ R₀ N₀ S₀
  obtain ⟨g, hg, rel, reps⟩ := ep_inclusion_l hZF hm hm (fun _ hx => hx)
    family family system limit system' limit'
  have onto E' (hE' : M.mem E' C') : ∃ E, M.mem E C ∧ Rd_entry_d E E' g := by
    obtain ⟨n, a, D, f, _, haJ, ha, hd, hf, ff, fe'⟩ := ep_repr_surjective_l hZF family system' limit' hE'
    obtain ⟨E, hE, fe⟩ := ep_repr_exists_l hZF family system limit
      ((system.indices a).mpr ((system'.indices a).mp haJ)) ha hd hf ff
    exact ⟨E, hE, (reps a f E E' fe).mpr fe'⟩
  obtain ⟨k, hk, ks⟩ := ZF.exists_compositionFunction hZF I hg.1 bij'.1.1
  have iso : Wc_iso_d C W N e := ⟨hN, fn0_of_function_l (ZF.modelsKP hZF) bij.1.1,
    bij.2, fun x _ y _ z _ => bij.1.2 x y z,
    fun E _ H _ x _ y _ => wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2⟩
  have iso' : Wc_iso_d C W N' k := by
    refine ⟨hN', fn0_of_function_l (ZF.modelsKP hZF) hk, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨E', hE', he⟩ := bij'.2 x hx
      obtain ⟨E, hE, hEE⟩ := onto E' hE'
      exact ⟨E, hE, (ks E x).mpr ⟨hE, E', hEE, he⟩⟩
    · intro E _ H _ x _ he hh
      obtain ⟨_, E', hEE, hex⟩ := (ks E x).mp he
      obtain ⟨_, H', hHH, hhx⟩ := (ks H x).mp hh
      exact hg.2 E H H' (bij'.1.2 E' H' x hex hhx ▸ hEE) hHH
    · intro E _ H _ x _ y _ he hh
      obtain ⟨_, E', hEE, hex⟩ := (ks E x).mp he
      obtain ⟨_, H', hHH, hhy⟩ := (ks H y).mp hh
      exact (rel E H E' H' hEE hHH).trans
        (wc'.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij'.1.1) bij'.1.2 hex hhy)
  have en := iso.unique_l hZF iso'
  have ek := iso.graph_unique_l hZF iso'
  subst N' k
  obtain ⟨ed, _⟩ := smem_unique_l I hZF.1 hn hn'
  refine ⟨rfl, ed, ?_⟩
  apply (fn0_of_function_l (ZF.modelsKP hZF) hj.1.1).ext_l hZF.1
    (fn0_of_function_l (ZF.modelsKP hZF) hj'.1.1)
  intro x hx
  obtain ⟨y, _, hxy⟩ := hj.1.1.2.2 x hx
  refine ⟨y, hxy, ?_⟩
  obtain ⟨E, hxE, hEy⟩ := (js.2 x y).mp hxy
  obtain ⟨u, a, B, f, D, _, sf, fc, hfB, pair, huE⟩ := constants x E hxE
  have fe : Ep_repr_d q a f E := ⟨u, B, pair, hfB, huE⟩
  obtain ⟨_, E', hEE, hE'y⟩ := (ks E y).mp hEy
  have fe' := (reps a f E E' fe).mp hEE
  obtain ⟨H, _, hxH⟩ := hi'.1.1.2.2 x hx
  obtain ⟨v, a', B', f', D', _, sf', fc', hfB', pair', hvH⟩ := constants' x H hxH
  have eq := ep_repr_constant_l hZF source family system' limit'
    (sf.function_l source.transitive) (sf'.function_l source.transitive) fc fc' fe' ⟨v, B', pair', hfB', hvH⟩
  exact (js'.2 x y).mpr ⟨H, hxH, eq ▸ hE'y⟩

end YesMetaZFC.SetTheory.LargeCardinal
