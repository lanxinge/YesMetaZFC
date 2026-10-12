import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedValue
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiniteSyntax

/-! # 共同极限秩段中的原超幂像

对每个低秩对象，取同一秩段中的传递容器。容器值函数图也属于该秩段，
两源因此使用相同的有界代表池。两次传递塌缩的唯一性逐点识别原嵌入像；
这里不要求共同秩段在任一源中正则。
-/
namespace YesMetaZFC.SetTheory
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

include hZF in
theorem Vr_d.transitive_cover_l {X α V x : M.Domain} (rank : Vr_d X α V)
    (xt : M.TransitiveSet X) (hV : M.mem V X) (hα : M.IsLimitOrdinal α) (hx : M.mem x V) :
    ∃ B, M.mem B V ∧ M.TransitiveSet B ∧ M.mem x B := by
  obtain ⟨C, f, hC, hf, cert⟩ := rank
  have fn := (cert V hV).2.1
  obtain ⟨β, hβ, U, hU, hβU, sub⟩ := ((cert x (xt V hV x hx)).2.2.2).mp hx
  obtain ⟨γ, hγ, hβγ⟩ := hα.2.2 β hβ
  obtain ⟨B, hB, hγB⟩ := fn.2.1 γ hγ
  exact ⟨B, ((cert B (xt C hC B hB)).2.2.2).mpr ⟨γ, hγ, B, hB, hγB, fun _ h => h⟩,
    (vc_transitive_l hZF xt hV hC cert).2 γ hγ B hγB,
    ((cert x (xt V hV x hx)).2.2.1 γ hγ B hB hγB).mpr ⟨β, hβγ, U, hU, hβU, sub⟩⟩

namespace LargeCardinal

/-- 两源中的同一有界值函数图自动落入共同极限秩段。 -/
theorem Ep_source_d.common_functions_l {ω κ K X R K' Y S α V B : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (target : Ep_source_d hZF ω κ K' Y S)
    (hV : M.mem V X) (rank : Vr_d X α V) (hV' : M.mem V Y) (rank' : Vr_d Y α V)
    (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V) (hB : M.mem B V) :
    ∀ n D f, M.mem n ω → Ep_space_d κ n D → Fn0_d D B f → (M.mem f X ↔ M.mem f Y) := by
  have hω := rank.subset_mem_l source.transitive hV hκ source.omega_mem source.below
  have hK := rank.relations_mem_l source.transitive hV hα hω hκ source.finite_mem
    (fun f hf p hp => by
      obtain ⟨n, hn, fn⟩ := (source.finite f).mp hf
      obtain ⟨i, hi, x, hx, pair⟩ := (fn0_of_function_l (ZF.modelsKP hZF) fn).1 p hp
      exact ⟨i, source.omega.transitive hZF n hn i hi, x, hx, pair⟩)
  intro n D f hn space fn
  have bound p (hp : M.mem p f) : ∃ s, M.mem s K ∧ ∃ x, M.mem x B ∧ KPair_d M p s x := by
    obtain ⟨s, hs, x, hx, pair⟩ := fn.1 p hp
    exact ⟨s, (source.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) ((space s).mp hs)⟩, x, hx, pair⟩
  exact ⟨fun hf => target.transitive V hV' f (rank.relation_mem_l hZF source.transitive hV hα hK hB hf bound),
    fun hf => source.transitive V hV f (rank'.relation_mem_l hZF target.transitive hV' hα hK hB hf bound)⟩

/-- 共同秩段内每个集合的实际常值像相同，只需极限秩闭包。 -/
theorem it_ultra_common_l {ω κ K K' L X R Y S F c c' d d' j j' N T N' T' α V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (source' : Ep_source_d hZF ω κ K' Y S)
    (power : Sc_power_d X) (hL : M.mem L X) (hF : M.mem F X) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hm' : Smem_d I c' Y S) (hn : Smem_d I d N T) (hn' : Smem_d I d' N' T')
    (ultra : It_ultra_d hZF ω κ L F c d j) (ultra' : It_ultra_d hZF ω κ L F c' d' j')
    (hV : M.mem V X) (rank : Vr_d X α V) (hV' : M.mem V Y) (rank' : Vr_d Y α V)
    (hα : M.IsLimitOrdinal α) (hκ : M.mem κ V) :
    ∀ x y, M.mem x V → Rd_entry_d x y j → Rd_entry_d x y j' := by
  have hN := ultra.transitive_l hZF hn.1
  have hN' := ultra'.transitive_l hZF hn'.1
  obtain ⟨X₀, R₀, N₀, T₀, J, O, Z, A, p, D, U, q, b, C, W, i, e,
    mx, mn, system, limit, _, wc, bij, _, hi, constants, hj, js⟩ := ultra
  obtain ⟨Y₀, S₀, N₁, T₁, J', O', Z', A', p', D', U', q', b', C', W', i', e',
    mx', mn', system', limit', _, wc', bij', _, hi', constants', hj', js'⟩ := ultra'
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, et⟩ := smdl_unique_l I mn.1 hn.1
  obtain ⟨ey, es⟩ := smdl_unique_l I mx'.1 hm'.1
  obtain ⟨en', et'⟩ := smdl_unique_l I mn'.1 hn'.1
  subst X₀ R₀ N₀ T₀ Y₀ S₀ N₁ T₁
  have eqJ := hZF.1.eq_of_same_members J' J (fun a => (system'.indices a).trans (system.indices a).symm)
  subst J'
  have agree : Ea_agree_d ω κ X Y := fun n D B hn hd sub =>
    ((source.rank_agree_l hZF hV rank hα hκ n D B hn hd sub).symm).trans
      (source'.rank_agree_l hZF hV' rank' hα hκ n D B hn hd sub)
  have family' := family.transfer_l agree
  intro x y hx hxy
  obtain ⟨B, hBV, bt, hxB⟩ := rank.transitive_cover_l hZF source.transitive hV hα hx
  have hBX := source.transitive V hV B hBV
  have hBY := source'.transitive V hV' B hBV
  have common := source.common_functions_l hZF source' hV rank hV' rank' hα hκ hBV
  -- 同一关系与同一代表池分别满射到两次超幂的 j(B)。
  let φ : BinarySchema 0 := { body := .mem (.bound 1) .newest }
  obtain ⟨V₀, hV₀, shape, rel⟩ := sc_relation_source_l hZF source.omega source.transitive hm source.theory φ (.mem ..)
    ⟨Fin.elim0, fun _ => B⟩ (fun i => Fin.elim0 i) hBX hBX
  have read x y : Rd_entry_d x y V₀ ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y :=
    (rel x y).trans (and_congr_right fun _ => and_congr_right fun _ => Formula.satisfies_mem_iff ..)
  have membership : Rd_fun_d .mem B B B V₀ := by
    intro p
    refine ⟨fun hp => ?_, ?_⟩
    · obtain ⟨x, y, pair⟩ := shape p hp
      obtain ⟨hx, hy, hxy⟩ := (read x y).mp ⟨p, pair, hp⟩
      exact ⟨x, y, hx, hy, hxy, pair⟩
    · rintro ⟨x, y, hx, hy, hxy, pair⟩
      obtain ⟨q, qp, hq⟩ := (read x y).mpr ⟨hx, hy, hxy⟩
      exact kpair_unique_l M hZF.1 qp pair ▸ hq
  obtain ⟨P, G, A₀, pool⟩ := eb_pool_l hZF source power hL hBX system.indices
  obtain ⟨U₀, Q₀, _, _, range, _, edges⟩ := pool.relation_l hZF source hL hBX hF hV₀
  obtain ⟨B₀, _, hBB⟩ := hj.1.1.2.2 B hBX
  obtain ⟨B₁, _, hBB'⟩ := hj'.1.1.2.2 B hBY
  have trans₀ := smap_delta_l I hZF source.omega source.transitive hN hm hn hj (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => B, fun _ => B⟩ ⟨fun _ => B₀, fun _ => B₀⟩ (fun _ => hBB)
  have trans₁ := smap_delta_l I hZF source'.omega source'.transitive hN' hm' hn' hj' (n := 1)
    (Formula.isTransitive .newest) (by simp -implicitDefEqProofs) (Formula.isTransitive_delta0 _)
    ⟨fun _ => B, fun _ => B⟩ ⟨fun _ => B₁, fun _ => B₁⟩ (fun _ => hBB')
  simp only [Formula.satisfies_isTransitive_iff] at trans₀ trans₁
  obtain ⟨H, hBH, hHB⟩ := (js.2 B B₀).mp hBB
  obtain ⟨u, a, E, f, D₀, _, sf, fc, hfE, pair, huH⟩ := constants B H hBH
  obtain ⟨H', hBH', hHB'⟩ := (js'.2 B B₁).mp hBB'
  obtain ⟨u', a', E', f', D₁, _, sf', fc', hfE', pair', huH'⟩ := constants' B H' hBH'
  obtain ⟨g, map, values, _⟩ := pool.realize_l hZF source source (fun _ _ _ _ _ _ => Iff.rfl) hBX family
    system limit wc bij (sf.function_l source.transitive) fc ⟨u, E, pair, hfE, huH⟩ hHB (trans₀.mp bt) range membership edges
  obtain ⟨g', map', values', _⟩ := pool.realize_l hZF source' source (fun n D f hn hd hf => (common n D f hn hd hf).symm)
    hBY family' system' limit' wc' bij' (sf'.function_l source'.transitive) fc' ⟨u', E', pair', hfE', huH'⟩
    hHB' (trans₁.mp bt) range membership edges
  have eqg := map.graph_unique_l hZF map'
  -- 原 x 的同一常值代表在两侧求值；塌缩图唯一性给出字面相同的像。
  obtain ⟨H₀, hxH, hHy⟩ := (js.2 x y).mp hxy
  obtain ⟨u₀, a₀, E₀, f₀, D₂, _, sf₀, fc₀, hfE₀, pair₀, huH₀⟩ := constants x H₀ hxH
  have fv : Ep_repr_d q a₀ f₀ H₀ := ⟨u₀, E₀, pair₀, hfE₀, huH₀⟩
  obtain ⟨hfX, n, hnω, ha, D₃, space, ff⟩ := fv.source_l hZF family system limit
  have eqD := ff.domain_eq_l hZF.1 (sf₀.function_l source.transitive)
  subst D₃
  have fb : Fn0_d D₂ B f₀ := ff.retarget_l fun s z hsz =>
    (fn0_function_l (ZF.modelsKP hZF) ff).1.2 s z x hsz (fc₀ s (ff.bound_l hsz).1) ▸ hxB
  have haJ := fv.index_l hZF system limit
  obtain ⟨v, pv⟩ := (I).total a₀ f₀
  have hv := pool.node_l hZF source hnω haJ ha space hfX fb pv
  have ev := (values v y).mpr ⟨hv, a₀, f₀, pv, H₀, fv, hHy⟩
  obtain ⟨_, a₁, f₁, pv', H₁, fv', hH₁y⟩ := (values' v y).mp (eqg ▸ ev)
  obtain ⟨rfl, rfl⟩ := kpair_injective_l M pv' pv
  obtain ⟨y', _, hxy'⟩ := hj'.1.1.2.2 x (source'.transitive B hBY x hxB)
  obtain ⟨H₂, hxH₂, hH₂y⟩ := (js'.2 x y').mp hxy'
  obtain ⟨u₂, a₂, E₂, f₂, D₄, _, sf₂, fc₂, hfE₂, pair₂, huH₂⟩ := constants' x H₂ hxH₂
  have eq := ep_repr_constant_l hZF source' family' system' limit'
    (fb.mono_target_l (source'.transitive B hBY)) (sf₂.function_l source'.transitive)
    fc₀ fc₂ fv' ⟨u₂, E₂, pair₂, hfE₂, huH₂⟩
  exact (bij'.1.1.1.2 H₁ y y' hH₁y (eq.symm ▸ hH₂y)).symm ▸ hxy'

end LargeCardinal
end YesMetaZFC.SetTheory
