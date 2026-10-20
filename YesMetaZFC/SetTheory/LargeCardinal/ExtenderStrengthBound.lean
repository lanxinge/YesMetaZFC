import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedGraph
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankSource
import YesMetaZFC.SetTheory.InaccessibleEnumeration
import YesMetaZFC.SetTheory.Card.Cantor

/-! # 不可达支撑长度处的真实强度上界

若目标包含 L 的全部子集，则它们都属于原 P(κ) 的像，因而都有处处取值于
P(κ) 的源代表。这些有限支撑节点全在 V_L 中；原商投影与坍缩的复合于是
把 V_L 的一个子集满射到 P(L)，与 |V_L|=L 及 Cantor 定理矛盾。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_inaccessible_bound_l {ω κ K L X R F J O Z A p T S q C W b d N V i t e P Γ : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hm : Smem_d I b X R) (hn : Smem_d I d N V) (hN : M.TransitiveSet N) (hi : Smap_d I ω b d X N i)
    (constants : Ep_constants_d X q t) (wc : Wc_graph_d C W e) (bij : M.IsSetBijectionFromTo I e C N)
    (comp : ∀ x y, Rd_entry_d x y i ↔ M.mem x X ∧ ∃ E, Rd_entry_d x E t ∧ Rd_entry_d E y e)
    (hP : M.IsPowerSetOf P κ) (hPX : M.mem P X) (hκi : Rd_entry_d κ Γ i) (hLΓ : M.MemberSubset L Γ)
    (hκL : M.mem κ L) (hωL : M.mem ω L) (hr : M.IsRegularCardinal I L) (hs : M.IsStrongLimitCardinal I L) :
    ∃ x, M.MemberSubset x L ∧ ¬ M.mem x N := by
  classical
  apply Classical.byContradiction
  intro missing
  have all x (hx : M.MemberSubset x L) : M.mem x N :=
    Classical.byContradiction (fun hn => missing ⟨x, hx, hn⟩)
  obtain ⟨B, hB⟩ := ZF.v_exists_l I hZF hr.isCardinal.1
  obtain ⟨R', rank⟩ := ep_regular_source_l hZFC source.omega hωL hr hB hκL source.below source.finite
  obtain ⟨c, code⟩ := rank.code
  have hPB := ZF.v_power_mem_l I hZF hB hr.isLimitOrdinal rank.cardinal_mem hP
  obtain ⟨U, hU, hKU, hPU⟩ := ZF.v_joint_bound_l I hZF hB rank.finite_mem hPB
  have node_rank u (node : Eb_node_d ω κ L K P J X X u) : M.mem u B := by
    obtain ⟨a, _, f, _, pair, n, hn, D, _, ha, space, ff⟩ := node
    have haB := sc_finite_function_l hZF source.omega rank.transitive rank.theory.algebra.pair rank.theory.algebra.union rank.omega_mem
      (ZF.v_ordinal_subset_l I hZF hB) hn ha
    have hfB := ZF.v_relation_mem_l I hZF hB hr.isLimitOrdinal hU (fun p hp => by
      obtain ⟨s, hd, x, hx, pair⟩ := ff.1 p hp
      exact ⟨s, hKU s (space.1 s hd), x, hPU x hx, pair⟩)
    obtain ⟨v, hv, vp⟩ := rank.theory.algebra.kpair_l haB hfB
    exact kpair_unique_l M hZF.1 vp pair ▸ hv
  -- 完整初等性只用于原幂集的源量词刻画。
  obtain ⟨P', _, hPP⟩ := hi.1.1.2.2 P hPX
  have power := hi.power_l hZF source.omega source.transitive hN hm hn hκi hPP
    (fun x => ⟨fun hx => ⟨source.transitive P hPX x hx, (hP x).mp hx⟩, fun ⟨_, hx⟩ => (hP x).mpr hx⟩)
  obtain ⟨_, H, hPH, hHP⟩ := (comp P P').mp hPP
  obtain ⟨u, a, D, f, Q, _, sf, fc, hfD, pair, huH⟩ := constants P H hPH
  have fv : Ep_repr_d q a f H := ⟨u, D, pair, hfD, huH⟩
  obtain ⟨_, n, hnω, ha, Q', space, ff⟩ := fv.source_l hZF family system limit
  have eq := (sf.function_l source.transitive).domain_eq_l hZF.1 ff
  subst Q'
  obtain ⟨PL, hPL⟩ := ZF.exists_powerSet hZF L
  -- 分离只收集原投影实际求值为 L 子集的节点，不另造求值关系。
  let ρ : Env M 10 := ⟨Fin.cases PL (Fin.cases e (Fin.cases q (Fin.cases X (Fin.cases J
    (Fin.cases P (Fin.cases K (Fin.cases L (Fin.cases κ (fun _ => ω))))))))), fun _ => ω⟩
  let φ : UnarySchema 10 := {
    body := .conj
      (eb_node_m (.bound 10) (.bound 9) (.bound 8) (.bound 7) (.bound 6) (.bound 5) (.bound 4) (.bound 4) .newest)
      (Formula.existsMem (.bound 1) (.existsE (.conj (eb_value_m (.bound 5) (.bound 2) .newest)
        (rd_entry0_m .newest (.bound 1) (.bound 4))))) }
  obtain ⟨D₀, ds⟩ := ZF.separation_exists_d hZF φ ρ B
  have spec u : M.mem u D₀ ↔ M.mem u B ∧ Eb_node_d ω κ L K P J X X u ∧
      ∃ x, M.mem x PL ∧ ∃ E, Eb_value_d q u E ∧ Rd_entry_d E x e := by
    simpa only [φ, Formula.satisfies_conj_iff, eb_node_sat_l hZF.1, Formula.satisfies_existsMem_iff,
      Formula.satisfies_exists_iff, eb_value_sat_l hZF.1, rd_entry0_sat_l hZF.1] using! ds u
  obtain ⟨v, vf, vs⟩ := eb_projection_l hZF source family system limit (source.transitive P hPX)
    (fun u hu => ((spec u).mp hu).2.1)
  obtain ⟨g, gf, gs⟩ := ZF.exists_compositionFunction hZF I (fn0_function_l (ZF.modelsKP hZF) vf) bij.1.1
  have into u x (hux : Rd_entry_d u x g) : M.mem x PL := by
    obtain ⟨hu, E, huE, hEx⟩ := (gs u x).mp hux
    obtain ⟨_, _, y, hy, H', value, hHy⟩ := (spec u).mp hu
    have h := (vs u H').mpr ⟨hu, value⟩
    have eq := (fn0_function_l (ZF.modelsKP hZF) vf).1.2 u H' E h huE
    exact bij.1.1.1.2 E y x (eq ▸ hHy) hEx ▸ hy
  have onto x (hx : M.mem x PL) : ∃ u, M.mem u D₀ ∧ Rd_entry_d u x g := by
    have hxN := all x ((hPL x).mp hx)
    obtain ⟨E, _, hEx⟩ := bij.2 x hxN
    have hxP := (power x).mpr ⟨hxN, fun y hy => hLΓ y ((hPL x).mp hx y hy)⟩
    have edge := (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hEx hHP).mpr hxP
    obtain ⟨m, a', D', f', hm, haJ, ha', hd, hf, fn, value⟩ :=
      ep_repr_bounded_l hZF source family system limit hnω ha space ff fc fv hPX edge
    obtain ⟨u', pair'⟩ := (I).total a' f'
    have node : Eb_node_d ω κ L K P J X X u' := ⟨a', haJ, f', hf, pair', m, hm, D',
      source.space_mem_l hZF hm hd, ha', (eb_space_iff_l (ZF.modelsKP hZF) source.finite hm).mpr hd, fn⟩
    have hu := (spec u').mpr ⟨node_rank u' node, node, x, hx, E, ⟨a', f', pair', value⟩, hEx⟩
    exact ⟨u', hu, (gs u' x).mpr ⟨hu, E, (vs u' E).mpr ⟨hu, a', f', pair', value⟩, hEx⟩⟩
  obtain ⟨r, rb⟩ := ZFC.inaccessible_enumeration_l I hZFC source.omega hωL hr hs hB
  obtain ⟨s, sb⟩ := ZF.exists_inverseBijection hZF I rb
  obtain ⟨t', ti⟩ := ZF.exists_inclusionInjection hZF I (fun u hu => ((spec u).mp hu).1)
  have small := ZF.exists_compositionInjection hZF I ti sb.1
  have bound := ZF.ordinal_image_bound_l I hZF hr.isCardinal.1 small
    (fn0_function_l (ZF.modelsKP hZF) ((fn0_of_function_l (ZF.modelsKP hZF) gf).retarget_l into)) onto
  have cantor := ZF.cardinalLess_powerSet hZF I hPL
  exact cantor.2 (ZF.equinumerous_of_cardinalLessOrEqual hZF I cantor.1 bound)

end YesMetaZFC.SetTheory.LargeCardinal
