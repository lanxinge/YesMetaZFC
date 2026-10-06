import YesMetaZFC.SetTheory.LargeCardinal.ExtenderSourceInclusion
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderBoundedRepresentative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRankClosure
import YesMetaZFC.SetTheory.LargeCardinal.IterationStep

/-! # 内部正则秩段的超幂就是原超幂的严格秩段

包含诱导的商映射以 j(Vα) 为像：正向用常值像下的代表计算；逆向先取
Vα 值代表，再以源内 κ 编号和 α 的内部正则性把整张代表图放回 Vα。
Mostowski 唯一性将其识别为同一个实际集合，常值代表保证新边恰为 j 的限制。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_rank_l {ω κ K L X R F c d j N S α V : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F) (hωL : M.MemberSubset ω L)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d hZF ω κ L F c d j)
    (hV : M.mem V X) (rank : Vr_d X α V) (regular : Sc_regular_d X α)
    (hκV : M.mem κ V) (hκ : M.IsOrdinal κ) :
    M.IsLimitOrdinal α ∧ ∃ K₀ b R₀ β B d' S' j', Ep_source_d hZF ω κ K₀ V R₀ ∧ Smem_d I b V R₀ ∧
      M.mem β N ∧ Rd_entry_d α β j ∧ M.mem B N ∧ Vr_d N β B ∧ Sc_regular_d N β ∧
      Smem_d I d' B S' ∧ It_ultra_d hZF ω κ L F b d' j' ∧ M.IsRestrictionOf I j' j V ∧
      ∃ K₁, Ep_source_d hZF ω ω K₁ B S' := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨X₀, R₁, N₀, S₀, J, O, Z, A, p, T, U, q, o, C, W, i, e,
    mx, nx, system, limit, model, wc, bij, he, hi, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₁ N₀ S₀
  have hωV := rank.subset_mem_l source.transitive hV hκV source.omega_mem source.below
  have hωα := rank.ordinal_height_l hZF source.transitive hV (source.omega.isOrdinal hZF) hωV
  obtain ⟨A₀, G, hA₀, hG, cert⟩ := rank
  have hαX := sc_function_domain_mem_l hZF source.omega source.transitive hm source.theory hG (cert V hV).2.1
  have rank : Vr_d X α V := ⟨A₀, G, hA₀, hG, cert⟩
  have hα := sc_omega_bound_limit_l hZF source.omega source.transitive hm source.theory source.omega_mem hαX
    (cert V hV).1 ⟨ω, hωα⟩ (regular ω hωα)
  obtain ⟨b, R₀, code⟩ := smdl_membership_l I hZF ⟨ω, hωV⟩
  obtain ⟨K₀, cut⟩ := source.rank_l hZF hV rank hα regular hωV code hκV hκ source.below
  have agree : Ea_agree_d ω κ X V := fun n D A hn hd sub => (source.rank_agree_l hZF hV rank hα hκV n D A hn hd sub).symm
  have family' := family.transfer_l agree
  obtain ⟨J', O', Z', A', p', T', U', q', o', C', W', system', limit', model', elementary'⟩ :=
    ep_ultrapower_l hZFC cut family' (coherent.transfer_l hZF agree) hωL
  obtain ⟨r, hr, rel, reps⟩ := ep_inclusion_l hZF code hm (source.transitive V hV) family' family system' limit' system limit
  obtain ⟨k, hk, ks⟩ := ZF.exists_compositionFunction hZF I hr.1 bij.1.1
  have inj x y z (hx : Rd_entry_d x z k) (hy : Rd_entry_d y z k) : x = y := by
    obtain ⟨_, E, hxE, hEz⟩ := (ks x z).mp hx
    obtain ⟨_, H, hyH, hHz⟩ := (ks y z).mp hy
    exact hr.2 x y H (bij.1.2 E H z hEz hHz ▸ hxE) hyH
  have member E H x y (hx : Rd_entry_d E x k) (hy : Rd_entry_d H y k) : Rd_entry_d E H W' ↔ M.mem x y := by
    obtain ⟨_, P, hEP, hPx⟩ := (ks E x).mp hx
    obtain ⟨_, Q, hHQ, hQy⟩ := (ks H y).mp hy
    exact (rel E H P Q hEP hHQ).trans (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hPx hQy)
  obtain ⟨H, _, hVH⟩ := hi.1.1.2.2 V hV
  obtain ⟨B, hB, hHB⟩ := he.1.1.2.2 H (hi.1.1.output_mem_of_pairMember hVH)
  have hVB := (js.2 V B).mpr ⟨H, hVH, hHB⟩
  obtain ⟨β, hβ, hαβ⟩ := hj.1.1.2.2 α hαX
  have rank' := (hj.hierarchy_l hZF source.omega source.transitive hN hm hn hαβ hVB).mp rank
  have regular' := (hj.regular_l hZF source.omega source.transitive hN hm hn hαβ).mp regular
  obtain ⟨u, a, P, f, D, _, sf, fc, hfP, pair, huH⟩ := constants V H hVH
  have fv : Ep_repr_d q a f H := ⟨u, P, pair, hfP, huH⟩
  obtain ⟨_, n, hno, ha, D', hd, ff⟩ := fv.source_l hZF family system limit
  have eq := (sf.function_l source.transitive).domain_eq_l hZF.1 ff
  subst D'
  have into E x (hEx : Rd_entry_d E x k) : M.mem x B := by
    obtain ⟨hE, H', hEH, hHx⟩ := (ks E x).mp hEx
    obtain ⟨m, b, Q, g, hm, _, hb, hQ, _, gf, gv⟩ := ep_repr_surjective_l hZF family' system' limit' hE
    have gv' := (reps b g E H' gv).mp hEH
    exact (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hHx hHB).mp
      (ep_repr_bound_mem_l hZF source family system limit ff fc fv hV hm hb hQ gf gv')
  obtain ⟨ι, hι, index⟩ := source.finite_index_l hZF hκ
  have onto x (hx : M.mem x B) : ∃ E, M.mem E C' ∧ Rd_entry_d E x k := by
    obtain ⟨H', hH', hHx⟩ := bij.2 x (hN B hB x hx)
    have edge := (wc.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 hHx hHB).mpr hx
    obtain ⟨m, a', Q, g, hm, haJ, ha', hQ, hg, gf, gv⟩ := ep_repr_bounded_l hZF source family system limit hno ha hd ff fc fv hV edge
    have sub s (hs : M.mem s Q) := (source.finite s).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) ((hQ s).mp hs)⟩
    have idx : Sc_index_d κ Q ι := ⟨hκ, fun s hs => index.1.2.2 s (sub s hs),
      fun s _ x _ y _ => index.1.1.2 s x y, fun s _ t _ x _ => index.2 s t x⟩
    have hgV := source.rank_function_l hZF hV rank hα regular (cut.space_mem_l hZF hm hQ) hκV hι idx hg gf
    obtain ⟨E, hE, ge⟩ := ep_repr_exists_l hZF family' system' limit' ((system'.indices a').mpr ((system.indices a').mp haJ)) ha' hQ hgV gf
    exact ⟨E, hE, (ks E x).mpr ⟨hE, H', (reps a' g E H' ge).mpr gv, hHx⟩⟩
  have iso : Wc_iso_d C' W' B k := ⟨rank'.transitive_l hZF hN hB,
    (fn0_of_function_l (ZF.modelsKP hZF) hk).retarget_l into, onto,
    fun x _ y _ z _ => inj x y z, fun E _ H _ x _ y _ => member E H x y⟩
  obtain ⟨_, b₀, i₀, B₀, e₀, _, d', S', j', mx₀, hi₀, const₀, ht₀, wc₀, bij₀, nx₀, he₀, _, _, _, hj', js', next⟩ :=
    ep_collapse_l hZF cut family' system' limit' model' elementary' (iso.well_founded_l (ZF.modelsKP hZF))
  obtain ⟨eb, _⟩ := smem_unique_l I hZF.1 mx₀ code
  subst b₀
  have iso₀ : Wc_iso_d C' W' B₀ e₀ := ⟨ht₀, fn0_of_function_l (ZF.modelsKP hZF) bij₀.1.1, bij₀.2,
    fun x _ y _ z _ => bij₀.1.2 x y z,
    fun E _ H _ x _ y _ => wc₀.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij₀.1.1) bij₀.1.2⟩
  have eb := iso₀.unique_l hZF iso
  have ee := iso₀.graph_unique_l hZF iso
  subst B₀ e₀
  have forward x y (hxy : Rd_entry_d x y j') : Rd_entry_d x y j := by
    obtain ⟨hx, E, hxE, hEy⟩ := (js' x y).mp hxy
    obtain ⟨u, a, Q, g, D, _, sg, gc, hgQ, pair, huE⟩ := const₀ x E hxE
    have gv : Ep_repr_d q' a g E := ⟨u, Q, pair, hgQ, huE⟩
    obtain ⟨_, H', hEH, hHy⟩ := (ks E y).mp hEy
    have gv' := (reps a g E H' gv).mp hEH
    obtain ⟨H₀, _, hxH⟩ := hi.1.1.2.2 x (source.transitive V hV x hx)
    obtain ⟨v, a₀, Q₀, g₀, D₀, _, sg₀, gc₀, hg₀, pair₀, hvH⟩ := constants x H₀ hxH
    have eq := ep_repr_constant_l hZF source family system limit
      ((sg.function_l cut.transitive).mono_target_l (source.transitive V hV)) (sg₀.function_l source.transitive)
      gc gc₀ gv' ⟨v, Q₀, pair₀, hg₀, hvH⟩
    exact (js.2 x y).mpr ⟨H₀, hxH, eq ▸ hHy⟩
  refine ⟨hα, K₀, b, R₀, β, B, d', S', j', cut, code, hβ, hαβ, hB, rank', regular', nx₀,
    ⟨V, R₀, B, S', J', O', Z', A', p', T', U', q', o', C', W', i₀, k,
      code, nx₀, system', limit', model', wc₀, bij₀, he₀, hi₀, const₀, hj', hj'.1.1.1.1,
      fun x y => (js' x y).trans ⟨And.right, fun ⟨z, hxz, hzy⟩ => ⟨hi₀.1.1.input_mem_of_pairMember hxz, z, hxz, hzy⟩⟩⟩,
    ⟨hj'.1.1.1.1, fun x y => ⟨fun h => ⟨hj'.1.1.input_mem_of_pairMember h, forward x y h⟩, ?_⟩⟩, next⟩
  rintro ⟨hx, hxy⟩
  obtain ⟨y', _, hxy'⟩ := hj'.1.1.2.2 x hx
  exact hj.1.1.1.2 x y' y (forward x y' hxy') hxy ▸ hxy'

end YesMetaZFC.SetTheory.LargeCardinal
