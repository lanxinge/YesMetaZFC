import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.SetTheory.LargeCardinal.Extender.UltraCertificate
import YesMetaZFC.SetTheory.LargeCardinal.Extender.RawCoherence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.Step
import YesMetaZFC.SetTheory.LargeCardinal.Extender.SkolemSource

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
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j)
    (hV : M.mem V X) (rank : Vr_d X α V) (regular : Sc_regular_d X α)
    (hκV : M.mem κ V) (hκ : M.IsOrdinal κ) :
    M.IsLimitOrdinal α ∧ ∃ K₀ b R₀ β B d' S' j', Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K₀ V R₀ ∧ Smem_d I b V R₀ ∧
      M.mem β N ∧ Rd_entry_d α β j ∧ M.mem B N ∧ Vr_d N β B ∧ Sc_regular_d N β ∧
      Smem_d I d' B S' ∧ It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F b d' j' ∧ M.IsRestrictionOf I j' j V ∧
      ∃ K₁, Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω ω K₁ B S' := by
  have hN := ultra.transitive_l hZF hn.1
  obtain ⟨X₀, R₁, N₀, S₀, J, O, Z, A, p, T, U, q, o, C, W, i, e,
    mx, nx, system, limit, model, wc, bij, he, hi, constants, hj, js⟩ := ultra
  obtain ⟨ex, er⟩ := smdl_unique_l I mx.1 hm.1
  obtain ⟨en, es⟩ := smdl_unique_l I nx.1 hn.1
  subst X₀ R₁ N₀ S₀
  have hωV := rank.subset_mem_l source.transitive hV hκV source.omega_mem source.below
  obtain ⟨hαX, hα⟩ := source.rank_height_l hZF hV rank regular hωV
  obtain ⟨b, R₀, code⟩ := smdl_membership_l I hZF ⟨ω, hωV⟩
  obtain ⟨K₀, cut⟩ := source.rank_l hZF hV rank hα regular hωV code hκV hκ source.below
  have agree : Ea_agree_d ω κ X V := fun n D A hn hd sub => (source.rank_agree_l hZF hV rank hα hκV n D A hn hd sub).symm
  have family' := family.transfer_l agree
  obtain ⟨J', O', Z', A', p', T', U', q', o', C', W', system', limit', model', elementary'⟩ :=
    ep_ultrapower_l hZF cut family' (coherent.transfer_l hZF agree)
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
    have sub s (hs : M.mem s Q) := ((source.finite_l (ZF.modelsKP hZF)) s).mpr ⟨m, hm, fn0_function_l (ZF.modelsKP hZF) ((hQ s).mp hs)⟩
    have idx : Sc_index_d κ Q ι := ⟨hκ, fun s hs => index.1.2.2 s (sub s hs),
      fun s _ x _ y _ => index.1.1.2 s x y, fun s _ t _ x _ => index.2 s t x⟩
    have hgV := source.rank_function_l hZF hV rank hα regular (cut.space_mem_l hZF hm hQ) hκV hι idx hg gf
    obtain ⟨E, hE, ge⟩ := ep_repr_exists_l hZF family' system' limit' ((system'.indices a').mpr ((system.indices a').mp haJ)) ha' hQ hgV gf
    exact ⟨E, hE, (ks E x).mpr ⟨hE, H', (reps a' g E H' ge).mpr gv, hHx⟩⟩
  have iso : Wc_iso_d C' W' B k := ⟨rank'.transitive_l hN hB,
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

/-! ## 同源同扩展器的实际超幂唯一

相同代表给出两份原始商之间的满同构。复合第二个塌缩后，Mostowski
唯一性识别两个实际传递集合；常值代表的支撑无关性再识别超幂嵌入本身。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_unique_l {ω κ K L X R F c d j N S d' j' N' S' : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (hm : Smem_d I c X R) (hn : Smem_d I d N S) (hn' : Smem_d I d' N' S')
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) (ultra' : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d' j') :
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

/-! ## 共同正则秩段上的超幂一致性

两源共有包含 κ 的正则 Vα 时，它们的有限 κ 幂子集相同。因此同一扩展器
可施于两侧，而两个 j(Vα) 都是同一个 Vα 的实际超幂。唯一性给出共同像、
共同高度及完全相同的限制嵌入；共同像以下的有限幂子集一致性随之成立。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_rank_agree_l {ω κ K K' L X R Y S F c c' d d' j j' N T N' T' α V : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (source' : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K' Y S)
    (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (hm : Smem_d I c X R) (hm' : Smem_d I c' Y S) (hn : Smem_d I d N T) (hn' : Smem_d I d' N' T')
    (ultra : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j) (ultra' : It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c' d' j')
    (hV : M.mem V X) (rank : Vr_d X α V) (regular : Sc_regular_d X α)
    (hV' : M.mem V Y) (rank' : Vr_d Y α V) (regular' : Sc_regular_d Y α)
    (hκV : M.mem κ V) (hκ : M.IsOrdinal κ) :
    ∃ β B r, M.mem β N ∧ M.mem β N' ∧ Rd_entry_d α β j ∧ Rd_entry_d α β j' ∧
      M.mem B N ∧ M.mem B N' ∧ Vr_d N β B ∧ Vr_d N' β B ∧ Sc_regular_d N β ∧ Sc_regular_d N' β ∧
      M.IsRestrictionOf I r j V ∧ M.IsRestrictionOf I r j' V ∧
      ∀ μ, M.mem μ β → Ea_agree_d ω μ N N' := by
  obtain ⟨hα, K₀, b, R₀, β, B, e, S₀, r, cut, code, hβ, hαβ, hB, image, reg, target, edge, res, K₁, next⟩ :=
    it_ultra_rank_l hZFC source family coherent hm hn ultra hV rank regular hκV hκ
  have agree : Ea_agree_d ω κ X Y := fun n D A hn hd sub =>
    ((source.rank_agree_l hZF hV rank hα hκV n D A hn hd sub).symm).trans
      (source'.rank_agree_l hZF hV' rank' hα hκV n D A hn hd sub)
  obtain ⟨_, K₀', b', R₀', β', B', e', S₀', r', _, code', hβ', hαβ', hB', image', reg', target', edge', res', _⟩ :=
    it_ultra_rank_l hZFC source' (family.transfer_l agree) (coherent.transfer_l hZF agree)
      hm' hn' ultra' hV' rank' regular' hκV hκ
  obtain ⟨eb, er⟩ := smem_unique_l I hZF.1 code code'
  subst b' R₀'
  have family₀ := family.transfer_l (fun n D A hn hd sub => (source.rank_agree_l hZF hV rank hα hκV n D A hn hd sub).symm)
  obtain ⟨eB, _, ej⟩ := it_ultra_unique_l hZF cut family₀ code target target' edge edge'
  subst B' r'
  have hN := ultra.transitive_l hZF hn.1
  have hN' := ultra'.transitive_l hZF hn'.1
  have eβ := image.height_unique_l hZF hN hN' hB hB' image'
  subst β'
  refine ⟨β, B, r, hβ, hβ', hαβ, hαβ', hB, hB', image, image', reg, reg', res, res', ?_⟩
  intro μ hμ n D A hn hd sub
  obtain ⟨E, hE, space⟩ := next.finite_space_l hZF (image.ordinal_subset_l hZF hN hB μ hμ) hn
  have eD := hZF.1.eq_of_same_members E D (fun s => (space s).trans
    ⟨fun hf => (hd s).mpr (fn0_of_function_l (ZF.modelsKP hZF) hf),
      fun hs => fn0_function_l (ZF.modelsKP hZF) ((hd s).mp hs)⟩)
  subst E
  exact ⟨fun hA => hN' B hB' A (image.subset_mem_l hN hB hE hA sub),
    fun hA => hN B hB A (image'.subset_mem_l hN' hB' hE hA sub)⟩

end YesMetaZFC.SetTheory.LargeCardinal
