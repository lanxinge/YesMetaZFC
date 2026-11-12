import YesMetaZFC.SetTheory.LargeCardinal.Extender.Ultrapower
import YesMetaZFC.Model.SetTheory.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Source.OmegaClosed
import YesMetaZFC.Model.SetTheory.Internal.Hereditary
import YesMetaZFC.SetTheory.Collapse.RelationSequence
import YesMetaZFC.SetTheory.LargeCardinal.Iteration.StepSyntax

/-! # 常值像以下的处处有界代表

先把集合及其成员移到共同支撑，再读原子 Łoś。源内改值只发生在测度零处，
所以得到同一极限元素的实际有界代表；无需预先塌缩极限。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

/-- 常值代表与支撑选择无关，直接比较同一极限中的实际商元素。 -/
theorem ep_repr_constant_l {ω κ K L X R F J O Z A p T S q C W D E x a b f g H P : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hf : Fn0_d D X f) (hg : Fn0_d E X g) (fc : Rs_const_d D x f) (gc : Rs_const_d E x g)
    (fv : Ep_repr_d q a f H) (gv : Ep_repr_d q b g P) : H = P := by
  obtain ⟨hfX, n, hn, ha, D', hd, hf'⟩ := fv.source_l hZF family system limit
  obtain ⟨hgX, m, hm, hb, E', he, hg'⟩ := gv.source_l hZF family system limit
  have eq := hf'.domain_eq_l hZF.1 hf
  subst D'
  have eq := hg'.domain_eq_l hZF.1 hg
  subst E'
  obtain ⟨c, hcJ, hac, hbc⟩ := system.order.directed a b (fv.index_l hZF system limit) (gv.index_l hZF system limit)
  obtain ⟨l, hl, hc, _⟩ := (system.indices c).mp hcJ
  obtain ⟨Q, _, hQ⟩ := source.space_l hZF hl
  obtain ⟨_, _, r, n', l', _, _, hr, hc', hra⟩ := (system.order_spec a c).mp hac
  have en := hra.1.domain_eq_l hZF.1 ha
  have el := hc'.domain_eq_l hZF.1 hc
  subst n' l'
  obtain ⟨f', _, ff, pull, fv'⟩ := ep_repr_reindex_l hZF source family system limit hn hl hr hcJ hc hra hd hQ hfX hf fv
  have fc' : Rs_const_d Q x f' := fun s hs => by
    obtain ⟨t, ht⟩ := cp0_exists_l (ZF.modelsKP hZF) hr ((hQ s).mp hs)
    exact (pull.2.2 s t ((hQ s).mp hs) ht x).mpr (fc t ((hd t).mpr ht.1))
  obtain ⟨_, _, r', m', l', _, _, hr', hc', hrb⟩ := (system.order_spec b c).mp hbc
  have em := hrb.1.domain_eq_l hZF.1 hb
  have el := hc'.domain_eq_l hZF.1 hc
  subst m' l'
  obtain ⟨g', _, gf, pull', gv'⟩ := ep_repr_reindex_l hZF source family system limit hm hl hr' hcJ hc hrb he hQ hgX hg gv
  have gc' : Rs_const_d Q x g' := fun s hs => by
    obtain ⟨t, ht⟩ := cp0_exists_l (ZF.modelsKP hZF) hr' ((hQ s).mp hs)
    exact (pull'.2.2 s t ((hQ s).mp hs) ht x).mpr (gc t ((he t).mpr ht.1))
  obtain ⟨U, hcU⟩ := family.total l c hl hc
  exact (ep_repr_atoms_l hZF family system limit hcU fv' gv').1.mpr
    ⟨Q, (family.at_l hZF.1 hcU hc hQ).base.top, fun s hs => ⟨x, (ff.bound_l (fc' s hs)).2, fc' s hs, gc' s hs⟩⟩

/-- 处处落入 B 的代表，其极限值属于 B 的常值像。 -/
theorem ep_repr_bound_mem_l {ω κ K L X R F J O Z A p T S q C W D B a f H m b Q g E : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hf : Fn0_d D X f) (constant : Rs_const_d D B f) (fv : Ep_repr_d q a f H) (hB : M.mem B X)
    (hm : M.mem m ω) (hb : Fn0_d m L b) (hQ : Ep_space_d κ m Q) (hg : Fn0_d Q B g)
    (gv : Ep_repr_d q b g E) : Rd_entry_d E H W := by
  obtain ⟨c, code⟩ := source.code
  obtain ⟨k, P, hk, hP, kf, ks⟩ := sc_constant_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hm hQ) hB
  have kc : Rs_const_d Q B k := fun s hs => (ks s B).mpr ⟨hs, rfl⟩
  have kf := kf.mono_target_l (source.transitive P hP)
  obtain ⟨H', _, kv⟩ := ep_repr_exists_l hZF family system limit (gv.index_l hZF system limit) hb hQ hk kf
  have eq := ep_repr_constant_l hZF source family system limit kf hf kc constant kv fv
  subst H'
  obtain ⟨U, hbU⟩ := family.total m b hm hb
  exact (ep_repr_atoms_l hZF family system limit hbU gv kv).2.mpr
    ⟨Q, (family.at_l hZF.1 hbU hb hQ).base.top, fun s hs => by
      obtain ⟨x, hx, hsx⟩ := hg.2.1 s hs
      exact ⟨x, source.transitive B hB x hx, B, hB, hsx, kc s hs,
        (code.2 x B).mpr ⟨source.transitive B hB x hx, hB, hx⟩⟩⟩

theorem ep_repr_bounded_l {ω κ K L X R F J O Z A p T S q C W n a D f B H E : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (hn : M.mem n ω) (ha : Fn0_d n L a) (hD : Ep_space_d κ n D) (hf : Fn0_d D X f)
    (constant : Rs_const_d D B f) (value : Ep_repr_d q a f H) (hB : M.mem B X) (edge : Rd_entry_d E H W) :
    ∃ m b Q g, M.mem m ω ∧ M.mem b J ∧ Fn0_d m L b ∧ Ep_space_d κ m Q ∧
      M.mem g X ∧ Fn0_d Q B g ∧ Ep_repr_d q b g E := by
  obtain ⟨c, code⟩ := source.code
  obtain ⟨m, b, Q, g, hm, hbJ, hb, hQ, hgX, hg, gv⟩ := ep_repr_surjective_l hZF family system limit (limit.bounded E H edge).1
  obtain ⟨s, hsJ, has, hbs⟩ := system.order.directed a b (value.index_l hZF system limit) hbJ
  obtain ⟨l, hl, hs, _⟩ := (system.indices s).mp hsJ
  obtain ⟨V, _, hV⟩ := source.space_l hZF hl
  obtain ⟨_, _, r, n', l', _, _, hr, hs', hra⟩ := (system.order_spec a s).mp has
  have en := hra.1.domain_eq_l hZF.1 ha
  have el := hs'.domain_eq_l hZF.1 hs
  subst n' l'
  obtain ⟨f', _, hff, pull, fv⟩ := ep_repr_reindex_l hZF source family system limit hn hl hr hsJ hs hra hD hV
    (value.source_l hZF family system limit).1 hf value
  have fc : Rs_const_d V B f' := by
    intro v hv
    obtain ⟨t, ht⟩ := cp0_exists_l (ZF.modelsKP hZF) hr ((hV v).mp hv)
    exact (pull.2.2 v t ((hV v).mp hv) ht B).mpr (constant t ((hD t).mpr ht.1))
  obtain ⟨_, _, r', m', l', _, _, hr', hs', hrb⟩ := (system.order_spec b s).mp hbs
  have em := hrb.1.domain_eq_l hZF.1 hb
  have el := hs'.domain_eq_l hZF.1 hs
  subst m' l'
  obtain ⟨g', hg', hgg, _, gv'⟩ := ep_repr_reindex_l hZF source family system limit hm hl hr' hsJ hs hrb hQ hV hgX hg gv
  obtain ⟨U, hsU⟩ := family.total l s hl hs
  have ultra := family.at_l hZF.1 hsU hs hV
  obtain ⟨P, hPU, point⟩ := (ep_repr_atoms_l hZF family system limit hsU gv' fv).2.mp edge
  have bound v (hv : M.mem v P) : ∃ x, M.mem x B ∧ Rd_entry_d v x g' := by
    obtain ⟨x, _, y, _, hvx, hvy, hxy⟩ := point v hv
    have ey := (fn0_function_l (ZF.modelsKP hZF) hff).1.2 v y B hvy (fc v (ultra.base.bounds P hPU v hv))
    exact ⟨x, ey ▸ ((code.2 x y).mp hxy).2.2, hvx⟩
  obtain ⟨v, hv⟩ := ultra.proper P hPU
  obtain ⟨z, hz, _⟩ := bound v hv
  obtain ⟨g'', hg'', hfn, eq⟩ := rs_bound_l hZF source.omega source.transitive code source.theory
    (source.space_mem_l hZF hl hV) hB hg' hgg hz ultra.base.bounds ⟨P, hPU, bound⟩
  obtain ⟨E', _, ev⟩ := ep_repr_exists_l hZF family system limit hsJ hs hV hg''
    (hfn.mono_target_l (source.transitive B hB))
  have ee := (ep_repr_atoms_l hZF family system limit hsU gv' ev).1.mpr eq
  exact ⟨l, s, V, g'', hl, hsJ, hs, hV, hg'', hfn, ee.symm ▸ ev⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 任意超幂下降链的统一源内值域界

首项代表的值域有一个源内传递包络 B。常值像 j(B) 在未塌缩极限中仍然
传递，因而包含整条下降链；每一项再由共同支撑改成 B 值的源内代表。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem ep_desc_bound_l {ω κ K L X R F J O Z A p T S q c C W g : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (cover : Sc_cover_d X) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d I ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
    (model : Smdl_d I c C W) (elementary : Di_elementary_d I ω O A p T S)
    (fn : Fn0_d ω C g) (desc : Wf_desc_d W g) : ∃ B, M.mem B X ∧ M.TransitiveSet B ∧
      ∀ i E, Rd_entry_d i E g → ∃ n a D f, M.mem n ω ∧ M.mem a J ∧ Fn0_d n L a ∧
        Ep_space_d κ n D ∧ M.mem f X ∧ Fn0_d D B f ∧ Ep_repr_d q a f E := by
  obtain ⟨z, hz, hzω⟩ := source.omega.1.1
  obtain ⟨E₀, he₀, hzE⟩ := fn.2.1 z hzω
  obtain ⟨n, a, D, f, hn, haJ, ha, hD, hfX, hf, fv⟩ := ep_repr_surjective_l hZF family system limit he₀
  obtain ⟨P, hP, coords⟩ := (source.algebra_l (ZF.modelsKP hZF)).envelope_l hfX
  obtain ⟨B, hB, bt, sub⟩ := cover P hP
  obtain ⟨_, models⟩ := system.codes
  obtain ⟨o, _, hao⟩ := models.2.1 a haJ
  obtain ⟨b, j, m, D', U, G, r, Y, V, code, hj, _, ha', hd', haU, functions, component, constants⟩ :=
    ep_constant_limit_l hZF source family system limit model elementary hao
  have en := ha'.domain_eq_l hZF.1 ha
  subst m
  have ed := hZF.1.eq_of_same_members D' D (fun s => (hd' s).trans (hD s).symm)
  subst D'
  have ultra := family.at_l hZF.1 haU ha hD
  obtain ⟨H, hH, hBH⟩ := hj.1.1.2.2 B hB
  obtain ⟨_, t, Q, u, htG, tc, htQ, hu, huH⟩ := (constants B H).mp hBH
  have tv : Ep_repr_d q a t H := ⟨u, Q, hu, component.map.representative_l I ultra.base htQ, huH⟩
  have ht := ((functions t).mp htG).2
  have initial : Rd_entry_d E₀ H W := (ep_repr_atoms_l hZF family system limit haU fv tv).2.mpr
    ⟨D, ultra.base.top, fun s hs => by
      obtain ⟨x, hx, hsx⟩ := hf.2.1 s hs
      exact ⟨x, hx, B, hB, hsx, tc s hs, (code.2 x B).mpr ⟨hx, hB, sub x (coords s x hsx).2⟩⟩⟩
  -- 原公式的初等性在商结构自身中给出传递性，不预设商已良基或已塌缩。
  let ρ : Env (smdl_structure_l I (R := R) code.1.2.1) 1 := ⟨fun _ => ⟨B, hB⟩, fun _ => ⟨B, hB⟩⟩
  let η : Env (smdl_structure_l I (R := W) model.2.1) 1 := ⟨fun _ => ⟨H, hH⟩, fun _ => ⟨H, hH⟩⟩
  have hs : Formula.satisfies ρ (Formula.isTransitive .newest) :=
    (smem_delta_image_l I code source.transitive (.forallMem _ (.forallMem _ (.mem ..))) ρ).mpr
      ((Formula.satisfies_isTransitive_iff ..).mpr bt)
  have image := (smap_source_l I hZF source.omega code.1 model hj (Formula.isTransitive .newest)
    (by simp -implicitDefEqProofs) ρ η (fun _ => hBH)).mp hs
  have trans := (Formula.satisfies_isTransitive_iff η .newest).mp image
  have closed x y (hx : M.mem x C) (hy : M.mem y C) (hxy : Rd_entry_d x y W) (hyH : Rd_entry_d y H W) :
      Rd_entry_d x H W := trans ⟨y, hy⟩ hyH ⟨x, hx⟩ hxy
  have all := wf_desc_invariant_l hZF source.omega fn desc hz hzE initial closed
  exact ⟨B, hB, bt, fun i E hiE => ep_repr_bounded_l hZF source family system limit hn ha hD ht tc tv hB
    (all i E hiE)⟩

end YesMetaZFC.SetTheory.LargeCardinal

/-! ## 从原代数证书恢复完整超幂边

Łoś 定理恢复常值图的完整内部初等性；常值代表唯一性保证恢复的是指定
图本身。原坍塌双射再给出同构，最终保留指定复合图。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem it_ultra_of_certificate_l {ω κ K L X R F J O Z A p T V q b C W c d Y S i e j : M.Domain}
    (source : Ep_source_d (kp_pair_l (ZF.modelsKP hZF)) ω κ K X R) (family : Em_source_d ω κ L X F)
    (coherent : Ec_source_d I ω κ L X F)
    (mx : Smem_d I c X R) (my : Smem_d I d Y S)
    (system : Ep_system_d I ω κ L X R F J O Z A p T V) (limit : Di_limit_d A p T V q C W)
    (model : Smdl_d I b C W) (collapse : Wc_graph_d C W e) (bij : M.IsSetBijectionFromTo I e C Y)
    (fi : Fn0_d X C i) (constants : Ep_constants_d X q i) (comp : It_comp_d i e j) :
    It_ultra_d (kp_pair_l (ZF.modelsKP hZF)) ω κ L F c d j := by
  obtain ⟨B, hB⟩ := model.2.1
  obtain ⟨u, hu⟩ := (limit.range B).mp hB
  obtain ⟨a, ha, _⟩ := system.projection.2.1 u (limit.projection.bound_l hu).1
  obtain ⟨_, maps⟩ := system.codes
  obtain ⟨v, _, hav⟩ := maps.2.1 a ha
  obtain ⟨c', i', n, D, U, G, r, H, Q, code, hi', _, hna, hd, hau, hg, quotient, values⟩ :=
    ep_constant_limit_l hZF source family system limit model
      (system.toEp_graph_d.elementary_l hZF source family coherent) hav
  have eqc := (smem_unique_l I hZF.1 code mx).1
  subst c'
  have eqi : i = i' := fi.ext_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF) hi'.1.1) (fun x hx => by
    obtain ⟨E, _, hxE⟩ := fi.2.1 x hx
    obtain ⟨E', _, hxE'⟩ := hi'.1.1.2.2 x hx
    obtain ⟨u, a, B, f, D', _, sf, fc, hf, hp, huE⟩ := constants x E hxE
    obtain ⟨_, g, B', u', hgG, gc, hgr, hp', huE'⟩ := (values x E').mp hxE'
    have eq := ep_repr_constant_l hZF source family system limit (sf.function_l source.transitive)
      ((hg g).mp hgG).2 fc gc ⟨u, B, hp, hf, huE⟩
      ⟨u', B', hp', quotient.map.representative_l I (family.at_l hZF.1 hau hna hd).base hgr, huE'⟩
    exact ⟨E, hxE, eq.symm ▸ hxE'⟩)
  have hi : Smap_d I ω c b X C i := eqi.symm ▸ hi'
  have he : Smap_d I ω b d C Y e := smap_of_iso_l I hZF source.omega model my.1 bij (fun a b x y ha hb =>
    (collapse.member_l (fn0_of_function_l (ZF.modelsKP hZF) bij.1.1) bij.1.2 ha hb).trans
      ⟨fun h => (my.2 x y).mpr ⟨bij.1.1.output_mem_of_pairMember ha, bij.1.1.output_mem_of_pairMember hb, h⟩,
        fun h => ((my.2 x y).mp h).2.2⟩)
  obtain ⟨j', hj', square⟩ := it_comp_elementary_l hZF hi he
  have hj : Smap_d I ω c d X Y j := (comp.unique_l hZF.1 square).symm ▸ hj'
  exact ⟨X, R, Y, S, J, O, Z, A, p, T, V, q, b, C, W, i, e,
    mx, my, system, limit, model, collapse, bij, he, hi, constants, hj, comp⟩

end YesMetaZFC.SetTheory.LargeCardinal
