import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRepresentative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderConstant
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.Bounded
import YesMetaZFC.Model.SetTheory.Internal.SourceCover

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
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
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
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
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
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W)
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
