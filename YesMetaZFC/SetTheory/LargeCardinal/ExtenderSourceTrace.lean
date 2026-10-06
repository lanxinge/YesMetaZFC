import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTrace
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderTupleValue

/-! # 源拥有扩展器时的支撑迹

把待测有限列与集合代表放到共同有限支撑上，用原测度的一条有界关系
判定成员资格。全部参数属于源时，分离得到支撑范围内的实际迹。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem eb_trace_read_l {ω κ K L X R F J O Z A p T S q c C W d N V e B R₀ U₀ n m D E a f ι H t : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) (model : Smdl_d I c C W)
    (hN : M.TransitiveSet N) (target : Smem_d I d N V) (he : Smap_d I ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e) (hωL : M.MemberSubset ω L)
    (kb : M.MemberSubset K B)
    (relation : ∀ x y, Rd_entry_d x y R₀ ↔ M.mem x B ∧ M.mem y B ∧ M.mem x y)
    (measures : ∀ a U, Rd_entry_d a U F → M.mem U U₀)
    (hn : M.mem n ω) (hm : M.mem m ω) (ha : Fn0_d n L a) (ht : Fn0_d m L t)
    (hd : Ep_space_d κ n D) (hE : Ep_space_d κ m E) (hfX : M.mem f X) (ff : Fn0_d D B f)
    (identity : ∀ s x, Rd_entry_d s x ι ↔ M.mem s E ∧ x = s) (value : Ep_value_d q e a f H) :
    Eb_edge_d ω κ L B J K U₀ R₀ F t ι a f ↔ M.mem t H := by
  obtain ⟨b, code⟩ := source.code
  obtain ⟨H₀, fv, hH₀⟩ := value
  have fx := ff.retarget_l (fun s x hsx => (rd_entry_transitive_l source.transitive hfX hsx).2)
  have finite x k (hk : M.mem k ω) (hx : Fn0_d k κ x) : M.mem x K :=
    (source.finite x).mpr ⟨k, hk, fn0_function_l (ZF.modelsKP hZF) hx⟩
  constructor
  · rintro ⟨c₀, hcJ, U, _, hcU, P, hPU, m', _, n', _, l, hl, r, _, v, _, hr, hv, hc, hct, hca, point⟩
    have em := hct.1.domain_eq_l hZF.1 ht
    have en := hca.1.domain_eq_l hZF.1 ha
    subst m' n'
    obtain ⟨D₀, _, hcD⟩ := source.space_l hZF hl
    obtain ⟨g, _, _, pg, gv⟩ := ep_repr_reindex_l hZF source family system limit hn hl hv hcJ hc hca hd hcD hfX fx fv
    obtain ⟨k, hkX, fk, ks⟩ := source.projection_l hZF hm hl hr hE hcD
    obtain ⟨E₀, kv, hE₀⟩ := ep_tuple_value_l hZFC source family coherent system limit model hN target he fixed
      hcJ hl hm hc hr hct hcD hE hkX fk (fun s x hsx => ((ks s x).mp hsx).2)
    have ultra := family.at_l hZF.1 hcU hc hcD
    have raw : Rd_entry_d E₀ H₀ W := by
      apply (ep_repr_atoms_l hZF family system limit hcU kv gv).2.mpr
      refine ⟨P, hPU, fun s hs => ?_⟩
      obtain ⟨u, _, v', _, x, _, y, _, ru, vv, ux, vy, xy⟩ := point s hs
      have eq := ((identity u x).mp ux).2
      subst x
      have sd := ultra.base.bounds P hPU s hs
      have huX := source.transitive K source.finite_mem u (finite u m hm ru.1)
      have hyX := (fx.bound_l vy).2
      exact ⟨u, huX, y, hyX,
        (ks s u).mpr ⟨sd, ru⟩, (pg.2.2 s v' ((hcD s).mp sd) vv y).mpr vy,
        (code.2 u y).mpr ⟨huX, hyX, ((relation u y).mp xy).2.2⟩⟩
    exact ((target.2 t H).mp ((he.relation_l I hZF source.omega model target.1 hE₀ hH₀).mp raw)).2.2
  · intro member
    obtain ⟨l, c₀, r, v, hl, hc, hr, hct, hv, hca⟩ := ec_join_l hZF source.omega hωL hm hn ht ha
    have hc' := fn0_of_function_l (ZF.modelsKP hZF) hc.1
    have hcJ := (system.indices c₀).mpr ⟨l, hl, hc', hc.2⟩
    obtain ⟨D₀, _, hcD⟩ := source.space_l hZF hl
    obtain ⟨g, _, _, pg, gv⟩ := ep_repr_reindex_l hZF source family system limit hn hl hv hcJ hc' hca hd hcD hfX fx fv
    obtain ⟨k, hkX, fk, ks⟩ := source.projection_l hZF hm hl hr hE hcD
    obtain ⟨E₀, kv, hE₀⟩ := ep_tuple_value_l hZFC source family coherent system limit model hN target he fixed
      hcJ hl hm hc' hr hct hcD hE hkX fk (fun s x hsx => ((ks s x).mp hsx).2)
    have raw := (he.relation_l I hZF source.omega model target.1 hE₀ hH₀).mpr ((target.2 t H).mpr
      ⟨he.1.1.output_mem_of_pairMember hE₀, he.1.1.output_mem_of_pairMember hH₀, member⟩)
    obtain ⟨U, hcU⟩ := family.total l c₀ hl hc'
    have ultra := family.at_l hZF.1 hcU hc' hcD
    obtain ⟨P, hPU, point⟩ := (ep_repr_atoms_l hZF family system limit hcU kv gv).2.mp raw
    have lk i (hi : M.mem i l) : M.mem i κ := source.below i (source.omega.transitive hZF l hl i hi)
    refine ⟨c₀, hcJ, U, measures c₀ U hcU, hcU, P, hPU, m, hm, n, hn, l, hl,
      r, finite r m hm (hr.mono_target_l lk), v, finite v n hn (hv.mono_target_l lk), hr, hv, hc', hct, hca, fun s hs => ?_⟩
    have sf := (hcD s).mp (ultra.base.bounds P hPU s hs)
    obtain ⟨x, _, y, _, sx, sy, xy⟩ := point s hs
    have ru := ((ks s x).mp sx).2
    obtain ⟨v', vv⟩ := cp0_exists_l (ZF.modelsKP hZF) hv sf
    have vy := (pg.2.2 s v' sf vv y).mp sy
    have hx := kb x (finite x m hm ru.1)
    have hy := (ff.bound_l vy).2
    exact ⟨x, finite x m hm ru.1, v', finite v' n hn vv.1, x, hx, y, hy, ru, vv,
      (identity x x).mpr ⟨(fk.bound_l sx).2, rfl⟩, vy, (relation x y).mpr ⟨hx, hy, ((code.2 x y).mp xy).2.2⟩⟩

/-- 所属源计算的迹也在原小模型的实际超幂中读取，无需另造所属源的超幂。 -/
theorem Eb_trace_d.read_l {ω κ K L X R F J O Z A p T S q c C W d N V e Y n m D E a f H B : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) (model : Smdl_d I c C W)
    (hN : M.TransitiveSet N) (target : Smem_d I d N V) (he : Smap_d I ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e) (hωL : M.MemberSubset ω L)
    (hn : M.mem n ω) (hm : M.mem m ω) (ha : Fn0_d n L a) (hd : Ep_space_d κ n D) (hE : Ep_space_d κ m E)
    (hfX : M.mem f X) (value : Ep_value_d q e a f H)
    (trace : Eb_trace_d ω κ L K Y F m D E a f B) :
    ∀ t, M.mem t B ↔ Fn0_d m L t ∧ M.mem t H := by
  obtain ⟨B₀, J₀, U₀, R₀, ι, T₀, _, _, _, _, _, _, kb, indices, range, rel, fb, fi, ids, seq, sub, spec⟩ := trace
  have eq : J₀ = J := hZF.1.eq_of_same_members J₀ J fun a => (indices a).trans (system.indices a).symm
  subst J₀
  have identity s x : Rd_entry_d s x ι ↔ M.mem s E ∧ x = s :=
    ⟨fun h => ⟨(fi.bound_l h).1, (fn0_function_l (ZF.modelsKP hZF) fi).1.2 s x s h (ids s (fi.bound_l h).1)⟩,
      fun ⟨hs, eq⟩ => eq.symm ▸ ids s hs⟩
  have read t (ht : Fn0_d m L t) : Eb_edge_d ω κ L B₀ J K U₀ R₀ F t ι a f ↔ M.mem t H :=
    eb_trace_read_l hZFC source family coherent system limit model hN target he fixed hωL kb
      (rt_mem_graph_l (ZF.modelsKP hZF) rel) (fun a U haU => (range U).mpr ⟨a, haU⟩)
      hn hm ha ht hd hE hfX fb identity value
  intro t
  exact ⟨fun ht => ((spec t (sub t ht)).mp ht).elim fun fn edge => ⟨fn, (read t fn).mp edge⟩,
    fun ⟨fn, member⟩ => (spec t ((seq t).mpr ⟨m, hm, fn⟩)).mpr ⟨fn, (read t fn).mpr member⟩⟩

/-- 一个源内代表的完整有限 L 幂迹由源内有界分离计算。 -/
theorem ep_source_trace_l {ω κ K L X R F J O Z A p T S q c C W d N V e n m D E a f H : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (hL : M.mem L X) (hF : M.mem F X)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) (model : Smdl_d I c C W)
    (hN : M.TransitiveSet N) (target : Smem_d I d N V) (he : Smap_d I ω c d C N e)
    (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e) (hωL : M.MemberSubset ω L)
    (hn : M.mem n ω) (hm : M.mem m ω) (ha : Fn0_d n L a) (hd : Ep_space_d κ n D) (hE : Ep_space_d κ m E)
    (hfX : M.mem f X) (ff : Fn0_d D X f) (value : Ep_value_d q e a f H) :
    ∃ B', M.mem B' X ∧ ∀ t, M.mem t B' ↔ Fn0_d m L t ∧ M.mem t H := by
  obtain ⟨B, hB, trace⟩ := eb_trace_l hZF source hL hF system.indices
    (value.elim fun _ h => h.1.index_l hZF system limit) hm hE hfX ff
  exact ⟨B, hB, trace.read_l hZFC source family coherent system limit model hN target he fixed hωL
    hn hm ha hd hE hfX value⟩

/-- 自身源拥有扩展器时，超幂中支撑范围内的子集仍属于原源。 -/
theorem ep_set_source_l {ω κ K L X R F J O Z A p T S q c C W d N V e m B : M.Domain}
    (source : Ep_source_d hZF ω κ K X R) (family : Em_source_d ω κ L X F) (coherent : Ec_source_d I ω κ L X F)
    (hL : M.mem L X) (hF : M.mem F X)
    (system : Ep_system_d hZF ω κ L X R F J O Z A p T S) (limit : Di_limit_d A p T S q C W) (model : Smdl_d I c C W)
    (hN : M.TransitiveSet N) (target : Smem_d I d N V) (he : Smap_d I ω c d C N e)
    (range : M.IsRangeOf I N e) (fixed : ∀ α H, Ep_seed_d κ L q α H → Rd_entry_d H α e)
    (hωL : M.MemberSubset ω L) (hm : M.mem m ω) (hB : M.mem B N) (bound : ∀ t, M.mem t B → Fn0_d m L t) : M.mem B X := by
  obtain ⟨H, hHB⟩ := (range B).mp hB
  obtain ⟨n, a, D, f, hn, _, ha, hd, hf, ff, value⟩ := ep_repr_surjective_l hZF family system limit (he.1.1.input_mem_of_pairMember hHB)
  obtain ⟨E, _, hE⟩ := source.space_l hZF hm
  obtain ⟨B', hB', read⟩ := ep_source_trace_l hZFC source family coherent hL hF system limit model hN target he fixed hωL
    hn hm ha hd hE hf ff ⟨H, value, hHB⟩
  exact hZF.1.eq_of_same_members B' B (fun t => (read t).trans ⟨And.right, fun ht => ⟨bound t ht, ht⟩⟩) ▸ hB'

end YesMetaZFC.SetTheory.LargeCardinal
