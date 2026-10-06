import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiberRelative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderRelative
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderNormalSource
import YesMetaZFC.Model.SetTheory.Internal.SourceUltrafilter
import YesMetaZFC.Model.SetTheory.Internal.ReducedPower.SourceModel
import YesMetaZFC.Model.SetTheory.Internal.TransitiveSource

/-! # 所属模型内部测度族的实际相对解释

有限函数由源闭包回收，极大性通过源内扩张滤子读成子集二择。
这里只需全部有限 κ 序列的一个相对幂集，不要求背景极大性或背景可数完备性。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem em_family_relative_l {ω κ K X R L F P : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hP : M.mem P X) (power : Source_d X K P) (hL : M.mem L X) (hF : M.mem F X)
    (family : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, source.cardinal_mem⟩ (fun _ => ⟨ω, source.omega_mem⟩))),
        fun _ => ⟨ω, source.omega_mem⟩⟩ : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4)
      (em_family_m (.bound 3) (.bound 2) (.bound 1) .newest)) : Em_source_d ω κ L X F := by
  let ne : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let N := rt_model_l X ne
  have he := rt_model_ext_l hZF.1 source.transitive ne
  have family := (em_family_sat_l he _ _ _ _ _).mp family
  obtain ⟨c, hm⟩ := source.code
  have finite {A n f} (hA : M.mem A X) (hn : M.mem n ω) (hf : Fn0_d n A f) : M.mem f X :=
    sc_finite_function_l hZF source.omega source.transitive hm source.theory source.omega_mem
      (source.transitive A hA) hn hf
  refine ⟨?_, ?_, ?_⟩
  · intro n a hn ha
    let n' : N.Domain := ⟨n, source.transitive ω source.omega_mem n hn⟩
    let a' : N.Domain := ⟨a, finite hL hn ha⟩
    obtain ⟨U, hu⟩ := family.total n' a' hn ((rt_fn_l source.transitive ne hZF.1 ..).mpr ha)
    exact ⟨U.val, (rt_entry_l source.transitive ne hZF.1 ..).mp hu⟩
  · intro a U V hu hv
    have au := rd_entry_transitive_l source.transitive hF hu
    have av := rd_entry_transitive_l source.transitive hF hv
    exact congrArg Subtype.val (family.function ⟨a, au.1⟩ ⟨U, au.2⟩ ⟨V, av.2⟩
      ((rt_entry_l source.transitive ne hZF.1 ..).mpr hu) ((rt_entry_l source.transitive ne hZF.1 ..).mpr hv))
  · intro a U hu
    have au := rd_entry_transitive_l source.transitive hF hu
    obtain ⟨n, D, hn, ha, hd, hU⟩ := family.measure ⟨a, au.1⟩ ⟨U, au.2⟩
      ((rt_entry_l source.transitive ne hZF.1 ..).mpr hu)
    have space : Ep_space_d κ n.val D.val := fun s => ⟨fun hs =>
      (rt_fn_l source.transitive ne hZF.1 ..).mp ((hd ⟨s, source.transitive D.val D.property s hs⟩).mp hs),
      fun hs => (hd ⟨s, finite source.cardinal_mem hn hs⟩).mpr ((rt_fn_l source.transitive ne hZF.1 ..).mpr hs)⟩
    obtain ⟨Q, hQ, subsets⟩ := sc_power_subset_l hZF source.omega source.transitive hm source.theory D.property hP power
      (fun s hs => (source.finite s).mpr ⟨n.val, hn, fn0_function_l (ZF.modelsKP hZF) ((space s).mp hs)⟩)
    exact ⟨n.val, D.val, hn, (rt_fn_l source.transitive ne hZF.1 ..).mp ha, space,
      sf_maximal_relative_l hZF source.omega source.transitive hm source.theory ne D ⟨U, au.2⟩ ⟨Q, hQ⟩ subsets hU⟩

theorem It_local_d.measures_l {ω κ K X R L F P : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hP : M.mem P X) (power : Source_d X K P) (locality : It_local_d ω X κ L F) : Em_source_d ω κ L X F := by
  obtain ⟨hω, hκ, hL, hF, loc⟩ := locality
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff] at loc
  exact em_family_relative_l hZF source hP power hL hF loc.1.2.2.2.2.2.2.1

theorem ec_coherent_relative_l {ω κ K X R L F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hL : M.mem L X) (hF : M.mem F X) (coherent : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, source.cardinal_mem⟩ (fun _ => ⟨ω, source.omega_mem⟩))),
        fun _ => ⟨ω, source.omega_mem⟩⟩ : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4)
      (es_coherent_m (𝒞 := kpair_convention_l) (.bound 3) (.bound 2) (.bound 1) .newest)) : Ec_source_d I ω κ L X F := by
  let ne : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let N := rt_model_l X ne
  have he := rt_model_ext_l hZF.1 source.transitive ne
  obtain ⟨c, code⟩ := source.code
  have finite {A n f} (hA : M.mem A X) (hn : M.mem n ω) (hf : Fn0_d n A f) : M.mem f X :=
    sc_finite_function_l hZF source.omega source.transitive code source.theory source.omega_mem (source.transitive A hA) hn hf
  have fn {d} (ρ : Env N d) (A B f : Term d) : Formula.satisfies ρ (fn0_m A B f) ↔
      Fn0_d (A.eval ρ).val (B.eval ρ).val (f.eval ρ).val :=
    (fn0_sat_l he ..).trans (rt_fn_l source.transitive ne hZF.1 ..)
  have cp {d} (ρ : Env N d) (m n K q s t : Term d) : Formula.satisfies ρ (cp0_m m n K q s t) ↔
      Cp0_d (m.eval ρ).val (n.eval ρ).val (K.eval ρ).val (q.eval ρ).val (s.eval ρ).val (t.eval ρ).val :=
    (cp0_sat_l he ..).trans (rt_cp_l source.transitive ne hZF.1 ..)
  have entry {d} (ρ : Env N d) (a b F : Term d) : Formula.satisfies ρ (Formula.orderedPairMem kpair_convention_l a b F) ↔
      Rd_entry_d (a.eval ρ).val (b.eval ρ).val (F.eval ρ).val :=
    (rd_entry_sat_l he ..).trans (rt_entry_l source.transitive ne hZF.1 ..)
  have pull {d} (ρ : Env N d) (m n q A Z : Term d) (k : Term d)
      (hk : k.eval ρ = (⟨κ, source.cardinal_mem⟩ : N.Domain)) (hn : M.mem (n.eval ρ).val ω) :
      Formula.satisfies ρ (es_pull_m m n k q A Z) ↔
      Es_pull_d (m.eval ρ).val (n.eval ρ).val κ (q.eval ρ).val (A.eval ρ).val (Z.eval ρ).val := by
    simp only [es_pull_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff, fn, cp, Definitional.Term.eval_weaken, hk]
    constructor
    · intro h s
      refine ⟨fun hs => ?_, ?_⟩
      · obtain ⟨hs, t, ht, comp⟩ := (h ⟨s, source.transitive _ (Z.eval ρ).property s hs⟩).mp hs
        exact ⟨hs, t.val, ht, comp⟩
      · rintro ⟨hs, t, ht, comp⟩
        exact (h ⟨s, finite source.cardinal_mem hn hs⟩).mpr
          ⟨hs, ⟨t, source.transitive _ (A.eval ρ).property t ht⟩, ht, comp⟩
    · intro h s
      exact (h s.val).trans (and_congr_right fun _ =>
        ⟨fun ⟨t, ht, comp⟩ => ⟨⟨t, source.transitive _ (A.eval ρ).property t ht⟩, ht, comp⟩,
          fun ⟨t, ht, comp⟩ => ⟨t.val, ht, comp⟩⟩)
  simp only [es_coherent_m, es_reindex_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, fn, cp, entry, Formula.satisfies_forallMem_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_iff_iff, Definitional.Term.eval_weaken] at coherent
  intro m n q a b U V A hm hn hA hq ha hb hav hbu all
  have hmX := source.transitive ω source.omega_mem m hm
  have hnX := source.transitive ω source.omega_mem n hn
  have av := rd_entry_transitive_l source.transitive hF hav
  have bu := rd_entry_transitive_l source.transitive hF hbu
  obtain ⟨Z, hz, decide⟩ := coherent ⟨m, hmX⟩ ⟨n, hnX⟩ ⟨q, finite hnX hm hq⟩
    ⟨a, av.1⟩ ⟨b, bu.1⟩ ⟨U, bu.2⟩ ⟨V, av.2⟩ ⟨A, hA⟩ hm hn hq ha hb hav hbu (fun t ht => all t.val ht)
  refine ⟨Z.val, (pull _ _ _ _ _ _ _ ?_ ?_).mp hz, decide⟩
  · rfl
  · exact hn

theorem It_local_d.coherent_l {ω κ K X R L F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (locality : It_local_d ω X κ L F) : Ec_source_d I ω κ L X F := by
  obtain ⟨hω, hκ, hL, hF, loc⟩ := locality
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff] at loc
  exact ec_coherent_relative_l hZF source hL hF loc.1.2.2.2.2.2.2.2.1

/-- 所有内部有限坐标图都在源中，故原子测度集合的完整背景规格可直接读取。 -/
theorem ea_atoms_relative_l {ω κ K X R L F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hL : M.mem L X) (hF : M.mem F X) (atoms : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, source.cardinal_mem⟩ (fun _ => ⟨ω, source.omega_mem⟩))),
        fun _ => ⟨ω, source.omega_mem⟩⟩ : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4)
      (ea_atoms_m (.bound 3) (.bound 2) (.bound 1) .newest)) : Ea_atoms_d ω κ L F := by
  let ne : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let N := rt_model_l X ne
  have he := rt_model_ext_l hZF.1 source.transitive ne
  have atoms := (ea_atoms_sat_l he _ _ _ _ _).mp atoms
  intro p n a U i r α β hn ha haU hi hr
  have au := rd_entry_transitive_l source.transitive hF haU
  have ia := rd_entry_transitive_l source.transitive au.1 hi
  have rb := rd_entry_transitive_l source.transitive au.1 hr
  let n' : N.Domain := ⟨n, source.transitive ω source.omega_mem n hn⟩
  let a' : N.Domain := ⟨a, au.1⟩
  let U' : N.Domain := ⟨U, au.2⟩
  let i' : N.Domain := ⟨i, ia.1⟩
  let r' : N.Domain := ⟨r, rb.1⟩
  let α' : N.Domain := ⟨α, ia.2⟩
  let β' : N.Domain := ⟨β, rb.2⟩
  let κ' : N.Domain := ⟨κ, source.cardinal_mem⟩
  have test (s : N.Domain) : Ea_test_d p κ' i' r' s ↔ Ea_test_d p κ i r s.val := by
    let ρ : Env N 4 := ⟨Fin.cases s (Fin.cases r' (Fin.cases i' (fun _ => κ'))), fun _ => s⟩
    exact (ea_test_sat_l he ρ p (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
      ((rt_model_delta_l source.transitive ne (ea_test_delta_l ..) ρ).trans (ea_test_sat_l hZF.1 ..))
  obtain ⟨T, ts, tu⟩ := atoms p n' a' U' i' r' α' β' hn
    ((rt_fn_l source.transitive ne hZF.1 ..).mpr ha) ((rt_entry_l source.transitive ne hZF.1 ..).mpr haU)
    ((rt_entry_l source.transitive ne hZF.1 ..).mpr hi) ((rt_entry_l source.transitive ne hZF.1 ..).mpr hr)
  have decision : (if p then α' = β' else N.mem α' β') ↔ if p then α = β else M.mem α β := by
    cases p
    · rfl
    · exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  refine ⟨T.val, fun s => ⟨fun hs => ?_, fun hs => ?_⟩, tu.trans decision⟩
  · let s' : N.Domain := ⟨s, source.transitive T.val T.property s hs⟩
    have hh := (ts s').mp hs
    exact ⟨(rt_fn_l source.transitive ne hZF.1 ..).mp hh.1, (test s').mp hh.2⟩
  · let s' : N.Domain := ⟨s, source.transitive K source.finite_mem s
      ((source.finite s).mpr ⟨n, hn, fn0_function_l (ZF.modelsKP hZF) hs.1⟩)⟩
    exact (ts s').mpr ⟨(rt_fn_l source.transitive ne hZF.1 ..).mpr hs.1, (test s').mpr hs.2⟩

theorem It_local_d.atoms_l {ω κ K X R L F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (loc : It_local_d ω X κ L F) : Ea_atoms_d ω κ L F := by
  obtain ⟨_, _, hL, hF, loc⟩ := loc
  have pre := ((Formula.satisfies_conj_iff _ _ _).mp loc).1
  simp only [ex_pre_m, Formula.satisfies_conj_iff] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, atoms, _, _, _⟩ := pre
  exact ea_atoms_relative_l hZF source hL hF atoms

/-- 正规性只读取源内代表；测度及其成员均由原源内扩展器图提供。 -/
theorem en_normal_relative_l {ω κ K X R L F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (hL : M.mem L X) (hF : M.mem F X) (normal : Formula.satisfies
      (⟨Fin.cases ⟨F, hF⟩ (Fin.cases ⟨L, hL⟩ (Fin.cases ⟨κ, source.cardinal_mem⟩ (fun _ => ⟨ω, source.omega_mem⟩))),
        fun _ => ⟨ω, source.omega_mem⟩⟩ : Env (rt_model_l X ⟨⟨ω, source.omega_mem⟩⟩) 4)
      (en_normal_m (.bound 3) (.bound 2) (.bound 1) .newest)) : En_source_d ω κ L X F := by
  let ne : Nonempty {x // M.mem x X} := ⟨⟨ω, source.omega_mem⟩⟩
  let N := rt_model_l X ne
  have he := rt_model_ext_l hZF.1 source.transitive ne
  have normal := (en_normal_sat_l he _ _ _ _ _).mp normal
  intro n a U D f i α A hn ha haU hd hf fn hi hA regressive
  have au := rd_entry_transitive_l source.transitive hF haU
  have ia := rd_entry_transitive_l source.transitive au.1 hi
  let n' : N.Domain := ⟨n, source.transitive ω source.omega_mem n hn⟩
  let a' : N.Domain := ⟨a, au.1⟩
  let U' : N.Domain := ⟨U, au.2⟩
  let D' : N.Domain := ⟨D, source.space_mem_l hZF hn hd⟩
  let f' : N.Domain := ⟨f, hf⟩
  let i' : N.Domain := ⟨i, ia.1⟩
  let α' : N.Domain := ⟨α, ia.2⟩
  let A' : N.Domain := ⟨A, source.transitive U au.2 A hA⟩
  let κ' : N.Domain := ⟨κ, source.cardinal_mem⟩
  obtain ⟨m, b, V, β, B, hm, succ, fb, sub, last, lt, hbV, hBV, point⟩ := normal n' a' U' D' f' i' α' A' hn
    ((rt_fn_l source.transitive ne hZF.1 ..).mpr ha) ((rt_entry_l source.transitive ne hZF.1 ..).mpr haU)
    (fun s => (hd s.val).trans (rt_fn_l source.transitive ne hZF.1 n' κ' s).symm)
    ((rt_fn_l source.transitive ne hZF.1 ..).mpr fn) ((rt_entry_l source.transitive ne hZF.1 ..).mpr hi) hA
    (fun s hs x y hfx hiy => regressive s.val hs x.val y.val
      ((rt_entry_l source.transitive ne hZF.1 ..).mp hfx) ((rt_entry_l source.transitive ne hZF.1 ..).mp hiy))
  have successor : M.SuccessorOf m.val n := by
    let ρ : Env N 2 := ⟨Fin.cases m (fun _ => n'), fun _ => m⟩
    exact (KP.succ0_sat_l hZF.1 _ _ _).mp ((rt_model_delta_l source.transitive ne
      (KP.succ0_delta_l .newest (.bound 1)) ρ).mp ((KP.succ0_sat_l he ρ .newest (.bound 1)).mpr succ))
  refine ⟨m.val, b.val, V.val, β.val, B.val, hm, successor, (rt_fn_l source.transitive ne hZF.1 ..).mp fb,
    fun x hx => sub ⟨x, source.transitive a au.1 x hx⟩ hx, (rt_entry_l source.transitive ne hZF.1 ..).mp last,
    lt, (rt_entry_l source.transitive ne hZF.1 ..).mp hbV, hBV, fun s hs => ?_⟩
  let s' : N.Domain := ⟨s, source.transitive B.val B.property s hs⟩
  let ρ : Env N 5 := ⟨Fin.cases s' (Fin.cases f' (Fin.cases A' (Fin.cases κ' (fun _ => n')))), fun _ => s'⟩
  exact (en_graph_sat_l hZF.1 ..).mp ((rt_model_delta_l source.transitive ne (en_graph_delta_l ..) ρ).mp
    ((en_graph_sat_l he ρ (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).mpr (point s' hs)))

theorem It_local_d.normal_l {ω κ K X R L F : M.Domain} (source : Ep_source_d hZF ω κ K X R)
    (loc : It_local_d ω X κ L F) : En_source_d ω κ L X F := by
  obtain ⟨_, _, hL, hF, loc⟩ := loc
  have pre := ((Formula.satisfies_conj_iff _ _ _).mp loc).1
  simp only [ex_pre_m, Formula.satisfies_conj_iff] at pre
  obtain ⟨_, _, _, _, _, _, _, _, _, _, normal, _, _⟩ := pre
  exact en_normal_relative_l hZF source hL hF normal

/-- 内部所属判断和子集一致性直接生成施加源的完整初等定向极限。 -/
theorem It_local_d.apply_l (hZFC : M.Models ZFC) {ω κ K K' X R Y S L F P : M.Domain}
    (source : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K X R)
    (owner : Ep_source_d (ZFC.models_zf_l hZFC) ω κ K' Y S)
    (hP : M.mem P Y) (power : Source_d Y K' P) (agree : Ea_agree_d ω κ Y X)
    (locality : It_local_d ω Y κ L F) : ∃ J O Z A p T V q c C W,
      Ep_system_d (ZFC.models_zf_l hZFC) ω κ L X R F J O Z A p T V ∧ Di_limit_d A p T V q C W ∧
      Smdl_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) c C W ∧
      Di_elementary_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) ω O A p T V := by
  let hZF := ZFC.models_zf_l hZFC
  have family := locality.measures_l hZF owner hP power
  have coherent := locality.coherent_l hZF owner
  have ord := (locality.ordinals_l (ZF.modelsKP hZF) owner.transitive).2
  obtain ⟨_, _, _, _, loc⟩ := locality
  simp only [ex_short_m, ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff] at loc
  exact ep_apply_l hZFC source family coherent agree
    (fun x hx => ord.transitive κ loc.1.2.2.2.2.1 x (source.below x hx))

/-- 同一内部测度的有界商全部留在当前源中，可供枝反射读取下降链。 -/
theorem It_local_d.bounded_model_l {ω κ K X S L F Q R a U : M.Domain}
    (source : Ep_source_d hZF ω κ K X S) (power : Sc_power_d X) (locality : It_local_d ω X κ L F)
    (ha : Rd_entry_d a U F) (hQ : M.mem Q X) (hR : M.mem R X) (nonempty : ∃ x, M.mem x Q) :
    ∃ n D G d p C T, M.mem n ω ∧ Fn0_d n L a ∧ Ep_space_d κ n D ∧
      M.mem G X ∧ M.mem d X ∧ M.mem p X ∧ M.mem C X ∧ M.mem T X ∧
      (∀ f, M.mem f G ↔ M.mem f X ∧ Fn0_d D Q f) ∧ Rp_model_d I D Q U R d G p C T := by
  obtain ⟨P, hP, subsets⟩ := power K source.finite_mem
  obtain ⟨n, D, hn, hna, space, ultra⟩ := (locality.measures_l hZF source hP subsets).measure a U ha
  obtain ⟨_, _, _, hF, _⟩ := locality
  obtain ⟨c, hm⟩ := source.code
  obtain ⟨G, d, p, C, T, hG, hd, hp, hC, hT, functions, model⟩ := rs_bounded_model_l hZF source.omega
    source.transitive hm source.theory power (source.space_mem_l hZF hn space) hQ
    (rd_entry_transitive_l source.transitive hF ha).2 hR ultra.base nonempty
  exact ⟨n, D, G, d, p, C, T, hn, hna, space, hG, hd, hp, hC, hT, functions, model⟩

end YesMetaZFC.SetTheory.LargeCardinal
