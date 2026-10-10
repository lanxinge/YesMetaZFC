import YesMetaZFC.SetTheory.LargeCardinal.ExtenderFiberRelative
import YesMetaZFC.Model.SetTheory.Internal.TransitiveCardinal

/-! # 原短扩展器在初始秩模型中的所属判断

同一张背景测度图、全部有限函数和可数共同纤维由极限秩闭包回收。
直接证明原公式的相对满足关系；不额外假设整个 Vδ 满足 ZF。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal FilterZF
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)
include hZF

private theorem ei_maximal_l {δ X : M.Domain} (hX : V_d I δ X)
    (nx : Nonempty {x // M.mem x X}) (D U : (rt_model_l X nx).Domain)
    (maximal : Maximal_d D.val U.val) : Maximal_d (ℳ := rt_model_l X nx) D U := by
  let N := rt_model_l X nx
  have ht := ZF.v_transitive_l I hZF hX
  have sub (A B : N.Domain) : M.MemberSubset A.val B.val ↔ N.MemberSubset A B :=
    ⟨fun h x hx => h x.val hx, fun h x hx => h ⟨x, ht A.val A.property x hx⟩ hx⟩
  refine ⟨⟨fun A hA => (sub A D).mp (maximal.1.1 A.val hA), maximal.1.2.1,
    fun A B hA ab bd => maximal.1.2.2.1 A.val B.val hA ((sub A B).mpr ab) ((sub B D).mpr bd), ?_⟩, ?_, ?_⟩
  · intro A B hA hB
    obtain ⟨C, hC, ca, cb⟩ := maximal.1.2.2.2 A.val B.val hA hB
    let c : N.Domain := ⟨C, ht U.val U.property C hC⟩
    exact ⟨c, hC, (sub c A).mp ca, (sub c B).mp cb⟩
  · intro A hA
    obtain ⟨x, hx⟩ := maximal.2.1 A.val hA
    exact ⟨⟨x, ht A.val A.property x hx⟩, hx⟩
  · intro G filter proper ug
    have full : IsFilter_d D.val G.val := by
      refine ⟨fun A hA => ?_, filter.2.1, fun A B hA ab bd => ?_, fun A B hA hB => ?_⟩
      · let a : N.Domain := ⟨A, ht G.val G.property A hA⟩
        exact (sub a D).mpr (filter.1 a hA)
      · let a : N.Domain := ⟨A, ht G.val G.property A hA⟩
        let b : N.Domain := ⟨B, ZF.v_subset_mem_l I hZF hX D.property bd⟩
        exact filter.2.2.1 a b hA ((sub a b).mp ab) ((sub b D).mp bd)
      · let a : N.Domain := ⟨A, ht G.val G.property A hA⟩
        let b : N.Domain := ⟨B, ht G.val G.property B hB⟩
        obtain ⟨C, hC, ca, cb⟩ := filter.2.2.2 a b hA hB
        exact ⟨C.val, hC, (sub C a).mpr ca, (sub C b).mpr cb⟩
    have proper' : Proper_d G.val := fun A hA => by
      obtain ⟨x, hx⟩ := proper ⟨A, ht G.val G.property A hA⟩ hA
      exact ⟨x.val, hx⟩
    exact (sub G U).mp (maximal.2.2 G.val full proper' ((sub U G).mpr ug))

/-- 源内实际参数的原短扩展器具有所属模型内部的全部短扩展器性质。 -/
theorem Ex_short_d.local_l {ω κ L F δ X : M.Domain} (h : Ex_short_d hZF ω κ L F)
    (hX : V_d I δ X) (hδ : M.IsLimitOrdinal δ) (hL : M.mem L X) (hF : M.mem F X) : It_local_d ω X κ L F := by
  have ht := ZF.v_transitive_l I hZF hX
  have hκ := ht L hL κ h.above
  have hω := ht κ hκ ω h.uncountable
  let nx : Nonempty {x // M.mem x X} := ⟨⟨ω, hω⟩⟩
  let N := rt_model_l X nx
  have he := rt_model_ext_l hZF.1 ht nx
  have pairs := sc_v_pair_l hZF hδ hX
  let J := rt_pair_l ht nx hZF.1 pairs
  let w : N.Domain := ⟨ω, hω⟩
  let k : N.Domain := ⟨κ, hκ⟩
  let z : N.Domain := ⟨L, hL⟩
  let e : N.Domain := ⟨F, hF⟩
  let ρ : Env N 4 := ⟨Fin.cases e (Fin.cases z (Fin.cases k (fun _ => w))), fun _ => w⟩
  have fn := rt_fn_l ht nx hZF.1
  have entry := rt_entry_l ht nx hZF.1
  have cp := rt_cp_l ht nx hZF.1
  have sub (A B : N.Domain) : N.MemberSubset A B ↔ M.MemberSubset A.val B.val :=
    ⟨fun g x hx => g ⟨x, ht A.val A.property x hx⟩ hx, fun g x hx => g x.val hx⟩
  -- 极限秩闭包同时回收函数图和由这些图组成的集合，供各条扩展器公理共用。
  have owned {A B f} (ha : M.mem A X) (hb : M.mem B X) (ff : Fn0_d A B f) : M.mem f X := by
    obtain ⟨Y, hy, ay, by'⟩ := ZF.v_joint_bound_l I hZF hX ha hb
    exact ZF.v_relation_mem_l I hZF hX hδ hy (fun p hp => (ff.1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, ay a ha.1, b, by' b hb.1, hb.2⟩)
  have family (n : N.Domain) (A : M.Domain) (all : ∀ s, M.mem s A → Fn0_d n.val κ s) : M.mem A X := by
    obtain ⟨Y, hy, ny, ky⟩ := ZF.v_joint_bound_l I hZF hX n.property hκ
    exact ZF.v_relations_mem_l I hZF hX hδ hy (fun f hf p hp => ((all f hf).1 p hp).elim fun a ha =>
      ha.2.elim fun b hb => ⟨a, ny a ha.1, b, ky b hb.1, hb.2⟩)
  have space (n D : N.Domain) (hd : ∀ s, N.mem s D ↔ Fn0_d n k s) : ∀ s, M.mem s D.val ↔ Fn0_d n.val κ s :=
    fun s => ⟨fun hs => (fn ..).mp ((hd ⟨s, ht D.val D.property s hs⟩).mp hs),
      fun hs => (hd ⟨s, owned n.property hκ hs⟩).mpr ((fn ..).mpr hs)⟩
  refine ⟨hω, hκ, hL, hF, (Formula.satisfies_conj_iff _ _ _).mpr ⟨?_, ?_⟩⟩
  · change Formula.satisfies ρ (ex_pre_m (.bound 3) (.bound 2) (.bound 1) .newest)
    simp only [ex_pre_m, Formula.satisfies_conj_iff, Formula.satisfies_isOmega_iff,
      Formula.satisfies_isCardinal_iff J he, Formula.satisfies_mem_iff, Formula.satisfies_isOrdinal_iff,
      Formula.satisfies_isFunction_iff J he, em_family_sat_l he, es_coherent_sat_l J he,
      ex_complete_sat_l he, ea_atoms_sat_l he, en_normal_sat_l he, ex_principal_sat_l he, ex_nonprincipal_sat_l he]
    refine ⟨rt_omega_l ht nx hZF.1 w h.omega,
      rt_cardinal_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pairs k h.critical, h.uncountable,
      rt_ordinal_l ht nx z h.length, h.above,
      (rt_function_l ht nx hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) pairs e).mpr h.graph, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨fun n a hn ha => ?_, fun a U V hu hv => ?_, fun a U hu => ?_⟩
      · obtain ⟨U, hu⟩ := h.measures.total n.val a.val hn ((fn ..).mp ha)
        exact ⟨⟨U, (rd_entry_transitive_l ht hF hu).2⟩, (entry ..).mpr hu⟩
      · exact Subtype.ext (h.measures.function a.val U.val V.val ((entry ..).mp hu) ((entry ..).mp hv))
      · obtain ⟨n, D, hn, ha, hd, maximal⟩ := h.measures.measure a.val U.val ((entry ..).mp hu)
        let n' : N.Domain := ⟨n, ht ω hω n hn⟩
        let D' : N.Domain := ⟨D, ht U.val U.property D maximal.1.2.1⟩
        exact ⟨n', D', hn, (fn n' z a).mpr ha, fun s => (hd s.val).trans (fn n' k s).symm,
          ei_maximal_l hZF hX nx D' U maximal⟩
    · intro m n q a b U V A hm hn hq ha hb hav hbu all
      obtain ⟨Z, pull, decide⟩ := h.coherent m.val n.val q.val a.val b.val U.val V.val A.val hm hn
        ((fn ..).mp hq) ((fn ..).mp ha) ((cp ..).mp hb) ((entry ..).mp hav) ((entry ..).mp hbu)
        (fun s hs => (fn ..).mp (all ⟨s, ht A.val A.property s hs⟩ hs))
      have hz := family n Z (fun s hs => ((pull s).mp hs).1)
      refine ⟨⟨Z, hz⟩, fun s => (pull s.val).trans (and_congr (fn n k s).symm ?_), decide⟩
      exact ⟨fun ⟨t, ht', comp⟩ => ⟨⟨t, ht A.val A.property t ht'⟩, ht', (cp ..).mpr comp⟩,
        fun ⟨t, ht', comp⟩ => ⟨t.val, ht', (cp ..).mp comp⟩⟩
    · intro n a U D ha hu hd μ hμ f hf
      obtain ⟨B, hB, spec⟩ := h.complete n.val a.val U.val D.val ((fn ..).mp ha) ((entry ..).mp hu)
        (space n D hd) μ.val hμ f.val ((fn ..).mp hf)
      refine ⟨⟨B, ht U.val U.property B hB⟩, hB, fun x => (spec x.val).trans (and_congr Iff.rfl ?_)⟩
      let η : Env N 4 := ⟨Fin.cases x (Fin.cases f (Fin.cases U (fun _ => μ))), fun _ => μ⟩
      exact ((ed_all_sat_l he η (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((rt_model_delta_l ht nx (ed_all_delta_l ..) η).trans (ed_all_sat_l hZF.1 _ _ _ _ _))).symm
    · intro p n a U i r α β hn ha hu hi hr
      obtain ⟨T, spec, decide⟩ := h.atoms p n.val a.val U.val i.val r.val α.val β.val hn
        ((fn ..).mp ha) ((entry ..).mp hu) ((entry ..).mp hi) ((entry ..).mp hr)
      have ht' := family n T (fun s hs => ((spec s).mp hs).1)
      refine ⟨⟨T, ht'⟩, fun s => (spec s.val).trans (and_congr (fn n k s).symm ?_), ?_⟩
      · let η : Env N 4 := ⟨Fin.cases s (Fin.cases r (Fin.cases i (fun _ => k))), fun _ => k⟩
        exact ((ea_test_sat_l he η p (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
          ((rt_model_delta_l ht nx (ea_test_delta_l ..) η).trans (ea_test_sat_l hZF.1 _ _ _ _ _ _))).symm
      · cases p with
        | false => exact decide
        | true => exact decide.trans ⟨Subtype.ext, congrArg Subtype.val⟩
    · intro n a U D f i α A hn ha hu hd hf hi hA reg
      obtain ⟨m, b, W, β, B, hm, succ, fb, ab, last, lt, hbW, hBW, graph⟩ := h.normal
        n.val a.val U.val D.val f.val i.val α.val A.val hn ((fn ..).mp ha) ((entry ..).mp hu)
        (space n D hd) ((fn ..).mp hf) ((entry ..).mp hi) hA (fun s hs x y hfx hiy => by
          have hsX := ht A.val A.property s hs
          have hx := (rd_entry_transitive_l ht f.property hfx).2
          have hy := (rd_entry_transitive_l ht hsX hiy).2
          exact reg ⟨s, hsX⟩ hs ⟨x, hx⟩ ⟨y, hy⟩ ((entry ..).mpr hfx) ((entry ..).mpr hiy))
      have bw := rd_entry_transitive_l ht hF hbW
      let m' : N.Domain := ⟨m, ht ω hω m hm⟩
      let b' : N.Domain := ⟨b, bw.1⟩
      let W' : N.Domain := ⟨W, bw.2⟩
      let β' : N.Domain := ⟨β, ht α.val α.property β lt⟩
      let B' : N.Domain := ⟨B, ht W bw.2 B hBW⟩
      refine ⟨m', b', W', β', B', hm, (rt_successor_l ht nx hZF.1 ..).mpr succ, (fn ..).mpr fb,
        (sub ..).mpr ab, (entry ..).mpr last, lt, (entry ..).mpr hbW, hBW, fun s hs => ?_⟩
      let η : Env N 5 := ⟨Fin.cases s (Fin.cases f (Fin.cases A (Fin.cases k (fun _ => n)))), fun _ => n⟩
      exact ((en_graph_sat_l he η (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest).symm.trans
        ((rt_model_delta_l ht nx (en_graph_delta_l ..) η).trans (en_graph_sat_l hZF.1 _ _ _ _ _ _))).mpr (graph s.val hs)
    · intro n a U hn ha hu A
      refine (h.principal n.val a.val U.val hn ((fn ..).mp ha) ((entry ..).mp hu) A.val).trans (and_congr ?_ Iff.rfl)
      exact ⟨fun all s hs => (fn ..).mpr (all s.val hs),
        fun all s hs => (fn ..).mp (all ⟨s, ht A.val A.property s hs⟩ hs)⟩
    · intro a U i α hu hi hα x s single
      apply h.nonprincipal a.val U.val i.val α.val ((entry ..).mp hu) ((entry ..).mp hi) hα x.val s.val
      intro y
      exact ⟨fun hy => congrArg Subtype.val ((single ⟨y, ht s.val s.property y hy⟩).mp hy),
        fun eq => eq.symm ▸ (single x).mpr rfl⟩
  -- 可数完备性：先读取原层族和纤维条件，再将实际共同纤维的图回收到源。
  · change Formula.satisfies ρ (ex_countable_m (.bound 3) (.bound 2) (.bound 1) .newest)
    simp only [ex_countable_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_exists_iff]
    intro H f levels fiber
    have levels := (ef_levels_sat_l he _ _ _ _).mp levels
    have levels' : Ef_levels_d ω κ H.val := by
      obtain ⟨⟨P, fp⟩, all⟩ := levels
      refine ⟨⟨P.val, (fn ..).mp fp⟩, fun n A hn s hs => ?_⟩
      have na := rd_entry_transitive_l ht H.property hn
      exact (fn ..).mp (all ⟨n, na.1⟩ ⟨A, na.2⟩ ((entry ..).mpr hn) ⟨s, ht A na.2 s hs⟩ hs)
    have fiber := (es_fiber_relative_l (ZF.modelsKP hZF) ht nx _ _ _ _ _ _).mp fiber
    obtain ⟨g, hg⟩ := h.countable H.val f.val levels' fiber
    exact ⟨⟨g, owned hω hκ hg.1⟩, (ef_fiber_relative_l hZF.1 ht nx _ _ _ _ _).mpr hg⟩

end YesMetaZFC.SetTheory.LargeCardinal
