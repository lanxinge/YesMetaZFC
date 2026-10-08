import YesMetaZFC.SetTheory.LargeCardinal.IterationAttemptSpace
import YesMetaZFC.SetTheory.LargeCardinal.ExtenderEmbeddingTree
import YesMetaZFC.Model.SetTheory.Internal.TransitiveSource

/-! # 联合尝试节点在实际工作源中的绝对性

有限列、有限程序和双边真值证书均实际属于源。无界量词通过图的坐标
与源的有限闭性回收，故不需要把任意一阶真值假定为绝对。
-/
namespace YesMetaZFC.SetTheory.LargeCardinal
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem Ep_source_d.sequences_relative_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w A Q : Term d) (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (fseq_space_m (𝒞 := kpair_convention_l) w A Q) ↔
      Fseq_space_d I ω (A.eval ρ).val (Q.eval ρ).val := by
  let J := rt_pair_l source.transitive nz hZF.1 source.theory.algebra.pair
  have tr (f a b : (rt_model_l Z nz).Domain) : (rt_model_l Z nz).IsSetFunctionFromTo J f a b ↔
      M.IsSetFunctionFromTo I f.val a.val b.val :=
    rt_function_from_l source.transitive nz hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
      source.theory.algebra.pair f a b
  simp only [fseq_space_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunctionFromTo_iff J (rt_model_ext_l hZF.1 source.transitive nz), tr,
    Definitional.Term.eval_weaken]
  obtain ⟨c, code⟩ := source.code
  constructor
  · intro h f
    constructor
    · intro hf
      obtain ⟨n, hn, fn⟩ := (h ⟨f, source.transitive _ (Q.eval ρ).property f hf⟩).mp hf
      exact ⟨n.val, hw ▸ hn, fn⟩
    · rintro ⟨n, hn, fn⟩
      have hf := sc_finite_function_l hZF source.omega source.transitive code source.theory source.omega_mem
        (source.transitive _ (A.eval ρ).property) hn (fn0_of_function_l (ZF.modelsKP hZF) fn)
      exact (h ⟨f, hf⟩).mpr ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw ▸ hn, fn⟩
  · intro h f
    exact (h f.val).trans ⟨fun ⟨n, hn, fn⟩ =>
      ⟨⟨n, source.transitive ω source.omega_mem n hn⟩, hw ▸ hn, fn⟩,
      fun ⟨n, hn, fn⟩ => ⟨n.val, hw ▸ hn, fn⟩⟩

theorem Ep_source_d.ja_elementary_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w A R B V e n p : Term d)
    (hw : (w.eval ρ).val = ω) (hn : M.mem (n.eval ρ).val ω) :
    Formula.satisfies ρ (ja_elementary_m w A R B V e n p) ↔
      At_elementary_d I ω (A.eval ρ).val (R.eval ρ).val (B.eval ρ).val (V.eval ρ).val
        (e.eval ρ).val (n.eval ρ).val (p.eval ρ).val := by
  simp only [ja_elementary_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    source.sequences_relative_l hZF nz, Definitional.Term.eval_weaken, hw,
    at_relative_sat_l (ZF.modelsKP hZF) source.transitive nz]
  constructor
  · rintro ⟨Q, J, L, hQ, hJ, hL, h⟩
    exact (source.at_elementary_l hZF (A.eval ρ).property (R.eval ρ).property
      (B.eval ρ).property (V.eval ρ).property hn hQ hJ hL).mp h
  · intro h
    obtain ⟨Q, hQZ, hQ⟩ := source.sequences.space ω source.omega_mem
    obtain ⟨J, hJZ, hJ⟩ := source.sequences.space (A.eval ρ).val (A.eval ρ).property
    obtain ⟨L, hLZ, hL⟩ := source.sequences.space (B.eval ρ).val (B.eval ρ).property
    exact ⟨⟨Q, hQZ⟩, ⟨J, hJZ⟩, ⟨L, hLZ⟩, hQ, hJ, hL,
      (source.at_elementary_l hZF (A.eval ρ).property (R.eval ρ).property
        (B.eval ρ).property (V.eval ρ).property hn hQ hJ hL).mpr h⟩

private theorem ja_map_relative_l (hE : Extensional M) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z nz) d) (G i j f : Term d) :
    Formula.satisfies ρ (it_map_m G i j f) ↔ It_map_d (G.eval ρ).val (i.eval ρ).val (j.eval ρ).val (f.eval ρ).val := by
  have pair (r a b : (rt_model_l Z nz).Domain) : KPair_d (rt_model_l Z nz) r a b ↔ KPair_d M r.val a.val b.val := by
    let η : Env (rt_model_l Z nz) 3 := ⟨Fin.cases r (Fin.cases a (fun _ => b)), fun _ => r⟩
    exact (kpair0_sat_l (rt_model_ext_l hE hZ nz) η .newest (.bound 1) (.bound 2)).symm.trans
      ((rt_model_delta_l hZ nz (kpair0_delta_l ..) η).trans (kpair0_sat_l hE ..))
  rw [it_map_sat_l (rt_model_ext_l hE hZ nz)]
  exact ⟨fun ⟨r, hp, hr⟩ => ⟨r.val, (pair r _ _).mp hp, (rt_entry_l hZ nz hE ..).mp hr⟩,
    fun ⟨r, hp, hr⟩ => ⟨⟨r, (rd_entry_transitive_l hZ (G.eval ρ).property hr).1⟩,
      (pair _ _ _).mpr hp, (rt_entry_l hZ nz hE ..).mpr hr⟩⟩

theorem Ep_source_d.ja_node_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w T Q G E Y W z π k P : Term d) (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (ja_node_m w T Q G E Y W z π k P) ↔
      Ja_node_d I ω (T.eval ρ).val (Q.eval ρ).val (G.eval ρ).val (E.eval ρ).val
        (Y.eval ρ).val (W.eval ρ).val (z.eval ρ).val (π.eval ρ).val (k.eval ρ).val (P.eval ρ).val := by
  have ent {a} (η : Env (rt_model_l Z nz) a) (x y f : Term a) : Formula.satisfies η (rd_entry0_m x y f) ↔
      Rd_entry_d (x.eval η).val (y.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (rd_entry0_delta_l x y f) η).trans (rd_entry0_sat_l hZF.1 ..)
  have pair {a} (η : Env (rt_model_l Z nz) a) (p x y : Term a) : Formula.satisfies η (kpair0_m p x y) ↔
      KPair_d M (p.eval η).val (x.eval η).val (y.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (kpair0_delta_l p x y) η).trans (kpair0_sat_l hZF.1 ..)
  have fn {a} (η : Env (rt_model_l Z nz) a) (x y f : Term a) : Formula.satisfies η (fn0_m x y f) ↔
      Fn0_d (x.eval η).val (y.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (fn0_delta_l x y f) η).trans (fn0_sat_l hZF.1 ..)
  have coh {a} (η : Env (rt_model_l Z nz) a) (n A B e p : Term a) : Formula.satisfies η (at_coherent_m n A B e p) ↔
      At_coherent_d (n.eval η).val (A.eval η).val (B.eval η).val (e.eval η).val (p.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (at_coherent_delta_l n A B e p) η).trans (at_coherent_sat_l hZF.1 ..)
  have pre {a} (η : Env (rt_model_l Z nz) a) (n A B e τ p : Term a) : Formula.satisfies η (at_prescribed_m n A B e τ p) ↔
      At_prescribed_d (n.eval η).val (A.eval η).val (B.eval η).val (e.eval η).val (τ.eval η).val (p.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (at_prescribed_delta_l n A B e τ p) η).trans (at_prescribed_sat_l hZF.1 ..)
  have rows (hk : M.mem (k.eval ρ).val ω) : Formula.satisfies ρ (ja_rows_m w Q E Y W k P) ↔
      Ja_rows_d I ω (Q.eval ρ).val (E.eval ρ).val (Y.eval ρ).val (W.eval ρ).val (k.eval ρ).val (P.eval ρ).val := by
    simp only [ja_rows_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, ent, pair, fn, coh, source.ja_elementary_l hZF nz,
      Definitional.Term.eval_weaken, hw, hk]
    constructor
    · intro h i p c A R e hi hc hp he
      have ip := rd_entry_transitive_l source.transitive (P.eval ρ).property hi
      have ic := rd_entry_transitive_l source.transitive (Q.eval ρ).property hc
      have ar := hp.mem_l M source.transitive ic.2
      have ie := rd_entry_transitive_l source.transitive (E.eval ρ).property he
      exact h ⟨i, ip.1⟩ ⟨p, ip.2⟩ ⟨c, ic.2⟩ ⟨A, ar.1⟩ ⟨R, ar.2⟩ ⟨e, ie.2⟩ hi hc hp he
    · exact fun h i p c A R e => h i.val p.val c.val A.val R.val e.val
  let J := rt_pair_l source.transitive nz hZF.1 source.theory.algebra.pair
  have funs (f : (rt_model_l Z nz).Domain) : (rt_model_l Z nz).IsSetFunction J f ↔ M.IsSetFunction I f.val :=
    rt_function_l source.transitive nz hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) source.theory.algebra.pair f
  have commute : Formula.satisfies ρ (ja_commute_m G E P) ↔ Ja_commute_d (G.eval ρ).val (E.eval ρ).val (P.eval ρ).val := by
    simp only [ja_commute_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      ent, ja_map_relative_l hZF.1 source.transitive nz, Formula.satisfies_extensionalEq_iff_eq
        (rt_model_ext_l hZF.1 source.transitive nz), Definitional.Term.eval_weaken]
    constructor
    · intro h i j p q e f g u v x y a b hi hj he hf hg hux hvy hxy hua hvb
      have ip := rd_entry_transitive_l source.transitive (P.eval ρ).property hi
      have jq := rd_entry_transitive_l source.transitive (P.eval ρ).property hj
      have ie := rd_entry_transitive_l source.transitive (E.eval ρ).property he
      have jf := rd_entry_transitive_l source.transitive (E.eval ρ).property hf
      have owned : M.mem g Z := by
        obtain ⟨_, _, hr⟩ := hg
        exact (rd_entry_transitive_l source.transitive (G.eval ρ).property hr).2
      have ux := rd_entry_transitive_l source.transitive ie.2 hux
      have vy := rd_entry_transitive_l source.transitive jf.2 hvy
      have ua := rd_entry_transitive_l source.transitive ip.2 hua
      have vb := rd_entry_transitive_l source.transitive jq.2 hvb
      exact congrArg Subtype.val (h ⟨i, ip.1⟩ ⟨j, jq.1⟩ ⟨p, ip.2⟩ ⟨q, jq.2⟩ ⟨e, ie.2⟩ ⟨f, jf.2⟩
        ⟨g, owned⟩ ⟨u, ux.1⟩ ⟨v, vy.1⟩ ⟨x, ux.2⟩ ⟨y, vy.2⟩ ⟨a, ua.2⟩ ⟨b, vb.2⟩ hi hj he hf hg hux hvy hxy hua hvb)
    · exact fun h i j p q e f g u v x y a b hi hj he hf hg hux hvy hxy hua hvb =>
        Subtype.ext (h i.val j.val p.val q.val e.val f.val g.val u.val v.val x.val y.val a.val b.val hi hj he hf hg hux hvy hxy hua hvb)
  simp only [ja_node_m, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_isFunction_iff J (rt_model_ext_l hZF.1 source.transitive nz), funs,
    Formula.satisfies_forall_iff, Formula.satisfies_iff_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_imp_iff, ent, pair, pre, Definitional.Term.eval_weaken, commute]
  constructor
  · rintro ⟨hk, hf, dom, rr, root, comm⟩
    have hk : M.mem (k.eval ρ).val ω := hw ▸ hk
    refine ⟨hk, hf, fun i => ⟨?_, ?_⟩, (rows hk).mp rr, ?_, comm⟩
    · rintro ⟨p, hp⟩
      have ip := rd_entry_transitive_l source.transitive (P.eval ρ).property hp
      exact (dom ⟨i, ip.1⟩).mp ⟨⟨p, ip.2⟩, hp⟩
    · intro hi
      obtain ⟨p, hp⟩ := (dom ⟨i, (rd_entry_transitive_l source.transitive (T.eval ρ).property hi).1⟩).mpr hi
      exact ⟨p.val, hp⟩
    · intro p c A R e hp hc pair he
      have zp := rd_entry_transitive_l source.transitive (P.eval ρ).property hp
      have zc := rd_entry_transitive_l source.transitive (Q.eval ρ).property hc
      have ar := pair.mem_l M source.transitive zc.2
      exact root ⟨p, zp.2⟩ ⟨c, zc.2⟩ ⟨A, ar.1⟩ ⟨R, ar.2⟩
        ⟨e, (rd_entry_transitive_l source.transitive (E.eval ρ).property he).2⟩ hp hc pair he
  · intro h
    refine ⟨(show M.mem (k.eval ρ).val (w.eval ρ).val from hw ▸ h.length), h.function, fun i => ?_, (rows h.length).mpr h.rows,
      fun p c A R e => h.root p.val c.val A.val R.val e.val, h.commute⟩
    exact ⟨fun ⟨p, hp⟩ => (h.domain i.val).mp ⟨p.val, hp⟩, fun hi => by
      obtain ⟨p, hp⟩ := (h.domain i.val).mpr hi
      exact ⟨⟨p, (rd_entry_transitive_l source.transitive (P.eval ρ).property hp).2⟩, hp⟩⟩

theorem Ep_source_d.ja_cell_l {ω κ K Z S : M.Domain}
    (source : Ep_source_d hZF ω κ K Z S) (nz : Nonempty {x // M.mem x Z})
    {d} (ρ : Env (rt_model_l Z nz) d) (w T Q G E Y W z π s : Term d) (hw : (w.eval ρ).val = ω) :
    Formula.satisfies ρ (ja_cell_m w T Q G E Y W z π s) ↔
      Ja_cell_d I ω (T.eval ρ).val (Q.eval ρ).val (G.eval ρ).val (E.eval ρ).val
        (Y.eval ρ).val (W.eval ρ).val (z.eval ρ).val (π.eval ρ).val (s.eval ρ).val := by
  have pair {a} (η : Env (rt_model_l Z nz) a) (p x y : Term a) : Formula.satisfies η (kpair0_m p x y) ↔
      KPair_d M (p.eval η).val (x.eval η).val (y.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l source.transitive nz (kpair0_delta_l p x y) η).trans (kpair0_sat_l hZF.1 ..)
  simp only [ja_cell_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    pair, source.ja_node_l hZF nz, Definitional.Term.eval_weaken, hw]
  exact ⟨fun ⟨k, P, hp, node⟩ => ⟨k.val, P.val, hp, node⟩, fun ⟨k, P, hp, node⟩ =>
    let owned := hp.mem_l M source.transitive (s.eval ρ).property
    ⟨⟨k, owned.1⟩, ⟨P, owned.2⟩, hp, node⟩⟩

/-- 扩展关系只读取已有节点的坐标，故仅需传递性。 -/
theorem ja_extend_relative_l (hE : Extensional M) {Z : M.Domain} (hZ : M.TransitiveSet Z)
    (nz : Nonempty {x // M.mem x Z}) {d} (ρ : Env (rt_model_l Z nz) d) (T s t : Term d) :
    Formula.satisfies ρ (ja_extend_m T s t) ↔ Ja_extend_d (T.eval ρ).val (s.eval ρ).val (t.eval ρ).val := by
  have pair {a} (η : Env (rt_model_l Z nz) a) (p x y : Term a) : Formula.satisfies η (kpair0_m p x y) ↔
      KPair_d M (p.eval η).val (x.eval η).val (y.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ nz (kpair0_delta_l p x y) η).trans (kpair0_sat_l hE ..)
  have entry {a} (η : Env (rt_model_l Z nz) a) (x y f : Term a) : Formula.satisfies η (rd_entry0_m x y f) ↔
      Rd_entry_d (x.eval η).val (y.eval η).val (f.eval η).val := by
    simpa only [eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ nz (rd_entry0_delta_l x y f) η).trans (rd_entry0_sat_l hE ..)
  have sub {a} (η : Env (rt_model_l Z nz) a) (x y : Term a) : Formula.satisfies η (Formula.subset x y) ↔
      M.MemberSubset (x.eval η).val (y.eval η).val := by
    simpa only [Formula.subset, Structure.MemberSubset, eval_image_env_l (M := rt_model_l Z nz) (N := M) Subtype.val] using
      (rt_model_delta_l hZ nz (.atom ..) η).trans (Formula.satisfies_subset_iff _ x y)
  simp only [ja_extend_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff, pair,
    Formula.satisfies_mem_iff, entry, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, sub,
    Definitional.Term.eval_weaken]
  constructor
  · rintro ⟨k, P, l, Q, hp, hq, hk, ht, subs⟩
    refine ⟨k.val, P.val, l.val, Q.val, hp, hq, hk, ht, fun i p q hip hiq => ?_⟩
    have ip := rd_entry_transitive_l hZ P.property hip
    have iq := rd_entry_transitive_l hZ Q.property hiq
    exact subs ⟨i, ip.1⟩ ⟨p, ip.2⟩ ⟨q, iq.2⟩ hip hiq
  · rintro ⟨k, P, l, Q, hp, hq, hk, ht, subs⟩
    have kp := hp.mem_l M hZ (s.eval ρ).property
    have lq := hq.mem_l M hZ (t.eval ρ).property
    exact ⟨⟨k, kp.1⟩, ⟨P, kp.2⟩, ⟨l, lq.1⟩, ⟨Q, lq.2⟩, hp, hq, hk, ht,
      fun i p q => subs i.val p.val q.val⟩

end YesMetaZFC.SetTheory.LargeCardinal
