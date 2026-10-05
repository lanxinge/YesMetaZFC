import YesMetaZFC.Model.SetTheory.Internal.EmbeddingOmega
import YesMetaZFC.SetTheory.InnerModel.Rudimentary.Graph
import YesMetaZFC.SetTheory.HereditaryAlgebra
import YesMetaZFC.SetTheory.CumulativeClosure

/-! # 源内基本运算与有界关系选择

配对、并、乘积及已有关系中的选择都是固定的一阶存在句子。它们在极限
Vδ 和正则 Hχ 中有实际实例；不要求源对无界见证作收集。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

structure Sc_algebra_d (X : M.Domain) : Prop where
  pair : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧ Pair_d M p a b
  union : ∀ a, M.mem a X → ∃ p, M.mem p X ∧ M.IsUnionOf p a
  product : ∀ a b, M.mem a X → M.mem b X → ∃ p, M.mem p X ∧
    ∀ t, M.mem t p ↔ ∃ x, M.mem x a ∧ ∃ y, M.mem y b ∧ KPair_d M t x y
  choice : ∀ A B R, M.mem A X → M.mem B X → M.mem R X →
    (∀ a, M.mem a A → ∃ b, M.mem b B ∧ Rd_entry_d a b R) →
      ∃ f, M.mem f X ∧ Fn0_d A B f ∧ M.MemberSubset f R
  fibers : ∀ R B, M.mem R X → M.mem B X → ∃ T, M.mem T X ∧ Rd_fun_d .fibers R B R T

def sc_total0_m {n} (A B R : Term n) : Formula 1 n :=
  Formula.forallMem A (Formula.existsMem B.weaken (rd_entry0_m (.bound 1) .newest R.weaken.weaken))
derive_free_closed sc_total0_m

theorem sc_total0_delta_l {n} (A B R : Term n) : (sc_total0_m A B R).IsDelta0 :=
  .forallMem _ (.existsMem _ (rd_entry0_delta_l ..))

theorem sc_total0_sat_l (hE : Extensional M) {n} (ρ : Env M n) (A B R : Term n) :
    Formula.satisfies ρ (sc_total0_m A B R) ↔
      ∀ a, M.mem a (A.eval ρ) → ∃ b, M.mem b (B.eval ρ) ∧ Rd_entry_d a b (R.eval ρ) := by
  simp only [sc_total0_m, Formula.satisfies_forallMem_iff, Formula.satisfies_existsMem_iff,
    rd_entry0_sat_l hE, Definitional.Term.eval_weaken]; rfl

def sc_algebra_m : Formula 1 0 :=
  let base := .conj (.forallE (.forallE (.existsE (pair0_m .newest (.bound 2) (.bound 1)))))
    (.conj (.forallE (.existsE (rd_graph_m .union (.bound 1) (.bound 1) (.bound 1) .newest)))
      (.conj (.forallE (.forallE (.existsE (rd_graph_m .prod (.bound 2) (.bound 1) (.bound 2) .newest))))
        (.forallE (.forallE (.forallE (.imp (sc_total0_m (.bound 2) (.bound 1) .newest)
          (.existsE (.conj (fn0_m (.bound 3) (.bound 2) .newest) (Formula.subset .newest (.bound 1))))))))))
  .conj base (.forallE (.forallE (.existsE (rd_graph_m .fibers (.bound 2) (.bound 1) (.bound 2) .newest))))

theorem sc_algebra_sat_l (hKP : M.Models KP) {X : M.Domain} (hX : M.TransitiveSet X)
    (hx : Nonempty {a // M.mem a X}) (ρ : Env (rt_model_l X hx) 0) :
    Formula.satisfies ρ sc_algebra_m ↔ Sc_algebra_d X := by
  have pair (η : Env (rt_model_l X hx) 3) :
      Formula.satisfies η (pair0_m .newest (.bound 2) (.bound 1)) ↔
        Pair_d M (η.bound 0).val (η.bound 2).val (η.bound 1).val :=
    (rt_model_delta_l hX hx (pair0_delta_l ..) η).trans (pair0_sat_l hKP.1 ..)
  have un (η : Env (rt_model_l X hx) 2) :
      Formula.satisfies η (rd_graph_m .union (.bound 1) (.bound 1) (.bound 1) .newest) ↔
        M.IsUnionOf (η.bound 0).val (η.bound 1).val :=
    (rt_model_delta_l hX hx (rd_graph_delta_l ..) η).trans (rd_graph_sat_l hKP ..)
  have prod (η : Env (rt_model_l X hx) 3) :
      Formula.satisfies η (rd_graph_m .prod (.bound 2) (.bound 1) (.bound 2) .newest) ↔
        ∀ t, M.mem t (η.bound 0).val ↔ ∃ x, M.mem x (η.bound 2).val ∧
          ∃ y, M.mem y (η.bound 1).val ∧ KPair_d M t x y := by
    apply ((rt_model_delta_l hX hx (rd_graph_delta_l ..) η).trans (rd_graph_sat_l hKP ..)).trans
    exact forall_congr' fun t => iff_congr Iff.rfl ⟨fun ⟨x, y, hx, hy, h⟩ => ⟨x, hx, y, hy, h⟩,
      fun ⟨x, hx, y, hy, h⟩ => ⟨x, y, hx, hy, h⟩⟩
  have total (η : Env (rt_model_l X hx) 3) :
      Formula.satisfies η (sc_total0_m (.bound 2) (.bound 1) .newest) ↔
        ∀ a, M.mem a (η.bound 2).val → ∃ b, M.mem b (η.bound 1).val ∧ Rd_entry_d a b (η.bound 0).val :=
    (rt_model_delta_l hX hx (sc_total0_delta_l ..) η).trans (sc_total0_sat_l hKP.1 ..)
  have graph (η : Env (rt_model_l X hx) 4) :
      Formula.satisfies η (.conj (fn0_m (.bound 3) (.bound 2) .newest) (Formula.subset .newest (.bound 1))) ↔
        Fn0_d (η.bound 3).val (η.bound 2).val (η.bound 0).val ∧ M.MemberSubset (η.bound 0).val (η.bound 1).val := by
    exact (rt_model_delta_l hX hx (.conj (fn0_delta_l ..) (.atom ..)) η).trans
      ((Formula.satisfies_conj_iff ..).trans (and_congr (fn0_sat_l hKP.1 ..) (Formula.satisfies_subset_iff ..)))
  have fibers (η : Env (rt_model_l X hx) 3) :
      Formula.satisfies η (rd_graph_m .fibers (.bound 2) (.bound 1) (.bound 2) .newest) ↔
        Rd_fun_d .fibers (η.bound 2).val (η.bound 1).val (η.bound 2).val (η.bound 0).val :=
    (rt_model_delta_l hX hx (rd_graph_delta_l ..) η).trans (rd_graph_sat_l hKP ..)
  simp only [sc_algebra_m, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff, Formula.satisfies_exists_iff,
    Formula.satisfies_imp_iff, pair, un, prod, total, graph, fibers]
  exact ⟨fun ⟨⟨hp, hu, hm, hc⟩, hf⟩ => ⟨fun a b ha hb => (hp ⟨a, ha⟩ ⟨b, hb⟩).elim fun p h => ⟨p.val, p.property, h⟩,
    fun a ha => (hu ⟨a, ha⟩).elim fun p h => ⟨p.val, p.property, h⟩,
    fun a b ha hb => (hm ⟨a, ha⟩ ⟨b, hb⟩).elim fun p h => ⟨p.val, p.property, h⟩,
    fun A B R ha hb hr ht => (hc ⟨A, ha⟩ ⟨B, hb⟩ ⟨R, hr⟩ ht).elim fun f h => ⟨f.val, f.property, h⟩,
    fun R B hr hb => (hf ⟨R, hr⟩ ⟨B, hb⟩).elim fun t ht => ⟨t.val, t.property, ht⟩⟩,
    fun h => ⟨⟨fun a b => (h.pair a.val b.val a.property b.property).elim fun p hp => ⟨⟨p, hp.1⟩, hp.2⟩,
      fun a => (h.union a.val a.property).elim fun p hp => ⟨⟨p, hp.1⟩, hp.2⟩,
      fun a b => (h.product a.val b.val a.property b.property).elim fun p hp => ⟨⟨p, hp.1⟩, hp.2⟩,
      fun A B R ht => (h.choice A.val B.val R.val A.property B.property R.property ht).elim fun f hf => ⟨⟨f, hf.1⟩, hf.2⟩⟩,
      fun R B => (h.fibers R.val B.val R.property B.property).elim fun t ht => ⟨⟨t, ht.1⟩, ht.2⟩⟩⟩

theorem sc_choice_graph_l (hZFC : M.Models ZFC) {A B R : M.Domain}
    (ht : ∀ a, M.mem a A → ∃ b, M.mem b B ∧ Rd_entry_d a b R) :
    ∃ f, Fn0_d A B f ∧ M.MemberSubset f R := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  let φ : BinarySchema 1 := { body := rd_entry0_m (.bound 1) .newest (.bound 2) }
  let ρ : Env M 1 := ⟨fun _ => R, fun _ => R⟩
  have sat a b : φ.denote ρ a b ↔ Rd_entry_d a b R := rd_entry0_sat_l hZF.1 ..
  obtain ⟨f, hf, select⟩ := ZFC.uniformize_formula_l I hZFC φ ρ (fun a ha =>
    (ht a ha).imp fun b hb => ⟨hb.1, (sat a b).mpr hb.2⟩)
  refine ⟨f, fn0_of_function_l (ZF.modelsKP hZF) hf, fun p hp => ?_⟩
  obtain ⟨a, b, code⟩ := hf.1.1 p hp
  obtain ⟨q, hq, hqR⟩ := (sat a b).mp (select a b ⟨p, code, hp⟩)
  exact kpair_unique_l M hZF.1 hq code ▸ hqR

theorem sc_v_algebra_l (hZFC : M.Models ZFC) {δ X : M.Domain} (hδ : M.IsLimitOrdinal δ)
    (hX : V_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) δ X) : Sc_algebra_d X := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨Y, hY, hAY, hBY⟩ := ZF.v_joint_bound_l I hZF hX ha hb
    obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF Y
    obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) a b
    exact ⟨p, ZF.v_subset_mem_l I hZF hX (ZF.v_power_mem_l I hZF hX hδ hY hP)
      (fun t ht => ((hp t).mp ht).elim (fun e => e ▸ (hP a).mpr hAY) (fun e => e ▸ (hP b).mpr hBY)), hp⟩
  · intro a ha
    obtain ⟨β, Y, hβ, hY, hAY⟩ := (ZF.v_unfold_l I hZF hX a).mp ha
    obtain ⟨p, hp⟩ := KP.exists_union (ZF.modelsKP hZF) a
    exact ⟨p, ZF.v_subset_mem_l I hZF hX (ZF.v_mem_l I hZF hY hX hβ) (fun t ht =>
      ((hp t).mp ht).elim fun b hb => ZF.v_transitive_l I hZF hY b (hAY b hb.1) t hb.2), hp⟩
  · intro a b ha hb
    obtain ⟨p, hp⟩ := ZF.exists_cartesianProduct hZF I a b
    exact ⟨p, ZF.v_product_mem_l I hZF hX hδ ha hb hp, hp⟩
  · intro A B R _ _ hr ht
    obtain ⟨f, hf, sub⟩ := sc_choice_graph_l hZFC ht
    exact ⟨f, ZF.v_subset_mem_l I hZF hX hr sub, hf, sub⟩
  · intro R B hr _
    obtain ⟨T, ht⟩ := rd_fibers_exists_l (ZF.modelsKP hZF) R B
    exact ⟨T, ZF.v_fibers_mem_l I hZF hX hδ hr ht, ht⟩

theorem sc_h_algebra_l (hZFC : M.Models ZFC) {ω χ X : M.Domain} (hω : M.IsOmega ω)
    (hχ : M.IsRegularCardinal (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ) (hωχ : M.mem ω χ)
    (hX : H_d (kp_pair_l (ZF.modelsKP (ZFC.models_zf_l hZFC))) χ X) : Sc_algebra_d X := by
  let hZF := ZFC.models_zf_l hZFC
  let I := kp_pair_l (ZF.modelsKP hZF)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨p, hp⟩ := KP.exists_pair (ZF.modelsKP hZF) a b
    exact ⟨p, ZFC.h_pair_l hZFC hω hχ hωχ hX hp ha hb, hp⟩
  · intro a ha
    obtain ⟨T, μ, hT, hμ, size⟩ := (hX a).mp ha
    obtain ⟨p, hp⟩ := KP.exists_union (ZF.modelsKP hZF) a
    exact ⟨p, (hX p).mpr (ZF.hmem_of_subset_l I hZF hχ.isLimitOrdinal hT.1 (fun t ht =>
      ((hp t).mp ht).elim fun b hb => hT.1 b (hT.1 a hT.2.1 b hb.1) t hb.2) hμ size), hp⟩
  · intro a b ha hb
    obtain ⟨p, hp⟩ := ZF.exists_cartesianProduct hZF I a b
    exact ⟨p, ZFC.h_product_l hZFC hω hχ hωχ hX ha hb hp, hp⟩
  · intro A B R _ _ hr ht
    obtain ⟨f, hf, sub⟩ := sc_choice_graph_l hZFC ht
    exact ⟨f, ZF.h_subsets_l I hZF hχ.isLimitOrdinal hX hr f sub, hf, sub⟩
  · intro R B hr hb
    obtain ⟨T, ht⟩ := rd_fibers_exists_l (ZF.modelsKP hZF) R B
    exact ⟨T, ZFC.h_fibers_l hZFC hω hχ hωχ hX hr hb ht, ht⟩

theorem Sc_algebra_d.kpair_l {X a b : M.Domain} (h : Sc_algebra_d X) (ha : M.mem a X) (hb : M.mem b X) :
    ∃ p, M.mem p X ∧ KPair_d M p a b := by
  obtain ⟨s, hsX, hs⟩ := h.pair a a ha ha
  obtain ⟨t, htX, ht⟩ := h.pair a b ha hb
  obtain ⟨p, hpX, hp⟩ := h.pair s t hsX htX
  exact ⟨p, hpX, s, t, (fun x => (hs x).trans ⟨fun hx => hx.elim id id, Or.inl⟩), ht, hp⟩

theorem Sc_algebra_d.insert_l {X A a : M.Domain} (h : Sc_algebra_d X) (hA : M.mem A X) (ha : M.mem a X) :
    ∃ B, M.mem B X ∧ ∀ x, M.mem x B ↔ M.mem x A ∨ x = a := by
  obtain ⟨S, hS, hs⟩ := h.pair a a ha ha
  obtain ⟨P, hP, hp⟩ := h.pair A S hA hS
  obtain ⟨B, hB, hb⟩ := h.union P hP
  refine ⟨B, hB, fun x => (hb x).trans ⟨?_, ?_⟩⟩
  · rintro ⟨t, ht, hx⟩
    rcases (hp t).mp ht with rfl | rfl
    · exact Or.inl hx
    · exact Or.inr (((hs x).mp hx).elim id id)
  · rintro (hx | rfl)
    · exact ⟨A, (hp A).mpr (Or.inl rfl), hx⟩
    · exact ⟨S, (hp S).mpr (Or.inr rfl), (hs x).mpr (Or.inl rfl)⟩

/-- 两次并给出已有图的坐标界，无须对其定义域使用无界收集。 -/
theorem Sc_algebra_d.envelope_l {X F : M.Domain} (h : Sc_algebra_d X) (hf : M.mem F X) :
    ∃ B, M.mem B X ∧ ∀ a b, Rd_entry_d a b F → M.mem a B ∧ M.mem b B := by
  obtain ⟨A, hA, ha⟩ := h.union F hf
  obtain ⟨B, hB, hb⟩ := h.union A hA
  refine ⟨B, hB, fun a b ⟨p, hp, hpf⟩ => ?_⟩
  have contains x (hx : x = a ∨ x = b) : M.mem x B := by
    obtain ⟨t, ht, hx⟩ := (kpair_union_l M hp x).mpr hx
    exact (hb x).mpr ⟨t, (ha t).mpr ⟨p, hpf, ht⟩, hx⟩
  exact ⟨contains a (Or.inl rfl), contains b (Or.inr rfl)⟩

theorem sc_algebra_iff_l {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hZF : M.Models ZF) {ω c d X R Y S q : M.Domain}
    (hω : M.IsOmega ω) (hX : M.TransitiveSet X) (hY : M.TransitiveSet Y)
    (hm : Smem_d I c X R) (hn : Smem_d I d Y S)
    (hq : Smap_d I ω c d X Y q) : Sc_algebra_d X ↔ Sc_algebra_d Y := by
  obtain ⟨x, hx⟩ := hm.1.2.1
  obtain ⟨y, hy⟩ := hn.1.2.1
  let nx : Nonempty {a // M.mem a X} := ⟨⟨x, hx⟩⟩
  let ny : Nonempty {a // M.mem a Y} := ⟨⟨y, hy⟩⟩
  let ρ : Env (rt_model_l X nx) 0 := ⟨Fin.elim0, fun _ => ⟨x, hx⟩⟩
  let η : Env (rt_model_l Y ny) 0 := ⟨Fin.elim0, fun _ => ⟨y, hy⟩⟩
  obtain ⟨e, he⟩ := KP.exists_empty (ZF.modelsKP hZF)
  have tr := spred_source_l _ hZF hω ⟨c, R, d, S, hm.empty_pred_l _ he, hn.empty_pred_l _ he, hq⟩ nx ny
    sc_algebra_m (by simp -implicitDefEqProofs [sc_algebra_m, Definitional.Formula.FreeClosed]) ρ η (fun i => Fin.elim0 i)
  exact (sc_algebra_sat_l (ZF.modelsKP hZF) hX nx ρ).symm.trans (tr.trans (sc_algebra_sat_l (ZF.modelsKP hZF) hY ny η))

end YesMetaZFC.SetTheory.Internal
