import YesMetaZFC.Model.Forcing.InternalCheckVal

/-! # 从原 ZF 公理取得规范名称递归

收集、分离及替换均使用下面写出的实际 Project 公式。调用端只传原 ZF 模型，
不必额外提供递归存在性、闭包或函数性证书。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u v
variable (M : SetTheory.Structure.{u})

private def cover_m {n} (b x F : Term n) : Formula 1 n :=
  .conj (check_graph_m b F) (.existsE (entry_m x.weaken .newest F.weaken))

derive_free_closed cover_m

private def weight_m {n} (b F y p : Term n) : Formula 1 n :=
  .existsE (.conj (entry_m y.weaken .newest F.weaken) (kpair_m p.weaken .newest b.weaken))

derive_free_closed weight_m

private theorem cover_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b x F : Term n) :
    Formula.satisfies ρ (cover_m b x F) ↔
      Check_graph_d M (b.eval ρ) (F.eval ρ) ∧ ∃ t, Entry_d M (x.eval ρ) t (F.eval ρ) := by
  simp only [cover_m, Formula.satisfies_conj_iff, Formula.satisfies_exists_iff,
    check_graph_sat_l M hE, entry_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

private theorem weight_sat_l (hE : Extensional M) {n} (ρ : Env M n) (b F y p : Term n) :
    Formula.satisfies ρ (weight_m b F y p) ↔
      ∃ s, Entry_d M (y.eval ρ) s (F.eval ρ) ∧ KPair_d M (p.eval ρ) s (b.eval ρ) := by
  simp only [weight_m, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, kpair_sat_l M hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

/-- 原 ZF 的具体模式实例实现全部递归操作。 -/
theorem check_ops_l (hZF : M.Models ZF) : Check_ops_d M where
  pair := KP.exists_pair (ZF.modelsKP hZF)
  union := KP.exists_union (ZF.modelsKP hZF)
  collect b x h := by
    let ρ : Env M 1 := ⟨fun _ => b, fun _ => b⟩
    let φ : BinarySchema 1 := { body := cover_m (.bound 2) (.bound 1) (.bound 0) }
    have hφ y F : φ.denote ρ y F ↔ Check_graph_d M b F ∧ ∃ t, Entry_d M y t F :=
      cover_sat_l M hZF.1 ((ρ.push y).push F) (.bound 2) (.bound 1) (.bound 0)
    obtain ⟨T, hT⟩ := ZF.collection_exists_d hZF φ ρ x (fun y hy => by
      obtain ⟨F, hF⟩ := h y hy
      exact ⟨F, (hφ y F).mpr hF⟩)
    let ψ : UnarySchema 1 := { body := check_graph_m (.bound 1) (.bound 0) }
    obtain ⟨C, hC⟩ := ZF.separation_exists_d hZF ψ ρ T
    have hc F : M.mem F C ↔ M.mem F T ∧ Check_graph_d M b F :=
      (hC F).trans (and_congr_right fun _ => check_graph_sat_l M hZF.1 (ρ.push F) (.bound 1) (.bound 0))
    refine ⟨C, fun F hF => ((hc F).mp hF).2, ?_⟩
    intro y hy
    obtain ⟨F, hF, hf⟩ := hT y hy
    obtain ⟨hf, t, ht⟩ := (hφ y F).mp hf
    exact ⟨F, t, (hc F).mpr ⟨hF, hf⟩, ht⟩
  image b F x h hu := by
    let ρ : Env M 2 := (⟨fun _ => b, fun _ => b⟩ : Env M 1).push F
    let φ : BinarySchema 2 := { body := weight_m (.bound 3) (.bound 2) (.bound 1) (.bound 0) }
    have hφ y p : φ.denote ρ y p ↔ ∃ s, Entry_d M y s F ∧ KPair_d M p s b :=
      weight_sat_l M hZF.1 ((ρ.push y).push p) (.bound 3) (.bound 2) (.bound 1) (.bound 0)
    obtain ⟨t, ht⟩ := ZF.exists_functionalImageOn hZF φ ρ x (fun y hy => by
      obtain ⟨s, hs⟩ := h y hy
      obtain ⟨p, hp⟩ := (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))).total s b
      exact ⟨p, (hφ y p).mpr ⟨s, hs, hp⟩⟩) (by
        intro y hy p q hp hq
        obtain ⟨s, hs, hp⟩ := (hφ y p).mp hp
        obtain ⟨t, ht, hq⟩ := (hφ y q).mp hq
        exact kpair_unique_l M hZF.1 ((hu y hy s t hs ht) ▸ hp) hq)
    refine ⟨t, fun p => (ht p).trans ?_⟩
    constructor
    · rintro ⟨y, hy, hp⟩
      obtain ⟨s, hs, hp⟩ := (hφ y p).mp hp
      exact ⟨y, s, hy, hs, hp⟩
    · rintro ⟨y, s, hy, hs, hp⟩
      exact ⟨y, hy, (hφ y p).mpr ⟨s, hs, hp⟩⟩

/-- 有序对右坐标在二重并集中，以实际值域公式分离即可。 -/
theorem check_range_l (hZF : M.Models ZF) (F : M.Domain) :
    ∃ S, ∀ t, M.mem t S ↔ ∃ x, Entry_d M x t F := by
  obtain ⟨A, hA⟩ := KP.exists_union (ZF.modelsKP hZF) F
  obtain ⟨D, hD⟩ := KP.exists_union (ZF.modelsKP hZF) A
  let ρ : Env M 1 := ⟨fun _ => F, fun _ => F⟩
  let φ : UnarySchema 1 := { body := .existsE (entry_m .newest (.bound 1) (.bound 2)) }
  obtain ⟨S, hS⟩ := ZF.separation_exists_d hZF φ ρ D
  have hφ t : φ.denote ρ t ↔ ∃ x, Entry_d M x t F := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, entry_sat_l M hZF.1,
      Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_two_push,
      Term.eval_bound_zero_push]
    rfl
  refine ⟨S, fun t => (hS t).trans ?_⟩
  constructor
  · exact fun h => (hφ t).mp h.2
  · rintro ⟨x, p, hp, hpf⟩
    obtain ⟨v, hv, htv⟩ := (kpair_union_l M hp t).mpr (Or.inr rfl)
    exact ⟨(hD t).mpr ⟨v, (hA v).mpr ⟨p, hpf, hv⟩, htv⟩,
      (hφ t).mpr ⟨x, p, hp, hpf⟩⟩

theorem check_ind_l (hZF : M.Models ZF) : Mem_ind_d M :=
  ZF.mem_ind_l M hZF (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF)))

/-- 一次调用取得规范名称、内部名称证书及唯一性；无需选择一个全局名称函数。 -/
theorem zf_check_l (hZF : M.Models ZF) {B b : M.Domain} (hb : M.mem b B) (x : M.Domain) :
    ∃ t, Check_d M b x t ∧ Name_d M B t ∧ ∀ s, Check_d M b x s → s = t := by
  obtain ⟨t, ht⟩ := check_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF) b x
  exact ⟨t, ht, check_name_l M (check_range_l M hZF) hb ht,
    fun s hs => check_unique_l M hZF.1 (check_ind_l M hZF) b x s t hs ht⟩

/-- 同时构造地模型对象的实际小图解释和内部规范名称，并核验求值还原。 -/
theorem zf_check_val_l (hZF : M.Models ZF) (hM : _root_.WellFounded M.mem)
    (hL : Setlike_d.{u, v} M) {B b : M.Domain} (hb : M.mem b B) (x : M.Domain) :
    ∃ t, Check_d M b x t ∧ Name_d M B t ∧ ∃ y : SmallGraph.SG_set.{v},
      Ground_d M x y ∧ ∀ U : M.Domain → Prop, U b → Val_d M B U t y := by
  obtain ⟨t, ht, hn, _⟩ := zf_check_l M hZF hb x
  obtain ⟨S, hx, hS⟩ := ZF.mem_hull_l M hZF
    (kpair_interpretation_l M hZF.1 (check_ops_l M hZF).pair) x
  obtain ⟨G, hG⟩ := ground_decode_l M hM hL hx hS
  exact ⟨t, ht, hn, SmallGraph.SG_set.mk G, ⟨G, hG, rfl⟩,
    check_val_exists_l M hZF.1 (check_ind_l M hZF) (check_ops_l M hZF).pair
      (check_range_l M hZF) hM hL hb ht ⟨G, hG, rfl⟩⟩

end YesMetaZFC.Model.Forcing.Internal
