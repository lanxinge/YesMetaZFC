import YesMetaZFC.SetTheory.InnerModel.OD.Minimum

/-! # 最小序数代表导出的 OD 全局良序

比较各对象的最小代码；每个非空 OD 集合有最小元，严格初段由有界代码的
实际像集得到。该定义在背景模型中计算，不声称 HOD 内部重算得到同一关系。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Od_lt_d (x y : M.Domain) : Prop := ∃ q r, Od_min_d I q x ∧ Od_min_d I r y ∧ M.mem q r

def od_lt_m {d} (x y : Term d) : Formula 1 d := .existsE (.existsE
  (.conj (od_min_m (𝒞 := 𝒞) (.bound 1) x.weaken.weaken)
    (.conj (od_min_m (𝒞 := 𝒞) .newest y.weaken.weaken) (.mem (.bound 1) .newest))))
derive_free_closed od_lt_m

theorem od_lt_sat_l (hE : Extensional M) {d} (ρ : Env M d) (x y : Term d) :
    Formula.satisfies ρ (od_lt_m (𝒞 := 𝒞) x y) ↔ Od_lt_d I (x.eval ρ) (y.eval ρ) := by
  simp only [od_lt_m, Od_lt_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    od_min_sat_l I hE, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem od_lt_irrefl_l (hZF : M.Models ZF) (x : M.Domain) : ¬ Od_lt_d I x x := by
  rintro ⟨q, r, hq, hr, hqr⟩
  have eq := od_min_unique_l I hZF hq hr; subst r
  exact KP.mem_irrefl_d (ZF.modelsKP hZF) q hqr

theorem od_lt_trans_l (hZF : M.Models ZF) {x y z}
    (h : Od_lt_d I x y) (g : Od_lt_d I y z) : Od_lt_d I x z := by
  obtain ⟨q, r, hq, hr, hqr⟩ := h
  obtain ⟨s, t, hs, ht, hst⟩ := g
  have eq := od_min_unique_l I hZF hr hs; subst s
  exact ⟨q, t, hq, ht, (od_eval_ordinal_l I hZF ht.1).transitive r hst q hqr⟩

theorem od_lt_compare_l (hZF : M.Models ZF) {x y : M.Domain} (hx : Od_d x) (hy : Od_d y) :
    x = y ∨ Od_lt_d I x y ∨ Od_lt_d I y x := by
  obtain ⟨q, hq⟩ := od_min_exists_l I hZF hx
  obtain ⟨r, hr⟩ := od_min_exists_l I hZF hy
  rcases (od_eval_ordinal_l I hZF hq.1).trichotomy hZF.1 (od_eval_ordinal_l I hZF hr.1)
    (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) q r) with he | hqr | hrq
  · have eq := hZF.1.eq_of_same_members q r he; subst r
    exact Or.inl (od_min_injective_l I hZF hq hr)
  · exact Or.inr (Or.inl ⟨q, r, hq, hr, hqr⟩)
  · exact Or.inr (Or.inr ⟨r, q, hr, hq, hrq⟩)

theorem od_lt_least_l (hZF : M.Models ZF) {A : M.Domain}
    (hA : ∀ x, M.mem x A → Od_d x) (hn : ∃ x, M.mem x A) :
    ∃ x, M.mem x A ∧ ∀ y, M.mem y A → x = y ∨ Od_lt_d I x y := by
  obtain ⟨x, hx, q, hq, hm⟩ := od_pick_exists_l I hZF (hn.imp fun x hx => ⟨hx, hA x hx⟩)
  have hmin : Od_min_d I q x := ⟨hq, fun r hr he => hm r hr x hx he⟩
  refine ⟨x, hx, fun y hy => ?_⟩
  obtain ⟨r, hr⟩ := od_min_exists_l I hZF (hA y hy)
  rcases (od_eval_ordinal_l I hZF hq).trichotomy hZF.1 (od_eval_ordinal_l I hZF hr.1)
    (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) q r) with he | hqr | hrq
  · have eq := hZF.1.eq_of_same_members q r he; subst r
    exact Or.inl (od_min_injective_l I hZF hmin hr)
  · exact Or.inr ⟨q, r, hmin, hr, hqr⟩
  · exact (hm r hrq y hy hr.1).elim

/-- 初段是小于当前最小代码的合法最小代码之像，故在背景模型中是集合。 -/
theorem od_lt_initial_l (hZF : M.Models ZF) {x : M.Domain} (hx : Od_d x) :
    ∃ A, ∀ y, M.mem y A ↔ Od_lt_d I y x := by
  obtain ⟨q, hq⟩ := od_min_exists_l I hZF hx
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => q⟩
  let φ : BinarySchema 0 := { body := od_min_m (𝒞 := 𝒞) (.bound 1) .newest }
  let ψ : UnarySchema 0 := { body := .existsE (od_min_m (𝒞 := 𝒞) (.bound 1) .newest) }
  have sat r y : φ.denote ρ r y ↔ Od_min_d I r y := od_min_sat_l I hZF.1 _ _ _
  obtain ⟨D, hD'⟩ := ZF.separation_exists_d hZF ψ ρ q
  have hD r : M.mem r D ↔ M.mem r q ∧ ∃ y, Od_min_d I r y := by
    simpa only [ψ, Formula.satisfies_exists_iff, od_min_sat_l I hZF.1,
      Definitional.Term.eval_newest, Term.eval_bound_one_push, Term.eval_bound_zero_push] using hD' r
  obtain ⟨A, hA⟩ := ZF.exists_functionalImageOn hZF φ ρ D
    (fun r hr => ((hD r).mp hr).2.imp fun y hy => (sat r y).mpr hy)
    (fun _ _ _ _ h g => od_min_injective_l I hZF ((sat _ _).mp h) ((sat _ _).mp g))
  refine ⟨A, fun y => (hA y).trans ?_⟩
  constructor
  · rintro ⟨r, hr, hy⟩
    exact ⟨r, q, (sat r y).mp hy, hq, ((hD r).mp hr).1⟩
  · rintro ⟨r, t, hr, ht, hrt⟩
    have eq := od_min_unique_l I hZF ht hq; subst t
    exact ⟨r, (hD r).mpr ⟨hrt, y, hr⟩, (sat r y).mpr hr⟩

end YesMetaZFC.SetTheory.InnerModel
