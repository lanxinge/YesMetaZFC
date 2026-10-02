import YesMetaZFC.SetTheory.InnerModel.OD.Definition
import YesMetaZFC.SetTheory.Ord.DefinableMinimum

/-! # OD 对象的唯一最小序数代表与规范选择

最小性沿原来的单序数解码关系定义。最小元来自内部序数类分离，允许背景
模型外部非良基；这里不把内部序数类换成宿主良序。
-/
namespace YesMetaZFC.SetTheory.InnerModel
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Od_min_d (q x : M.Domain) : Prop := Od_eval_d I q x ∧ ∀ r, M.mem r q → ¬ Od_eval_d I r x

def od_min_m {d} (q x : Term d) : Formula 1 d := .conj (od_eval_m (𝒞 := 𝒞) q x)
  (Formula.forallMem q (.neg (od_eval_m (𝒞 := 𝒞) .newest x.weaken)))
derive_free_closed od_min_m

theorem od_min_sat_l (hE : Extensional M) {d} (ρ : Env M d) (q x : Term d) :
    Formula.satisfies ρ (od_min_m (𝒞 := 𝒞) q x) ↔ Od_min_d I (q.eval ρ) (x.eval ρ) := by
  simp only [od_min_m, Od_min_d, Formula.satisfies_conj_iff, od_eval_sat_l I hE,
    Formula.satisfies_forallMem_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
  rfl

theorem od_min_exists_l (hZF : M.Models ZF) {x : M.Domain} (hx : Od_d x) : ∃ q, Od_min_d I q x := by
  obtain ⟨a, ha⟩ := (od_code_range_l I hZF).mp hx
  let φ : UnarySchema 1 := { body := od_eval_m (𝒞 := 𝒞) .newest (.bound 1) }
  let ρ : Env M 1 := ⟨fun _ => x, fun _ => x⟩
  have sat q : φ.denote ρ q ↔ Od_eval_d I q x := od_eval_sat_l I hZF.1 _ _ _
  obtain ⟨q, _, hq, hm⟩ := ZF.ordinal_min_l hZF φ ρ (od_eval_ordinal_l I hZF ha) ((sat a).mpr ha)
  exact ⟨q, (sat q).mp hq, fun r hr he => hm r hr ((sat r).mpr he)⟩

theorem od_min_unique_l (hZF : M.Models ZF) {q r x}
    (h : Od_min_d I q x) (g : Od_min_d I r x) : q = r := by
  rcases (od_eval_ordinal_l I hZF h.1).trichotomy hZF.1 (od_eval_ordinal_l I hZF g.1)
    (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) q r) with he | hqr | hrq
  · exact hZF.1.eq_of_same_members q r he
  · exact (g.2 q hqr h.1).elim
  · exact (h.2 r hrq g.1).elim

theorem od_min_injective_l (hZF : M.Models ZF) {q x y}
    (h : Od_min_d I q x) (g : Od_min_d I q y) : x = y := od_eval_unique_l I hZF h.1 g.1

def Od_pick_d (A x : M.Domain) : Prop := M.mem x A ∧ ∃ q, Od_eval_d I q x ∧
  ∀ r, M.mem r q → ∀ y, M.mem y A → ¬ Od_eval_d I r y

def od_pick_m {d} (A x : Term d) : Formula 1 d := .conj (.mem x A) (.existsE
  (.conj (od_eval_m (𝒞 := 𝒞) .newest x.weaken) (Formula.forallMem .newest
    (Formula.forallMem A.weaken.weaken (.neg (od_eval_m (𝒞 := 𝒞) (.bound 1) .newest))))))
derive_free_closed od_pick_m

theorem od_pick_sat_l (hE : Extensional M) {d} (ρ : Env M d) (A x : Term d) :
    Formula.satisfies ρ (od_pick_m (𝒞 := 𝒞) A x) ↔ Od_pick_d I (A.eval ρ) (x.eval ρ) := by
  simp only [od_pick_m, Od_pick_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, od_eval_sat_l I hE, Formula.satisfies_forallMem_iff,
    Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]
  rfl

/-- 一个集合只要含有 OD 元素，就有规范选择值。 -/
theorem od_pick_exists_l (hZF : M.Models ZF) {A : M.Domain} (hn : ∃ x, M.mem x A ∧ Od_d x) :
    ∃ x, Od_pick_d I A x := by
  obtain ⟨x, hx, hOD⟩ := hn
  obtain ⟨q, hq⟩ := (od_code_range_l I hZF).mp hOD
  let φ : UnarySchema 1 := {
    body := Formula.existsMem (.bound 1)
      (od_eval_m (𝒞 := 𝒞) (.bound 1) .newest) }
  let ρ : Env M 1 := ⟨fun _ => A, fun _ => A⟩
  have sat r : φ.denote ρ r ↔ ∃ y, M.mem y A ∧ Od_eval_d I r y := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_existsMem_iff, od_eval_sat_l I hZF.1]
    rfl
  obtain ⟨r, _, hr, hm⟩ := ZF.ordinal_min_l hZF φ ρ (od_eval_ordinal_l I hZF hq) ((sat q).mpr ⟨x, hx, hq⟩)
  obtain ⟨y, hy, he⟩ := (sat r).mp hr
  exact ⟨y, hy, r, he, fun s hs z hz hh => hm s hs ((sat s).mpr ⟨z, hz, hh⟩)⟩

theorem od_pick_unique_l (hZF : M.Models ZF) {A x y}
    (h : Od_pick_d I A x) (g : Od_pick_d I A y) : x = y := by
  obtain ⟨hx, q, hq, hmin⟩ := h
  obtain ⟨hy, r, hr, hmin'⟩ := g
  rcases (od_eval_ordinal_l I hZF hq).trichotomy hZF.1 (od_eval_ordinal_l I hZF hr)
    (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) q r) with he | hqr | hrq
  · have eq := hZF.1.eq_of_same_members q r he; subst r
    exact od_eval_unique_l I hZF hq hr
  · exact (hmin' q hqr x hx hq).elim
  · exact (hmin r hrq y hy hr).elim

end YesMetaZFC.SetTheory.InnerModel
