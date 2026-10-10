import YesMetaZFC.SetTheory.SetConstruction
import YesMetaZFC.SetTheory.Separation

/-! # ZF 模型内部的集合滤子

载体、滤子和生成族均为模型中的集合。闭包只量化内部子集；分离始终应用于
下方实际给出的纯集合论公式，不要求模型外部标准、良基或具有全部外部子集。
构造结果使用存在量词，不借选择把存在性转换成返回模型对象的函数。
-/

namespace YesMetaZFC.SetTheory.FilterZF
open Definitional.Project
universe u
variable {ℳ : Structure.{u}}

def Subset_d (A B : ℳ.Domain) : Prop := ∀ x, ℳ.mem x A → ℳ.mem x B

/-- 有限交封闭采用共同细化表述；在 ZF 中等价于通常的交集封闭。 -/
def IsFilter_d (A F : ℳ.Domain) : Prop :=
  (∀ s, ℳ.mem s F → Subset_d (ℳ := ℳ) s A) ∧ ℳ.mem A F ∧
  (∀ s t, ℳ.mem s F → Subset_d (ℳ := ℳ) s t → Subset_d (ℳ := ℳ) t A → ℳ.mem t F) ∧
  ∀ s t, ℳ.mem s F → ℳ.mem t F →
    ∃ r, ℳ.mem r F ∧ Subset_d (ℳ := ℳ) r s ∧ Subset_d (ℳ := ℳ) r t

def Proper_d (F : ℳ.Domain) : Prop := ∀ s, ℳ.mem s F → ∃ x, ℳ.mem x s

def Maximal_d (A F : ℳ.Domain) : Prop :=
  IsFilter_d (ℳ := ℳ) A F ∧ Proper_d (ℳ := ℳ) F ∧
  ∀ G, IsFilter_d (ℳ := ℳ) A G → Proper_d (ℳ := ℳ) G →
    Subset_d (ℳ := ℳ) F G → Subset_d (ℳ := ℳ) G F

def filter_m {n : Nat} (A F : Term n) : Formula 1 n :=
  .conj (.forallE (.imp (.mem .newest F.weaken) (Formula.subset .newest A.weaken))) <|
  .conj (.mem A F) <|
  .conj (.forallE (.forallE (.imp (.mem (.bound 1) F.weaken.weaken)
    (.imp (Formula.subset (.bound 1) .newest)
      (.imp (Formula.subset .newest A.weaken.weaken) (.mem .newest F.weaken.weaken)))))) <|
  .forallE (.forallE (.imp (.mem (.bound 1) F.weaken.weaken)
    (.imp (.mem .newest F.weaken.weaken)
      (.existsE (.conj (.mem .newest F.weaken.weaken.weaken)
        (.conj (Formula.subset .newest (.bound 2)) (Formula.subset .newest (.bound 1))))))))

derive_free_closed filter_m

def proper_m {n : Nat} (F : Term n) : Formula 1 n :=
  .forallE (.imp (.mem .newest F.weaken) (.existsE (.mem .newest (.bound 1))))

derive_free_closed proper_m

theorem filter_sat_d {n : Nat} (e : Env ℳ n) (A F : Term n) :
    Formula.satisfies e (filter_m A F) ↔ IsFilter_d (A.eval e) (F.eval e) := by
  simp only [filter_m, IsFilter_d, Subset_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_exists_iff, Formula.satisfies_imp_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_subset_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_zero_push]

theorem proper_sat_d {n : Nat} (e : Env ℳ n) (F : Term n) :
    Formula.satisfies e (proper_m F) ↔ Proper_d (F.eval e) := by
  simp only [proper_m, Proper_d, Formula.satisfies_forall_iff,
    Formula.satisfies_exists_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_zero_push]

def principal_m : UnarySchema 1 where
  body := Formula.subset (.bound 1) (.bound 0)

/-- 主滤子作为内部幂集的可分离子集存在。 -/
theorem principal_exists_d (hZF : ℳ.Models ZF) (A B : ℳ.Domain)
    (h : Subset_d (ℳ := ℳ) B A) :
    ∃ F, IsFilter_d (ℳ := ℳ) A F ∧
      ∀ s, ℳ.mem s F ↔ Subset_d (ℳ := ℳ) s A ∧ Subset_d (ℳ := ℳ) B s := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  let e : Env ℳ 1 := ⟨fun _ => B, fun _ => A⟩
  obtain ⟨F, hF⟩ := ZF.separation_exists_d hZF principal_m e P
  have k : ∀ s, ℳ.mem s F ↔ Subset_d (ℳ := ℳ) s A ∧ Subset_d (ℳ := ℳ) B s := by
    intro s
    rw [hF, hP]
    simp only [principal_m, Formula.satisfies_subset_iff, Term.eval_bound, Subset_d]
    rfl
  refine ⟨F, ⟨fun s hs => ((k s).mp hs).1, (k A).mpr ⟨fun _ hx => hx, h⟩,
    ?_, ?_⟩, k⟩
  · intro s t hs hst ht
    exact (k t).mpr ⟨ht, fun x hx => hst x (((k s).mp hs).2 x hx)⟩
  · intro s t hs ht
    exact ⟨B, (k B).mpr ⟨h, fun _ hx => hx⟩, ((k s).mp hs).2, ((k t).mp ht).2⟩

theorem principal_proper_d {A B F : ℳ.Domain}
    (h : ∀ s, ℳ.mem s F ↔ Subset_d (ℳ := ℳ) s A ∧ Subset_d (ℳ := ℳ) B s)
    (k : Subset_d (ℳ := ℳ) B A) : Proper_d (ℳ := ℳ) F ↔ ∃ x, ℳ.mem x B := by
  constructor
  · intro hF
    exact hF B ((h B).mpr ⟨k, fun _ hx => hx⟩)
  · rintro ⟨x, hx⟩ s hs
    exact ⟨x, ((h s).mp hs).2 x hx⟩

/-- 内部交集存在时，共同细化与向上封闭给出交集封闭。 -/
theorem inter_mem_d {A F s t r : ℳ.Domain} (hF : IsFilter_d (ℳ := ℳ) A F)
    (hs : ℳ.mem s F) (ht : ℳ.mem t F)
    (hr : ∀ x, ℳ.mem x r ↔ ℳ.mem x s ∧ ℳ.mem x t) : ℳ.mem r F := by
  obtain ⟨q, hq, hqs, hqt⟩ := hF.2.2.2 s t hs ht
  exact hF.2.2.1 q r hq (fun x hx => (hr x).mpr ⟨hqs x hx, hqt x hx⟩)
    (fun x hx => hF.1 s hs x ((hr x).mp hx).1)

def generated_m : UnarySchema 2 where
  body := .forallE (.imp (.conj (filter_m (.bound 3) (.bound 0))
    (Formula.subset (.bound 2) (.bound 0))) (.mem (.bound 1) (.bound 0)))

/-- 生成滤子由所有内部扩张滤子的交定义，覆盖任意内部生成族。 -/
theorem generated_exists_d (hZF : ℳ.Models ZF) (A S : ℳ.Domain)
    (hS : ∀ s, ℳ.mem s S → Subset_d (ℳ := ℳ) s A) :
    ∃ G, IsFilter_d (ℳ := ℳ) A G ∧ Subset_d (ℳ := ℳ) S G ∧
      ∀ F, IsFilter_d (ℳ := ℳ) A F → Subset_d (ℳ := ℳ) S F → Subset_d (ℳ := ℳ) G F := by
  obtain ⟨P, hP⟩ := ZF.exists_powerSet hZF A
  let e : Env ℳ 2 := ⟨fun i => if i = 0 then S else A, fun _ => A⟩
  obtain ⟨G, hG⟩ := ZF.separation_exists_d hZF generated_m e P
  have k : ∀ s, ℳ.mem s G ↔ Subset_d (ℳ := ℳ) s A ∧
      ∀ F, IsFilter_d (ℳ := ℳ) A F → Subset_d (ℳ := ℳ) S F → ℳ.mem s F := by
    intro s
    rw [hG, hP]
    simp only [generated_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, filter_sat_d, Formula.satisfies_subset_iff,
      Formula.satisfies_mem_iff, Term.eval_bound, Subset_d, and_imp]
    rfl
  refine ⟨G, ⟨fun s hs => ((k s).mp hs).1, (k A).mpr ⟨fun _ hx => hx,
    fun _ hF _ => hF.2.1⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro s t hs hst ht
    exact (k t).mpr ⟨ht, fun F hF hSF =>
      hF.2.2.1 s t (((k s).mp hs).2 F hF hSF) hst ht⟩
  · intro s t hs ht
    obtain ⟨r, hr⟩ := KP.intersection_exists_d (ZF.modelsKP hZF) s t
    refine ⟨r, (k r).mpr ⟨fun x hx => ((k s).mp hs).1 x ((hr x).mp hx).1,
      fun F hF hSF => inter_mem_d hF (((k s).mp hs).2 F hF hSF)
        (((k t).mp ht).2 F hF hSF) hr⟩,
      fun x hx => ((hr x).mp hx).1, fun x hx => ((hr x).mp hx).2⟩
  · intro s hs
    exact (k s).mpr ⟨hS s hs, fun F _ hSF => hSF s hs⟩
  · intro F hF hSF s hs
    exact ((k s).mp hs).2 F hF hSF

/-- 生成滤子的适当性精确等价于存在适当的内部扩张。 -/
theorem generated_proper_d {A S G : ℳ.Domain} (hG : IsFilter_d (ℳ := ℳ) A G)
    (hSG : Subset_d (ℳ := ℳ) S G)
    (h : ∀ F, IsFilter_d (ℳ := ℳ) A F → Subset_d (ℳ := ℳ) S F → Subset_d (ℳ := ℳ) G F) :
    Proper_d (ℳ := ℳ) G ↔ ∃ F, IsFilter_d (ℳ := ℳ) A F ∧
      Proper_d (ℳ := ℳ) F ∧ Subset_d (ℳ := ℳ) S F :=
  ⟨fun k => ⟨G, hG, k, hSG⟩, fun ⟨F, hF, k, hSF⟩ s hs => k s (h F hF hSF s hs)⟩

end YesMetaZFC.SetTheory.FilterZF
