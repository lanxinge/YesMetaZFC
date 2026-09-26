import YesMetaZFC.SetTheory.Boolean.Algebra

/-! # 集合编码布尔代数中的滤子与理想

载体、序、顶底与滤子／理想均为内部对象。纯公式及其满足对应可直接用于 ZF
分离；生成构造量化内部子集，不需要枚举生成元或选择有限表示。
-/

namespace YesMetaZFC.SetTheory.BooleanZF
open Definitional.Project FilterZF
universe u
variable {ℳ : Structure.{u}} {𝒞 : OrderedPairConvention}

def Join_d (𝕀 : 𝒞.Interpretation ℳ) (B R a b c : ℳ.Domain) : Prop :=
  ℳ.mem c B ∧ ∀ d, ℳ.mem d B →
    (ℳ.PairMember 𝕀 c d R ↔ ℳ.PairMember 𝕀 a d R ∧ ℳ.PairMember 𝕀 b d R)

def Filter_d (𝕀 : 𝒞.Interpretation ℳ) (B R t F : ℳ.Domain) : Prop :=
  Subset_d (ℳ := ℳ) F B ∧ ℳ.mem t F ∧
  (∀ a b, ℳ.mem a F → ℳ.mem b B → ℳ.PairMember 𝕀 a b R → ℳ.mem b F) ∧
  ∀ a b c, ℳ.mem a F → ℳ.mem b F → Meet_d 𝕀 B R a b c → ℳ.mem c F

def Ideal_d (𝕀 : 𝒞.Interpretation ℳ) (B R z I : ℳ.Domain) : Prop :=
  Subset_d (ℳ := ℳ) I B ∧ ℳ.mem z I ∧
  (∀ a b, ℳ.mem a I → ℳ.mem b B → ℳ.PairMember 𝕀 b a R → ℳ.mem b I) ∧
  ∀ a b c, ℳ.mem a I → ℳ.mem b I → Join_d 𝕀 B R a b c → ℳ.mem c I

def join_m (𝒞 : OrderedPairConvention) {n : Nat} (B R a b c : Term n) : Formula 1 n :=
  .conj (.mem c B) (.forallE (.imp (.mem .newest B.weaken)
    (.iff (Formula.orderedPairMem 𝒞 c.weaken .newest R.weaken)
      (.conj (Formula.orderedPairMem 𝒞 a.weaken .newest R.weaken)
        (Formula.orderedPairMem 𝒞 b.weaken .newest R.weaken)))))

derive_free_closed join_m

theorem join_sat_d (𝕀 : 𝒞.Interpretation ℳ) {n : Nat} (e : Env ℳ n)
    (B R a b c : Term n) : Formula.satisfies e (join_m 𝒞 B R a b c) ↔
      Join_d 𝕀 (B.eval e) (R.eval e) (a.eval e) (b.eval e) (c.eval e) := by
  simp only [join_m, Join_d, Formula.satisfies_conj_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_imp_iff, Formula.satisfies_iff_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_orderedPairMem_iff 𝕀, Definitional.Term.eval_newest,
    Definitional.Term.eval_weaken]

def filter_m (𝒞 : OrderedPairConvention) {n : Nat} (B R t F : Term n) : Formula 1 n :=
  .conj (Formula.subset F B) (.conj (.mem t F) (.conj
    (.forallE (.forallE (.imp (.mem (.bound 1) F.weaken.weaken)
      (.imp (.mem .newest B.weaken.weaken)
        (.imp (Formula.orderedPairMem 𝒞 (.bound 1) .newest R.weaken.weaken)
          (.mem .newest F.weaken.weaken))))))
    (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) F.weaken.weaken.weaken)
      (.imp (.mem (.bound 1) F.weaken.weaken.weaken)
        (.imp (meet_m 𝒞 B.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
          (.mem .newest F.weaken.weaken.weaken)))))))))

derive_free_closed filter_m

def ideal_m (𝒞 : OrderedPairConvention) {n : Nat} (B R z I : Term n) : Formula 1 n :=
  .conj (Formula.subset I B) (.conj (.mem z I) (.conj
    (.forallE (.forallE (.imp (.mem (.bound 1) I.weaken.weaken)
      (.imp (.mem .newest B.weaken.weaken)
        (.imp (Formula.orderedPairMem 𝒞 .newest (.bound 1) R.weaken.weaken)
          (.mem .newest I.weaken.weaken))))))
    (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) I.weaken.weaken.weaken)
      (.imp (.mem (.bound 1) I.weaken.weaken.weaken)
        (.imp (join_m 𝒞 B.weaken.weaken.weaken R.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
          (.mem .newest I.weaken.weaken.weaken)))))))))

derive_free_closed ideal_m

theorem filter_sat_d (𝕀 : 𝒞.Interpretation ℳ) {n : Nat} (e : Env ℳ n)
    (B R t F : Term n) : Formula.satisfies e (filter_m 𝒞 B R t F) ↔
      Filter_d 𝕀 (B.eval e) (R.eval e) (t.eval e) (F.eval e) := by
  simp only [filter_m, Filter_d, Subset_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_orderedPairMem_iff 𝕀, meet_sat_d 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_zero_push]

theorem ideal_sat_d (𝕀 : 𝒞.Interpretation ℳ) {n : Nat} (e : Env ℳ n)
    (B R z I : Term n) : Formula.satisfies e (ideal_m 𝒞 B R z I) ↔
      Ideal_d 𝕀 (B.eval e) (R.eval e) (z.eval e) (I.eval e) := by
  simp only [ideal_m, Ideal_d, Subset_d, Formula.satisfies_conj_iff,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_subset_iff, Formula.satisfies_orderedPairMem_iff 𝕀, join_sat_d 𝕀,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken,
    Term.eval_bound_one_push, Term.eval_bound_two_push, Term.eval_bound_zero_push]

def generated_filter_m (𝒞 : OrderedPairConvention) : UnarySchema 4 where
  body := .forallE (.imp (.conj (filter_m 𝒞 (.bound 5) (.bound 4) (.bound 3) (.bound 0))
    (Formula.subset (.bound 2) (.bound 0))) (.mem (.bound 1) (.bound 0)))

def generated_ideal_m (𝒞 : OrderedPairConvention) : UnarySchema 4 where
  body := .forallE (.imp (.conj (ideal_m 𝒞 (.bound 5) (.bound 4) (.bound 3) (.bound 0))
    (Formula.subset (.bound 2) (.bound 0))) (.mem (.bound 1) (.bound 0)))

theorem generated_filter_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    (B R t S : ℳ.Domain) (ht : ℳ.mem t B) (hS : Subset_d (ℳ := ℳ) S B) :
    ∃ G, Filter_d 𝕀 B R t G ∧ Subset_d (ℳ := ℳ) S G ∧
      ∀ F, Filter_d 𝕀 B R t F → Subset_d (ℳ := ℳ) S F → Subset_d (ℳ := ℳ) G F := by
  let e : Env ℳ 4 := ⟨fun i => if i = 0 then S else if i = 1 then t else
    if i = 2 then R else B, fun _ => B⟩
  obtain ⟨G, hG⟩ := ZF.separation_exists_d hZF (generated_filter_m 𝒞) e B
  have k : ∀ a, ℳ.mem a G ↔ ℳ.mem a B ∧
      ∀ F, Filter_d 𝕀 B R t F → Subset_d (ℳ := ℳ) S F → ℳ.mem a F := by
    intro a
    rw [hG]
    simp only [generated_filter_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, filter_sat_d 𝕀, Formula.satisfies_subset_iff,
      Formula.satisfies_mem_iff, Term.eval_bound, Subset_d, and_imp]
    rfl
  refine ⟨G, ⟨fun a ha => ((k a).mp ha).1, (k t).mpr ⟨ht, fun _ h _ => h.2.1⟩,
    ?_, ?_⟩, fun a ha => (k a).mpr ⟨hS a ha, fun _ _ h => h a ha⟩,
    fun F hF hSF a ha => ((k a).mp ha).2 F hF hSF⟩
  · intro a b ha hb hab
    exact (k b).mpr ⟨hb, fun F hF hSF => hF.2.2.1 a b (((k a).mp ha).2 F hF hSF) hb hab⟩
  · intro a b c ha hb hc
    exact (k c).mpr ⟨hc.1, fun F hF hSF => hF.2.2.2 a b c
      (((k a).mp ha).2 F hF hSF) (((k b).mp hb).2 F hF hSF) hc⟩

theorem generated_ideal_exists_d (𝕀 : 𝒞.Interpretation ℳ) (hZF : ℳ.Models ZF)
    (B R z S : ℳ.Domain) (hz : ℳ.mem z B) (hS : Subset_d (ℳ := ℳ) S B) :
    ∃ G, Ideal_d 𝕀 B R z G ∧ Subset_d (ℳ := ℳ) S G ∧
      ∀ I, Ideal_d 𝕀 B R z I → Subset_d (ℳ := ℳ) S I → Subset_d (ℳ := ℳ) G I := by
  let e : Env ℳ 4 := ⟨fun i => if i = 0 then S else if i = 1 then z else
    if i = 2 then R else B, fun _ => B⟩
  obtain ⟨G, hG⟩ := ZF.separation_exists_d hZF (generated_ideal_m 𝒞) e B
  have k : ∀ a, ℳ.mem a G ↔ ℳ.mem a B ∧
      ∀ I, Ideal_d 𝕀 B R z I → Subset_d (ℳ := ℳ) S I → ℳ.mem a I := by
    intro a
    rw [hG]
    simp only [generated_ideal_m, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_conj_iff, ideal_sat_d 𝕀, Formula.satisfies_subset_iff,
      Formula.satisfies_mem_iff, Term.eval_bound, Subset_d, and_imp]
    rfl
  refine ⟨G, ⟨fun a ha => ((k a).mp ha).1, (k z).mpr ⟨hz, fun _ h _ => h.2.1⟩,
    ?_, ?_⟩, fun a ha => (k a).mpr ⟨hS a ha, fun _ _ h => h a ha⟩,
    fun I hI hSI a ha => ((k a).mp ha).2 I hI hSI⟩
  · intro a b ha hb hab
    exact (k b).mpr ⟨hb, fun I hI hSI => hI.2.2.1 a b (((k a).mp ha).2 I hI hSI) hb hab⟩
  · intro a b c ha hb hc
    exact (k c).mpr ⟨hc.1, fun I hI hSI => hI.2.2.2 a b c
      (((k a).mp ha).2 I hI hSI) (((k b).mp hb).2 I hI hSI) hc⟩

end YesMetaZFC.SetTheory.BooleanZF
