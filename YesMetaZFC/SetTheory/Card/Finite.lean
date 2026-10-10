import YesMetaZFC.SetTheory.Card.Omega

/-! # 模型内部的有限集合与删除归纳

有限性由模型内向某个 n∈ω 的集合编码单射见证。删除一个元素时，将末位移到被删
元素的位置，得到严格减小的界；因此插入归纳只需模型自己的自然数归纳。
-/

namespace YesMetaZFC.SetTheory
open Definitional.Project
universe u

def Finite_d {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (ω X : M.Domain) : Prop := ∃ n, M.mem n ω ∧ M.CardinalLessOrEqual I X n

def finite_m (𝒞 : OrderedPairConvention) {n} (ω X : Term n) : Formula 1 n :=
  .existsE (.conj (.mem .newest ω.weaken) (Formula.cardinalLessOrEqual 𝒞 X.weaken .newest))
derive_free_closed finite_m

theorem finite_sat_l {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)
    (hE : Extensional M) {n} (ρ : Env M n) (ω X : Term n) :
    Formula.satisfies ρ (finite_m 𝒞 ω X) ↔ Finite_d I (ω.eval ρ) (X.eval ρ) := by
  simp only [finite_m, Finite_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_cardinalLessOrEqual_iff I hE,
    Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

namespace ZF
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M) (hZF : M.Models ZF)
include hZF

def erase_m {n} (a X Y : Term n) : Formula 1 n :=
  .forallE (.iff (.mem .newest Y.weaken) (.conj (.mem .newest X.weaken)
    (.neg (Formula.extensionalEq .newest a.weaken))))
derive_free_closed erase_m

theorem erase_sat_l {n} (ρ : Env M n) (a X Y : Term n) :
    Formula.satisfies ρ (erase_m a X Y) ↔
      ∀ x, M.mem x (Y.eval ρ) ↔ M.mem x (X.eval ρ) ∧ x ≠ a.eval ρ := by
  simp only [erase_m, Formula.satisfies_forall_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq hZF.1, Definitional.Term.eval_newest, Definitional.Term.eval_weaken]

theorem erase_set_l (a X : M.Domain) : ∃ Y, ∀ x, M.mem x Y ↔ M.mem x X ∧ x ≠ a := by
  let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
  let φ : UnarySchema 1 := { body := .neg (Formula.extensionalEq .newest (.bound 1)) }
  obtain ⟨Y, hY⟩ := separation_exists_d hZF φ ρ X
  refine ⟨Y, fun x => (hY x).trans (and_congr_right fun _ => ?_)⟩
  simp only [φ, Formula.satisfies_neg_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1]
  rfl

/-- 族中每个成员都含 a 时，删除 a 的像保留该族基数。 -/
theorem erase_family_l {A a} (ha : ∀ X, M.mem X A → M.mem a X) : ∃ E,
    (∀ Y, M.mem Y E ↔ ∃ X, M.mem X A ∧ ∀ x, M.mem x Y ↔ M.mem x X ∧ x ≠ a) ∧
      M.CardinalLessOrEqual I A E := by
  let ρ : Env M 1 := ⟨fun _ => a, fun _ => a⟩
  let φ : BinarySchema 1 := { body := erase_m (.bound 2) (.bound 1) .newest }
  have hφ X Y : φ.denote ρ X Y ↔ ∀ x, M.mem x Y ↔ M.mem x X ∧ x ≠ a :=
    erase_sat_l hZF ((ρ.push X).push Y) (.bound 2) (.bound 1) .newest
  have ht X (_ : M.mem X A) : ∃ Y, φ.denote ρ X Y := by
    obtain ⟨Y, hY⟩ := erase_set_l hZF a X
    exact ⟨Y, (hφ X Y).mpr hY⟩
  have hu X (_ : M.mem X A) Y Z (hY : φ.denote ρ X Y) (hZ : φ.denote ρ X Z) : Y = Z :=
    hZF.1.eq_of_same_members Y Z (fun x => ((hφ X Y).mp hY x).trans ((hφ X Z).mp hZ x).symm)
  obtain ⟨E, hE⟩ := exists_functionalImageOn hZF φ ρ A ht hu
  refine ⟨E, fun Y => (hE Y).trans (exists_congr fun X => and_congr_right fun _ => hφ X Y), ?_⟩
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ ht hu
    (fun X Y hX hY => (hE Y).mpr ⟨X, hX, hY⟩)
  intro X Y Z hX hY hXZ hYZ
  apply hZF.1.eq_of_same_members X Y
  intro x
  classical
  by_cases hxa : x = a
  · exact iff_of_true (hxa ▸ ha X hX) (hxa ▸ ha Y hY)
  · exact ⟨fun hx => ((hφ Y Z).mp hYZ x).mp (((hφ X Z).mp hXZ x).mpr ⟨hx, hxa⟩) |>.1,
      fun hx => ((hφ X Z).mp hXZ x).mp (((hφ Y Z).mp hYZ x).mpr ⟨hx, hxa⟩) |>.1⟩

/-- 删除原像 a 后，把原来占用末位 n 的值移到 f(a)。 -/
theorem delete_bound_l {X Y a n s} (hs : M.SuccessorOf s n) (hX : M.CardinalLessOrEqual I X s)
    (ha : M.mem a X) (hY : ∀ x, M.mem x Y ↔ M.mem x X ∧ x ≠ a) : M.CardinalLessOrEqual I Y n := by
  classical
  obtain ⟨F, hF⟩ := hX
  obtain ⟨k, hk, hak⟩ := hF.1.2.2 a ha
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push n).push k
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.orderedPairMem 𝒞 (.bound 1) (.bound 3) (.bound 4))
      (Formula.extensionalEq .newest (.bound 2))) (.conj
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))
        (.neg (Formula.extensionalEq .newest (.bound 3)))) }
  have hφ x y : φ.denote ρ x y ↔ (M.PairMember I x n F ∧ y = k) ∨ (M.PairMember I x y F ∧ y ≠ n) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_orderedPairMem_iff I, Formula.satisfies_extensionalEq_iff_eq hZF.1,
      Formula.satisfies_neg_iff]
    rfl
  have in_n {x y} (hy : M.PairMember I x y F) (hn : y ≠ n) : M.mem y n :=
    ((hs y).mp (hF.1.output_mem_of_pairMember hy)).elim id (fun h => False.elim (hn (hZF.1.eq_of_same_members y n h)))
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro x hx
    obtain ⟨y, _, hxy⟩ := hF.1.2.2 x ((hY x).mp hx).1
    by_cases hyn : y = n
    · exact ⟨k, (hφ x k).mpr (Or.inl ⟨hyn ▸ hxy, rfl⟩)⟩
    · exact ⟨y, (hφ x y).mpr (Or.inr ⟨hxy, hyn⟩)⟩
  · intro x _ y z hy hz
    rcases (hφ x y).mp hy with ⟨hxn, hyk⟩ | ⟨hxy, hyn⟩ <;>
      rcases (hφ x z).mp hz with ⟨hxn', hzk⟩ | ⟨hxz, hzn⟩
    · exact hyk.trans hzk.symm
    · exact False.elim (hzn (hF.1.1.2 x z n hxz hxn))
    · exact False.elim (hyn (hF.1.1.2 x y n hxy hxn'))
    · exact hF.1.1.2 x y z hxy hxz
  · intro x y hx hy
    rcases (hφ x y).mp hy with ⟨hxn, rfl⟩ | ⟨hxy, hyn⟩
    · apply in_n hak
      intro he
      exact ((hY x).mp hx).2 (hF.2 x a n hxn (he ▸ hak))
    · exact in_n hxy hyn
  · intro x y v hx hy hxy hyv
    rcases (hφ x v).mp hxy with ⟨hxn, hv⟩ | ⟨hxv, _⟩ <;>
      rcases (hφ y v).mp hyv with ⟨hyn, hv'⟩ | ⟨hyv, _⟩
    · exact hF.2 x y n hxn hyn
    · exact False.elim (((hY y).mp hy).2 (hF.2 y a k (hv ▸ hyv) hak))
    · exact False.elim (((hY x).mp hx).2 (hF.2 x a k (hv' ▸ hxv) hak))
    · exact hF.2 x y v hxv hyv

/-- 新元素使用末位，旧元素保留原单射值。 -/
theorem insert_bound_l {X Y a n s} (hs : M.SuccessorOf s n) (hX : M.CardinalLessOrEqual I X n)
    (hY : ∀ x, M.mem x Y ↔ M.mem x X ∨ x = a) : M.CardinalLessOrEqual I Y s := by
  classical
  obtain ⟨F, hF⟩ := hX
  let ρ : Env M 3 := ((⟨fun _ => F, fun _ => F⟩ : Env M 1).push a).push n
  let φ : BinarySchema 3 := {
    body := .disj (.conj (Formula.extensionalEq (.bound 1) (.bound 3))
      (Formula.extensionalEq .newest (.bound 2))) (.conj
        (.neg (Formula.extensionalEq (.bound 1) (.bound 3)))
        (Formula.orderedPairMem 𝒞 (.bound 1) .newest (.bound 4))) }
  have hφ x y : φ.denote ρ x y ↔ (x = a ∧ y = n) ∨ (x ≠ a ∧ M.PairMember I x y F) := by
    simp only [BinarySchema.denote, φ, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
      Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_orderedPairMem_iff I]
    rfl
  have hn x (hx : M.PairMember I x n F) : False := KP.mem_irrefl_d (ZF.modelsKP hZF) n (hF.1.output_mem_of_pairMember hx)
  apply exists_setInjectionFromTo_of_denote hZF I φ ρ
  · intro x hx
    by_cases he : x = a
    · exact ⟨n, (hφ x n).mpr (Or.inl ⟨he, rfl⟩)⟩
    · obtain ⟨y, _, hy⟩ := hF.1.2.2 x (((hY x).mp hx).resolve_right he)
      exact ⟨y, (hφ x y).mpr (Or.inr ⟨he, hy⟩)⟩
  · intro x _ y z hy hz
    rcases (hφ x y).mp hy with hy | hy <;> rcases (hφ x z).mp hz with hz | hz
    · exact hy.2.trans hz.2.symm
    · exact False.elim (hz.1 hy.1)
    · exact False.elim (hy.1 hz.1)
    · exact hF.1.1.2 x y z hy.2 hz.2
  · intro x y _ hy
    rcases (hφ x y).mp hy with ⟨_, rfl⟩ | ⟨_, hy⟩
    · exact hs.predecessor_mem
    · exact (hs y).mpr (Or.inl (hF.1.output_mem_of_pairMember hy))
  · intro x y v _ _ hx hy
    rcases (hφ x v).mp hx with ⟨hxa, hv⟩ | ⟨_, hxv⟩ <;>
      rcases (hφ y v).mp hy with ⟨hya, hv'⟩ | ⟨_, hyv⟩
    · exact hxa.trans hya.symm
    · exact False.elim (hn y (hv ▸ hyv))
    · exact False.elim (hn x (hv' ▸ hxv))
    · exact hF.2 x y v hxv hyv

theorem finite_empty_l {ω E} (hω : M.IsOmega ω) (he : ∀ x, ¬ M.mem x E) : Finite_d I ω E := by
  obtain ⟨e, _, heω⟩ := hω.1.1
  exact ⟨e, heω, exists_inclusionInjection hZF I (fun x hx => False.elim (he x hx))⟩

theorem finite_insert_l {ω X Y a} (hω : M.IsOmega ω) (hX : Finite_d I ω X)
    (hY : ∀ x, M.mem x Y ↔ M.mem x X ∨ x = a) : Finite_d I ω Y := by
  obtain ⟨n, hn, hX⟩ := hX
  obtain ⟨s, hs, hsω⟩ := hω.1.2 n hn
  exact ⟨s, hsω, insert_bound_l I hZF hs hX hY⟩

theorem finite_countable_l {ω X} (hω : M.IsOmega ω) (hX : Finite_d I ω X) : M.CardinalLessOrEqual I X ω := by
  obtain ⟨n, hn, F, hF⟩ := hX
  obtain ⟨G, hG⟩ := exists_inclusionInjection hZF I (hω.transitive hZF n hn)
  exact exists_compositionInjection hZF I hF hG

theorem finite_subset_l {ω X Y} (hX : Finite_d I ω X) (hY : M.MemberSubset Y X) : Finite_d I ω Y := by
  obtain ⟨n, hn, F, hF⟩ := hX
  obtain ⟨G, hG⟩ := exists_inclusionInjection hZF I hY
  exact ⟨n, hn, exists_compositionInjection hZF I hG hF⟩

/-- 对实际公式的有限集合插入归纳，允许模型内部的非标准有限集合。 -/
theorem finite_ind_l {ω} (hω : M.IsOmega ω) {k} (φ : UnarySchema k) (ρ : Env M k)
    (he : ∀ E, (∀ x, ¬ M.mem x E) → φ.denote ρ E)
    (hi : ∀ X a Y, Finite_d I ω X → φ.denote ρ X →
      (∀ x, M.mem x Y ↔ M.mem x X ∨ x = a) → φ.denote ρ Y) :
    ∀ X, Finite_d I ω X → φ.denote ρ X := by
  let ψ : UnarySchema k := {
    body := .forallE (.imp (Formula.cardinalLessOrEqual 𝒞 .newest (.bound 1))
      (φ.body.rename BoundEmbedding.unaryUnderOne)) }
  have hψ n : ψ.denote ρ n ↔ ∀ X, M.CardinalLessOrEqual I X n → φ.denote ρ X := by
    have henv X : ((ρ.push n).push X).reindex BoundEmbedding.unaryUnderOne = ρ.push X := by
      rw [Env.mk.injEq]
      exact ⟨funext (Fin.cases rfl (fun _ => rfl)), rfl⟩
    simp only [UnarySchema.denote, ψ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_cardinalLessOrEqual_iff I hZF.1, Formula.satisfies_rename, henv]
    rfl
  have hall : ∀ n, M.mem n ω → ∀ X, M.CardinalLessOrEqual I X n → φ.denote ρ X := by
    apply hω.induction (fun n => ∀ X, M.CardinalLessOrEqual I X n → φ.denote ρ X)
    · obtain ⟨D, hD⟩ := separation_exists_d hZF ψ ρ ω
      exact ⟨D, fun n => (hD n).trans (and_congr_right fun _ => hψ n)⟩
    · intro e h0 X ⟨F, hF⟩
      apply he X
      intro x hx
      obtain ⟨y, hy, _⟩ := hF.1.2.2 x hx
      exact h0 y hy
    · intro n hn ih s hs X hX
      classical
      by_cases hx : ∃ a, M.mem a X
      · obtain ⟨a, ha⟩ := hx
        obtain ⟨Y, hY⟩ := erase_set_l hZF a X
        have hYn := delete_bound_l I hZF hs hX ha hY
        apply hi Y a X ⟨n, hn, hYn⟩ (ih Y hYn)
        intro x
        rw [hY x]
        exact ⟨fun hx => (Classical.em (x = a)).elim (fun h => Or.inr h) (fun h => Or.inl ⟨hx, h⟩),
          fun h => h.elim And.left (fun h => h ▸ ha)⟩
      · exact he X (fun x hx' => hx ⟨x, hx'⟩)
  exact fun X ⟨n, hn, hX⟩ => hall n hn X hX

theorem finite_union_l {ω X Y Z} (hω : M.IsOmega ω) (hX : Finite_d I ω X) (hY : Finite_d I ω Y)
    (hZ : M.IsUnionOfTwo Z X Y) : Finite_d I ω Z := by
  let ρ : Env M 2 := (⟨fun _ => Y, fun _ => Y⟩ : Env M 1).push ω
  let φ : UnarySchema 2 := {
    body := .forallE (.imp (.forallE (.iff (.mem .newest (.bound 1))
      (.disj (.mem .newest (.bound 2)) (.mem .newest (.bound 4)))))
      (finite_m 𝒞 (.bound 2) .newest)) }
  have hφ A : φ.denote ρ A ↔ ∀ Z, M.IsUnionOfTwo Z A Y → Finite_d I ω Z := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
      Formula.satisfies_iff_iff, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff, finite_sat_l I hZF.1]
    rfl
  apply (hφ X).mp (finite_ind_l I hZF hω φ ρ ?_ ?_ X hX) Z hZ
  · intro E hE
    apply (hφ E).mpr
    intro A hA
    have heq : A = Y := hZF.1.eq_of_same_members A Y (fun x => (hA x).trans
      ⟨fun h => h.elim (fun h => False.elim (hE x h)) id, Or.inr⟩)
    exact heq ▸ hY
  · intro A a C _ ih hC
    apply (hφ C).mpr
    intro D hD
    obtain ⟨T, hT⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A Y
    apply finite_insert_l I hZF hω ((hφ A).mp ih T hT)
    intro x
    rw [hD x, hC x, hT x]
    exact ⟨fun h => h.elim (fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr)
      (fun h => Or.inl (Or.inr h)), fun h => h.elim
        (fun h => h.elim (fun h => Or.inl (Or.inl h)) Or.inr) (fun h => Or.inl (Or.inr h))⟩

end ZF
end YesMetaZFC.SetTheory
