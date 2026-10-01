import YesMetaZFC.Model.Forcing.Iteration.Stage.SystemSyntax

/-! # 递归历史的两个实际坐标序列

递归定理返回一张序列，其值为条件集与序关系的有序对。本模块在模型内投影
这张图，取得已有迭代系统使用的两张序列；投影和限制严格交换。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_part_d (k : Bool) (S F : M.Domain) : Prop :=
  (∀ v, M.mem v F → ∃ i x, KPair_d M v i x) ∧
  ∀ i x, Entry_d M i x F ↔ ∃ c a b, Entry_d M i c S ∧ KPair_d M c a b ∧ x = if k then b else a

def row_part_m (k : Bool) {n} (S F : Term n) : Formula 1 n :=
  .conj (Formula.isRelation kpair_convention_l F) (.forallE (.forallE
    (.iff (entry_m (.bound 1) .newest F.weaken.weaken)
      (.existsE (.existsE (.existsE (.conj (entry_m (.bound 4) (.bound 2) S.weaken.weaken.weaken.weaken.weaken)
        (.conj (kpair_m (.bound 2) (.bound 1) .newest)
          (Formula.extensionalEq (.bound 3) (if k then .newest else .bound 1))))))))))
@[simp] theorem row_part_closed_l (k : Bool) {n} (S F : Term n)
    (hS : S.freeSupport = []) (hF : F.freeSupport = []) : (row_part_m k S F).FreeClosed := by
  cases k <;> simp [row_part_m, Definitional.Formula.FreeClosed, hF]
  all_goals exact ⟨entry_m_freeClosed _ _ _ rfl rfl (by simpa using hF),
    entry_m_freeClosed _ _ _ rfl rfl (by simpa using hS), kpair_m_freeClosed _ _ _ rfl rfl rfl⟩

theorem row_part_sat_l (hE : Extensional M) (k : Bool) {n} (ρ : Env M n) (S F : Term n) :
    Formula.satisfies ρ (row_part_m k S F) ↔ Row_part_d k (S.eval ρ) (F.eval ρ) := by
  cases k <;> simp only [row_part_m, Row_part_d, Formula.isRelation, kpair_convention_l,
    Formula.satisfies_conj_iff, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_exists_iff, Formula.satisfies_extensionalEq_iff_eq hE,
    entry_sat_l M hE, kpair_sat_l M hE, Definitional.Term.eval_weaken, Definitional.Term.eval_newest,
    Bool.false_eq_true, ↓reduceIte, Term.eval_bound_zero_push, Term.eval_bound_one_push] <;> rfl

def Row_history_d (S F H : M.Domain) : Prop := Row_part_d false S F ∧ Row_part_d true S H

def row_history_m {n} (S F H : Term n) : Formula 1 n := .conj (row_part_m false S F) (row_part_m true S H)
derive_free_closed row_history_m

theorem row_history_sat_l (hE : Extensional M) {n} (ρ : Env M n) (S F H : Term n) :
    Formula.satisfies ρ (row_history_m S F H) ↔ Row_history_d (S.eval ρ) (F.eval ρ) (H.eval ρ) := by
  simp only [row_history_m, Row_history_d, Formula.satisfies_conj_iff, row_part_sat_l hE]

theorem row_part_unique_l (hE : Extensional M) {k} {S F F' : M.Domain} (h : Row_part_d k S F) (h' : Row_part_d k S F') : F = F' :=
  entry_ext_l M hE h.1 h'.1 (fun i x => (h.2 i x).trans (h'.2 i x).symm)

theorem row_history_unique_l (hE : Extensional M) {S F H F' H' : M.Domain}
    (h : Row_history_d S F H) (h' : Row_history_d S F' H') : F = F' ∧ H = H' :=
  ⟨row_part_unique_l hE h.1 h'.1, row_part_unique_l hE h.2 h'.2⟩

theorem row_history_entry_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {δ S F H}
    (hS : M.IsSequenceOfLength (kpair_interpretation_l M hE hP) S δ) (h : Row_history_d S F H) (i B R) :
    (Entry_d M i B F ∧ Entry_d M i R H) ↔ ∃ c, Entry_d M i c S ∧ KPair_d M c B R := by
  constructor
  · rintro ⟨hB, hR⟩
    obtain ⟨c, a, b, hc, hab, hb⟩ := (h.1.2 i B).mp hB
    obtain ⟨c', a', b', hc', hab', hr⟩ := (h.2.2 i R).mp hR
    have he := hS.2.1.2 i c c' hc hc'
    subst c'
    obtain ⟨ha, hbb⟩ := kpair_injective_l M hab hab'
    subst a'; subst b'
    exact ⟨c, hc, hb.symm ▸ hr.symm ▸ hab⟩
  · rintro ⟨c, hc, hab⟩
    exact ⟨(h.1.2 i B).mpr ⟨c, B, R, hc, hab, rfl⟩, (h.2.2 i R).mpr ⟨c, B, R, hc, hab, rfl⟩⟩

/-- 只对实际配对值作替换，未选择外部坐标函数。 -/
theorem row_part_exists_l (hZF : M.Models ZF) {S}
    (hS : ∀ w, M.mem w S → ∃ i c, KPair_d M w i c)
    (hPair : ∀ i c, Entry_d M i c S → ∃ a b, KPair_d M c a b) (k : Bool) : ∃ F, Row_part_d k S F := by
  let I := kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))
  let P w v := ∃ i c a b, KPair_d M w i c ∧ KPair_d M c a b ∧ KPair_d M v i (if k then b else a)
  let φ : BinarySchema 0 := {
    body := .existsE (.existsE (.existsE (.existsE (.conj (kpair_m (.bound 5) (.bound 3) (.bound 2))
      (.conj (kpair_m (.bound 2) (.bound 1) .newest) (kpair_m (.bound 4) (.bound 3) (if k then .newest else .bound 1)))))))
    freeClosed := by
      cases k <;> simp [Definitional.Formula.FreeClosed]
      all_goals exact ⟨kpair_m_freeClosed _ _ _ rfl rfl rfl,
        kpair_m_freeClosed _ _ _ rfl rfl rfl, kpair_m_freeClosed _ _ _ rfl rfl rfl⟩ }
  let ρ : Env M 0 := ⟨Fin.elim0, fun _ => S⟩
  have hφ w v : φ.denote ρ w v ↔ P w v := by
    cases k <;> simp only [φ, P, BinarySchema.denote, Formula.satisfies_exists_iff,
      Formula.satisfies_conj_iff, kpair_sat_l M hZF.1, Bool.false_eq_true, ↓reduceIte] <;> rfl
  obtain ⟨F, hF⟩ := ZF.exists_functionalImageOn hZF φ ρ S (fun w hw => by
    obtain ⟨i, c, hwc⟩ := hS w hw
    obtain ⟨a, b, hc⟩ := hPair i c ⟨w, hwc, hw⟩
    obtain ⟨v, hv⟩ := I.total i (if k then b else a)
    exact ⟨v, (hφ w v).mpr ⟨i, c, a, b, hwc, hc, hv⟩⟩) (by
      intro w _ v v' hv hv'
      obtain ⟨i, c, a, b, hw, hc, hv⟩ := (hφ w v).mp hv
      obtain ⟨i', c', a', b', hw', hc', hv'⟩ := (hφ w v').mp hv'
      obtain ⟨hi, hh⟩ := kpair_injective_l M hw hw'
      subst i'; subst c'
      obtain ⟨ha, hb⟩ := kpair_injective_l M hc hc'
      subst a'; subst b'
      exact kpair_unique_l M hZF.1 hv hv')
  have graph v (hv : M.mem v F) : ∃ i x, KPair_d M v i x := by
    obtain ⟨w, _, hw⟩ := (hF v).mp hv
    obtain ⟨i, _, a, b, _, _, hv⟩ := (hφ w v).mp hw
    exact ⟨i, if k then b else a, hv⟩
  refine ⟨F, graph, fun i x => ⟨?_, ?_⟩⟩
  · rintro ⟨v, hix, hv⟩
    obtain ⟨w, hw, hmap⟩ := (hF v).mp hv
    obtain ⟨j, c, a, b, hwc, hc, hv⟩ := (hφ w v).mp hmap
    obtain ⟨hi, hx⟩ := kpair_injective_l M hix hv
    subst j
    exact ⟨c, a, b, ⟨w, hwc, hw⟩, hc, hx⟩
  · rintro ⟨c, a, b, ⟨w, hwc, hw⟩, hc, hx⟩
    obtain ⟨v, hv⟩ := I.total i x
    refine ⟨v, hv, (hF v).mpr ⟨w, hw, (hφ w v).mpr ⟨i, c, a, b, hwc, hc, ?_⟩⟩⟩
    exact hx ▸ hv

theorem row_part_sequence_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {δ S F k}
    (hS : M.IsSequenceOfLength (kpair_interpretation_l M hE hP) S δ) (h : Row_part_d k S F)
    (hPair : ∀ i c, Entry_d M i c S → ∃ a b, KPair_d M c a b) : M.IsSequenceOfLength (kpair_interpretation_l M hE hP) F δ := by
  refine ⟨hS.1, ⟨h.1, ?_⟩, fun i => ⟨?_, ?_⟩⟩
  · intro i x y hx hy
    obtain ⟨c, a, b, hc, hab, hx⟩ := (h.2 i x).mp hx
    obtain ⟨c', a', b', hc', hab', hy⟩ := (h.2 i y).mp hy
    have he := hS.2.1.2 i c c' hc hc'
    subst c'
    obtain ⟨ha, hb⟩ := kpair_injective_l M hab hab'
    subst a'; subst b'
    exact hx.trans hy.symm
  · intro hi
    obtain ⟨c, hc⟩ := (hS.2.2 i).mp hi
    obtain ⟨a, b, hab⟩ := hPair i c hc
    exact ⟨if k then b else a, (h.2 i _).mpr ⟨c, a, b, hc, hab, rfl⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨c, _, _, hc, _⟩ := (h.2 i x).mp hx
    exact (hS.2.2 i).mpr ⟨c, hc⟩

theorem row_history_exists_l (hZF : M.Models ZF) {δ S}
    (hS : M.IsSequenceOfLength (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) S δ)
    (hPair : ∀ i c, Entry_d M i c S → ∃ a b, KPair_d M c a b) : ∃ F H, Row_history_d S F H ∧
      M.IsSequenceOfLength (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) F δ ∧
      M.IsSequenceOfLength (kpair_interpretation_l M hZF.1 (KP.exists_pair (ZF.modelsKP hZF))) H δ := by
  obtain ⟨F, hF⟩ := row_part_exists_l hZF hS.2.1.1 hPair false
  obtain ⟨H, hH⟩ := row_part_exists_l hZF hS.2.1.1 hPair true
  exact ⟨F, H, ⟨hF, hH⟩, row_part_sequence_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hS hF hPair,
    row_part_sequence_l hZF.1 (KP.exists_pair (ZF.modelsKP hZF)) hS hH hPair⟩

theorem row_part_restrict_l (hE : Extensional M) (hP : ∀ a b, ∃ p, Pair_d M p a b) {α S S' F F' k}
    (hs : M.IsRestrictionOf (kpair_interpretation_l M hE hP) S' S α) (h : Row_part_d k S F) (h' : Row_part_d k S' F') :
    M.IsRestrictionOf (kpair_interpretation_l M hE hP) F' F α := by
  refine ⟨h'.1, fun i x => ?_⟩
  change Entry_d M i x F' ↔ M.mem i α ∧ Entry_d M i x F
  rw [h'.2, h.2]
  exact ⟨fun ⟨c, a, b, hc, hab, he⟩ => ⟨((hs.2 i c).mp hc).1, c, a, b, ((hs.2 i c).mp hc).2, hab, he⟩,
    fun ⟨hi, c, a, b, hc, hab, he⟩ => ⟨c, a, b, (hs.2 i c).mpr ⟨hi, hc⟩, hab, he⟩⟩

end YesMetaZFC.Model.Forcing.Internal
