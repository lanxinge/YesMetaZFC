import YesMetaZFC.Model.SetTheory.Internal.FiniteAssignment

/-! # 内部公式的坐标界与赋值一致性

程序只读取各条指令中出现的两个坐标。用一个内部自然数同时界住它们，得到
后续真值比较所需的有限参数支撑；坐标界和赋值一致性均由实际原公式表达。
-/

namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project
universe u
variable {M : Structure.{u}} {𝒞 : OrderedPairConvention} (I : 𝒞.Interpretation M)

def Scoord_d (F r i j : M.Domain) : Prop := ∃ c o a,
  M.PairMember I r c F ∧ I.Codes c o a ∧ I.Codes a i j

def scoord_m {d} (F r i j : Term d) : Formula 1 d :=
  .existsE (.existsE (.existsE (.conj (Formula.orderedPairMem 𝒞 r.weaken.weaken.weaken (.bound 2) F.weaken.weaken.weaken)
    (.conj (𝒞.code (.bound 2) (.bound 1) .newest) (𝒞.code .newest i.weaken.weaken.weaken j.weaken.weaken.weaken)))))
derive_free_closed scoord_m

theorem scoord_sat_l {d} (ρ : Env M d) (F r i j : Term d) :
    Formula.satisfies ρ (scoord_m (𝒞 := 𝒞) F r i j) ↔ Scoord_d I (F.eval ρ) (r.eval ρ) (i.eval ρ) (j.eval ρ) := by
  simp only [scoord_m, Scoord_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    Formula.satisfies_orderedPairMem_iff I, I.satisfies_code_iff, Definitional.Term.eval_weaken]
  rfl

def Sbound_d (F b : M.Domain) : Prop := ∀ r i j, Scoord_d I F r i j → M.mem i b ∧ M.mem j b

def sbound_m {d} (F b : Term d) : Formula 1 d :=
  .forallE (.forallE (.forallE (.imp (scoord_m (𝒞 := 𝒞) F.weaken.weaken.weaken (.bound 2) (.bound 1) .newest)
    (.conj (.mem (.bound 1) b.weaken.weaken.weaken) (.mem .newest b.weaken.weaken.weaken)))))
derive_free_closed sbound_m

theorem sbound_sat_l {d} (ρ : Env M d) (F b : Term d) :
    Formula.satisfies ρ (sbound_m (𝒞 := 𝒞) F b) ↔ Sbound_d I (F.eval ρ) (b.eval ρ) := by
  simp only [sbound_m, Sbound_d, Formula.satisfies_forall_iff, Formula.satisfies_imp_iff,
    scoord_sat_l I, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff, Definitional.Term.eval_weaken]
  rfl

theorem Sbound_d.operands_l {F b r c k i j} (h : Sbound_d I F b) (hc : M.PairMember I r c F)
    (hs : Sop_d I k c i j) : M.mem i b ∧ M.mem j b := by
  obtain ⟨a, o, _, ha, ho⟩ := hs
  exact h r i j ⟨c, o, a, hc, ho, ha⟩

def Senv_agree_d (b f g : M.Domain) : Prop := ∀ i x, M.mem i b → (M.PairMember I i x f ↔ M.PairMember I i x g)

def senv_agree_m {d} (b f g : Term d) : Formula 1 d :=
  Formula.forallMem b (.forallE (.iff (Formula.orderedPairMem 𝒞 (.bound 1) .newest f.weaken.weaken)
    (Formula.orderedPairMem 𝒞 (.bound 1) .newest g.weaken.weaken)))
derive_free_closed senv_agree_m

theorem senv_agree_sat_l {d} (ρ : Env M d) (b f g : Term d) :
    Formula.satisfies ρ (senv_agree_m (𝒞 := 𝒞) b f g) ↔ Senv_agree_d I (b.eval ρ) (f.eval ρ) (g.eval ρ) := by
  simp only [senv_agree_m, Senv_agree_d, Formula.satisfies_forallMem_iff, Formula.satisfies_forall_iff,
    Formula.satisfies_iff_iff, Formula.satisfies_orderedPairMem_iff I, Definitional.Term.eval_weaken]
  exact ⟨fun h i x hi => h i hi x, fun h i hi x => h i x hi⟩

theorem Senv_agree_d.symm_l {b f g} (h : Senv_agree_d I b f g) : Senv_agree_d I b g f :=
  fun i x hi => (h i x hi).symm

theorem Senv_agree_d.update_l {b f g i x h k} (ha : Senv_agree_d I b f g)
    (hh : Senv_update_d I f i x h) (hk : Senv_update_d I g i x k) : Senv_agree_d I b h k := by
  intro j y hj
  exact (hh.2 j y).trans ((or_congr Iff.rfl (and_congr Iff.rfl (ha j y hj))).trans (hk.2 j y).symm)

theorem senv_fill_agree_l {ω u b s f g} (hb : M.MemberSubset b ω) (hs : M.IsRestrictionOf I s f b)
    (hg : Senv_fill_d I ω u b s g) : Senv_agree_d I b f g := by
  intro i x hi
  exact ⟨fun hx => (hg.2 i x).mpr ⟨hb i hi, Or.inl ⟨hi, (hs.2 i x).mpr ⟨hi, hx⟩⟩⟩,
    fun hx => (((hg.2 i x).mp hx).2.elim (fun h => ((hs.2 i x).mp h.2).2) (fun h => (h.1 hi).elim))⟩

end YesMetaZFC.SetTheory.Internal
