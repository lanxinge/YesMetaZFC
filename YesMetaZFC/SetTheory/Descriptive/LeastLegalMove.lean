import YesMetaZFC.SetTheory.Descriptive.LegalHistory
import YesMetaZFC.SetTheory.Ord.DefinableMinimum

/-! # 枚举中的最小合法走法

合法性只读取既定有限历史集合 L，故同一算法可用于地模型及其力迫扩张。
无合法项时返回内部零；有合法项时返回真正的最小编号，整个选择表由 ZF 构造。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

def Cg_admit_d (ω L h a : M.Domain) : Prop := ∃ t, M.mem t L ∧ Fseq_end_d I ω t h a
def cg_admit_m {d} (ω L h a : Term d) : Formula 1 d := set[d] ⟪∃ t ∈ ⌜L⌝ₛ,
  ⌜fseq_end_m (𝒞 := kpair_convention_l)⌝ₚ(⌜ω⌝ₛ, t, ⌜h⌝ₛ, ⌜a⌝ₛ)⟫
derive_free_closed cg_admit_m

theorem cg_admit_sat_l {d} (ρ : Env M d) (ω L h a : Term d) :
    Formula.satisfies ρ (cg_admit_m ω L h a) ↔ Cg_admit_d hZF (ω.eval ρ) (L.eval ρ) (h.eval ρ) (a.eval ρ) := by
  simp only [cg_admit_m, Cg_admit_d, Formula.satisfies_existsMem_iff, fseq_end_sat_l I hZF.1,
    Definitional.Term.eval_weaken]; rfl

def Cg_scan_d (ω L g h i : M.Domain) : Prop := M.mem i ω ∧
  (∃ a, Rd_entry_d i a g ∧ Cg_admit_d hZF ω L h a) ∧
  ∀ j a, M.mem j i → Rd_entry_d j a g → ¬ Cg_admit_d hZF ω L h a

def cg_scan_m {d} (ω L g h i : Term d) : Formula 1 d := set[d] ⟪⌜i⌝ₛ ∈ ⌜ω⌝ₛ ∧
  (∃ a, ⌜rd_entry0_m⌝ₚ(⌜i⌝ₛ, a, ⌜g⌝ₛ) ∧ ⌜cg_admit_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜h⌝ₛ, a)) ∧
  (∀ j a, j ∈ ⌜i⌝ₛ → ⌜rd_entry0_m⌝ₚ(j, a, ⌜g⌝ₛ) → ¬ ⌜cg_admit_m⌝ₚ(⌜ω⌝ₛ, ⌜L⌝ₛ, ⌜h⌝ₛ, a))⟫
derive_free_closed cg_scan_m

theorem cg_scan_sat_l {d} (ρ : Env M d) (ω L g h i : Term d) :
    Formula.satisfies ρ (cg_scan_m ω L g h i) ↔ Cg_scan_d hZF (ω.eval ρ) (L.eval ρ) (g.eval ρ) (h.eval ρ) (i.eval ρ) := by
  simp only [cg_scan_m, Cg_scan_d, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
    Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, cg_admit_sat_l hZF,
    Formula.satisfies_forall_iff, Formula.satisfies_imp_iff, Formula.satisfies_neg_iff, Definitional.Term.eval_weaken]; rfl

theorem Cg_scan_d.le_l {ω L g h i j a : M.Domain} (hw : M.IsOmega ω) (scan : Cg_scan_d hZF ω L g h i)
    (hj : M.mem j ω) (ja : Rd_entry_d j a g) (legal : Cg_admit_d hZF ω L h a) : M.mem i j ∨ i = j := by
  rcases (hw.isOrdinal hZF).wellOrder.linear.compare i scan.1 j hj with eq | lt | gt
  · exact Or.inr (hZF.1.eq_of_same_members i j eq)
  · exact Or.inl lt
  · exact (scan.2.2 j a gt ja legal).elim

theorem Cg_scan_d.unique_l {ω L g h i j : M.Domain} (hw : M.IsOmega ω)
    (scan : Cg_scan_d hZF ω L g h i) (other : Cg_scan_d hZF ω L g h j) : i = j := by
  obtain ⟨a, ja, legal⟩ := other.2.1
  rcases scan.le_l hZF hw other.1 ja legal with lt | eq
  · obtain ⟨b, ib, legal⟩ := scan.2.1
    exact (other.2.2 i b lt ib legal).elim
  · exact eq

theorem cg_scan_exists_l {ω L g h : M.Domain} (hw : M.IsOmega ω)
    (hit : ∃ i a, M.mem i ω ∧ Rd_entry_d i a g ∧ Cg_admit_d hZF ω L h a) :
    ∃ i, Cg_scan_d hZF ω L g h i := by
  let ρ : Env M 4 := ⟨fun i => [ω, L, g, h].get i, fun _ => ω⟩
  let φ : UnarySchema 4 := { body := set[5] ⟪⌜(.newest : Term 5)⌝ₛ ∈ ⌜(.bound 1 : Term 5)⌝ₛ ∧
    (∃ a, ⌜rd_entry0_m⌝ₚ(⌜(.newest : Term 5)⌝ₛ, a, ⌜(.bound 3 : Term 5)⌝ₛ) ∧
      ⌜cg_admit_m⌝ₚ(⌜(.bound 1 : Term 5)⌝ₛ, ⌜(.bound 2 : Term 5)⌝ₛ, ⌜(.bound 4 : Term 5)⌝ₛ, a))⟫ }
  have sat i : φ.denote ρ i ↔ M.mem i ω ∧ ∃ a, Rd_entry_d i a g ∧ Cg_admit_d hZF ω L h a := by
    simp only [φ, UnarySchema.denote, Formula.satisfies_conj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_exists_iff, rd_entry0_sat_l hZF.1, cg_admit_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  obtain ⟨i, a, hi, ia, legal⟩ := hit
  obtain ⟨j, _, hj, least⟩ := ZF.ordinal_min_l hZF φ ρ (hw.members_areOrdinals hZF i hi)
    ((sat i).mpr ⟨hi, a, ia, legal⟩)
  have hj := (sat j).mp hj
  exact ⟨j, hj.1, hj.2, fun k a hk ka legal => least k hk
    ((sat k).mpr ⟨hw.transitive hZF j hj.1 k hk, a, ka, legal⟩)⟩

/-- 对全部有限历史一次构造最小编号表；不要求每个历史都存在合法后继。 -/
theorem cg_selector_l {ω e F L g : M.Domain} (hw : M.IsOmega ω) (he : ∀ x, ¬ M.mem x e) :
    ∃ K, Fn0_d F ω K ∧ ∀ h i, Rd_entry_d h i K →
      (∃ j a, M.mem j ω ∧ Rd_entry_d j a g ∧ Cg_admit_d hZF ω L h a) → Cg_scan_d hZF ω L g h i := by
  classical
  let ρ : Env M 4 := ⟨fun i => [ω, e, L, g].get i, fun _ => ω⟩
  let φ : BinarySchema 4 := { body := set[6] ⟪
    ⌜cg_scan_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, ⌜(.bound 5 : Term 6)⌝ₛ,
      ⌜(.bound 1 : Term 6)⌝ₛ, ⌜(.bound 0 : Term 6)⌝ₛ) ∨
    (⌜(.bound 0 : Term 6)⌝ₛ = ⌜(.bound 3 : Term 6)⌝ₛ ∧ ¬ (∃ i a, i ∈ ⌜(.bound 2 : Term 6)⌝ₛ ∧
      ⌜rd_entry0_m⌝ₚ(i, a, ⌜(.bound 5 : Term 6)⌝ₛ) ∧
      ⌜cg_admit_m⌝ₚ(⌜(.bound 2 : Term 6)⌝ₛ, ⌜(.bound 4 : Term 6)⌝ₛ, ⌜(.bound 1 : Term 6)⌝ₛ, a)))⟫ }
  let hit h := ∃ j a, M.mem j ω ∧ Rd_entry_d j a g ∧ Cg_admit_d hZF ω L h a
  have sat h i : φ.denote ρ h i ↔ Cg_scan_d hZF ω L g h i ∨ i = e ∧ ¬ hit h := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_disj_iff, cg_scan_sat_l hZF,
      Formula.satisfies_conj_iff, Formula.satisfies_extensionalEq_iff_eq hZF.1, Formula.satisfies_neg_iff,
      Formula.satisfies_exists_iff, Formula.satisfies_mem_iff, rd_entry0_sat_l hZF.1,
      cg_admit_sat_l hZF, Definitional.Term.eval_weaken]; rfl
  have seen h i (scan : Cg_scan_d hZF ω L g h i) : hit h :=
    scan.2.1.elim fun a ha => ⟨i, a, scan.1, ha⟩
  obtain ⟨K, fn, graph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I φ ρ (source := F) (target := ω) (by
    intro h _
    by_cases yes : hit h
    · obtain ⟨i, scan⟩ := cg_scan_exists_l hZF hw yes
      exact ⟨i, (sat h i).mpr (Or.inl scan)⟩
    · exact ⟨e, (sat h e).mpr (Or.inr ⟨rfl, yes⟩)⟩) (by
    intro h _ i j hi hj
    rcases (sat h i).mp hi with si | ⟨ie, no⟩ <;> rcases (sat h j).mp hj with sj | ⟨je, no'⟩
    · exact si.unique_l hZF hw sj
    · exact (no' (seen h i si)).elim
    · exact (no (seen h j sj)).elim
    · exact ie.trans je.symm) (by
    intro h i _ hi
    exact ((sat h i).mp hi).elim And.left (fun h => h.1.symm ▸ num_mem_l hZF.1 hw (show Num_d 0 e from he)))
  exact ⟨K, fn0_of_function_l (ZF.modelsKP hZF) fn, fun h i hi yes =>
    ((sat h i).mp ((graph h i).mp hi).2).elim id (fun no => (no.2 yes).elim)⟩

end YesMetaZFC.SetTheory.Descriptive
