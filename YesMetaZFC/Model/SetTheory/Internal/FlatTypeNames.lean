import YesMetaZFC.Model.SetTheory.Internal.ProgramRecodeSemantics
import YesMetaZFC.Model.SetTheory.Internal.TypeNames

/-! # 原名字列对平坦元组的有界求值矩阵

名字仍是原 Kuratowski 码；实现元组与完整赋值用平坦图。
矩阵只量化实际的 ω、对象载体和名字所在秩层，因而可以穿过后继秩层。
-/
namespace YesMetaZFC.SetTheory.Internal
open Definitional.Project InnerModel
universe u
variable {M : Structure.{u}}

def fp_entry0_m {d} (ω i x f : Term d) : Formula 1 d :=
  Formula.existsMem f (fp_pair0_m ω.weaken i.weaken x.weaken .newest)
derive_free_closed fp_entry0_m

theorem fp_entry0_delta_l {d} (ω i x f : Term d) : (fp_entry0_m ω i x f).IsDelta0 :=
  .existsMem _ (fp_pair0_delta_l ..)

theorem fp_entry0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω i x f : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (fp_entry0_m ω i x f) ↔
      M.PairMember (fp_interpretation_l hKPi) (i.eval ρ) (x.eval ρ) (f.eval ρ) := by
  have hKP := (KPi.models_iff_l.mp hKPi).1
  have read p := fp_pair0_sat_l hKP (ρ.push p) ω.weaken i.weaken x.weaken .newest
    (by simpa only [Definitional.Term.eval_weaken] using hω.1)
  simp only [fp_entry0_m, Formula.satisfies_existsMem_iff, read,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]
  exact ⟨fun ⟨p, hp, code⟩ => ⟨p, (fp_fixed_l hKP.1 hω).mpr code, hp⟩,
    fun ⟨p, code, hp⟩ => ⟨p, hp, (fp_fixed_l hKP.1 hω).mp code⟩⟩

variable (J : FlatPairing.convention.Interpretation M)

def Tf_value_d (n h δ a x : M.Domain) : Prop :=
  M.PairMember J a x h ∨ (a = n ∧ x = δ) ∨ KPair_d M a x x

def tf_value0_m {d} (ω n h δ a x : Term d) : Formula 1 d := .disj (fp_entry0_m ω a x h)
  (.disj (.conj (Formula.extensionalEq a n) (Formula.extensionalEq x δ)) (kpair0_m a x x))
derive_free_closed tf_value0_m

theorem tf_value0_delta_l {d} (ω n h δ a x : Term d) : (tf_value0_m ω n h δ a x).IsDelta0 :=
  .disj (fp_entry0_delta_l ..) (.disj (.conj (.atom _ _ _) (.atom _ _ _)) (kpair0_delta_l ..))

theorem tf_value0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω n h δ a x : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tf_value0_m ω n h δ a x) ↔
      Tf_value_d (fp_interpretation_l hKPi) (n.eval ρ) (h.eval ρ) (δ.eval ρ) (a.eval ρ) (x.eval ρ) := by
  simp only [tf_value0_m, Tf_value_d, Formula.satisfies_disj_iff, Formula.satisfies_conj_iff,
    fp_entry0_sat_l hKPi _ _ _ _ _ hω, Formula.satisfies_extensionalEq_iff_eq (KPi.models_iff_l.mp hKPi).1.1,
    kpair0_sat_l (KPi.models_iff_l.mp hKPi).1.1]

def Tf_fill_d (ω X Z n h δ b e g : M.Domain) : Prop := ∀ i, M.mem i ω → ∀ x, M.mem x X →
  (M.PairMember J i x g ↔ (M.mem i b ∧ ∃ a, M.mem a Z ∧ Rd_entry_d i a e ∧ Tf_value_d J n h δ a x) ∨
    (¬ M.mem i b ∧ x = δ))

def tf_fill0_m {d} (ω X Z n h δ b e g : Term d) : Formula 1 d := set[d] ⟪∀ i ∈ ⌜ω⌝ₛ, ∀ x ∈ ⌜X⌝ₛ,
  ⌜fp_entry0_m⌝ₚ(⌜ω⌝ₛ, i, x, ⌜g⌝ₛ) ↔
    (i ∈ ⌜b⌝ₛ ∧ (∃ a ∈ ⌜Z⌝ₛ, ⌜rd_entry0_m⌝ₚ(i, a, ⌜e⌝ₛ) ∧ ⌜tf_value0_m⌝ₚ(⌜ω⌝ₛ, ⌜n⌝ₛ, ⌜h⌝ₛ, ⌜δ⌝ₛ, a, x))) ∨
    (¬ i ∈ ⌜b⌝ₛ ∧ x = ⌜δ⌝ₛ)⟫
derive_free_closed tf_fill0_m

theorem tf_fill0_delta_l {d} (ω X Z n h δ b e g : Term d) : (tf_fill0_m ω X Z n h δ b e g).IsDelta0 :=
  .forallMem _ (.forallMem _ (.iff (fp_entry0_delta_l ..) (.disj
    (.conj (.mem _ _) (.existsMem _ (.conj (rd_entry0_delta_l ..) (tf_value0_delta_l ..))))
    (.conj (.neg (.mem _ _)) (.atom _ _ _)))))

theorem tf_fill0_sat_l (hKPi : M.Models KPi) {d} (ρ : Env M d) (ω X Z n h δ b e g : Term d)
    (hω : M.IsOmega (ω.eval ρ)) : Formula.satisfies ρ (tf_fill0_m ω X Z n h δ b e g) ↔
      Tf_fill_d (fp_interpretation_l hKPi) (ω.eval ρ) (X.eval ρ) (Z.eval ρ) (n.eval ρ) (h.eval ρ)
        (δ.eval ρ) (b.eval ρ) (e.eval ρ) (g.eval ρ) := by
  have entry i x := fp_entry0_sat_l hKPi ((ρ.push i).push x) ω.weaken.weaken
    (.newest : Term (d+1)).weaken .newest g.weaken.weaken
    (by simpa only [Definitional.Term.eval_weaken] using hω)
  have value i x a := tf_value0_sat_l hKPi (((ρ.push i).push x).push a)
    ω.weaken.weaken.weaken n.weaken.weaken.weaken h.weaken.weaken.weaken δ.weaken.weaken.weaken
    .newest (.newest : Term (d+2)).weaken
    (by simpa only [Definitional.Term.eval_weaken] using hω)
  simp only [tf_fill0_m, Tf_fill_d, Formula.satisfies_forallMem_iff, Formula.satisfies_iff_iff,
    Formula.satisfies_disj_iff, Formula.satisfies_conj_iff, Formula.satisfies_existsMem_iff,
    Formula.satisfies_mem_iff, Formula.satisfies_neg_iff,
    Formula.satisfies_extensionalEq_iff_eq (KPi.models_iff_l.mp hKPi).1.1,
    entry, rd_entry0_sat_l (KPi.models_iff_l.mp hKPi).1.1, value,
    Definitional.Term.eval_weaken, Definitional.Term.eval_newest]

variable (hZF : M.Models ZF)
local notation "Q" => kp_pair_l (ZF.modelsKP hZF)
local notation "K" => fp_interpretation_l (ZF.models_kpi_l hZF)

theorem tf_value_recode_l {n s h δ a x : M.Domain} (agree : Sx_graph_d Q K s h) :
    Tf_value_d K n h δ a x ↔ Tn_value_d n s δ a x :=
  or_congr (agree a x) Iff.rfl

/-- 有界矩阵恰好要求原完整赋值的逐点重编码，不依赖源内拥有原图。 -/
theorem tf_fill_iff_l {ω X Z n s h δ b e r f g : M.Domain}
    (hZ : M.TransitiveSet Z) (he : M.mem e Z) (tuple : Sx_graph_d Q K s h)
    (assign : Tn_assign_d n s δ e r) (fill : Senv_fill_d Q ω δ b r f)
    (hf : M.IsSetFunctionFromTo Q f ω X) (hg : M.IsSetFunctionFromTo K g ω X) :
    Tf_fill_d K ω X Z n h δ b e g ↔ Sx_graph_d Q K f g := by
  have value i x : (∃ a, M.mem a Z ∧ Rd_entry_d i a e ∧ Tf_value_d K n h δ a x) ↔ Rd_entry_d i x r := by
    refine Iff.trans ?_ (assign.2 i x).symm
    exact ⟨fun ⟨a, _, ha, hx⟩ => ⟨a, ha, (tf_value_recode_l hZF tuple).mp hx⟩,
      fun ⟨a, ha, hx⟩ => ⟨a, (rd_entry_transitive_l hZ he ha).2, ha, (tf_value_recode_l hZF tuple).mpr hx⟩⟩
  have old i x (hi : M.mem i ω) : M.PairMember Q i x f ↔
      (M.mem i b ∧ ∃ a, M.mem a Z ∧ Rd_entry_d i a e ∧ Tf_value_d K n h δ a x) ∨ (¬ M.mem i b ∧ x = δ) :=
    (fill.2 i x).trans ((and_iff_right hi).trans (or_congr (and_congr Iff.rfl (value i x).symm) Iff.rfl))
  constructor
  · intro matrix i x
    by_cases hi : M.mem i ω
    · by_cases hx : M.mem x X
      · exact (matrix i hi x hx).trans (old i x hi).symm
      · exact iff_of_false (fun h => hx (hg.output_mem_of_pairMember h)) (fun h => hx (hf.output_mem_of_pairMember h))
    · exact iff_of_false (fun h => hi (hg.input_mem_of_pairMember h)) (fun h => hi (hf.input_mem_of_pairMember h))
  · exact fun agree i hi x _ => (agree i x).trans (old i x hi)

end YesMetaZFC.SetTheory.Internal
