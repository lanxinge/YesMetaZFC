import YesMetaZFC.SetTheory.Descriptive.GameCompletion

/-! # 两条策略的实际对弈

按回合集 J 在两张策略图之间选择下一项。固定目标集的序数递归产生整个
内部 ω 对局，故不需要选择公理，也不要求 ω 外部标准。
-/
namespace YesMetaZFC.SetTheory.Descriptive
open Definitional.Project InnerModel Internal
universe u
variable {M : Structure.{u}} (hZF : M.Models ZF)
local notation "I" => kp_pair_l (ZF.modelsKP hZF)

theorem cg_battle_l {ω X F J σ τ : M.Domain} (hw : M.IsOmega ω)
    (space : Fseq_space_d I ω X F) (hs : Fn0_d F X σ) (ht : Fn0_d F X τ) :
    ∃ f, M.IsSetFunctionFromTo I f ω X ∧
      Cg_follows_d I true ω J σ f ∧ Cg_follows_d I false ω J τ f := by
  classical
  let ρ : Env M 5 := ⟨fun i => [τ, σ, J, X, ω].get i, fun _ => ω⟩
  let φ : BinarySchema 5 := {
    body := set[7] ⟪∃ i ∈ ⌜(.bound 6 : Term 7)⌝ₛ,
      ⌜fn0_m⌝ₚ(i, ⌜(.bound 5 : Term 7)⌝ₛ, ⌜(.bound 1 : Term 7)⌝ₛ) ∧
      ((i ∈ ⌜(.bound 4 : Term 7)⌝ₛ ∧
        ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ, ⌜(.newest : Term 7)⌝ₛ, ⌜(.bound 3 : Term 7)⌝ₛ)) ∨
       (¬ (i ∈ ⌜(.bound 4 : Term 7)⌝ₛ) ∧
        ⌜rd_entry0_m⌝ₚ(⌜(.bound 1 : Term 7)⌝ₛ, ⌜(.newest : Term 7)⌝ₛ, ⌜(.bound 2 : Term 7)⌝ₛ)))⟫ }
  have sat g v : φ.denote ρ g v ↔ ∃ i, M.mem i ω ∧ Fn0_d i X g ∧
      ((M.mem i J ∧ Rd_entry_d g v σ) ∨ (¬ M.mem i J ∧ Rd_entry_d g v τ)) := by
    simp only [φ, BinarySchema.denote, Formula.satisfies_existsMem_iff, Formula.satisfies_conj_iff,
      fn0_sat_l hZF.1, Formula.satisfies_disj_iff, Formula.satisfies_mem_iff,
      Formula.satisfies_neg_iff, rd_entry0_sat_l hZF.1, Definitional.Term.eval_weaken]; rfl
  have function : M.IsClassFunctionOnSequencesInBelow I (φ.denote ρ) ω X := by
    rintro g ⟨_, i, hi, _, fg⟩
    have fg₀ := fn0_of_function_l (ZF.modelsKP hZF) fg
    have hg := (space g).mpr ⟨i, hi, fg⟩
    have total : ∃ v, φ.denote ρ g v := by
      by_cases turn : M.mem i J
      · obtain ⟨v, _, hv⟩ := hs.2.1 g hg
        exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inl ⟨turn, hv⟩⟩⟩
      · obtain ⟨v, _, hv⟩ := ht.2.1 g hg
        exact ⟨v, (sat g v).mpr ⟨i, hi, fg₀, Or.inr ⟨turn, hv⟩⟩⟩
    obtain ⟨v, hv⟩ := total
    refine ⟨v, hv, fun w hw => ?_⟩
    obtain ⟨k, _, fk, hk⟩ := (sat g v).mp hv
    obtain ⟨l, _, fl, hl⟩ := (sat g w).mp hw
    have ek := fk.domain_eq_l hZF.1 fg₀
    have el := fl.domain_eq_l hZF.1 fg₀
    subst k l
    rcases hl with ⟨turn, hw⟩ | ⟨turn, hw⟩ <;> rcases hk with ⟨own, hv⟩ | ⟨own, hv⟩
    · exact (fn0_function_l (ZF.modelsKP hZF) hs).1.2 g w v hw hv
    · exact (own turn).elim
    · exact (turn own).elim
    · exact (fn0_function_l (ZF.modelsKP hZF) ht).1.2 g w v hw hv
  have into : M.MapsSequencesInBelowInto I (φ.denote ρ) ω X := by
    intro g v _ hv
    obtain ⟨_, _, _, ⟨_, hv⟩ | ⟨_, hv⟩⟩ := (sat g v).mp hv
    · exact (hs.bound_l hv).2
    · exact (ht.bound_l hv).2
  obtain ⟨f, rec⟩ := ZF.recursiveSequenceIn_exists hZF I ρ φ
    (hw.isOrdinal hZF) (hw.isOrdinal hZF) (Or.inl rfl) function into
  have read i v (hi : M.mem i ω) (hv : Rd_entry_d i v f) : ∃ g, M.IsRestrictionOf I g f i ∧
      ((M.mem i J ∧ Rd_entry_d g v σ) ∨ (¬ M.mem i J ∧ Rd_entry_d g v τ)) := by
    obtain ⟨g, cut, step⟩ := rec.2 i hi v hv
    obtain ⟨k, _, fk, step⟩ := (sat g v).mp step
    have eq := fk.domain_eq_l hZF.1 (fn0_of_function_l (ZF.modelsKP hZF)
      (cut.isSetFunctionFromTo rec.1.2 (hw.transitive hZF i hi)))
    exact ⟨g, cut, eq ▸ step⟩
  refine ⟨f, rec.1.2, ?_, ?_⟩
  · intro i hi turn h cut v hv
    obtain ⟨g, cut', ⟨_, value⟩ | ⟨bad, _⟩⟩ := read i v hi hv
    · exact cut'.eq hZF.1 cut ▸ value
    · exact (bad turn).elim
  · intro i hi turn h cut v hv
    obtain ⟨g, cut', ⟨bad, _⟩ | ⟨_, value⟩⟩ := read i v hi hv
    · exact (turn bad).elim
    · exact cut'.eq hZF.1 cut ▸ value

end YesMetaZFC.SetTheory.Descriptive
