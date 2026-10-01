import YesMetaZFC.Model.Forcing.Iteration.Closed.Interval
import YesMetaZFC.Model.Forcing.Iteration.Stage.System
import YesMetaZFC.Model.SetTheory.ClassChoice
import YesMetaZFC.SetTheory.Card.Cofinality.Composition

/-! # 极限下降链的实际下界前缀序列

状态是在指定共尾阶段压住原下降链全部投影的条件。较短闭区间逐次延长它，
类上带指标依赖选择生成模型内部函数图，每次精确保留原有前缀。
-/

namespace YesMetaZFC.Model.Forcing.Internal
open SetTheory SetTheory.Definitional.Project
universe u
variable {M : SetTheory.Structure.{u}}

def Row_cl_at_d (I : kpair_convention_l.Interpretation M) (F G f A i q : M.Domain) : Prop :=
  ∃ α B R, Entry_d M i α A ∧ Entry_d M α B F ∧ Entry_d M α R G ∧ M.mem q B ∧ Row_chain_lower_d I α R f q

def row_cl_at_m {n} (F G f A i q : Term n) : Formula 1 n :=
  .existsE (.existsE (.existsE (.conj (entry_m i.weaken.weaken.weaken (.bound 2) A.weaken.weaken.weaken)
    (.conj (entry_m (.bound 2) (.bound 1) F.weaken.weaken.weaken)
      (.conj (entry_m (.bound 2) .newest G.weaken.weaken.weaken)
        (.conj (.mem q.weaken.weaken.weaken (.bound 1))
          (row_chain_lower_m (.bound 2) .newest f.weaken.weaken.weaken q.weaken.weaken.weaken)))))))
derive_free_closed row_cl_at_m

theorem row_cl_at_sat_l (I : kpair_convention_l.Interpretation M) (hE : Extensional M) {n}
    (ρ : Env M n) (F G f A i q : Term n) : Formula.satisfies ρ (row_cl_at_m F G f A i q) ↔
      Row_cl_at_d I (F.eval ρ) (G.eval ρ) (f.eval ρ) (A.eval ρ) (i.eval ρ) (q.eval ρ) := by
  simp only [row_cl_at_m, Row_cl_at_d, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
    entry_sat_l M hE, Formula.satisfies_mem_iff, row_chain_lower_sat_l I hE, Definitional.Term.eval_weaken]
  rfl

variable (hZFC : M.Models ZFC)
local notation "hZF" => ZFC.models_zf_l hZFC
local notation "I" => kpair_interpretation_l M (And.left hZFC) (KP.exists_pair (ZF.modelsKP hZF))

theorem row_cl_thread_l {ω δ F G b β D V f A α B R p}
    (hω : M.IsOmega ω) (h : Row_system_d I δ F G b) (hD : Entry_d M β D F) (hV : Entry_d M β V G)
    (hf : Chain_d I D V D ω f) (hA : M.IsCofinalOrdinalSequence I A ω β)
    (hPast : ∀ ξ, M.mem ξ β → Row_cl_stage_d I ω F G ξ)
    (hB : Entry_d M α B F) (hR : Entry_d M α R G) (hp : M.mem p B)
    (hpf : Row_chain_lower_d I α R f p)
    (ha : ∀ i ξ, Entry_d M i ξ A → M.MemberSubset α ξ) :
    ∃ X Q q₀, M.IsSetFunctionFromTo I Q ω X ∧ Entry_d M b q₀ Q ∧ M.IsRestrictionOf I p q₀ α ∧
      (∀ i q, Entry_d M i q Q → Row_cl_at_d I F G f A i q) ∧
      ∀ i j q r ξ, M.SuccessorOf j i → Entry_d M i q Q → Entry_d M j r Q → Entry_d M i ξ A →
        M.IsRestrictionOf I q r ξ := by
  have hAF := hA.isSetFunctionFromTo
  have hβδ := (h.conditions.2.2 β).mpr ⟨D, hD⟩
  have idx {i ξ} (hi : Entry_d M i ξ A) : M.mem ξ δ :=
    h.conditions.1.transitive β hβδ ξ (hAF.output_mem_of_pairMember hi)
  obtain ⟨o, ho, hoω⟩ := hω.1.1
  have hob := hZFC.1.eq_of_same_members o b (fun x => iff_of_false (ho x) (h.empty x))
  have hbω := hob ▸ hoω
  obtain ⟨ξ₀, hξ₀β, hξ₀⟩ := hAF.2.2 b hbω
  obtain ⟨B₀, hB₀⟩ := (h.conditions.2.2 ξ₀).mp (idx hξ₀)
  obtain ⟨R₀, hR₀⟩ := (h.relations.2.2 ξ₀).mp (idx hξ₀)
  obtain ⟨q₀, hq₀, hpq₀, hq₀f⟩ := row_cl_project_l hZF (ha b ξ₀ hξ₀)
    (h.links ξ₀ β B₀ R₀ D V hB₀ hR₀ hD hV (hA.1.1.transitive.memberSubset hξ₀β))
    (hPast ξ₀ hξ₀β α B R B₀ R₀ (ha b ξ₀ hξ₀) hB hR hB₀ hR₀) hf hp hpf
  let ρ : Env M 4 := (((⟨fun _ => F, fun _ => F⟩ : Env M 1).push G).push f).push A
  let θ : BinarySchema 4 := { body := row_cl_at_m (.bound 5) (.bound 4) (.bound 3) (.bound 2) (.bound 1) .newest }
  let φ : UnarySchema 6 := {
    body := .existsE (.conj (entry_m (.bound 3) .newest (.bound 4))
      (Formula.isRestriction kpair_convention_l (.bound 2) (.bound 1) .newest)) }
  have hθ i q : θ.denote ρ i q ↔ Row_cl_at_d I F G f A i q := row_cl_at_sat_l I hZFC.1 _ _ _ _ _ _ _
  have hφ i q r : φ.denote ((ρ.push i).push q) r ↔ ∃ ξ, Entry_d M i ξ A ∧ M.IsRestrictionOf I q r ξ := by
    simp only [UnarySchema.denote, φ, Formula.satisfies_exists_iff, Formula.satisfies_conj_iff,
      entry_sat_l M hZFC.1, Formula.satisfies_isRestriction_iff I]
    rfl
  obtain ⟨X, Q, hQ, hz, hv, hs⟩ := ZFC.class_indexed_choice_l I hZFC θ φ ρ hω h.empty
    ((hθ b q₀).mpr ⟨ξ₀, B₀, R₀, hξ₀, hB₀, hR₀, hq₀, hq₀f⟩) (by
      intro i j q hi hij hq
      obtain ⟨ξ, B', R', hiξ, hB', hR', hqB, hqf⟩ := (hθ i q).mp hq
      obtain ⟨j', hij', hj'⟩ := hω.1.2 i hi
      have hj : M.mem j ω := Structure.SuccessorOf.eq hZFC.1 hij' hij ▸ hj'
      obtain ⟨ζ, hζβ, hjζ⟩ := hAF.2.2 j hj
      obtain ⟨C, hC⟩ := (h.conditions.2.2 ζ).mp (idx hjζ)
      obtain ⟨T, hT⟩ := (h.relations.2.2 ζ).mp (idx hjζ)
      have hξζ := (hA.1.1.mem hζβ).transitive.memberSubset (hA.isIncreasing.2 i hi j hj hij.predecessor_mem ξ ζ hiξ hjζ)
      obtain ⟨r, hr, hqr, hrf⟩ := row_cl_project_l hZF hξζ
        (h.links ζ β C T D V hC hT hD hV (hA.1.1.transitive.memberSubset hζβ))
        (hPast ζ hζβ ξ B' R' C T hξζ hB' hR' hC hT) hf hqB hqf
      exact ⟨r, (hθ j r).mpr ⟨ζ, C, T, hjζ, hC, hT, hr, hrf⟩, (hφ i q r).mpr ⟨ξ, hiξ, hqr⟩⟩)
  refine ⟨X, Q, q₀, hQ, hz, hpq₀, fun i q hi => (hθ i q).mp (hv i q hi), ?_⟩
  intro i j q r ξ hij hiq hjr hiξ
  obtain ⟨ζ, hiζ, hqr⟩ := (hφ i q r).mp (hs i j q r hij hiq hjr)
  exact hAF.1.2 i ζ ξ hiζ hiξ ▸ hqr

end YesMetaZFC.Model.Forcing.Internal
