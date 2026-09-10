import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.InternalHornReflection
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceSyntaxRank
import YesMetaZFC.Logic.FirstOrder.FormalSystem.Metatheory.ProofT.ZFC.PureSourceStrongInduction

/-! # 原一般语法图的内部正反射

项、参数列和公式共同按输入语法码强归纳，覆盖全部内部自然数。
归纳正文是实际对象公式，量词下增长的上下文不影响输入秩。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
open Nonlogical.BasicSetTheory PureFinalArithmetic PureSourceCoding PureSourceInstantiation PureSourceInfinity PureSourceNumerals
open PureSourceTraceComposition PureSourceHornConstruction PureSourceSyntaxRank ReducedProofCodeSemantics
open _root_.YesMetaZFC.Automation RelationalTranslation ObjectHornSemantics ObjectSyntaxReflection
set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local irreducible] ReducedProofPresentation.presentation ReducedProofCodeSemantics.ProvableCode
attribute [local implicit_reducible] Expansion.model PureProjectEmbedding.reduct
universe x
variable {𝒩 : Structure.{0,0,0,x} signature}

def SyntaxAt (𝒩 : Structure.{0,0,0,x} signature) (input : 𝒩.Carrier .set) : Prop :=
  ∀ row : Row (𝒩.Carrier .set), Natural 𝒩 row → row.input = input →
    Witness (ObjectHorn.step ObjectFormulaSyntax.rules) (Value 𝒩 row) →
      HornProv 𝒩 ObjectFormulaSyntax.rules (Value 𝒩 row)

theorem syntaxAt_satisfies (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {bound free : SetContext} (env : Env 𝒩 bound free) (input : SetTerm bound free)
    (hi : mem 𝒩 (input.eval env) (w 𝒩)) :
    (ObjectSyntaxReflection.atInput ReducedProofPresentation.presentation.graph input).satisfies env ↔
      SyntaxAt 𝒩 (input.eval env) := by
  simp only [ObjectSyntaxReflection.atInput, forallNatural_satisfies, allOf_satisfies,
    List.forall_mem_cons, List.not_mem_nil, forall_false, implies_true, and_true,
    implication_satisfies, horn_satisfies, hornAt_satisfies,
    Row.tag, Row.fields, node_eval, List.map_cons, List.map_nil, Term.eval_weakenFree]
  change (∀ b, mem 𝒩 b (w 𝒩) → ∀ f, mem 𝒩 f (w 𝒩) → ∀ c, mem 𝒩 c (w 𝒩) →
    (Witness (ObjectHorn.step ObjectFormulaSyntax.rules) (Value 𝒩 (.term b f (input.eval env))) →
      HornProv 𝒩 ObjectFormulaSyntax.rules (Value 𝒩 (.term b f (input.eval env)))) ∧
    (Witness (ObjectHorn.step ObjectFormulaSyntax.rules) (Value 𝒩 (.arguments b f c (input.eval env))) →
      HornProv 𝒩 ObjectFormulaSyntax.rules (Value 𝒩 (.arguments b f c (input.eval env)))) ∧
    (Witness (ObjectHorn.step ObjectFormulaSyntax.rules) (Value 𝒩 (.formula b f (input.eval env))) →
      HornProv 𝒩 ObjectFormulaSyntax.rules (Value 𝒩 (.formula b f (input.eval env))))) ↔ _
  constructor
  · intro h row hr he
    cases row with
    | term b f value =>
      change value = input.eval env at he
      subst value
      exact (h b (hr _ List.mem_cons_self) f (hr _ (by simp [Row.fields]))
        (z 𝒩) (omega_closed h𝒩).1).1
    | arguments b f count value =>
      change value = input.eval env at he
      subst value
      exact (h b (hr _ List.mem_cons_self) f (hr _ (by simp [Row.fields]))
        count (hr _ (by simp [Row.fields]))).2.1
    | formula b f value =>
      change value = input.eval env at he
      subst value
      exact (h b (hr _ List.mem_cons_self) f (hr _ (by simp [Row.fields]))
        (z 𝒩) (omega_closed h𝒩).1).2.2
  · intro h b hb f hf c hc
    exact ⟨h (.term b f (input.eval env)) (by simpa [Natural, Row.fields] using And.intro hb (And.intro hf hi)) rfl,
      h (.arguments b f c (input.eval env)) (by simpa [Natural, Row.fields] using And.intro hb (And.intro hf (And.intro hc hi))) rfl,
      h (.formula b f (input.eval env)) (by simpa [Natural, Row.fields] using And.intro hb (And.intro hf hi)) rfl⟩

theorem syntaxAt_agrees (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) :
    (ObjectSyntaxReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) ↔
    (ObjectSyntaxReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)).satisfies
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) := by
  rw [syntaxAt_satisfies h𝒩 (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) (.fvar .here) hi,
    syntaxAt_satisfies (PureZFCModels.models (PureZFCModels.reduct_models h𝒩))
      (templateEnv (.cons input .nil) : Env (canonical h𝒩) [] [.set]) (.fvar .here) (omega_agrees h𝒩 ▸ hi)]
  unfold SyntaxAt
  apply forall_congr'; intro row
  have hn : Natural 𝒩 row ↔ Natural (canonical h𝒩) row := by
    unfold Natural
    change (∀ value ∈ row.fields, mem 𝒩 value (w 𝒩)) ↔
      (∀ value ∈ row.fields, mem 𝒩 value (w (canonical h𝒩)))
    rw [← omega_agrees h𝒩]
  rw [← hn]
  apply imp_congr_right; intro hr
  apply imp_congr_right; intro _
  have he : Value 𝒩 row = Value (canonical h𝒩) row := node_agrees h𝒩 row.tag hr
  have ht := witness_agrees h𝒩 (ObjectHorn.step ObjectFormulaSyntax.rules) (Value 𝒩 row)
    (fun root hRoot trace => PureSourceHorn.step_agrees h𝒩 ObjectFormulaSyntax.rules hRoot trace)
  have hp := hornProv_agrees h𝒩 ObjectFormulaSyntax.rules (value_natural h𝒩 hr)
  exact imp_congr
    (ht.trans (iff_of_eq (congrArg (fun root => @Witness (canonical h𝒩) (ObjectHorn.step ObjectFormulaSyntax.rules) root) he)))
    (hp.trans (iff_of_eq (congrArg (HornProv (canonical h𝒩) ObjectFormulaSyntax.rules) he)))

/-- 规则装配只消费严格较小语法输入的反射结果。 -/
theorem syntax_step (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set}
    (hLower : ∀ previous, mem 𝒩 previous input → SyntaxAt 𝒩 previous) : SyntaxAt 𝒩 input := by
  intro row hr he hg
  obtain ⟨rule, hRule, values, hv, hHead, hGuards, hPremises⟩ :=
    rule_cases h𝒩 ObjectFormulaSyntax.rules (value_natural h𝒩 hr) hg
  obtain ⟨head, hHeadNat, hValue, hChildren⟩ := rule_ranked h𝒩 rule hRule values hv
  have hRank := (rank_unique h𝒩 hHeadNat hr (hValue.trans hHead.symm)).trans he
  rw [hHead]
  apply horn_rule_values h𝒩 ObjectFormulaSyntax.rules rule hRule
    (ObjectSyntaxReflection.head_variables rule hRule) values hv hGuards
  intro premise hp
  obtain ⟨child, hc, hChild, hLess⟩ := hChildren premise hp
  rw [hRank] at hLess
  rw [← hChild]
  exact hLower child.input hLess child hc rfl (hChild.symm ▸ hPremises premise hp)

theorem syntax_at_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {input : 𝒩.Carrier .set} (hi : mem 𝒩 input (w 𝒩)) : SyntaxAt 𝒩 input := by
  let property : SetOpenFormula [.set] :=
    ObjectSyntaxReflection.atInput ReducedProofPresentation.presentation.graph (.fvar .here)
  have hAll : ∀ input, mem 𝒩 input (w 𝒩) →
      property.satisfies (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) := by
    apply PureSourceInduction.strong_induction h𝒩 property .nil
    · exact fun _ hi => syntaxAt_agrees h𝒩 hi
    · intro input hi hLower
      apply (syntaxAt_satisfies h𝒩 (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) (.fvar .here) hi).mpr
      apply syntax_step h𝒩
      intro previous hp
      exact (syntaxAt_satisfies h𝒩 (templateEnv (.cons previous .nil) : Env 𝒩 [] [.set]) (.fvar .here) (member_natural h𝒩 hi hp)).mp (hLower previous hp)
  exact (syntaxAt_satisfies h𝒩 (templateEnv (.cons input .nil) : Env 𝒩 [] [.set]) (.fvar .here) hi).mp (hAll input hi)

/-- 原一般语法图的任意内部根行，包括全部项、参数列和公式规则。 -/
theorem syntax_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {root : 𝒩.Carrier .set} (hr : mem 𝒩 root (w 𝒩))
    (hg : Witness (ObjectHorn.step ObjectFormulaSyntax.rules) root) :
    HornProv 𝒩 ObjectFormulaSyntax.rules root := by
  obtain ⟨rule, hRule, values, hv, hHead, _, _⟩ := rule_cases h𝒩 ObjectFormulaSyntax.rules hr hg
  obtain ⟨head, hn, he, _⟩ := rule_ranked h𝒩 rule hRule values hv
  have hRoot : root = Value 𝒩 head := hHead.trans he.symm
  rw [hRoot] at hg ⊢
  exact syntax_at_positive h𝒩 (input_natural hn) head hn rfl hg

theorem syntax_term_positive (h𝒩 : Theory.Models 𝒩 intrinsic_zfc_theory)
    {free : SetContext} (env : Env 𝒩 [] free) (values : Nat → 𝒩.Carrier .set) (hv : NumeralValues 𝒩 values)
    (root : SetOpenTerm free) (hr : TermEvaluates env values root)
    (hg : (ObjectHorn.condition ObjectFormulaSyntax.rules root).satisfies env) :
    ProvableCode 𝒩 (formula 𝒩 values (ObjectHorn.condition ObjectFormulaSyntax.rules root)) :=
  (horn_term_transfer h𝒩 env values hv ObjectFormulaSyntax.rules root hr).mpr
    (syntax_positive h𝒩 hr.1 ((horn_satisfies env ObjectFormulaSyntax.rules root).mp hg))

theorem syntax_positive_derives : Derives intrinsic_zfc_theory []
    (ObjectHornReflection.onNaturals ReducedProofPresentation.presentation.graph ObjectFormulaSyntax.rules) := by
  apply Completeness.strong_completeness PureRosserSchedule.source
  intro 𝒩 h𝒩
  change (ObjectHornReflection.onNaturals ReducedProofPresentation.presentation.graph ObjectFormulaSyntax.rules).satisfies (Env.empty : Env 𝒩 [] [])
  unfold ObjectHornReflection.onNaturals
  rw [forallNatural_satisfies]
  intro root hr
  rw [implication_satisfies, horn_satisfies, hornAt_satisfies]
  exact syntax_positive h𝒩 hr

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.InternalNumeralReflection
