import YesMetaZFC.Model.ZFC.Pure.PureSentenceTransfer
import YesMetaZFC.Model.Henkin.OpenCompleteness

/-! # 原支撑语言与纯隶属语言的开放公式传输

参数列按解释逐排序映射，环境按同一变量映射回读。全部 binder 及公式递归复用关系翻译。
-/
namespace YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOpenTransfer
open Nonlogical.BasicSetTheory
open _root_.YesMetaZFC.Automation RelationalTranslation
set_option autoImplicit false
attribute [local implicit_reducible] _root_.YesMetaZFC.SetTheory.signature Expansion.model
universe x

abbrev pureContext_m (parameters : SetContext) := parameters.map PureCompletedStage.interpretation.sort

/-- 纯参数列的变量回到对应源槽位；只递归变量，不遍历公式。 -/
def sourceVariable_m : {parameters : SetContext} → {s : _root_.YesMetaZFC.SetTheory.SetSort} →
    Variable (pureContext_m parameters) s → Variable parameters SetSort.set
  | .set :: _, _, .here => .here
  | _ :: _, _, .there v => .there (sourceVariable_m v)

def embed_m {parameters : SetContext} (φ : OpenFormula ℒ (pureContext_m parameters)) :
    SetOpenFormula parameters :=
  formula PureSentenceTransfer.inclusion_m (fun {s} (v : Variable [] s) => nomatch v)
    (fun v => .fvar (sourceVariable_m v)) φ

noncomputable def translate_m {parameters : SetContext} (φ : SetOpenFormula parameters) :
    OpenFormula ℒ (pureContext_m parameters) :=
  openFormula PureCompletedStage.interpretation φ

noncomputable def sourceEnv_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) {parameters : SetContext}
    (env : Env ℳ [] (pureContext_m parameters)) :
    Env (PureCompletedStage.expansion hℳ).model [] parameters :=
  sourceEnv (PureCompletedStage.expansion hℳ) env
    (fun {s} (v : Variable [] s) => nomatch v)
    (fun v => .fvar (mapVariable PureCompletedStage.interpretation v))

def reductEnv_m {𝒩 : Structure.{0,0,0,x} signature} {parameters : SetContext}
    (env : Env 𝒩 [] parameters) : Env (PureProjectEmbedding.reduct 𝒩) [] (pureContext_m parameters) :=
  sourceEnv (PureSentenceTransfer.reductExpansion_m 𝒩) env
    (fun {s} (v : Variable [] s) => nomatch v) (fun v => .fvar (sourceVariable_m v))

theorem translate_satisfies_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) {parameters : SetContext}
    (env : Env ℳ [] (pureContext_m parameters)) (φ : SetOpenFormula parameters) :
    (translate_m φ).satisfies env ↔ φ.satisfies (sourceEnv_m hℳ env) := by
  unfold translate_m openFormula sourceEnv_m
  refine Iff.trans ?_ (formula_correct (PureCompletedStage.expansion hℳ) (PureCompletedStage.realizes hℳ) env
    (fun {s} (v : Variable [] s) => nomatch v)
    (fun v => .fvar (mapVariable PureCompletedStage.interpretation v)) φ)
  apply Iff.of_eq
  congr 2
  funext s v
  cases v

theorem embed_satisfies_m (𝒩 : Structure.{0,0,0,x} signature) {parameters : SetContext}
    (env : Env 𝒩 [] parameters) (φ : OpenFormula ℒ (pureContext_m parameters)) :
    (embed_m φ).satisfies env ↔ φ.satisfies (reductEnv_m env) :=
  formula_correct (PureSentenceTransfer.reductExpansion_m 𝒩)
    (PureSentenceTransfer.reduct_realizes_m 𝒩) env _ _ φ

theorem translate_derives_m {parameters : SetContext} {φ : SetOpenFormula parameters}
    (h : Derives intrinsic_zfc_theory [] φ) : Derives PureModel.theory [] (translate_m φ) := by
  apply SemanticTransfer.derives_open_m PureRosserSchedule.target
  intro ℳ hℳ env
  exact (translate_satisfies_m hℳ env φ).mpr
    (h.sound (PureZFCModels.models hℳ) (sourceEnv_m hℳ env) (by intro ψ hψ; cases hψ))

theorem embed_derives_m {parameters : SetContext} {φ : OpenFormula ℒ (pureContext_m parameters)}
    (h : Derives PureModel.theory [] φ) : Derives intrinsic_zfc_theory [] (embed_m φ) := by
  apply SemanticTransfer.derives_open_m PureRosserSchedule.source
  intro 𝒩 h𝒩 env
  exact (embed_satisfies_m 𝒩 env φ).mpr
    (h.sound (PureZFCModels.reduct_models h𝒩) (reductEnv_m env) (by intro ψ hψ; cases hψ))

theorem map_sourceVariable_m {parameters : SetContext}
    (v : Variable (pureContext_m parameters) PureModel.setSort) :
    mapVariable PureCompletedStage.interpretation (sourceVariable_m v) = v := by
  induction parameters with
  | nil => cases v
  | cons s parameters ih =>
    cases s
    cases v with
    | here => rfl
    | there v => exact congrArg Variable.there (ih v)

/-- 在同一任意纯模型环境中，嵌入后再规范解释保留原公式真值。 -/
theorem embed_canonical_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) {parameters : SetContext}
    (env : Env ℳ [] (pureContext_m parameters)) (φ : OpenFormula ℒ (pureContext_m parameters)) :
    (embed_m φ).satisfies (sourceEnv_m hℳ env) ↔ φ.satisfies env := by
  -- 只整理单排序模型的记录，公式和量词的传输仍调用通用可靠性。
  cases ℳ with
  | mk C hn f r =>
    obtain ⟨X, rfl⟩ : ∃ X : Type x, C = fun _ => X := by
      refine ⟨C PureModel.setSort, ?_⟩
      funext s
      cases s
      rfl
    have hf : f = (fun symbol => nomatch symbol) := by
      funext symbol
      cases symbol
    subst f
    let E : Expansion PureSentenceTransfer.inclusion_m (PureCompletedStage.expansion hℳ).model :=
      { function := fun symbol => nomatch symbol
        relation := r }
    have hE : Realizes E := by
      constructor
      · intro symbol; cases symbol
      · intro symbol args
        cases symbol
        cases args with | cons a rest =>
        cases rest with | cons b rest =>
        cases rest
        rfl
    have h := formula_correct E hE (sourceEnv_m hℳ env)
      (fun {s} (v : Variable [] s) => nomatch v) (fun v => .fvar (sourceVariable_m v)) φ
    have hEnv : sourceEnv E (sourceEnv_m hℳ env)
        (fun {s} (v : Variable [] s) => nomatch v) (fun v => .fvar (sourceVariable_m v)) = env := by
      apply Env.ext
      · intro s v; cases v
      · intro s v
        cases s
        change env.freeVal (mapVariable PureCompletedStage.interpretation (sourceVariable_m v)) = env.freeVal v
        rw [map_sourceVariable_m]
    rwa [hEnv] at h


theorem sourceEnv_push_m {ℳ : Structure.{0,0,0,x} ℒ}
    (hℳ : Theory.Models ℳ PureModel.theory) {parameters : SetContext}
    (env : Env ℳ [] (pureContext_m parameters)) (a : PureModel.Carrier ℳ) :
    sourceEnv_m hℳ (parameters := SetSort.set :: parameters) (env.pushFree a) =
      (sourceEnv_m hℳ env).pushFree a := by
  apply Env.ext
  · intro s v; cases v
  · intro s v; cases v <;> rfl

theorem translate_embed_m {parameters : SetContext}
    (φ : OpenFormula ℒ (pureContext_m parameters)) :
    Derives PureModel.theory [] (.iff (translate_m (embed_m φ)) φ) := by
  apply SemanticTransfer.derives_open_m PureRosserSchedule.target
  intro ℳ hℳ env
  exact (translate_satisfies_m hℳ env (embed_m φ)).trans (embed_canonical_m hℳ env φ)

theorem derives_iff_m {parameters : SetContext}
    (φ : OpenFormula ℒ (pureContext_m parameters)) :
    Derives intrinsic_zfc_theory [] (embed_m φ) ↔ Derives PureModel.theory [] φ :=
  ⟨fun h => Derives.iff_elim_left (translate_embed_m φ) (translate_derives_m h), embed_derives_m⟩

end YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC.PureOpenTransfer
